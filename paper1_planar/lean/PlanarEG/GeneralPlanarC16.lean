import PlanarEG.GraphCore
import PlanarEG.CertTree
import PlanarEG.CertTree16
import PlanarEG.CubicDischarging
import PlanarEG.GenPlanarBFData
import PlanarEG.GenPlanarC5DP1Data
import PlanarEG.GenPlanarC5DP2Data
import PlanarEG.GenPlanarC6DPData
import PlanarEG.GenPlanarC3Rim1Data
import PlanarEG.GenPlanarC3Rim2Data
import PlanarEG.GenPlanarC5Rim1Data
import PlanarEG.GenPlanarC5V9A
import PlanarEG.GenPlanarC5V9B
import PlanarEG.GenPlanarC5V9C
import PlanarEG.GenPlanarC5V9D

/-!
# PlanarEG.GeneralPlanarC16

Kernel-verified discharging contradictions, arithmetic absorption/budget/`F_10` lemmas,
proof-carrying Bellman-Ford & cyclic-DP bounds, and strict-schema explicit simple dyadic
cycle (`C_4, C_8, C_16`) outer-rim quotient certificates supporting **Main Theorem 3**
(*General Planar `δ ≥ 3` `C_16` Trilogy — `C_3`-free, `C_5`-free [ZERO `R10`], & `C_6`-free*).

**Scope note:** This module kernel-verifies the combinatorial vertex-face discharging
contradiction, universal vertex-absorption inequalities, exact budget & `F_10` 5-triangle
combinatorial bounds, packed BF/DP state-graph bounds, and strict face-schema + simple
`C_4/C_8/C_16` cycle witnesses for all `1,260 + 3,501 + 45 = 4,806` outer-rim quotients.
Graph-level cut reductions, non-adjacent `V_{≥ 4}` / rim-geometry reductions, token-mapping
soundness, and cycle-preserving quotient lifts are proved in the paper manuscript (`manuscript/planar_eg.tex`),
and DP automaton collapse simulations are independently verified in `cert/verify_parity_and_dp.py`.

Pure Lean 4 (`import Std`, ZERO Mathlib, ZERO `sorry`, ZERO `axiom`, ZERO `native_decide`).
-/

namespace PlanarEG

open CertTree
open GenPlanarBFData
open GenPlanarC5DP1Data
open GenPlanarC5DP2Data
open GenPlanarC6DPData
open GenPlanarC3Rim1Data
open GenPlanarC3Rim2Data
open GenPlanarC5Rim1Data
open GenPlanarC5V9A
open GenPlanarC5V9B
open GenPlanarC5V9C
open GenPlanarC5V9D

/-! ## 1. General Vertex-Face Discharging Master Contradiction & `C_16` Weld Bridge -/

/-- Element tag for unified vertex-face discharging on a `PlaneMap n`. -/
inductive VFElem (n : Nat) where
  | vert (v : Fin n)
  | face (f : List (Fin n))

private theorem sumInt_append (a b : List Int) :
    sumInt (a ++ b) = sumInt a + sumInt b := by
  induction a with
  | nil => simp [sumInt]
  | cons x xs ih =>
    simp only [List.cons_append, sumInt, ih]
    omega

/-- **General Vertex-Face Discharging Master Contradiction (`general_planar_discharging_contradiction`):**
For ANY `PlaneMap n` (arbitrary vertex degrees & arbitrary connectivity!), positive common
denominator `S > 0`, and charge-conserving transfers between vertices and faces:
if every non-frozen vertex and non-frozen face ends with scaled final charge `≤ 0`, and the
frozen elements sum to `< 12 * S` (e.g., `≤ 8 * S` for `C_3`-free or `≤ 10 * S` for `C_5`/`C_6`-free),
then `False`! -/
theorem general_planar_discharging_contradiction {n : Nat} (M : PlaneMap n)
    (isFrozen : VFElem n → Bool) (S : Int) (_hS : S > 0)
    (inCh outCh cFin : VFElem n → Int)
    (hdefV : ∀ v : Fin n, cFin (.vert v) = S * ((6 : Int) - 2 * (M.graph.deg v : Int)) + inCh (.vert v) - outCh (.vert v))
    (hdefF : ∀ f ∈ M.faces, cFin (.face f) = S * ((6 : Int) - (f.length : Int)) + inCh (.face f) - outCh (.face f))
    (hbal : sumInt (((List.finRange n).map VFElem.vert ++ M.faces.map VFElem.face).map inCh) =
            sumInt (((List.finRange n).map VFElem.vert ++ M.faces.map VFElem.face).map outCh))
    (hcleanV : ∀ v : Fin n, isFrozen (.vert v) = false → cFin (.vert v) ≤ 0)
    (hcleanF : ∀ f ∈ M.faces, isFrozen (.face f) = false → cFin (.face f) ≤ 0)
    (hfrozen : sumInt ((((List.finRange n).map VFElem.vert ++ M.faces.map VFElem.face).filter isFrozen).map cFin) < 12 * S) :
    False := by
  let elems : List (VFElem n) := (List.finRange n).map VFElem.vert ++ M.faces.map VFElem.face
  let c0 : VFElem n → Int := fun e => match e with
    | .vert v => S * ((6 : Int) - 2 * (M.graph.deg v : Int))
    | .face f => S * ((6 : Int) - (f.length : Int))
  have hinit : sumInt (elems.map c0) = 12 * S := by
    show sumInt (((List.finRange n).map VFElem.vert ++ M.faces.map VFElem.face).map c0) = 12 * S
    rw [List.map_append, sumInt_append, List.map_map, List.map_map]
    have hV : sumInt ((List.finRange n).map (c0 ∘ VFElem.vert)) =
              S * sumInt ((List.finRange n).map fun v => (6 : Int) - 2 * (M.graph.deg v : Int)) := by
      show sumInt ((List.finRange n).map fun v => S * ((6 : Int) - 2 * (M.graph.deg v : Int))) = _
      exact sumInt_map_mul_left _ _ _
    have hF : sumInt (M.faces.map (c0 ∘ VFElem.face)) =
              S * sumInt (M.faces.map fun f => (6 : Int) - (f.length : Int)) := by
      show sumInt (M.faces.map fun f => S * ((6 : Int) - (f.length : Int))) = _
      exact sumInt_map_mul_left _ _ _
    rw [hV, hF, ← Int.mul_add, euler_vertex_face_sum M]
    omega
  have hdef : ∀ e ∈ elems, cFin e = c0 e + inCh e - outCh e := by
    intro e he
    rcases List.mem_append.mp he with hv | hf
    · rcases List.mem_map.mp hv with ⟨v, _, rfl⟩
      exact hdefV v
    · rcases List.mem_map.mp hf with ⟨f, hfm, rfl⟩
      exact hdefF f hfm
  have hcons : sumInt (elems.map cFin) = sumInt (elems.map c0) :=
    charge_conserved_of_transfers elems c0 cFin inCh outCh hdef hbal
  have hclean : ∀ e ∈ elems, isFrozen e = false → cFin e ≤ 0 := by
    intro e he hnf
    rcases List.mem_append.mp he with hv | hf
    · rcases List.mem_map.mp hv with ⟨v, _, rfl⟩
      exact hcleanV v hnf
    · rcases List.mem_map.mp hf with ⟨f, hfm, rfl⟩
      exact hcleanF f hfm hnf
  exact charge_conservation_contradiction elems isFrozen c0 cFin S hinit hcons hclean hfrozen

/-! ### Weld-to-`FinGraph` `C_16` Dyadic Cycle Bridge (`weldFaceGraph_hasDyadicCycle16`) -/

private theorem allLtNat16_head {n x : Nat} {xs : List Nat}
    (h : allLtNat n (x :: xs) = true) : x < n := by
  unfold allLtNat at h
  cases hx : Nat.blt x n
  · rw [hx] at h; cases h
  · unfold Nat.blt at hx; have := Nat.le_of_ble_eq_true hx; omega

private theorem allLtNat16_tail {n x : Nat} {xs : List Nat}
    (h : allLtNat n (x :: xs) = true) : allLtNat n xs = true := by
  unfold allLtNat at h
  cases hx : Nat.blt x n
  · rw [hx] at h; cases h
  · rw [hx] at h; exact h

private def toFinList16 (n : Nat) : (xs : List Nat) → allLtNat n xs = true → List (Fin n)
  | [], _ => []
  | x :: xs, h => ⟨x, allLtNat16_head h⟩ :: toFinList16 n xs (allLtNat16_tail h)

private theorem toFinList16_length (n : Nat) :
    ∀ (xs : List Nat) (h : allLtNat n xs = true), (toFinList16 n xs h).length = xs.length
  | [], _ => rfl
  | _ :: xs, h => congrArg Nat.succ (toFinList16_length n xs (allLtNat16_tail h))

private theorem toFinList16_getElem (n : Nat) :
    ∀ (xs : List Nat) (h : allLtNat n xs = true) (i : Nat) (hi : i < xs.length),
      ((toFinList16 n xs h)[i]'(by rw [toFinList16_length]; exact hi)).val = xs[i]'hi
  | [], _, _, hi => absurd hi (Nat.not_lt_zero _)
  | _ :: _, _, 0, _ => rfl
  | _ :: xs, h, j + 1, hi =>
    toFinList16_getElem n xs (allLtNat16_tail h) j (Nat.lt_of_succ_lt_succ hi)

private theorem nodup_of_nodupNat16 :
    ∀ {xs : List Nat}, nodupNat xs = true → xs.Nodup
  | [], _ => List.nodup_nil
  | x :: xs, h => by
    unfold nodupNat at h
    cases hc : xs.contains x
    · rw [hc] at h
      have hmem : x ∉ xs := fun hm => by
        have := List.contains_iff_mem.mpr hm; rw [this] at hc; cases hc
      exact List.nodup_cons.mpr ⟨hmem, nodup_of_nodupNat16 h⟩
    · rw [hc] at h; cases h

private theorem mem_toFinList16_val (n : Nat) :
    ∀ (xs : List Nat) (h : allLtNat n xs = true) (y : Fin n),
      y ∈ toFinList16 n xs h → y.val ∈ xs
  | [], _, _, hy => by cases hy
  | x :: xs, h, y, hy => by
    rcases List.mem_cons.mp hy with rfl | hrest
    · exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem x (mem_toFinList16_val n xs (allLtNat16_tail h) y hrest)

private theorem toFinList16_nodup (n : Nat) :
    ∀ (xs : List Nat) (hlt : allLtNat n xs = true), xs.Nodup → (toFinList16 n xs hlt).Nodup
  | [], _, _ => List.nodup_nil
  | x :: xs, hlt, hnd => by
    rcases List.nodup_cons.mp hnd with ⟨hxnot, hndxs⟩
    refine List.nodup_cons.mpr ⟨?_, toFinList16_nodup n xs (allLtNat16_tail hlt) hndxs⟩
    intro hmem
    exact hxnot (mem_toFinList16_val n xs (allLtNat16_tail hlt) ⟨x, allLtNat16_head hlt⟩ hmem)

private theorem nodup16_getElem_ne {α : Type} :
    ∀ (l : List α), l.Nodup → ∀ (i j : Nat) (hi : i < l.length) (hj : j < l.length),
      i ≠ j → l[i]'hi ≠ l[j]'hj
  | [], _, _, _, hi, _, _ => absurd hi (Nat.not_lt_zero _)
  | x :: xs, hnd, i, j, hi, hj, hne => by
    rcases List.nodup_cons.mp hnd with ⟨hxnot, hndxs⟩
    cases i with
    | zero =>
      cases j with
      | zero => exact absurd rfl hne
      | succ j' =>
        intro heq
        simp only [List.getElem_cons_zero, List.getElem_cons_succ] at heq
        exact hxnot (heq ▸ List.getElem_mem (Nat.lt_of_succ_lt_succ hj))
    | succ i' =>
      cases j with
      | zero =>
        intro heq
        simp only [List.getElem_cons_zero, List.getElem_cons_succ] at heq
        exact hxnot (heq.symm ▸ List.getElem_mem (Nat.lt_of_succ_lt_succ hi))
      | succ j' =>
        exact nodup16_getElem_ne xs hndxs i' j' (Nat.lt_of_succ_lt_succ hi)
          (Nat.lt_of_succ_lt_succ hj) (fun h => hne (congrArg Nat.succ h))

private theorem closedWalk16_go_adj (faces : List (List Nat)) (x : Nat) :
    ∀ (prev : Nat) (xs : List Nat),
      isFaceGraphClosedWalk.go faces x prev xs = true →
      (∀ (i : Nat) (hi : i < (prev :: xs).length),
        facesHaveEdge faces ((prev :: xs)[i]'hi)
          (if h2 : i + 1 < (prev :: xs).length then (prev :: xs)[i + 1]'h2 else x) = true)
  | prev, [], h, i, hi => by
    have hi0 : i = 0 := by simp at hi; omega
    subst hi0; simpa [isFaceGraphClosedWalk.go] using h
  | prev, y :: ys, h, i, hi => by
    unfold isFaceGraphClosedWalk.go at h
    cases he : facesHaveEdge faces prev y
    · rw [he] at h; cases h
    · rw [he] at h
      cases i with
      | zero => simpa using he
      | succ j =>
        have hj : j < (y :: ys).length := Nat.lt_of_succ_lt_succ hi
        have ih := closedWalk16_go_adj faces x y ys h j hj
        by_cases h2 : j + 1 < (y :: ys).length
        · have h2' : j + 1 + 1 < (prev :: y :: ys).length := Nat.succ_lt_succ h2
          simp only [h2, ↓reduceDIte] at ih
          simp only [h2', ↓reduceDIte, List.getElem_cons_succ]; exact ih
        · have h2' : ¬(j + 1 + 1 < (prev :: y :: ys).length) := fun hc => h2 (Nat.lt_of_succ_lt_succ hc)
          simp only [h2, ↓reduceDIte] at ih
          simp only [h2', ↓reduceDIte, List.getElem_cons_succ]; exact ih

private theorem closedWalk16_adj (faces : List (List Nat)) :
    ∀ (xs : List Nat), isFaceGraphClosedWalk faces xs = true →
      ∀ (i : Nat) (hi : i < xs.length),
        facesHaveEdge faces (xs[i]'hi)
          (xs[(i + 1) % xs.length]'(Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le i) hi))) = true
  | [], h, _, hi => absurd hi (Nat.not_lt_zero _)
  | x :: xs, h, i, hi => by
    have hgo := closedWalk16_go_adj faces x x xs h i hi
    by_cases hlt : i + 1 < (x :: xs).length
    · have hmod : (i + 1) % (x :: xs).length = i + 1 := Nat.mod_eq_of_lt hlt
      simp only [hlt, ↓reduceDIte] at hgo
      have hidx : (x :: xs)[(i + 1) % (x :: xs).length]'(Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le i) hi)) =
                  (x :: xs)[i + 1]'hlt := by simp only [hmod]
      rw [hidx]; exact hgo
    · have heq : i + 1 = (x :: xs).length := by omega
      have hmod : (i + 1) % (x :: xs).length = 0 := by rw [heq, Nat.mod_self]
      simp only [hlt, ↓reduceDIte] at hgo
      have hidx : (x :: xs)[(i + 1) % (x :: xs).length]'(Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le i) hi)) =
                  x := by simp only [hmod, List.getElem_cons_zero]
      rw [hidx]; exact hgo

/-- **Weld-to-`FinGraph` `C_16` Dyadic Cycle Bridge (`weldFaceGraph_hasDyadicCycle16`):**
Any `WeldWitness` verified by `checkWeldDyadic16` contains a genuine simple dyadic cycle
(`C_4, C_8,` or `C_16`, i.e. `HasDyadicCycleUpTo 16`) in `weldFaceGraph w`! -/
theorem weldFaceGraph_hasDyadicCycle16 (w : WeldWitness)
    (h : checkWeldDyadic16 w.numVerts w.faces w.cycle = true) :
    (weldFaceGraph w).HasDyadicCycleUpTo 16 := by
  unfold checkWeldDyadic16 at h
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at h
  rcases h with ⟨⟨⟨hlen, hlt⟩, hnd_b⟩, hwalk⟩
  have hnd : w.cycle.Nodup := nodup_of_nodupNat16 hnd_b
  let cycF : List (Fin w.numVerts) := toFinList16 w.numVerts w.cycle hlt
  have hlenF : cycF.length = w.cycle.length := toFinList16_length w.numVerts w.cycle hlt
  have hndF : cycF.Nodup := toFinList16_nodup w.numVerts w.cycle hlt hnd
  have hge3 : cycF.length ≥ 3 := by
    rw [hlenF]; rcases hlen with (h4 | h8) | h16 <;> omega
  have hsimple : (weldFaceGraph w).IsSimpleCycle cycF := by
    refine ⟨hge3, hndF, ?_⟩
    intro i hi
    have hi' : i < w.cycle.length := by rw [← hlenF]; exact hi
    let j := (i + 1) % cycF.length
    have hj : j < cycF.length := Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le i) hi)
    have hj' : j < w.cycle.length := by rw [← hlenF]; exact hj
    have hij_ne : i ≠ j := by
      show i ≠ (i + 1) % cycF.length
      by_cases hlt1 : i + 1 < cycF.length
      · rw [Nat.mod_eq_of_lt hlt1]; omega
      · have : i + 1 = cycF.length := by omega
        rw [this, Nat.mod_self]; omega
    have hne_fin : cycF[i]'hi ≠ cycF[j]'hj := nodup16_getElem_ne cycF hndF i j hi hj hij_ne
    have hedge : facesHaveEdge w.faces (cycF[i]'hi).val (cycF[j]'hj).val = true := by
      have h1 := toFinList16_getElem w.numVerts w.cycle hlt i hi'
      have h2 := toFinList16_getElem w.numVerts w.cycle hlt j hj'
      have hadj := closedWalk16_adj w.faces w.cycle hwalk i hi'
      have hj_eq : j = (i + 1) % w.cycle.length := by show (i + 1) % cycF.length = _; rw [hlenF]
      rw [h1, h2]; simpa [hj_eq] using hadj
    simp only [weldFaceGraph, Bool.and_eq_true, bne_iff_ne]
    exact ⟨hne_fin, hedge⟩
  rcases hlen with (h4 | h8) | h16
  · exact ⟨2, by omega, by decide, cycF, hsimple, by rw [hlenF, h4]⟩
  · exact ⟨3, by omega, by decide, cycF, hsimple, by rw [hlenF, h8]⟩
  · exact ⟨4, by omega, by decide, cycF, hsimple, by rw [hlenF, h16]⟩

private theorem chunks_all_dyadic16 (chunks : List (List WeldWitness))
    (hok : chunks.all checkWeldList16 = true) :
    ∀ c ∈ chunks, ∀ w ∈ c, WeldSchemaValid w ∧ (weldFaceGraph w).HasDyadicCycleUpTo 16 := by
  intro c hc w hw
  have hc_ok : checkWeldList16 c = true := List.all_eq_true.mp hok c hc
  have ⟨hsch, hcyc⟩ := checkWeldList16_eq_true hc_ok w hw
  exact ⟨weldSchema_valid_of_bool w hsch, weldFaceGraph_hasDyadicCycle16 w hcyc⟩

private theorem list_all_dyadic16 (ws : List WeldWitness)
    (hok : checkWeldList16 ws = true) :
    ∀ w ∈ ws, WeldSchemaValid w ∧ (weldFaceGraph w).HasDyadicCycleUpTo 16 := by
  intro w hw
  have ⟨hsch, hcyc⟩ := checkWeldList16_eq_true hok w hw
  exact ⟨weldSchema_valid_of_bool w hsch, weldFaceGraph_hasDyadicCycle16 w hcyc⟩

/-! ## 2. Main Theorem 3(a) — ALL `C_3`-Free General Planar Graphs (`δ ≥ 3`) → `C_4, C_8, C_16` -/

/-- **Universal `C_3`-Free Vertex Absorption (`c3free_vertex_absorption`):**
For EVERY high-degree vertex `k ≥ 4` and EVERY `c` with `2 * c ≤ k`:
`((k - 2*c + 1)/2) + c = (k + 1)/2` and
`6 - 2*k + (k - 2*c + 1)/2 + c = 6 - 2*k + (k + 1)/2 ≤ 0` (exact integer form with floor
division — tight `= 0` at `k = 4`, and strict `2*(6 - 2*k) + (k + 1) ≤ 0` for all `k ≥ 5`)! -/
theorem c3free_vertex_absorption (k c : Nat) (hk : k ≥ 4) (hc : 2 * c ≤ k) :
    (k - 2 * c + 1) / 2 + c = (k + 1) / 2 ∧
    (6 : Int) - 2 * (k : Int) + (((k - 2 * c + 1) / 2 : Nat) : Int) + (c : Int) ≤ 0 ∧
    (6 : Int) - 2 * (k : Int) + (((k + 1) / 2 : Nat) : Int) ≤ 0 := by
  have heq : (k - 2 * c + 1) / 2 + c = (k + 1) / 2 := by omega
  have h1 : (k + 1) / 2 + 6 ≤ 2 * k := by omega
  refine ⟨heq, ?_, ?_⟩
  · have h2 : (k - 2 * c + 1) / 2 + c + 6 ≤ 2 * k := by omega
    generalize (k - 2 * c + 1) / 2 = q at h2 ⊢
    omega
  · generalize (k + 1) / 2 = q at h1 ⊢
    omega

/-- **ALL `1,260` `C_3`-Free Outer-Rim Quotient Kills (`c3free_outer_rim_all_killed`):**
Every valid outer-rim quotient of `P+(6,6,6,6,7)` (`59`), `P+(6,6,6,6,9)` (`105`),
`Cor+P` (`106`), and `Cor+val` (`350 + 640 = 990`) satisfies strict `WeldSchemaValid w` and
carries a kernel-verified explicit simple `C_8` or `C_16` cycle (`HasDyadicCycleUpTo 16`)! -/
theorem c3free_outer_rim_all_killed :
    (c3P67WeldsChunks.map List.length).foldl (· + ·) 0 = 59 ∧
    (c3P69WeldsChunks.map List.length).foldl (· + ·) 0 = 105 ∧
    (c3CorPWeldsChunks.map List.length).foldl (· + ·) 0 = 106 ∧
    (c3CorVal1WeldsChunks.map List.length).foldl (· + ·) 0 +
      (c3CorVal2WeldsChunks.map List.length).foldl (· + ·) 0 = 990 ∧
    (∀ c ∈ c3P67WeldsChunks, ∀ w ∈ c, WeldSchemaValid w ∧ (weldFaceGraph w).HasDyadicCycleUpTo 16) ∧
    (∀ c ∈ c3P69WeldsChunks, ∀ w ∈ c, WeldSchemaValid w ∧ (weldFaceGraph w).HasDyadicCycleUpTo 16) ∧
    (∀ c ∈ c3CorPWeldsChunks, ∀ w ∈ c, WeldSchemaValid w ∧ (weldFaceGraph w).HasDyadicCycleUpTo 16) ∧
    (∀ c ∈ c3CorVal1WeldsChunks, ∀ w ∈ c, WeldSchemaValid w ∧ (weldFaceGraph w).HasDyadicCycleUpTo 16) ∧
    (∀ c ∈ c3CorVal2WeldsChunks, ∀ w ∈ c, WeldSchemaValid w ∧ (weldFaceGraph w).HasDyadicCycleUpTo 16) := by
  refine ⟨c3P67WeldsChunks_count, c3P69WeldsChunks_count, c3CorPWeldsChunks_count, ?_,
    chunks_all_dyadic16 c3P67WeldsChunks c3P67WeldsChunks_ok,
    chunks_all_dyadic16 c3P69WeldsChunks c3P69WeldsChunks_ok,
    chunks_all_dyadic16 c3CorPWeldsChunks c3CorPWeldsChunks_ok,
    chunks_all_dyadic16 c3CorVal1WeldsChunks c3CorVal1WeldsChunks_ok,
    chunks_all_dyadic16 c3CorVal2WeldsChunks c3CorVal2WeldsChunks_ok⟩
  rw [c3CorVal1WeldsChunks_count, c3CorVal2WeldsChunks_count]

/-- **`C_3`-Free Clean Big Faces `d ≥ 14` Bellman-Ford Bound (`c3free_clean_d_ge_14_bound`):**
With `scale = 20`, slope `11/20`, every closed cycle of length `d ≥ 14` has `recvScaled ≤ 11 * d ≤ 20 * (d - 6)`. -/
theorem c3free_clean_d_ge_14_bound (d : Nat) (hd : d ≥ 14)
    {u k : Nat} {recvScaled : Int}
    (hc : DirWalk (PackedEdge c3D14Edges) u u k (recvScaled - 11 * (d : Int))) :
    recvScaled ≤ 20 * ((d : Int) - 6) := by
  have hcyc := packedCycle_bound c3D14Pi c3D14Edges c3D14Edges_ok hc
  omega

/-- **`C_3`-Free Clean Small Faces `d ∈ {6, 7, 9, 10, 11, 12, 13}` Cyclic DP Bounds:** -/
theorem c3free_clean_small_bounds :
    (∀ {k : Nat} {totW : Int}, DirWalk (PackedEdge c3CleanD6Edges) 0 1 k totW → totW ≤ 20 * (6 - 6)) ∧
    (∀ {k : Nat} {totW : Int}, DirWalk (PackedEdge c3CleanD7Edges) 0 1 k totW → totW ≤ 20 * (7 - 6)) ∧
    (∀ {k : Nat} {totW : Int}, DirWalk (PackedEdge c3CleanD9Edges) 0 1 k totW → totW ≤ 20 * (9 - 6)) ∧
    (∀ {k : Nat} {totW : Int}, DirWalk (PackedEdge c3CleanD10Edges) 0 1 k totW → totW ≤ 20 * (10 - 6)) ∧
    (∀ {k : Nat} {totW : Int}, DirWalk (PackedEdge c3CleanD11Edges) 0 1 k totW → totW ≤ 20 * (11 - 6)) ∧
    (∀ {k : Nat} {totW : Int}, DirWalk (PackedEdge c3CleanD12Edges) 0 1 k totW → totW ≤ 20 * (12 - 6)) ∧
    (∀ {k : Nat} {totW : Int}, DirWalk (PackedEdge c3CleanD13Edges) 0 1 k totW → totW ≤ 20 * (13 - 6)) :=
  ⟨fun hp => dag_potential_path_bound c3CleanD6U c3CleanD6Edges c3CleanD6Budget c3CleanD6Edges_ok c3CleanD6_src_zero c3CleanD6_snk_le hp,
   fun hp => dag_potential_path_bound c3CleanD7U c3CleanD7Edges c3CleanD7Budget c3CleanD7Edges_ok c3CleanD7_src_zero c3CleanD7_snk_le hp,
   fun hp => dag_potential_path_bound c3CleanD9U c3CleanD9Edges c3CleanD9Budget c3CleanD9Edges_ok c3CleanD9_src_zero c3CleanD9_snk_le hp,
   fun hp => dag_potential_path_bound c3CleanD10U c3CleanD10Edges c3CleanD10Budget c3CleanD10Edges_ok c3CleanD10_src_zero c3CleanD10_snk_le hp,
   fun hp => dag_potential_path_bound c3CleanD11U c3CleanD11Edges c3CleanD11Budget c3CleanD11Edges_ok c3CleanD11_src_zero c3CleanD11_snk_le hp,
   fun hp => dag_potential_path_bound c3CleanD12U c3CleanD12Edges c3CleanD12Budget c3CleanD12Edges_ok c3CleanD12_src_zero c3CleanD12_snk_le hp,
   fun hp => dag_potential_path_bound c3CleanD13U c3CleanD13Edges c3CleanD13Budget c3CleanD13Edges_ok c3CleanD13_src_zero c3CleanD13_snk_le hp⟩

/-- **`C_3`-Free Frozen `CAP` Face Charge Bound (`c3free_frozen_cap_bound`):**
1. Exact DP DAG covering ALL `d ∈ 3..24`: every frozen path to an end node at length `d - 1`
   obeys `20 * (6 - d) + totW ≤ 4 * 20` (and two frozen faces sum to `≤ 8 * 20 < 12 * 20`);
2. Universal Bellman-Ford for ALL `d ≥ 4` (slope `1/2`, excess `1/2`): `20 * (6 - d) + recvScaled ≤ 4 * 20`
   and `2 * (20 * (6 - d) + recvScaled) ≤ 8 * 20 < 12 * 20`! -/
theorem c3free_frozen_cap_bound :
    (∀ entry ∈ c3FrzEndChecks,
      ∀ u ∈ entry.2.1, ∀ {k : Nat} {totW : Int},
        DirWalk (PackedEdge c3FrzEdges) 0 u k totW →
          totW ≤ (entry.2.2 : Int) - (PI_BIAS : Int)) ∧
    (∀ d : Nat, d ≥ 4 →
      ∀ {p0 uEnd k : Nat} {coreW recvScaled : Int},
        p0 ∈ c3FrzAllInit → uEnd ∈ c3FrzAllEnds →
        DirWalk (PackedEdge c3FrzAllEdges) (p0 / WT_RADIX) uEnd k coreW →
        recvScaled - 10 * ((d : Int) - 1) = (((p0 % WT_RADIX : Nat) : Int) - (PI_BIAS : Int)) + coreW →
        20 * ((6 : Int) - (d : Int)) + recvScaled ≤ 4 * 20 ∧
        2 * (20 * ((6 : Int) - (d : Int)) + recvScaled) ≤ 8 * 20 ∧
        2 * (20 * ((6 : Int) - (d : Int)) + recvScaled) < 12 * 20) := by
  refine ⟨?_, ?_⟩
  · intro entry hentry u hu k totW hp
    have hchk : checkNodeUpper c3FrzU entry.2.2 entry.2.1 = true :=
      List.all_eq_true.mp c3Frz_ends_ok entry hentry
    have hwk := packedWalk_bound c3FrzU c3FrzEdges c3FrzEdges_ok hp
    have hup := checkNodeUpper_eq_true c3FrzU PI_BIAS entry.2.2 hchk u hu
    have h0 := c3Frz_src_zero
    omega
  · intro d hd p0 uEnd k coreW recvScaled hp0 hend hw htot
    have hi := checkInitLower_eq_true c3FrzAllPi PI_BIAS c3FrzAll_init_ok p0 hp0
    have hwk := packedWalk_bound c3FrzAllPi c3FrzAllEdges c3FrzAllEdges_ok hw
    have hu := checkNodeUpper_eq_true c3FrzAllPi PI_BIAS (10 + PI_BIAS) c3FrzAll_ends_ok uEnd hend
    omega

/-! ## 3. Main Theorem 3(b) — ALL `C_5`-Free General Planar Graphs (`δ ≥ 3`, ZERO `R10`) → `C_4, C_8, C_16` -/

/-- **Exact `C_5`-Free Discharging Budget Identities (`c5free_budget_identities`):**
Common denominator `12`:
`2/3 + 2*(7/6) = 3`, `2*(11/12) + 7/6 = 3`, `3*1 = 3`, `1 + 1/2 + 1/2 = 2`,
`3*(2/3) = 2`, `5/6 + 1/2 + 2/3 = 2`, `0 ≤ 2 - 2/3 - 7/6 ≤ 1/2`, `0 ≤ 2 - 2/3 - 1/2 ≤ 7/6`. -/
theorem c5free_budget_identities :
    8 + 2 * 14 = 36 ∧
    2 * 11 + 14 = 36 ∧
    3 * 12 = 36 ∧
    12 + 6 + 6 = 24 ∧
    3 * 8 = 24 ∧
    10 + 6 + 8 = 24 ∧
    (0 ≤ 24 - 8 - 14 ∧ 24 - 8 - 14 ≤ 6) ∧
    (0 ≤ 24 - 8 - 6 ∧ 24 - 8 - 6 ≤ 14) := by
  omega

/-! ### Kernel-Verified `F_10` 5-Triangle Exhaustive Check (`max = 47/12 < 4`) -/

private def bitOn (mask i : Nat) : Bool :=
  ((mask >>> i) &&& 1) == 1

private def f10ReqHighMask (cm : Nat) : Nat :=
  cm &&& (((cm <<< 1) ||| (cm >>> 9)) &&& 1023)

private def isIndepC10 (hm : Nat) : Bool :=
  (hm &&& (((hm <<< 1) ||| (hm >>> 9)) &&& 1023)) == 0

private def maskSubset (sub sup : Nat) : Bool :=
  (sub &&& sup) == sub

private def f10FiveTriScore12 (cm hm : Nat) : Nat :=
  let okGap (a : Nat) : Nat :=
    let bef := if a == 0 then 9 else a - 1
    let aft := if a == 9 then 0 else a + 1
    if bitOn cm bef && bitOn cm aft && !(bitOn hm a) && !(bitOn hm aft) then 1 else 0
  let step (acc i : Nat) : Nat :=
    if bitOn cm i then
      let ip1 := if i == 9 then 0 else i + 1
      if bitOn hm i || bitOn hm ip1 then acc + 8
      else
        let im1 := if i == 0 then 9 else i - 1
        let s := okGap ip1 + okGap im1
        acc + (if s == 0 then 12 else if s == 1 then 11 else 8)
    else acc
  step (step (step (step (step (step (step (step (step (step 0 0) 1) 2) 3) 4) 5) 6) 7) 8) 9

private def chooseKMasks : Nat → Nat → List Nat
  | 0, _ => [0]
  | _ + 1, 0 => []
  | k + 1, n + 1 => (chooseKMasks k n).map (fun m => m + (1 <<< n)) ++ chooseKMasks (k + 1) n

private def choose5Masks : List Nat := chooseKMasks 5 10

/-- All independent sets on `n` vertices `0..n-1` of a path (with `prevOn` tracking vertex `n` if constrained). -/
private def indepPathMasks : Nat → Bool → List Nat
  | 0, _ => [0]
  | n + 1, true => indepPathMasks n false
  | n + 1, false => (indepPathMasks n true).map (fun m => m + (1 <<< n)) ++ indepPathMasks n false

/-- All `123` independent vertex subsets of the 10-cycle `C_10` (vertex `9` off → path on `0..8`;
vertex `9` on → vertex `0` and vertex `8` off, path on `1..7` shifted by `* 2`). -/
private def indepC10Masks : List Nat :=
  indepPathMasks 9 false ++
  (indepPathMasks 7 false).map (fun m => 512 + 2 * m)

private def checkF10FiveTriMax47 : Bool :=
  choose5Masks.all fun cm =>
    let req := f10ReqHighMask cm
    indepC10Masks.all fun hm =>
      if maskSubset req hm then Nat.ble (f10FiveTriScore12 cm hm) 47 else true

private def existsF10FiveTri47 : Bool :=
  choose5Masks.any fun cm =>
    let req := f10ReqHighMask cm
    indepC10Masks.any fun hm =>
      maskSubset req hm && (f10FiveTriScore12 cm hm == 47)

set_option maxRecDepth 4096 in
/-- **`C_5`-Free `F_10` 5-Triangle Exhaustive Charge Bound (`c5free_f10_5tri_bound`):**
Across ALL `C(10, 5) = 252` placements of `5` triangles around `F_10` and ALL `123`
independent high-vertex sets `hm` containing `reqHigh(cm)`, EVERY valid configuration has
total scaled charge `≤ 47` (`47/12 < 4 = 48/12`), and exact `47/12` is achieved! -/
theorem c5free_f10_5tri_bound :
    choose5Masks.length = 252 ∧
    indepC10Masks.length = 123 ∧
    (∀ hm ∈ indepC10Masks, isIndepC10 hm = true) ∧
    (∀ cm ∈ choose5Masks, ∀ hm ∈ indepC10Masks,
      maskSubset (f10ReqHighMask cm) hm = true →
      f10FiveTriScore12 cm hm ≤ 47 ∧ f10FiveTriScore12 cm hm < 4 * 12) ∧
    (∃ cm ∈ choose5Masks, ∃ hm ∈ indepC10Masks,
      maskSubset (f10ReqHighMask cm) hm = true ∧ f10FiveTriScore12 cm hm = 47) := by
  have h1 : choose5Masks.length = 252 := by decide
  have h2 : indepC10Masks.length = 123 := by decide
  have hind : indepC10Masks.all isIndepC10 = true := by decide
  have hall : checkF10FiveTriMax47 = true := by decide
  have hex : existsF10FiveTri47 = true := by decide
  refine ⟨h1, h2, fun hm hhm => List.all_eq_true.mp hind hm hhm, ?_, ?_⟩
  · intro cm hcm hm hhm hsub
    have hcm' := List.all_eq_true.mp hall cm hcm
    have hhm' := List.all_eq_true.mp hcm' hm hhm
    simp only [hsub, ↓reduceIte] at hhm'
    have hle := Nat.le_of_ble_eq_true hhm'
    omega
  · rcases List.any_eq_true.mp hex with ⟨cm, hcm, hex2⟩
    rcases List.any_eq_true.mp hex2 with ⟨hm, hhm, hboth⟩
    simp only [Bool.and_eq_true, beq_iff_eq] at hboth
    exact ⟨cm, hcm, hm, hhm, hboth.1, hboth.2⟩

/-- **`C_5`-Free Clean Big Faces `d ≥ 18` Bellman-Ford Bound (`c5free_clean_d_ge_18_bound`):**
All `452` edges (`42` nodes, `scale = 12`, slope `b = 2/3` = `8/12`) satisfy the dual potential;
every closed cycle of length `d ≥ 18` has `recvScaled ≤ 8 * d ≤ 12 * (d - 6)`. -/
theorem c5free_clean_d_ge_18_bound (d : Nat) (hd : d ≥ 18)
    {u k : Nat} {recvScaled : Int}
    (hc : DirWalk (PackedEdge c5D18Edges) u u k (recvScaled - 8 * (d : Int))) :
    recvScaled ≤ 12 * ((d : Int) - 6) := by
  have hcyc := packedCycle_bound c5D18Pi c5D18Edges c5D18Edges_ok hc
  omega

/-- **`C_5`-Free Frozen `CAP` Bellman-Ford Bound (`c5free_frozen_cap_bound`):**
All `1,029` edges (`89` nodes, `scale = 12`, slope `b = 1`) satisfy the dual potential;
every closed cycle through `CAP#0` gives final charge `≤ 5`, so two frozen faces sum to `≤ 10 < 12`! -/
theorem c5free_frozen_cap_bound (d : Nat)
    {k : Nat} {recvScaled : Int}
    (hc : DirWalk (PackedEdge c5FrzEdges) c5FrzCapIdx c5FrzCapIdx k (recvScaled - 12 * ((d : Int) - 1))) :
    12 * ((6 : Int) - (d : Int)) + recvScaled ≤ 5 * 12 ∧
    2 * (12 * ((6 : Int) - (d : Int)) + recvScaled) < 12 * 12 := by
  have hcyc := packedCycle_bound c5FrzPi c5FrzEdges c5FrzEdges_ok hc
  omega

/-- **`C_5`-Free Clean `d ∈ {9, 10, 11, 12, 13, 14, 15, 17}` Bounds (`c5free_clean_small_bounds`):**
- `d ∈ {9, 10, 11, 12, 13, 14}`: exact cyclic DP DAGs (`scale = 120`),
- `d = 15`: plain Bellman-Ford (`10` nodes, `44` edges, `scale = 10`, slope `3/5`),
- `d = 17`: exact 17-row backward DP (`56` states, `7` start classes, `scale = 120`, `≤ 1320`). -/
theorem c5free_clean_small_bounds :
    (∀ {k : Nat} {totW : Int}, DirWalk (PackedEdge c5CleanD9Edges) 0 1 k totW → totW ≤ 120 * (9 - 6)) ∧
    (∀ {k : Nat} {totW : Int}, DirWalk (PackedEdge c5CleanD10Edges) 0 1 k totW → totW ≤ 120 * (10 - 6)) ∧
    (∀ {k : Nat} {totW : Int}, DirWalk (PackedEdge c5CleanD11Edges) 0 1 k totW → totW ≤ 120 * (11 - 6)) ∧
    (∀ {k : Nat} {totW : Int}, DirWalk (PackedEdge c5CleanD12Edges) 0 1 k totW → totW ≤ 120 * (12 - 6)) ∧
    (∀ {k : Nat} {totW : Int}, DirWalk (PackedEdge c5CleanD13Edges) 0 1 k totW → totW ≤ 120 * (13 - 6)) ∧
    (∀ {k : Nat} {totW : Int}, DirWalk (PackedEdge c5CleanD14Edges) 0 1 k totW → totW ≤ 120 * (14 - 6)) ∧
    (∀ {u k : Nat} {recvScaled : Int},
      DirWalk (PackedEdge c5D15Edges) u u k (recvScaled - 6 * 15) → recvScaled ≤ 10 * (15 - 6)) ∧
    (∀ {s z : Nat} {totW : Int}, s ∈ c5D17StartQs → z ∈ c5D17ClosingQs →
      LenWalk (PackedBwdEdge c5D17BwdEdges) s z 17 totW → totW ≤ 120 * (17 - 6)) := by
  refine ⟨
    fun hp => dag_potential_path_bound c5CleanD9U c5CleanD9Edges c5CleanD9Budget c5CleanD9Edges_ok c5CleanD9_src_zero c5CleanD9_snk_le hp,
    fun hp => dag_potential_path_bound c5CleanD10U c5CleanD10Edges c5CleanD10Budget c5CleanD10Edges_ok c5CleanD10_src_zero c5CleanD10_snk_le hp,
    fun hp => dag_potential_path_bound c5CleanD11U c5CleanD11Edges c5CleanD11Budget c5CleanD11Edges_ok c5CleanD11_src_zero c5CleanD11_snk_le hp,
    fun hp => dag_potential_path_bound c5CleanD12U c5CleanD12Edges c5CleanD12Budget c5CleanD12Edges_ok c5CleanD12_src_zero c5CleanD12_snk_le hp,
    fun hp => dag_potential_path_bound c5CleanD13U c5CleanD13Edges c5CleanD13Budget c5CleanD13Edges_ok c5CleanD13_src_zero c5CleanD13_snk_le hp,
    fun hp => dag_potential_path_bound c5CleanD14U c5CleanD14Edges c5CleanD14Budget c5CleanD14Edges_ok c5CleanD14_src_zero c5CleanD14_snk_le hp,
    ?_, ?_⟩
  · intro u k recvScaled hc
    have hcyc := packedCycle_bound c5D15Pi c5D15Edges c5D15Edges_ok hc
    omega
  · intro s z totW hs hz hp
    have hwalk : totW ≤ (c5D17Rows 17).getInt PI_BIAS s :=
      bwd_dp_upper_bound_sound (fun rem st => (c5D17Rows rem).getInt PI_BIAS st)
        (fun q => q ∈ c5D17ClosingQs) 17
        (fun q hq => by
          have hmem : q * WT_RADIX + PI_BIAS ∈ c5D17ClosingQs.map (fun x => x * WT_RADIX + PI_BIAS) :=
            List.mem_map.mpr ⟨q, hq, rfl⟩
          have hlo := checkInitLower_eq_true c5D17Row0 PI_BIAS c5D17_bwd_base_ok _ hmem
          have hdiv : (q * WT_RADIX + PI_BIAS) / WT_RADIX = q := by
            have hlt : PI_BIAS < WT_RADIX := by decide
            rw [Nat.mul_comm, Nat.mul_add_div (by decide), Nat.div_eq_of_lt hlt, Nat.add_zero]
          have hmod : (q * WT_RADIX + PI_BIAS) % WT_RADIX = PI_BIAS := by
            have hlt : PI_BIAS < WT_RADIX := by decide
            rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hlt]
          rw [hdiv, hmod] at hlo
          show 0 ≤ c5D17Row0.getInt PI_BIAS q
          omega)
        (fun _ _ _ _ ⟨c, hc, e, he, hu, hv, hl, hw⟩ rem hrem hln => by
          subst hu; subst hv; subst hl; subst hw
          exact (checkBwdEdgeChunks_eq_true c5D17Rows PI_BIAS 17 c5D17_bwd_edges_ok c hc e he).2 rem hrem hln)
        (Nat.le_refl 17) hz hp
    have hst := checkNodeUpper_eq_true c5D17Row17 PI_BIAS (1320 + PI_BIAS) c5D17_bwd_starts_ok s hs
    show totW ≤ 120 * (17 - 6)
    have h17 : c5D17Rows 17 = c5D17Row17 := rfl
    rw [h17] at hwalk
    omega

/-- **ALL `3,501` `C_5`-Free Outer-Rim Quotient Kills (`c5free_outer_rim_all_killed`):**
Every valid outer-rim quotient of `F_10 aux10` (`71`), `F_10 H6` (`385`), `vertex_abs` (`51` = `4` core + `47` `3-hex+2T`),
`F_7` (`102`, incl. `31` `F_7`-pair quotients), `T_frz+H6+T'` (`5`), and ALL `valley-9`
(`720 + 720 + 720 + 727 = 2,887`) satisfies strict `WeldSchemaValid w` and carries a
kernel-verified explicit simple `C_4, C_8,` or `C_16` cycle (`HasDyadicCycleUpTo 16`)! -/
theorem c5free_outer_rim_all_killed :
    (c5Aux10WeldsChunks.map List.length).foldl (· + ·) 0 = 71 ∧
    (c5H6WeldsChunks.map List.length).foldl (· + ·) 0 = 385 ∧
    c5VAbsWelds.length = 51 ∧
    (c5F7WeldsChunks.map List.length).foldl (· + ·) 0 = 102 ∧
    c5TFrzWelds.length = 5 ∧
    ((c5V9AWeldsChunks.map List.length).foldl (· + ·) 0 +
      (c5V9BWeldsChunks.map List.length).foldl (· + ·) 0 +
      (c5V9CWeldsChunks.map List.length).foldl (· + ·) 0 +
      (c5V9DWeldsChunks.map List.length).foldl (· + ·) 0 = 2887) ∧
    (∀ c ∈ c5Aux10WeldsChunks, ∀ w ∈ c, WeldSchemaValid w ∧ (weldFaceGraph w).HasDyadicCycleUpTo 16) ∧
    (∀ c ∈ c5H6WeldsChunks, ∀ w ∈ c, WeldSchemaValid w ∧ (weldFaceGraph w).HasDyadicCycleUpTo 16) ∧
    (∀ w ∈ c5VAbsWelds, WeldSchemaValid w ∧ (weldFaceGraph w).HasDyadicCycleUpTo 16) ∧
    (∀ c ∈ c5F7WeldsChunks, ∀ w ∈ c, WeldSchemaValid w ∧ (weldFaceGraph w).HasDyadicCycleUpTo 16) ∧
    (∀ w ∈ c5TFrzWelds, WeldSchemaValid w ∧ (weldFaceGraph w).HasDyadicCycleUpTo 16) ∧
    (∀ c ∈ c5V9AWeldsChunks, ∀ w ∈ c, WeldSchemaValid w ∧ (weldFaceGraph w).HasDyadicCycleUpTo 16) ∧
    (∀ c ∈ c5V9BWeldsChunks, ∀ w ∈ c, WeldSchemaValid w ∧ (weldFaceGraph w).HasDyadicCycleUpTo 16) ∧
    (∀ c ∈ c5V9CWeldsChunks, ∀ w ∈ c, WeldSchemaValid w ∧ (weldFaceGraph w).HasDyadicCycleUpTo 16) ∧
    (∀ c ∈ c5V9DWeldsChunks, ∀ w ∈ c, WeldSchemaValid w ∧ (weldFaceGraph w).HasDyadicCycleUpTo 16) := by
  refine ⟨c5Aux10WeldsChunks_count, c5H6WeldsChunks_count, c5VAbsWelds_len,
    c5F7WeldsChunks_count, c5TFrzWelds_len, ?_,
    chunks_all_dyadic16 c5Aux10WeldsChunks c5Aux10WeldsChunks_ok,
    chunks_all_dyadic16 c5H6WeldsChunks c5H6WeldsChunks_ok,
    list_all_dyadic16 c5VAbsWelds c5VAbsWelds_ok,
    chunks_all_dyadic16 c5F7WeldsChunks c5F7WeldsChunks_ok,
    list_all_dyadic16 c5TFrzWelds c5TFrzWelds_ok,
    chunks_all_dyadic16 c5V9AWeldsChunks c5V9AWeldsChunks_ok,
    chunks_all_dyadic16 c5V9BWeldsChunks c5V9BWeldsChunks_ok,
    chunks_all_dyadic16 c5V9CWeldsChunks c5V9CWeldsChunks_ok,
    chunks_all_dyadic16 c5V9DWeldsChunks c5V9DWeldsChunks_ok⟩
  rw [c5V9AWeldsChunks_count, c5V9BWeldsChunks_count, c5V9CWeldsChunks_count, c5V9DWeldsChunks_count]

/-! ## 4. Main Theorem 3(c) — ALL `C_6`-Free General Planar Graphs (`δ ≥ 3`) → `C_4, C_8, C_16` -/

/-- **Universal `C_6`-Free Vertex Absorption (`c6free_vertex_absorption`):**
For EVERY `k, t, p` with `t + p ≤ k / 2`:
- If `k = 4`, `6 - 2*k + (t + p) ≤ 0`;
- If `k ≥ 5`, `6 - 2*k + (2*t + p) ≤ 0`! (Proved universally for ALL `k ≥ 4`, not just `k < 200`!) -/
theorem c6free_vertex_absorption (k t p : Nat) (htp : t + p ≤ k / 2) :
    (k = 4 → (6 : Int) - 2 * (k : Int) + ((t + p : Nat) : Int) ≤ 0) ∧
    (k ≥ 5 → (6 : Int) - 2 * (k : Int) + ((2 * t + p : Nat) : Int) ≤ 0) := by
  constructor <;> intro _ <;> omega

/-- **Exact `C_6`-Free Discharging, `F_7`, & `F_10` Budget Identities (`c6free_f10_and_budget_identities`):**
Common denominator `120` (exact integer forms of every identity in `verify_theorem3_c6free`):
- `3/4 + 2*(9/8) = 3`, `4/5 + 2*(11/10) = 3`, `2*(9/10) + 6/5 = 3`
- `1/2 + 2*(3/4) = 2`, `13/12 + 1/4 + 2/3 = 2` with `13/12 ≤ 6/5`, `1/4 + 1/4 + 1/2 = 1`
- `F_7`: `(6 - 7) + 3*(1/5) ≤ 0`
- `F_10`: `5*(4/5) ≤ 4`, `3*(4/5) + 9/10 + 2/3 ≤ 4`, `4/5 + 2*(9/10) + 2*(2/3) ≤ 4`,
  `2*1 + 3*(2/3) ≤ 4`, `3*1 + 2*(1/5) ≤ 4`. -/
theorem c6free_f10_and_budget_identities :
    90 + 2 * 135 = 360 ∧
    96 + 2 * 132 = 360 ∧
    2 * 108 + 144 = 360 ∧
    60 + 2 * 90 = 240 ∧
    (130 + 30 + 80 = 240 ∧ 130 ≤ 144) ∧
    30 + 30 + 60 = 120 ∧
    (120 * (6 - 7 : Int) + 3 * 24 ≤ 0) ∧
    5 * 96 ≤ 480 ∧
    3 * 96 + 108 + 80 ≤ 480 ∧
    96 + 2 * 108 + 2 * 80 ≤ 480 ∧
    2 * 120 + 3 * 80 ≤ 480 ∧
    3 * 120 + 2 * 24 ≤ 480 := by
  omega

/-- **`C_6`-Free Clean Big Faces `d ≥ 15` Bellman-Ford Bound (`c6free_clean_d_ge_15_bound`):**
All `20` edges (`7` nodes, `scale = 20`, slope `b = 3/5` = `12/20`) satisfy the dual potential;
every closed cycle of length `d ≥ 15` has `recvScaled ≤ 12 * d ≤ 20 * (d - 6)`. -/
theorem c6free_clean_d_ge_15_bound (d : Nat) (hd : d ≥ 15)
    {u k : Nat} {recvScaled : Int}
    (hc : DirWalk (PackedEdge c6D15Edges) u u k (recvScaled - 12 * (d : Int))) :
    recvScaled ≤ 20 * ((d : Int) - 6) := by
  have hcyc := packedCycle_bound c6D15Pi c6D15Edges c6D15Edges_ok hc
  omega

/-- **`C_6`-Free Frozen `CAP` Bellman-Ford Bound (`c6free_frozen_cap_bound`):**
All `54` edges (`15` nodes, `scale = 20`, slope `b = 1`) satisfy the dual potential;
every closed cycle through `CAP#0` gives final charge `≤ 5`, so two frozen faces sum to `≤ 10 < 12`! -/
theorem c6free_frozen_cap_bound (d : Nat)
    {k : Nat} {recvScaled : Int}
    (hc : DirWalk (PackedEdge c6FrzEdges) c6FrzCapIdx c6FrzCapIdx k (recvScaled - 20 * ((d : Int) - 1))) :
    20 * ((6 : Int) - (d : Int)) + recvScaled ≤ 5 * 20 ∧
    2 * (20 * ((6 : Int) - (d : Int)) + recvScaled) < 12 * 20 := by
  have hcyc := packedCycle_bound c6FrzPi c6FrzEdges c6FrzEdges_ok hc
  omega

/-- **`C_6`-Free Clean Small Faces `d ∈ {7, 9, 11, 12, 13, 14}` Bounds (`c6free_clean_small_bounds`):**
Exact `d = 7` bound (`3 * (1/5) ≤ 1`) plus exact cyclic DP DAGs for `d ∈ {9, 11, 12, 13, 14}` (`scale = 120`). -/
theorem c6free_clean_small_bounds :
    (120 * ((6 : Int) - 7) + 3 * 24 ≤ 0) ∧
    (∀ {k : Nat} {totW : Int}, DirWalk (PackedEdge c6CleanD9Edges) 0 1 k totW → totW ≤ 120 * (9 - 6)) ∧
    (∀ {k : Nat} {totW : Int}, DirWalk (PackedEdge c6CleanD11Edges) 0 1 k totW → totW ≤ 120 * (11 - 6)) ∧
    (∀ {k : Nat} {totW : Int}, DirWalk (PackedEdge c6CleanD12Edges) 0 1 k totW → totW ≤ 120 * (12 - 6)) ∧
    (∀ {k : Nat} {totW : Int}, DirWalk (PackedEdge c6CleanD13Edges) 0 1 k totW → totW ≤ 120 * (13 - 6)) ∧
    (∀ {k : Nat} {totW : Int}, DirWalk (PackedEdge c6CleanD14Edges) 0 1 k totW → totW ≤ 120 * (14 - 6)) :=
  ⟨by omega,
   fun hp => dag_potential_path_bound c6CleanD9U c6CleanD9Edges c6CleanD9Budget c6CleanD9Edges_ok c6CleanD9_src_zero c6CleanD9_snk_le hp,
   fun hp => dag_potential_path_bound c6CleanD11U c6CleanD11Edges c6CleanD11Budget c6CleanD11Edges_ok c6CleanD11_src_zero c6CleanD11_snk_le hp,
   fun hp => dag_potential_path_bound c6CleanD12U c6CleanD12Edges c6CleanD12Budget c6CleanD12Edges_ok c6CleanD12_src_zero c6CleanD12_snk_le hp,
   fun hp => dag_potential_path_bound c6CleanD13U c6CleanD13Edges c6CleanD13Budget c6CleanD13Edges_ok c6CleanD13_src_zero c6CleanD13_snk_le hp,
   fun hp => dag_potential_path_bound c6CleanD14U c6CleanD14Edges c6CleanD14Budget c6CleanD14Edges_ok c6CleanD14_src_zero c6CleanD14_snk_le hp⟩

/-- **ALL `45` `C_6`-Free Full-Rim Quotient Kills (`c6free_outer_rim_all_killed`):**
Every single one of the `45` valid full-rim quotients across all `9` `C_6`-free patches
satisfies strict `WeldSchemaValid w` and carries a kernel-verified explicit simple `C_8`
or `C_16` cycle (`HasDyadicCycleUpTo 16`)! -/
theorem c6free_outer_rim_all_killed :
    c6RimWelds.length = 45 ∧
    ∀ w ∈ c6RimWelds, WeldSchemaValid w ∧ (weldFaceGraph w).HasDyadicCycleUpTo 16 :=
  ⟨c6RimWelds_len, list_all_dyadic16 c6RimWelds c6RimWelds_ok⟩

end PlanarEG
