import ClawFreeEG.LiftWindows
import ClawFreeEG.Treewidth3Data
import ClawFreeEG.Treewidth3Q3DataA
import ClawFreeEG.Treewidth3Q3DataB

/-!
# ClawFreeEG.Treewidth3AndBowties

Pure Lean 4 (`v4.36.0`, ZERO Mathlib, ZERO `Std`, ZERO `sorry`, ZERO `axiom`,
ZERO `native_decide`, ZERO `unsafe`/`implemented_by`/`extern`/`partial`) formalization &
kernel verification for the graph-witness, local-port-kill, and arithmetic components of
Main Theorem 4 (General `Δ ≤ 4, δ ≥ 3` Bowtie Claw-Free Reductions, `d_avg ≥ 7/2`,
`tw(H/B) ≤ 3 → C_8` or `C_16`, Dyadic-Cycle-Free Independent-Bowtie Order `≥ 120`, and
Tier-1 Hamiltonian All-Chord-`B`):

1. **Generic Bitmask-to-`FinGraph` Soundness Bridges (Layer 1):**
   - `masksGraph n masks : FinGraph n` with exact soundness of `checkCycleMasks`
     (`HasSimpleCycleOfLen`), `hasSimpleCycleLenBool = false` (`¬HasSimpleCycleOfLen` via
     minimum-vertex rotation & bitmask DFS induction), `isClawFreeMasks` (`IsClawFree`),
     `maskDeg` (`FinGraph.deg`), and `checkK5MinorBool` (`FinGraph.HasK5Minor`).
2. **Direct Expanded-Port Kills (`0/4`, `0/128`, `0/2048`) Directly on `FinGraph` (Layers 1–2):**
   - Kernel-verifies `SplitConfigWellFormed` on ALL `4 + 128 + 2,048` configurations plus
     `f11G39SplitConfig` (`port_configs_wellFormed`),
   - Kernel-verifies ALL `4` `deg3_tri` (`C_8`), ALL `128` `K_{2,3}` (`C_8` or `C_16`), and
     ALL `2,048` `Q_3 - v^*` (`C_8` or `C_16`) expanded-port configurations via
     `FinGraph.HasSimpleCycleOfLen`, plus parallel-edge `C_8` exclusion.
3. **Sharp Non-Planar `K_5`-Minor Witness `G_39 = T(H_14)/B` (Layers 1–2):**
   - Exact `F_11` (`tw(F_11) ≤ 3` via BOTH explicit 8-bag tree decomposition AND explicit
     `IsSpanning3Tree T11` supergraph connecting to `universal_3tree_lemma`),
   - Exact `H_14` (cubic 14v with `H14.HasK5Minor`),
   - Exact `G_39` (`|V| = 39`, `Δ = 4`, `δ = 3`, 3 independent deg-4 vertices `[2, 7, 12]`,
     `G39.IsClawFree`, `¬G39.HasSimpleCycleOfLen 4`, `¬G39.HasSimpleCycleOfLen 8`,
     `G39.HasSimpleCycleOfLen 16`, and `G39.HasK5Minor` — sharp for `C_16` vs. `C_8`, with
     `C_4` also excluded, and pairwise vertex-disjoint connected branch sets within each
     `K_5`-minor model, proving non-planarity purely combinatorially with ZERO topological axioms).
4. **Dyadic-Cycle-Free Independent-Bowtie Order `≥ 120` & Tier-1 Hamiltonian All-Chord-`B` (Layers 1–4):**
   - Exact quotient-to-graph arithmetic bridge `|V(G)| = 5 * |V(F)|`, `allowed_s` table,
     cycle-merge kills, and Moore/distance-3 arithmetic `24 → 120` (applying strictly to
     **dyadic-cycle-free** independent-bowtie claw-free graphs with `δ(G) ≥ 3` and `Δ(G) ≤ 4`;
     unconditionally a 25-vertex `K_5`-quotient independent-bowtie graph exists and contains `C_16`).
   - Tier-1 Hamiltonian All-Chord-`B`: `L_2 ≥ 10`, universal 4-Tier Dyadic-Octave interval coverage
     for ALL `a ≥ 4` (`P = 2^a ≥ 16`), Rim-`C_256` closure for ALL even `104 ≤ N ≤ 128`, and exact
     Tier-1 `39`-period & `23`-open-odd classification.

*Transparent scope boundary (Layers 3–4):* The `360,612` lifted-`H` + `166` overlap enumerations
(dyadic-cycle-free Independent-Bowtie `120`), `K_{3,3}`/`Q_3` `4,608` bowtie subsets, and Tier-1
Hamiltonian backtracking sweeps (`W ≤ 31` `L_win = 17` [`29,357`], `k = 8`, `23` odd [`93,902`],
arbitrary matchings even `N ≤ 136` [`641` leaves `≤ 102`, `{130:73, 132:236, 134:242, 136:723}`])
are verified zero-float in `cert/verify_clawfree_eg.py`; global graph-to-port embeddings,
distance-3 case analysis, and periodic/finite-search reductions are proved in the LaTeX manuscript.
-/

namespace ClawFreeEG

open ClawFreeEG.Treewidth3Data
open ClawFreeEG.Treewidth3Q3DataA
open ClawFreeEG.Treewidth3Q3DataB

/-! ## 1. Generic Bitmask-to-`FinGraph` Soundness Bridges -/

/-- Construct a `FinGraph n` directly from a bitmask list `masks : List Nat` via `maskAdj`. -/
def masksGraph (n : Nat) (masks : List Nat) : FinGraph n where
  adj u v := maskAdj masks u.val v.val
  symm := by
    intro u v
    unfold maskAdj
    have hne : (u.val != v.val) = (v.val != u.val) := by
      by_cases h : u.val = v.val
      · simp [h]
      · rw [bne_iff_ne.mpr h, bne_iff_ne.mpr (Ne.symm h)]
    rw [hne]
    cases (v.val != u.val) <;> cases (getNat masks u.val).testBit v.val <;>
      cases (getNat masks v.val).testBit u.val <;> rfl
  loopless := by
    intro u
    simp [maskAdj]

private theorem nat_beq_false_of_ne {a b : Nat} (h : a ≠ b) : Nat.beq a b = false := by
  change (a == b) = false
  exact beq_false_of_ne h

private theorem rawPortAdj_symm (rowsH : List (List Nat)) (bowties : List (Nat × Nat)) (x y : Nat) :
    rawPortAdj rowsH bowties x y = rawPortAdj rowsH bowties y x := by
  unfold rawPortAdj
  have hxy : Nat.beq x y = Nat.beq y x := by
    by_cases h : x = y
    · subst h; rfl
    · rw [nat_beq_false_of_ne h, nat_beq_false_of_ne (Ne.symm h)]
  rw [hxy]
  cases Nat.beq y x
  · dsimp only
    have huv : Nat.beq (Nat.div x 3) (Nat.div y 3) = Nat.beq (Nat.div y 3) (Nat.div x 3) := by
      by_cases h : Nat.div x 3 = Nat.div y 3
      · rw [h]
      · rw [nat_beq_false_of_ne h, nat_beq_false_of_ne (Ne.symm h)]
    rw [huv]
    cases Nat.beq (Nat.div y 3) (Nat.div x 3)
    · cases Nat.beq (get3 (getRow (Nat.div x 3) rowsH) (Nat.mod x 3)) (Nat.div y 3) <;>
      cases Nat.beq (get3 (getRow (Nat.div y 3) rowsH) (Nat.mod y 3)) (Nat.div x 3) <;>
      cases isBtPair (Nat.div x 3) (Nat.div y 3) bowties <;>
      cases isBtPair (Nat.div y 3) (Nat.div x 3) bowties <;> rfl
    · rfl
  · rfl

private theorem rawPortAdj_loopless (rowsH : List (List Nat)) (bowties : List (Nat × Nat)) (x : Nat) :
    rawPortAdj rowsH bowties x x = false := by
  unfold rawPortAdj
  simp [Nat.beq_refl]

/-- Expanded port-graph `FinGraph` of a vertex-splitting configuration `cfg` via direct bounded-instance port adjacency. -/
def expandedPortGraph (cfg : SplitConfig) : FinGraph (expandedPortCount cfg) where
  adj u v := portAdjConfig cfg u.val v.val
  symm := fun _ _ => rawPortAdj_symm _ _ _ _
  loopless := fun _ => rawPortAdj_loopless _ _ _

/-! ### 1A. Cycle Witness Soundness (`checkCycleMasks = true → HasSimpleCycleOfLen`) -/

private theorem memNat_iff_mem (x : Nat) : ∀ (xs : List Nat), memNat x xs = true ↔ x ∈ xs
  | [] => by simp [memNat]
  | y :: ys => by
    unfold memNat
    by_cases h : x = y
    · subst h; simp [Nat.beq_refl]
    · rw [nat_beq_false_of_ne h]
      simp only [Bool.false_eq_true, ↓reduceIte, List.mem_cons]
      rw [memNat_iff_mem x ys]
      exact ⟨Or.inr, fun h' => h'.resolve_left h⟩

private theorem allLt_sound (n : Nat) : ∀ {xs : List Nat}, allLt n xs = true → ∀ v ∈ xs, v < n
  | [], _, _, hv => by cases hv
  | x :: xs, h, v, hv => by
    unfold allLt at h
    cases hx : Nat.blt x n
    · rw [hx] at h; cases h
    · rw [hx] at h; simp only [↓reduceIte] at h
      rcases List.mem_cons.mp hv with rfl | hrest
      · unfold Nat.blt at hx; have := Nat.le_of_ble_eq_true hx; omega
      · exact allLt_sound n h v hrest

private theorem nodupNat_sound : ∀ {xs : List Nat}, nodupNat xs = true → xs.Nodup
  | [], _ => List.nodup_nil
  | x :: xs, h => by
    unfold nodupNat at h
    cases hm : memNat x xs
    · rw [hm] at h; simp only [Bool.false_eq_true, ↓reduceIte] at h
      have hmem : x ∉ xs := fun hx => by
        have ht := (memNat_iff_mem x xs).mpr hx
        rw [ht] at hm; cases hm
      exact List.nodup_cons.mpr ⟨hmem, nodupNat_sound h⟩
    · rw [hm] at h; cases h

private def toFinList (n : Nat) : (xs : List Nat) → (∀ v ∈ xs, v < n) → List (Fin n)
  | [], _ => []
  | x :: xs, h =>
    ⟨x, h x (List.mem_cons_self ..)⟩ :: toFinList n xs (fun v hv => h v (List.mem_cons_of_mem x hv))

private theorem toFinList_length (n : Nat) :
    ∀ (xs : List Nat) (h : ∀ v ∈ xs, v < n), (toFinList n xs h).length = xs.length
  | [], _ => rfl
  | _ :: xs, h => by simp [toFinList, toFinList_length n xs]

private theorem toFinList_getElem (n : Nat) :
    ∀ (xs : List Nat) (h : ∀ v ∈ xs, v < n) (i : Nat) (hi : i < (toFinList n xs h).length),
      ((toFinList n xs h)[i]'hi).val = xs[i]'(toFinList_length n xs h ▸ hi)
  | [], _, _, hi => by simp [toFinList] at hi
  | _ :: xs, h, 0, _ => rfl
  | _ :: xs, h, i + 1, hi => toFinList_getElem n xs _ i (by simp [toFinList] at hi ⊢; exact hi)

private theorem toFinList_nodup (n : Nat) :
    ∀ (xs : List Nat) (h : ∀ v ∈ xs, v < n), xs.Nodup → (toFinList n xs h).Nodup
  | [], _, _ => List.nodup_nil
  | x :: xs, h, hnd => by
    rcases List.nodup_cons.mp hnd with ⟨hxnot, hndxs⟩
    apply List.nodup_cons.mpr
    refine ⟨?_, toFinList_nodup n xs _ hndxs⟩
    intro hmem
    have hval : x ∈ xs := by
      have rec_mem : ∀ (ys : List Nat) (hy : ∀ v ∈ ys, v < n) (a : Fin n),
          a ∈ toFinList n ys hy → a.val ∈ ys := by
        intro ys hy a ha
        induction ys with
        | nil => cases ha
        | cons y yt ih =>
          simp only [toFinList, List.mem_cons] at ha
          rcases ha with rfl | hrest
          · exact List.mem_cons_self ..
          · exact List.mem_cons_of_mem y (ih _ hrest)
      exact rec_mem xs _ ⟨x, h x (List.mem_cons_self ..)⟩ hmem
    exact hxnot hval

private theorem checkCycleGo_sound (masks : List Nat) (first : Nat) :
    ∀ (xs : List Nat), checkCycleMasks.go masks first xs = true →
      (∀ (i : Nat) (hi : i + 1 < xs.length),
        maskAdj masks (xs[i]'(by omega)) (xs[i + 1]'hi) = true) ∧
      (∀ (hne : xs ≠ []), maskAdj masks (xs[xs.length - 1]'(by cases xs with | nil => exact absurd rfl hne | cons _ _ => simp)) first = true)
  | [], _ => ⟨fun _ hi => by simp at hi, fun hne => absurd rfl hne⟩
  | [last], h => by
    unfold checkCycleMasks.go at h
    exact ⟨fun _ hi => by simp at hi, fun _ => h⟩
  | a :: b :: rest, h => by
    unfold checkCycleMasks.go at h
    cases hab : maskAdj masks a b
    · rw [hab] at h; cases h
    · rw [hab] at h
      simp only [↓reduceIte] at h
      rcases checkCycleGo_sound masks first (b :: rest) h with ⟨ih_adj, ih_last⟩
      refine ⟨?_, ?_⟩
      · intro i hi
        cases i with
        | zero => exact hab
        | succ i' => exact ih_adj i' (by simpa using hi)
      · intro _
        simpa using ih_last (List.cons_ne_nil b rest)

/-- **Soundness of `checkCycleMasks`:**
Any cycle accepted by `checkCycleMasks n masks cyc` is a genuine simple cycle of length
`cyc.length` in `masksGraph n masks` (`FinGraph.HasSimpleCycleOfLen`). -/
theorem checkCycleMasks_sound (n : Nat) (masks : List Nat) (cyc : List Nat)
    (h : checkCycleMasks n masks cyc = true) :
    (masksGraph n masks).HasSimpleCycleOfLen cyc.length := by
  unfold checkCycleMasks at h
  dsimp only at h
  have hlen3 : 3 ≤ cyc.length := by
    by_cases hlt : Nat.blt cyc.length 3 = true
    · simp only [hlt, ↓reduceIte] at h; cases h
    · have hf : Nat.blt cyc.length 3 = false := Bool.eq_false_iff.mpr hlt
      unfold Nat.blt at hf
      by_cases hge : 3 ≤ cyc.length
      · exact hge
      · have hle : cyc.length + 1 ≤ 3 := by omega
        rw [Nat.ble_eq_true_of_le hle] at hf; cases hf
  have hlt_f : Nat.blt cyc.length 3 = false := by
    cases hb : Nat.blt cyc.length 3
    · rfl
    · unfold Nat.blt at hb; have := Nat.le_of_ble_eq_true hb; omega
  rw [hlt_f] at h; simp only [Bool.false_eq_true, ↓reduceIte] at h
  cases hall : cyc.all (fun v => Nat.blt v n)
  · rw [hall] at h; simp at h
  · rw [hall] at h; simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
    cases hnd : nodupNat cyc
    · rw [hnd] at h; simp at h
    · rw [hnd] at h; simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
      have hlt_n : ∀ v ∈ cyc, v < n := by
        intro v hv
        have hb := List.all_eq_true.mp hall v hv
        unfold Nat.blt at hb
        have := Nat.le_of_ble_eq_true hb
        omega
      let cFin := toFinList n cyc hlt_n
      have hcLen : cFin.length = cyc.length := toFinList_length n cyc hlt_n
      refine ⟨cFin, ⟨by omega, toFinList_nodup n cyc hlt_n (nodupNat_sound hnd), ?_⟩, hcLen⟩
      match hcyc : cyc with
      | [] => simp at hlen3
      | first :: rest =>
        rcases checkCycleGo_sound masks first (first :: rest) h with ⟨hadj, hlast⟩
        intro i hi
        have hi_c : i < (first :: rest).length := hcLen ▸ hi
        change maskAdj masks (cFin[i]'hi).val (cFin[(i + 1) % cFin.length]'_).val = true
        rw [toFinList_getElem, toFinList_getElem]
        by_cases hstep : i + 1 < (first :: rest).length
        · have hmod : (i + 1) % cFin.length = i + 1 := by rw [hcLen]; exact Nat.mod_eq_of_lt hstep
          have hget : (first :: rest)[(i + 1) % cFin.length]'(by omega) = (first :: rest)[i + 1]'hstep := by
            congr 1
          have hgetL : cyc[i]'(by rw [hcyc]; exact hi_c) = (first :: rest)[i]'hi_c := by simp [hcyc]
          have hgetR : cyc[(i + 1) % cFin.length]'(by rw [hcyc]; omega) = (first :: rest)[i + 1]'hstep := by
            simp [hcyc, hmod]
          rw [hgetL, hgetR]
          exact hadj i hstep
        · have hi_last : i = (first :: rest).length - 1 := by omega
          have hmod : (i + 1) % cFin.length = 0 := by
            rw [hcLen, show i + 1 = (first :: rest).length by omega, Nat.mod_self]
          have hget0 : cyc[(i + 1) % cFin.length]'(by rw [hcyc]; omega) = first := by
            simp [hmod, hcyc]
          have hgetL : cyc[i]'(by rw [hcyc]; exact hi_c) = (first :: rest)[(first :: rest).length - 1]'(by simp) := by
            simp [hcyc, hi_last]
          rw [hgetL, hget0]
          exact hlast (List.cons_ne_nil first rest)

private theorem mapUnrelabel_length (removed : List Nat) :
    ∀ (xs : List Nat), (mapUnrelabel removed xs).length = xs.length
  | [] => rfl
  | _ :: xs => by simp [mapUnrelabel, mapUnrelabel_length removed xs]

private theorem mapUnrelabel_getElem (removed : List Nat) :
    ∀ (xs : List Nat) (i : Nat) (hi : i < (mapUnrelabel removed xs).length),
      (mapUnrelabel removed xs)[i]'hi = unrelabel (xs[i]'(mapUnrelabel_length removed xs ▸ hi)) removed
  | [], _, hi => by simp [mapUnrelabel] at hi
  | _ :: _, 0, _ => rfl
  | _ :: xs, i + 1, hi => mapUnrelabel_getElem removed xs i (by simp [mapUnrelabel] at hi ⊢; exact hi)

private theorem checkRawCycleGo_sound (rowsH : List (List Nat)) (bowties : List (Nat × Nat)) (first : Nat) :
    ∀ (xs : List Nat), checkRawCycleGo rowsH bowties first xs = true →
      (∀ (i : Nat) (hi : i + 1 < xs.length),
        rawPortAdj rowsH bowties (xs[i]'(by omega)) (xs[i + 1]'hi) = true) ∧
      (∀ (hne : xs ≠ []), rawPortAdj rowsH bowties (xs[xs.length - 1]'(by cases xs with | nil => exact absurd rfl hne | cons _ _ => simp)) first = true)
  | [], _ => ⟨fun _ hi => by simp at hi, fun hne => absurd rfl hne⟩
  | [last], h => by
    unfold checkRawCycleGo at h
    exact ⟨fun _ hi => by simp at hi, fun _ => h⟩
  | a :: b :: rest, h => by
    unfold checkRawCycleGo at h
    cases hab : rawPortAdj rowsH bowties a b
    · rw [hab] at h; cases h
    · rw [hab] at h
      simp only [↓reduceIte] at h
      rcases checkRawCycleGo_sound rowsH bowties first (b :: rest) h with ⟨ih_adj, ih_last⟩
      refine ⟨?_, ?_⟩
      · intro i hi
        cases i with
        | zero => exact hab
        | succ i' => exact ih_adj i' (by simpa using hi)
      · intro _
        simpa using ih_last (List.cons_ne_nil b rest)

/-- **Soundness of `checkCycleDirect`:**
Any cycle accepted by `checkCycleDirect cfg cyc` is a genuine simple cycle of length
`cyc.length` in `expandedPortGraph cfg` (`FinGraph.HasSimpleCycleOfLen`). -/
theorem checkCycleDirect_sound (cfg : SplitConfig) (cyc : List Nat)
    (h : checkCycleDirect cfg cyc = true) :
    (expandedPortGraph cfg).HasSimpleCycleOfLen cyc.length := by
  unfold checkCycleDirect at h
  have hlen3 : 3 ≤ cyc.length := by
    by_cases hlt : Nat.blt cyc.length 3 = true
    · simp only [hlt, ↓reduceIte] at h; cases h
    · have hf : Nat.blt cyc.length 3 = false := Bool.eq_false_iff.mpr hlt
      unfold Nat.blt at hf
      by_cases hge : 3 ≤ cyc.length
      · exact hge
      · have hle : cyc.length + 1 ≤ 3 := by omega
        rw [Nat.ble_eq_true_of_le hle] at hf; cases hf
  have hlt_f : Nat.blt cyc.length 3 = false := by
    cases hb : Nat.blt cyc.length 3
    · rfl
    · unfold Nat.blt at hb; have := Nat.le_of_ble_eq_true hb; omega
  rw [hlt_f] at h; simp only [Bool.false_eq_true, ↓reduceIte] at h
  generalize hsq : splitQuotient cfg = sq at h
  rcases sq with ⟨rowsH, bowties⟩
  have hn_eq : expandedPortCount cfg = Nat.sub (Nat.mul 3 rowsH.length) bowties.length := by
    unfold expandedPortCount; rw [hsq]
  cases hall : allLt (Nat.sub (Nat.mul 3 rowsH.length) bowties.length) cyc
  · rw [hall] at h; cases h
  · rw [hall] at h; simp only [↓reduceIte] at h
    cases hnd : nodupNat cyc
    · rw [hnd] at h; cases h
    · rw [hnd] at h; simp only [↓reduceIte] at h
      have hlt_n : ∀ v ∈ cyc, v < expandedPortCount cfg := by
        rw [hn_eq]; exact allLt_sound _ hall
      let cFin := toFinList (expandedPortCount cfg) cyc hlt_n
      have hcLen : cFin.length = cyc.length := toFinList_length _ cyc hlt_n
      refine ⟨cFin, ⟨by omega, toFinList_nodup _ cyc hlt_n (nodupNat_sound hnd), ?_⟩, hcLen⟩
      let removed := mkRemoved rowsH bowties
      match hcyc : cyc with
      | [] => simp at hlen3
      | v0 :: rest =>
        simp only [mapUnrelabel] at h
        rcases checkRawCycleGo_sound rowsH bowties (unrelabel v0 removed)
          (unrelabel v0 removed :: mapUnrelabel removed rest) h with ⟨hadj, hlast⟩
        intro i hi
        have hi_c : i < (v0 :: rest).length := hcLen ▸ hi
        change portAdjConfig cfg (cFin[i]'hi).val (cFin[(i + 1) % cFin.length]'_).val = true
        rw [toFinList_getElem, toFinList_getElem]
        have hpadj : ∀ a b, portAdjConfig cfg a b = rawPortAdj rowsH bowties (unrelabel a removed) (unrelabel b removed) := by
          intro a b; unfold portAdjConfig portAdj; rw [hsq]
        rw [hpadj]
        have hmap_len : (unrelabel v0 removed :: mapUnrelabel removed rest).length = (v0 :: rest).length := by
          simp [mapUnrelabel_length]
        by_cases hstep : i + 1 < (v0 :: rest).length
        · have hmod : (i + 1) % cFin.length = i + 1 := by rw [hcLen]; exact Nat.mod_eq_of_lt hstep
          have hgetL : cyc[i]'(by rw [hcyc]; exact hi_c) = (v0 :: rest)[i]'hi_c := by simp [hcyc]
          have hgetR : cyc[(i + 1) % cFin.length]'(by rw [hcyc]; omega) = (v0 :: rest)[i + 1]'hstep := by
            simp [hcyc, hmod]
          rw [hgetL, hgetR]
          have h1 := hadj i (by omega)
          have hl : (unrelabel v0 removed :: mapUnrelabel removed rest)[i]'(by omega) =
                    unrelabel ((v0 :: rest)[i]'hi_c) removed := by
            have := mapUnrelabel_getElem removed (v0 :: rest) i (by simp [mapUnrelabel_length]; exact hi_c)
            simpa [mapUnrelabel] using this
          have hr : (unrelabel v0 removed :: mapUnrelabel removed rest)[i + 1]'(by omega) =
                    unrelabel ((v0 :: rest)[i + 1]'hstep) removed := by
            have := mapUnrelabel_getElem removed (v0 :: rest) (i + 1) (by simp [mapUnrelabel_length]; simpa using hstep)
            simpa [mapUnrelabel] using this
          rw [← hl, ← hr]
          exact h1
        · have hi_last : i = (v0 :: rest).length - 1 := by omega
          have hmod : (i + 1) % cFin.length = 0 := by
            rw [hcLen, show i + 1 = (v0 :: rest).length by omega, Nat.mod_self]
          have hgetL : cyc[i]'(by rw [hcyc]; exact hi_c) = (v0 :: rest)[i]'hi_c := by simp [hcyc]
          have hget0 : cyc[(i + 1) % cFin.length]'(by rw [hcyc]; omega) = v0 := by simp [hmod, hcyc]
          rw [hgetL, hget0]
          have h1 := hlast (List.cons_ne_nil _ _)
          have hidx_eq : (unrelabel v0 removed :: mapUnrelabel removed rest).length - 1 = i := by
            omega
          have hget_last : (unrelabel v0 removed :: mapUnrelabel removed rest)[(unrelabel v0 removed :: mapUnrelabel removed rest).length - 1]'(by simp) =
                           (unrelabel v0 removed :: mapUnrelabel removed rest)[i]'(by omega) := by
            congr 1
          rw [hget_last] at h1
          have hl := mapUnrelabel_getElem removed (v0 :: rest) i (by simp [mapUnrelabel_length]; exact hi_c)
          simp only [mapUnrelabel] at hl
          rw [← hl]
          exact h1

/-! ### 1B. Exact Cycle-Absence Soundness (`hasSimpleCycleLenBool = false → ¬HasSimpleCycleOfLen`) -/

private theorem rotCycle_isSimpleCycle {n : Nat} (G : FinGraph n) (cyc : List (Fin n))
    (hcyc : G.IsSimpleCycle cyc) (k : Nat) (hk : k < cyc.length) :
    let rot := cyc.drop k ++ cyc.take k
    G.IsSimpleCycle rot ∧ rot.length = cyc.length := by
  dsimp only
  rcases hcyc with ⟨hlen, hnd, hadj⟩
  have hrot_len : (cyc.drop k ++ cyc.take k).length = cyc.length := by
    simp [List.length_append, List.length_drop, List.length_take]; omega
  have hrot_nd : (cyc.drop k ++ cyc.take k).Nodup := by
    have hsplit : cyc = cyc.take k ++ cyc.drop k := (List.take_append_drop k cyc).symm
    rw [hsplit] at hnd
    rw [List.nodup_append] at hnd ⊢
    exact ⟨hnd.2.1, hnd.1, fun a ha b hb => Ne.symm (hnd.2.2 b hb a ha)⟩
  have hrot_get : ∀ (i : Nat) (hi : i < (cyc.drop k ++ cyc.take k).length),
      (cyc.drop k ++ cyc.take k)[i]'hi = cyc[(k + i) % cyc.length]'(Nat.mod_lt _ (by omega)) := by
    intro i hi
    have hi' : i < cyc.length := hrot_len ▸ hi
    by_cases hlt : i < (cyc.drop k).length
    · rw [List.getElem_append_left hlt, List.getElem_drop]
      have hki : k + i < cyc.length := by simp [List.length_drop] at hlt; omega
      congr 1; exact (Nat.mod_eq_of_lt hki).symm
    · rw [List.getElem_append_right (by omega), List.getElem_take]
      have hdl : (cyc.drop k).length = cyc.length - k := List.length_drop
      have hge : cyc.length ≤ k + i := by omega
      have hsub : (k + i) % cyc.length = i - (cyc.length - k) := by
        have h1 : k + i = cyc.length + (i - (cyc.length - k)) := by omega
        rw [h1, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
      congr 1; omega
  refine ⟨⟨by omega, hrot_nd, ?_⟩, hrot_len⟩
  intro i hi
  rw [hrot_get i hi, hrot_get ((i + 1) % (cyc.drop k ++ cyc.take k).length) _]
  have hidx : (k + (i + 1) % (cyc.drop k ++ cyc.take k).length) % cyc.length =
              ((k + i) % cyc.length + 1) % cyc.length := by
    rw [hrot_len, Nat.add_mod, Nat.mod_mod, ← Nat.add_mod,
        Nat.add_mod ((k + i) % cyc.length) 1, Nat.mod_mod, ← Nat.add_mod,
        show k + (i + 1) = (k + i) + 1 by omega]
  have hcongr : cyc[(k + (i + 1) % (cyc.drop k ++ cyc.take k).length) % cyc.length]'(Nat.mod_lt _ (by omega)) =
                cyc[((k + i) % cyc.length + 1) % cyc.length]'(Nat.mod_lt _ (by omega)) := by
    congr 1
  rw [hcongr]
  exact hadj ((k + i) % cyc.length) (Nat.mod_lt _ (by omega))

private theorem exists_min_index {n : Nat} :
    ∀ (xs : List (Fin n)), xs ≠ [] →
      ∃ k, ∃ (hk : k < xs.length), ∀ (i : Nat) (hi : i < xs.length), (xs[k]'hk).val ≤ (xs[i]'hi).val
  | [], hne => absurd rfl hne
  | [x], _ => ⟨0, by simp, fun i hi => by
      have hi0 : i = 0 := by simp at hi; omega
      subst hi0; exact Nat.le_refl _⟩
  | x :: y :: rest, _ => by
    rcases exists_min_index (y :: rest) (List.cons_ne_nil y rest) with ⟨k, hk, hmin⟩
    by_cases hxy : x.val ≤ ((y :: rest)[k]'hk).val
    · refine ⟨0, by simp, fun i hi => ?_⟩
      cases i with
      | zero => exact Nat.le_refl _
      | succ i' => exact Nat.le_trans hxy (hmin i' (by simpa using hi))
    · refine ⟨k + 1, by simpa using hk, fun i hi => ?_⟩
      cases i with
      | zero => simp; omega
      | succ i' => exact hmin i' (by simpa using hi)

private theorem hasCycleFromNbs_true (start vis : Nat) (recFn : Nat → Nat → Bool)
    (w0 : Nat) (hw_lo : start < w0) (hvis : vis.testBit w0 = false)
    (hrec : recFn w0 (vis ||| (1 <<< w0)) = true) :
    ∀ (nbs : List Nat), w0 ∈ nbs →
      hasCycleFromNbs start vis recFn nbs = true
  | [], hmem => by cases hmem
  | w :: ws, hmem => by
    unfold hasCycleFromNbs
    rcases List.mem_cons.mp hmem with rfl | hrest
    · have hblt : Nat.blt start w0 = true := Nat.ble_eq_true_of_le (by omega)
      simp [hblt, hvis, hrec]
    · cases hok : (if (Nat.blt start w && !vis.testBit w) = true then recFn w (vis ||| 1 <<< w) else false)
      · simp only [Bool.false_eq_true, ↓reduceIte]
        exact hasCycleFromNbs_true start vis recFn w0 hw_lo hvis hrec ws hrest
      · simp

private theorem testBit_or_shift (vis a b : Nat) :
    (vis ||| (1 <<< a)).testBit b = (vis.testBit b || (a == b)) := by
  rw [Nat.testBit_or, Nat.testBit_shiftLeft]
  by_cases h : a = b
  · subst h; simp
  · have hne : (a == b) = false := beq_false_of_ne h
    rw [hne, Bool.or_false]
    by_cases hge : a ≤ b
    · have hpos : b - a ≠ 0 := by omega
      have h0 : (1 : Nat).testBit (b - a) = false := by
        cases hsub : b - a with
        | zero => exact absurd hsub hpos
        | succ k => simp [Nat.testBit_succ]
      simp [hge, h0]
    · simp [hge]

private theorem hasCycleFromAdj_complete (n : Nat) (masks : List Nat) (adj : List (List Nat))
    (hCov : ∀ u v, u < n → v < n → maskAdj masks u v = true → v ∈ getAdj adj u)
    (start : Nat) (hstart : start < n) :
    ∀ (rem : Nat) (cur : Fin n) (tail : List (Fin n)) (vis : Nat) (hlen : tail.length = rem),
      (cur :: tail).Nodup →
      (∀ x ∈ tail, start < x.val ∧ vis.testBit x.val = false) →
      (∀ (i : Nat) (hi : i + 1 < (cur :: tail).length),
        maskAdj masks ((cur :: tail)[i]'(by omega)).val ((cur :: tail)[i + 1]'hi).val = true) →
      maskAdj masks ((cur :: tail)[rem]'(by simp [hlen])).val start = true →
      hasCycleFromAdj adj start rem cur.val vis = true
  | 0, cur, tail, vis, hlen, _, _, _, hclose => by
    cases tail with
    | nil =>
      unfold hasCycleFromAdj
      exact List.contains_iff_mem.mpr (hCov cur.val start cur.isLt hstart hclose)
    | cons _ _ => simp at hlen
  | rem + 1, cur, tail, vis, hlen, hnd, hgt, hadj, hclose => by
    match tail with
    | [] => simp at hlen
    | next :: rest =>
      have hlen' : rest.length = rem := by simpa using hlen
      rcases List.nodup_cons.mp hnd with ⟨_, hnd_nr⟩
      have hnext_props := hgt next (List.mem_cons_self ..)
      have hcur_next : maskAdj masks cur.val next.val = true := hadj 0 (by simp)
      have hnext_mem : next.val ∈ getAdj adj cur.val := hCov cur.val next.val cur.isLt next.isLt hcur_next
      have hrest_gt : ∀ x ∈ rest, start < x.val ∧ (vis ||| (1 <<< next.val)).testBit x.val = false := by
        intro x hx
        have hx_p := hgt x (List.mem_cons_of_mem next hx)
        have hne : next.val ≠ x.val := by
          rcases List.nodup_cons.mp hnd_nr with ⟨hnot, _⟩
          intro heq; exact hnot (Fin.ext heq ▸ hx)
        rw [testBit_or_shift, hx_p.2, beq_false_of_ne hne]
        exact ⟨hx_p.1, rfl⟩
      have hrec := hasCycleFromAdj_complete n masks adj hCov start hstart rem next rest (vis ||| (1 <<< next.val))
        hlen' hnd_nr hrest_gt
        (fun i hi => hadj (i + 1) (by simpa using hi))
        (by simpa using hclose)
      unfold hasCycleFromAdj
      exact hasCycleFromNbs_true start vis (hasCycleFromAdj adj start rem) next.val
        hnext_props.1 hnext_props.2 hrec (getAdj adj cur.val) hnext_mem

private theorem hasSimpleCycleLenBool_go_true (adj : List (List Nat)) (L s0 : Nat)
    (h1 : hasCycleFromAdj adj s0 (L - 1) s0 (1 <<< s0) = true) :
    ∀ k, s0 < k → hasSimpleCycleLenGo adj L k = true
  | 0, hk => by omega
  | k + 1, hk => by
    unfold hasSimpleCycleLenGo
    by_cases heq : s0 = k
    · subst heq; simp [h1]
    · cases hc : hasCycleFromAdj adj k (L - 1) k (1 <<< k)
      · simp only [Bool.false_eq_true, ↓reduceIte]
        exact hasSimpleCycleLenBool_go_true adj L s0 h1 k (by omega)
      · simp

/-- **Soundness of `hasSimpleCycleLenBool = false`:**
If `adj` covers every edge of `(n, masks)` and `hasSimpleCycleLenBool n adj L = false` (`L ≥ 3`),
then `masksGraph n masks` has NO simple cycle of length `L` (`¬(masksGraph n masks).HasSimpleCycleOfLen L`). -/
theorem hasSimpleCycleLenBool_false_sound (n : Nat) (masks : List Nat) (adj : List (List Nat)) (L : Nat)
    (hL : L ≥ 3)
    (hCov : ∀ u v, u < n → v < n → maskAdj masks u v = true → v ∈ getAdj adj u)
    (hfalse : hasSimpleCycleLenBool n adj L = false) :
    ¬(masksGraph n masks).HasSimpleCycleOfLen L := by
  rintro ⟨cyc, hcyc, hclen⟩
  have hne : cyc ≠ [] := by intro h0; subst h0; simp at hclen; omega
  rcases exists_min_index cyc hne with ⟨k, hk, hmin⟩
  rcases rotCycle_isSimpleCycle (masksGraph n masks) cyc hcyc k hk with ⟨hrot_cyc, hrot_len⟩
  have hrot_L : (cyc.drop k ++ cyc.take k).length = L := hrot_len.trans hclen
  cases hrot_eq : (cyc.drop k ++ cyc.take k) with
  | nil => rw [hrot_eq] at hrot_L; simp at hrot_L; omega
  | cons s tail =>
    rw [hrot_eq] at hrot_cyc hrot_L
    have hs_eq : s = cyc[k]'hk := by
      have h0 : (cyc.drop k ++ cyc.take k)[0]'(by rw [hrot_eq]; simp) = s := by simp [hrot_eq]
      have hdrop : (cyc.drop k ++ cyc.take k)[0]'(by rw [hrot_eq]; simp) = cyc[k]'hk := by
        have hdl : 0 < (cyc.drop k).length := by simp [List.length_drop]; omega
        rw [List.getElem_append_left hdl, List.getElem_drop]
        simp
      exact h0.symm.trans hdrop
    rcases hrot_cyc with ⟨_, hnd, hadj⟩
    have htail_len : tail.length = L - 1 := by simp at hrot_L; omega
    have hgt : ∀ x ∈ tail, s.val < x.val ∧ (1 <<< s.val).testBit x.val = false := by
      intro x hx
      have hx_in_rot : x ∈ (cyc.drop k ++ cyc.take k) := by rw [hrot_eq]; exact List.mem_cons_of_mem s hx
      have hx_in_cyc : x ∈ cyc := by
        have hsplit : cyc = cyc.take k ++ cyc.drop k := (List.take_append_drop k cyc).symm
        rw [List.mem_append] at hx_in_rot
        rw [hsplit, List.mem_append]
        exact hx_in_rot.symm
      rcases List.mem_iff_getElem.mp hx_in_cyc with ⟨i, hi, rfl⟩
      have hle : s.val ≤ (cyc[i]'hi).val := hs_eq ▸ hmin i hi
      have hne_sx : s ≠ cyc[i]'hi := by
        rcases List.nodup_cons.mp hnd with ⟨hnot, _⟩
        intro heq; exact hnot (heq ▸ hx)
      have hlt_sx : s.val < (cyc[i]'hi).val := by
        have : s.val ≠ (cyc[i]'hi).val := fun h => hne_sx (Fin.ext h)
        omega
      refine ⟨hlt_sx, ?_⟩
      have htb := testBit_or_shift 0 s.val (cyc[i]'hi).val
      simp only [Nat.zero_or, Nat.zero_testBit, Bool.false_or] at htb
      rw [htb]
      exact beq_false_of_ne (by omega)
    have hpath_adj : ∀ (i : Nat) (hi : i + 1 < (s :: tail).length),
        maskAdj masks ((s :: tail)[i]'(by omega)).val ((s :: tail)[i + 1]'hi).val = true := by
      intro i hi
      have hi_r : i < (s :: tail).length := by omega
      have hmod : (i + 1) % (s :: tail).length = i + 1 := Nat.mod_eq_of_lt hi
      have ha := hadj i hi_r
      change maskAdj masks ((s :: tail)[i]'hi_r).val ((s :: tail)[(i + 1) % (s :: tail).length]'_).val = true at ha
      have hget : (s :: tail)[(i + 1) % (s :: tail).length]'(Nat.mod_lt _ (by omega)) = (s :: tail)[i + 1]'hi := by
        congr 1
      rw [hget] at ha
      exact ha
    have hclose : maskAdj masks ((s :: tail)[L - 1]'(by simp [htail_len])).val s.val = true := by
      have hi_r : L - 1 < (s :: tail).length := by omega
      have hmod : (L - 1 + 1) % (s :: tail).length = 0 := by rw [hrot_L, show L - 1 + 1 = L by omega, Nat.mod_self]
      have ha := hadj (L - 1) hi_r
      change maskAdj masks ((s :: tail)[L - 1]'hi_r).val ((s :: tail)[(L - 1 + 1) % (s :: tail).length]'_).val = true at ha
      have hget0 : (s :: tail)[(L - 1 + 1) % (s :: tail).length]'(Nat.mod_lt _ (by omega)) = s := by
        simp only [hmod]; rfl
      rw [hget0] at ha
      exact ha
    have hfrom := hasCycleFromAdj_complete n masks adj hCov s.val s.isLt (L - 1) s tail (1 <<< s.val)
      htail_len hnd hgt hpath_adj hclose
    have htrue : hasSimpleCycleLenBool n adj L = true := by
      unfold hasSimpleCycleLenBool
      have hlt_f : Nat.blt L 3 = false := by
        cases hb : Nat.blt L 3
        · rfl
        · unfold Nat.blt at hb; have := Nat.le_of_ble_eq_true hb; omega
      rw [hlt_f]; simp only [Bool.false_eq_true, ↓reduceIte]
      exact hasSimpleCycleLenBool_go_true adj L s.val hfrom n s.isLt
    rw [htrue] at hfalse; cases hfalse

/-! ### 1C. Degree, Claw-Freeness, & `K_5`-Minor Soundness -/

private theorem maskDeg_go_eq (n : Nat) (masks : List Nat) (u : Nat) :
    ∀ (k v acc : Nat), v + k = n →
      maskDeg.go masks u v acc k =
      acc + ((List.finRange n).filter fun w => Nat.ble v w.val && maskAdj masks u w.val).length
  | 0, v, acc, hvk => by
    unfold maskDeg.go
    have hnil : (List.finRange n).filter (fun w => Nat.ble v w.val && maskAdj masks u w.val) = [] := by
      apply List.filter_eq_nil_iff.mpr
      intro w _
      have : ¬(v ≤ w.val) := by omega
      cases hb : Nat.ble v w.val
      · simp
      · exact absurd (Nat.le_of_ble_eq_true hb) this
    rw [hnil]; simp
  | k + 1, v, acc, hvk => by
    unfold maskDeg.go
    have ih := maskDeg_go_eq n masks u k (v + 1) (if maskAdj masks u v then acc + 1 else acc) (by omega)
    rw [ih]
    have hv_lt : v < n := by omega
    let vFin : Fin n := ⟨v, hv_lt⟩
    let p : Fin n → Bool := fun w => Nat.ble (v + 1) w.val && maskAdj masks u w.val
    let q : Fin n → Bool := fun w => Nat.ble v w.val && maskAdj masks u w.val
    change (if maskAdj masks u v then acc + 1 else acc) + countPred p = acc + countPred q
    cases hadj : maskAdj masks u v
    · simp only [Bool.false_eq_true, ↓reduceIte]
      congr 1
      apply countPred_congr; intro w
      dsimp only [p, q]
      by_cases hvw : w.val = v
      · rw [hvw, hadj]; simp
      · have hble : Nat.ble (v + 1) w.val = Nat.ble v w.val := by
          by_cases hle : v + 1 ≤ w.val
          · rw [Nat.ble_eq_true_of_le hle, Nat.ble_eq_true_of_le (by omega)]
          · have h1 : Nat.ble (v + 1) w.val = false := by
              cases hb : Nat.ble (v + 1) w.val; rfl; exact absurd (Nat.le_of_ble_eq_true hb) hle
            have h2 : Nat.ble v w.val = false := by
              cases hb : Nat.ble v w.val; rfl; have := Nat.le_of_ble_eq_true hb; omega
            rw [h1, h2]
        rw [hble]
    · simp only [↓reduceIte]
      have hpv : p vFin = false := by
        dsimp only [p, vFin]
        have h1 : Nat.ble (v + 1) v = false := by
          cases hb : Nat.ble (v + 1) v; rfl; have := Nat.le_of_ble_eq_true hb; omega
        simp [h1]
      have hins := countPred_insert p vFin hpv
      have hcongr : countPred (fun w => p w || (w == vFin)) = countPred q := by
        apply countPred_congr; intro w
        dsimp only [p, q, vFin]
        by_cases hvw : w.val = v
        · have hweq : w = ⟨v, hv_lt⟩ := Fin.ext hvw
          subst hweq
          simp [hadj, Nat.ble_eq_true_of_le (Nat.le_refl v)]
        · have hneq : (w == ⟨v, hv_lt⟩) = false := beq_false_of_ne (fun h => hvw (congrArg Fin.val h))
          rw [hneq, Bool.or_false]
          by_cases hle : v + 1 ≤ w.val
          · rw [Nat.ble_eq_true_of_le hle, Nat.ble_eq_true_of_le (by omega)]
          · have h1 : Nat.ble (v + 1) w.val = false := by
              cases hb : Nat.ble (v + 1) w.val; rfl; exact absurd (Nat.le_of_ble_eq_true hb) hle
            have h2 : Nat.ble v w.val = false := by
              cases hb : Nat.ble v w.val; rfl; have := Nat.le_of_ble_eq_true hb; omega
            rw [h1, h2]
      rw [hcongr] at hins
      omega

/-- Exact equivalence between `maskDeg` and `FinGraph.deg`. -/
theorem maskDeg_eq_deg (n : Nat) (masks : List Nat) (u : Fin n) :
    maskDeg n masks u.val = (masksGraph n masks).deg u := by
  unfold maskDeg
  rw [maskDeg_go_eq n masks u.val n 0 0 (Nat.zero_add n), Nat.zero_add]
  unfold FinGraph.deg FinGraph.neighbors
  rfl

private theorem isClawFreeMasks_nbsOf_mem (masks : List Nat) (u : Nat) :
    ∀ (k v w : Nat), v ≤ w → w < v + k → maskAdj masks u w = true →
      w ∈ isClawFreeMasks.nbsOf masks u v k
  | 0, _, _, _, hlt, _ => by omega
  | k + 1, v, w, hle, hlt, hadj => by
    unfold isClawFreeMasks.nbsOf
    by_cases hvw : v = w
    · subst hvw; simp [hadj]
    · cases h : maskAdj masks u v
      · simp only [Bool.false_eq_true, ↓reduceIte]
        exact isClawFreeMasks_nbsOf_mem masks u k (v + 1) w (by omega) (by omega) hadj
      · simp only [↓reduceIte]
        exact List.mem_cons_of_mem v (isClawFreeMasks_nbsOf_mem masks u k (v + 1) w (by omega) (by omega) hadj)

private theorem isClawFreeMasks_nbsOf_sorted (masks : List Nat) (u : Nat) :
    ∀ (k v : Nat), (isClawFreeMasks.nbsOf masks u v k).Pairwise (· < ·)
  | 0, _ => List.Pairwise.nil
  | k + 1, v => by
    unfold isClawFreeMasks.nbsOf
    have ih := isClawFreeMasks_nbsOf_sorted masks u k (v + 1)
    have hgt : ∀ x ∈ isClawFreeMasks.nbsOf masks u (v + 1) k, v < x := by
      have rec_gt : ∀ (m s x : Nat), x ∈ isClawFreeMasks.nbsOf masks u s m → s ≤ x := by
        intro m
        induction m with
        | zero => intro _ _ hx; simp [isClawFreeMasks.nbsOf] at hx
        | succ m' ihm =>
          intro s x hx
          unfold isClawFreeMasks.nbsOf at hx
          split at hx
          · rcases List.mem_cons.mp hx with rfl | hrest
            · exact Nat.le_refl _
            · exact Nat.le_trans (by omega) (ihm (s + 1) x hrest)
          · exact Nat.le_trans (by omega) (ihm (s + 1) x hx)
      intro x hx; have := rec_gt k (v + 1) x hx; omega
    cases maskAdj masks u v
    · exact ih
    · exact List.pairwise_cons.mpr ⟨hgt, ih⟩

private theorem checkTriples_sound (masks : List Nat) :
    ∀ (xs : List Nat), xs.Pairwise (· < ·) → isClawFreeMasks.checkTriples masks xs = true →
      ∀ a b c, a ∈ xs → b ∈ xs → c ∈ xs → a < b → b < c →
        maskAdj masks a b = true ∨ maskAdj masks a c = true ∨ maskAdj masks b c = true
  | [], _, _, _, _, _, ha, _, _, _, _ => by cases ha
  | x :: rest, hpw, hok, a, b, c, ha, hb, hc, hab, hbc => by
    rcases List.pairwise_cons.mp hpw with ⟨hgt, hpw_r⟩
    unfold isClawFreeMasks.checkTriples at hok
    simp only [Bool.and_eq_true] at hok
    rcases List.mem_cons.mp ha with rfl | ha'
    · have hb' : b ∈ rest := by
        rcases List.mem_cons.mp hb with rfl | h
        · omega
        · exact h
      have hc' : c ∈ rest := by
        rcases List.mem_cons.mp hc with rfl | h
        · omega
        · exact h
      have hcp : ∀ (ys : List Nat), ys.Pairwise (· < ·) →
          isClawFreeMasks.checkTriples.checkPairs masks a ys = true →
          ∀ u v, u ∈ ys → v ∈ ys → u < v →
            maskAdj masks a u = true ∨ maskAdj masks a v = true ∨ maskAdj masks u v = true := by
        intro ys
        induction ys with
        | nil => intro _ _ _ _ hu; cases hu
        | cons y yt ihy =>
          intro hpw_y hok_y u v hu hv huv
          rcases List.pairwise_cons.mp hpw_y with ⟨hgt_y, hpw_yt⟩
          unfold isClawFreeMasks.checkTriples.checkPairs at hok_y
          simp only [Bool.and_eq_true] at hok_y
          rcases List.mem_cons.mp hu with rfl | hu'
          · have hv' : v ∈ yt := by
              rcases List.mem_cons.mp hv with rfl | h
              · omega
              · exact h
            have h3 := List.all_eq_true.mp hok_y.1 v hv'
            simp only [Bool.or_eq_true] at h3
            rcases h3 with (h1 | h2) | h3
            · exact Or.inl h1
            · exact Or.inr (Or.inl h2)
            · exact Or.inr (Or.inr h3)
          · have hv' : v ∈ yt := by
              rcases List.mem_cons.mp hv with rfl | h
              · have := hgt_y u hu'; omega
              · exact h
            exact ihy hpw_yt hok_y.2 u v hu' hv' huv
      exact hcp rest hpw_r hok.1 b c hb' hc' hbc
    · have hb' : b ∈ rest := by
        rcases List.mem_cons.mp hb with rfl | h
        · have := hgt a ha'; omega
        · exact h
      have hc' : c ∈ rest := by
        rcases List.mem_cons.mp hc with rfl | h
        · have := hgt a ha'; omega
        · exact h
      exact checkTriples_sound masks rest hpw_r hok.2 a b c ha' hb' hc' hab hbc

private theorem isClawFreeMasks_go_sound (n : Nat) (masks : List Nat) :
    ∀ k, isClawFreeMasks.go n masks k = true → ∀ u, u < k →
      isClawFreeMasks.checkTriples masks (isClawFreeMasks.nbsOf masks u 0 n) = true
  | 0, _, _, hu => by omega
  | k + 1, h, u, hu => by
    unfold isClawFreeMasks.go at h
    simp only [Bool.and_eq_true] at h
    by_cases huk : u = k
    · subst huk; exact h.1
    · exact isClawFreeMasks_go_sound n masks k h.2 u (by omega)

/-- **Soundness of `isClawFreeMasks`:** `isClawFreeMasks n masks = true → (masksGraph n masks).IsClawFree`. -/
theorem isClawFreeMasks_sound (n : Nat) (masks : List Nat)
    (h : isClawFreeMasks n masks = true) : (masksGraph n masks).IsClawFree := by
  intro u a b c hab hac hbc hua hub huc
  have htri := isClawFreeMasks_go_sound n masks n h u.val u.isLt
  have hpw := isClawFreeMasks_nbsOf_sorted masks u.val n 0
  have hma : a.val ∈ isClawFreeMasks.nbsOf masks u.val 0 n :=
    isClawFreeMasks_nbsOf_mem masks u.val n 0 a.val (Nat.zero_le _) (by omega) hua
  have hmb : b.val ∈ isClawFreeMasks.nbsOf masks u.val 0 n :=
    isClawFreeMasks_nbsOf_mem masks u.val n 0 b.val (Nat.zero_le _) (by omega) hub
  have hmc : c.val ∈ isClawFreeMasks.nbsOf masks u.val 0 n :=
    isClawFreeMasks_nbsOf_mem masks u.val n 0 c.val (Nat.zero_le _) (by omega) huc
  have hne_ab : a.val ≠ b.val := fun heq => hab (Fin.ext heq)
  have hne_ac : a.val ≠ c.val := fun heq => hac (Fin.ext heq)
  have hne_bc : b.val ≠ c.val := fun heq => hbc (Fin.ext heq)
  have hsym : ∀ x y : Fin n, maskAdj masks x.val y.val = true → maskAdj masks y.val x.val = true := by
    intro x y hxy
    change (masksGraph n masks).adj y x = true
    rw [(masksGraph n masks).symm]
    exact hxy
  -- Sort `(a.val, b.val, c.val)` into strictly increasing order (6 cases):
  by_cases h1 : a.val < b.val
  · by_cases h2 : b.val < c.val
    · exact checkTriples_sound masks _ hpw htri a.val b.val c.val hma hmb hmc h1 h2
    · by_cases h3 : a.val < c.val
      · rcases checkTriples_sound masks _ hpw htri a.val c.val b.val hma hmc hmb h3 (by omega) with h | h | h
        · exact Or.inr (Or.inl h)
        · exact Or.inl h
        · exact Or.inr (Or.inr (hsym c b h))
      · rcases checkTriples_sound masks _ hpw htri c.val a.val b.val hmc hma hmb (by omega) h1 with h | h | h
        · exact Or.inr (Or.inl (hsym c a h))
        · exact Or.inr (Or.inr (hsym c b h))
        · exact Or.inl h
  · by_cases h2 : a.val < c.val
    · rcases checkTriples_sound masks _ hpw htri b.val a.val c.val hmb hma hmc (by omega) h2 with h | h | h
      · exact Or.inl (hsym b a h)
      · exact Or.inr (Or.inr h)
      · exact Or.inr (Or.inl h)
    · by_cases h3 : b.val < c.val
      · rcases checkTriples_sound masks _ hpw htri b.val c.val a.val hmb hmc hma h3 (by omega) with h | h | h
        · exact Or.inr (Or.inr h)
        · exact Or.inl (hsym b a h)
        · exact Or.inr (Or.inl (hsym c a h))
      · rcases checkTriples_sound masks _ hpw htri c.val b.val a.val hmc hmb hma (by omega) (by omega) with h | h | h
        · exact Or.inr (Or.inr (hsym c b h))
        · exact Or.inr (Or.inl (hsym c a h))
        · exact Or.inl (hsym b a h)

/-- Inductive reachability inside an induced vertex subset `S : Fin n → Bool` of `FinGraph`. -/
inductive FinGraph.ReachableIn {n : Nat} (G : FinGraph n) (S : Fin n → Bool) : Fin n → Fin n → Prop
  | refl {u : Fin n} (hu : S u = true) : G.ReachableIn S u u
  | step {u v w : Fin n} (huv : G.ReachableIn S u v) (hw : S w = true) (hadj : G.adj v w = true) :
      G.ReachableIn S u w

theorem FinGraph.ReachableIn.symm {n : Nat} {G : FinGraph n} {S : Fin n → Bool}
    {u v : Fin n} (h : G.ReachableIn S u v) : G.ReachableIn S v u := by
  have htrans : ∀ {a b c : Fin n}, G.ReachableIn S a b → G.ReachableIn S b c → G.ReachableIn S a c := by
    intro a b c hab hbc
    induction hbc with
    | refl _ => exact hab
    | step _ hw hadj ih => exact FinGraph.ReachableIn.step ih hw hadj
  have hright : ∀ {a b : Fin n}, G.ReachableIn S a b → S b = true := by
    intro a b hab
    cases hab with
    | refl ha => exact ha
    | step _ hb _ => exact hb
  induction h with
  | refl hu => exact FinGraph.ReachableIn.refl hu
  | step hab hw hadj ih =>
    exact htrans (FinGraph.ReachableIn.step (FinGraph.ReachableIn.refl hw) (hright hab) (by rw [G.symm]; exact hadj)) ih

theorem FinGraph.ReachableIn.trans {n : Nat} {G : FinGraph n} {S : Fin n → Bool}
    {u v w : Fin n} (h1 : G.ReachableIn S u v) (h2 : G.ReachableIn S v w) : G.ReachableIn S u w := by
  induction h2 with
  | refl _ => exact h1
  | step _ hx hadj ih => exact FinGraph.ReachableIn.step ih hx hadj

/-- **Pure Combinatorial `K_5`-Minor Predicate on `FinGraph`:**
Five nonempty, pairwise vertex-disjoint, induced-connected branch sets `B : Fin 5 → List (Fin n)`
with at least one edge between every pair `i ≠ j` (certifying non-planarity with ZERO topological axioms). -/
def FinGraph.HasK5Minor {n : Nat} (G : FinGraph n) : Prop :=
  ∃ B : Fin 5 → List (Fin n),
    (∀ i : Fin 5, (B i) ≠ [] ∧ (B i).Nodup ∧
      ∀ u ∈ B i, ∀ v ∈ B i, G.ReachableIn (fun x => (B i).contains x) u v) ∧
    (∀ i j : Fin 5, i ≠ j →
      (∀ u ∈ B i, u ∉ B j) ∧
      ∃ u ∈ B i, ∃ v ∈ B j, G.adj u v = true)

private theorem foldl_or_testBit :
    ∀ (xs : List Nat) (init v : Nat),
      (xs.foldl (fun m x => m ||| (1 <<< x)) init).testBit v = (init.testBit v || xs.contains v)
  | [], init, v => by simp
  | x :: xs, init, v => by
    simp only [List.foldl_cons, List.contains_cons]
    rw [foldl_or_testBit xs (init ||| (1 <<< x)) v, testBit_or_shift]
    have hxv : (x == v) = (v == x) := by
      by_cases h : x = v
      · subst h; rfl
      · rw [beq_false_of_ne h, beq_false_of_ne (Ne.symm h)]
    rw [hxv]
    cases init.testBit v <;> cases (v == x) <;> cases xs.contains v <;> rfl

private theorem isSubsetConnected_sound (n : Nat) (masks : List Nat)
    (hSymm : ∀ a b, a < n → b < n → (getNat masks a).testBit b = true → maskAdj masks a b = true)
    (S : List Nat) (hS_lt : ∀ v ∈ S, v < n) (hconn : isSubsetConnected masks S = true) :
    let SFin := toFinList n S hS_lt
    SFin ≠ [] ∧ ∀ u ∈ SFin, ∀ v ∈ SFin,
      (masksGraph n masks).ReachableIn (fun x => SFin.contains x) u v := by
  dsimp only
  match hSeq : S with
  | [] => simp [isSubsetConnected] at hconn
  | s0 :: rest =>
    subst hSeq
    let SFin := toFinList n (s0 :: rest) hS_lt
    have hs0_lt : s0 < n := hS_lt s0 (List.mem_cons_self ..)
    let s0Fin : Fin n := ⟨s0, hs0_lt⟩
    have hmem_iff : ∀ (x : Fin n), SFin.contains x = true ↔ x.val ∈ (s0 :: rest) := by
      intro x
      rw [List.contains_iff_mem]
      have rec_iff : ∀ (ys : List Nat) (hy : ∀ v ∈ ys, v < n), x ∈ toFinList n ys hy ↔ x.val ∈ ys := by
        intro ys hy
        induction ys with
        | nil => simp [toFinList]
        | cons y yt ih =>
          simp only [toFinList, List.mem_cons]
          constructor
          · rintro (rfl | h)
            · exact Or.inl rfl
            · exact Or.inr ((ih _).mp h)
          · rintro (h | h)
            · exact Or.inl (Fin.ext h)
            · exact Or.inr ((ih _).mpr h)
      exact rec_iff (s0 :: rest) hS_lt
    unfold isSubsetConnected at hconn
    dsimp only at hconn
    let sMask := (s0 :: rest).foldl (fun m v => m ||| (1 <<< v)) 0
    have hsMask_bit : ∀ v, sMask.testBit v = (s0 :: rest).contains v := by
      intro v; dsimp only [sMask]; rw [foldl_or_testBit]; simp
    let step : Nat → Nat := fun vis =>
      (s0 :: rest).foldl (fun acc u => if vis.testBit u then acc ||| (getNat masks u &&& sMask) else acc) vis
    have hstep_reach : ∀ (vis : Nat),
        (∀ (x : Fin n), vis.testBit x.val = true →
          (masksGraph n masks).ReachableIn (fun y => SFin.contains y) s0Fin x) →
        ∀ (x : Fin n), (step vis).testBit x.val = true →
          (masksGraph n masks).ReachableIn (fun y => SFin.contains y) s0Fin x := by
      intro vis hvis
      have hfold : ∀ (us : List Nat) (acc : Nat),
          (∀ u ∈ us, u < n) →
          (∀ (x : Fin n), acc.testBit x.val = true →
            (masksGraph n masks).ReachableIn (fun y => SFin.contains y) s0Fin x) →
          ∀ (x : Fin n),
            (us.foldl (fun a u => if vis.testBit u then a ||| (getNat masks u &&& sMask) else a) acc).testBit x.val = true →
            (masksGraph n masks).ReachableIn (fun y => SFin.contains y) s0Fin x := by
        intro us
        induction us with
        | nil => intro acc _ hacc x hx; exact hacc x hx
        | cons u ur ih =>
          intro acc hus hacc x hx
          simp only [List.foldl_cons] at hx
          apply ih _ (fun v hv => hus v (List.mem_cons_of_mem u hv)) _ x hx
          intro z hz
          cases hvisu : vis.testBit u
          · simp only [hvisu, Bool.false_eq_true, ↓reduceIte] at hz
            exact hacc z hz
          · simp only [hvisu, ↓reduceIte, Nat.testBit_or, Nat.testBit_and, Bool.or_eq_true, Bool.and_eq_true] at hz
            rcases hz with hz1 | ⟨hbit, hsm⟩
            · exact hacc z hz1
            · have hu_lt : u < n := hus u (List.mem_cons_self ..)
              have hru := hvis ⟨u, hu_lt⟩ hvisu
              have hz_in : SFin.contains z = true := (hmem_iff z).mpr (List.contains_iff_mem.mp (hsMask_bit z.val ▸ hsm))
              have hadj : (masksGraph n masks).adj ⟨u, hu_lt⟩ z = true := hSymm u z.val hu_lt z.isLt hbit
              exact FinGraph.ReachableIn.step hru hz_in hadj
      exact hfold (s0 :: rest) vis hS_lt hvis
    have hiter_reach : ∀ (k vis : Nat),
        (∀ (x : Fin n), vis.testBit x.val = true →
          (masksGraph n masks).ReachableIn (fun y => SFin.contains y) s0Fin x) →
        ∀ (x : Fin n),
          (isSubsetConnected.iter step k vis).testBit x.val = true →
          (masksGraph n masks).ReachableIn (fun y => SFin.contains y) s0Fin x := by
      intro k
      induction k with
      | zero =>
        intro vis hvis x hx
        unfold isSubsetConnected.iter at hx
        exact hvis x hx
      | succ k' ih =>
        intro vis hvis x hx
        unfold isSubsetConnected.iter at hx
        exact ih (step vis) (hstep_reach vis hvis) x hx
    have hinit : ∀ (x : Fin n), (1 <<< s0).testBit x.val = true →
        (masksGraph n masks).ReachableIn (fun y => SFin.contains y) s0Fin x := by
      intro x hx
      have htb := testBit_or_shift 0 s0 x.val
      simp only [Nat.zero_or, Nat.zero_testBit, Bool.false_or] at htb
      rw [htb, beq_iff_eq] at hx
      have heq : x = s0Fin := Fin.ext hx.symm
      subst heq
      exact FinGraph.ReachableIn.refl ((hmem_iff s0Fin).mpr (List.mem_cons_self ..))
    refine ⟨List.cons_ne_nil _ _, ?_⟩
    intro u hu v hv
    have hu_val : u.val ∈ (s0 :: rest) := (hmem_iff u).mp (List.contains_iff_mem.mpr hu)
    have hv_val : v.val ∈ (s0 :: rest) := (hmem_iff v).mp (List.contains_iff_mem.mpr hv)
    have hru := hiter_reach (s0 :: rest).length (1 <<< s0) hinit u (List.all_eq_true.mp hconn u.val hu_val)
    have hrv := hiter_reach (s0 :: rest).length (1 <<< s0) hinit v (List.all_eq_true.mp hconn v.val hv_val)
    exact hru.symm.trans hrv

/-- **Soundness of `checkK5MinorBool`:**
If `masks` is symmetric & loopless on `0..n-1` and `checkK5MinorBool n masks sets = true`, then
`masksGraph n masks` contains a genuine `K_5`-minor (`FinGraph.HasK5Minor`)! -/
theorem checkK5MinorBool_sound (n : Nat) (masks : List Nat) (sets : List (List Nat))
    (hSymm : ∀ a b, a < n → b < n → (getNat masks a).testBit b = true → maskAdj masks a b = true)
    (hok : checkK5MinorBool n masks sets = true) :
    (masksGraph n masks).HasK5Minor := by
  unfold checkK5MinorBool at hok
  simp only [Bool.and_eq_true, beq_iff_eq] at hok
  rcases hok with ⟨⟨hlen5, hall_bs⟩, hall_pairs⟩
  have hlt_bs : ∀ (i : Fin 5) (v : Nat), v ∈ sets.getD i.val [] → v < n := by
    intro i v hv
    have hi : i.val < sets.length := by omega
    have hget : sets.getD i.val [] = sets[i.val]'hi := by simp [List.getD_eq_getElem?_getD, hi]
    rw [hget] at hv
    have hmem : sets[i.val]'hi ∈ sets := List.getElem_mem hi
    have hbs := List.all_eq_true.mp hall_bs _ hmem
    simp only [Bool.and_eq_true] at hbs
    have hblt := List.all_eq_true.mp hbs.1.2 v hv
    unfold Nat.blt at hblt; have := Nat.le_of_ble_eq_true hblt; omega
  let B : Fin 5 → List (Fin n) := fun i => toFinList n (sets.getD i.val []) (hlt_bs i)
  have hmemB : ∀ (i : Fin 5) (x : Fin n), x ∈ B i ↔ x.val ∈ sets.getD i.val [] := by
    intro i x
    dsimp only [B]
    have rec_iff : ∀ (ys : List Nat) (hy : ∀ v ∈ ys, v < n), x ∈ toFinList n ys hy ↔ x.val ∈ ys := by
      intro ys hy
      induction ys with
      | nil => simp [toFinList]
      | cons y yt ih =>
        simp only [toFinList, List.mem_cons]
        constructor
        · rintro (rfl | h)
          · exact Or.inl rfl
          · exact Or.inr ((ih _).mp h)
        · rintro (h | h)
          · exact Or.inl (Fin.ext h)
          · exact Or.inr ((ih _).mpr h)
    exact rec_iff (sets.getD i.val []) (hlt_bs i)
  refine ⟨B, ?_, ?_⟩
  · intro i
    have hi : i.val < sets.length := by omega
    have hget : sets.getD i.val [] = sets[i.val]'hi := by simp [List.getD_eq_getElem?_getD, hi]
    have hbs := List.all_eq_true.mp hall_bs _ (hget ▸ List.getElem_mem hi)
    simp only [Bool.and_eq_true] at hbs
    rcases isSubsetConnected_sound n masks hSymm (sets.getD i.val []) (hlt_bs i) hbs.2 with ⟨hne, hreach⟩
    exact ⟨hne, toFinList_nodup n _ (hlt_bs i) (nodupNat_sound hbs.1.1.2), hreach⟩
  · intro i j hij
    have hne_val : i.val ≠ j.val := fun h => hij (Fin.ext h)
    have hpair_lt : ∀ (p q : Fin 5), p.val < q.val →
        (∀ u ∈ B p, u ∉ B q) ∧ (∃ u ∈ B p, ∃ v ∈ B q, (masksGraph n masks).adj u v = true) := by
      intro p q hpq
      have h1 := List.all_eq_true.mp hall_pairs p.val (List.mem_range.mpr p.isLt)
      have h2 := List.all_eq_true.mp h1 q.val (List.mem_range.mpr q.isLt)
      have hblt : Nat.blt p.val q.val = true := Nat.ble_eq_true_of_le (by omega)
      simp only [hblt, ↓reduceIte, Bool.and_eq_true] at h2
      rcases h2 with ⟨hdisj, hedge⟩
      refine ⟨?_, ?_⟩
      · intro u hup huq
        have hnot := List.all_eq_true.mp hdisj u.val ((hmemB p u).mp hup)
        simp only [Bool.not_eq_true'] at hnot
        have hc := List.contains_iff_mem.mpr ((hmemB q u).mp huq)
        rw [hc] at hnot; cases hnot
      · rcases List.any_eq_true.mp hedge with ⟨u0, hu0, hany⟩
        rcases List.any_eq_true.mp hany with ⟨v0, hv0, hadj⟩
        let uFin : Fin n := ⟨u0, hlt_bs p u0 hu0⟩
        let vFin : Fin n := ⟨v0, hlt_bs q v0 hv0⟩
        exact ⟨uFin, (hmemB p uFin).mpr hu0, vFin, (hmemB q vFin).mpr hv0, hadj⟩
    by_cases hlt : i.val < j.val
    · exact hpair_lt i j hlt
    · rcases hpair_lt j i (by omega) with ⟨hdisj, u, huj, v, hvi, hadj⟩
      exact ⟨fun w hwi hwj => hdisj w hwj hwi, v, hvi, u, huj, by rw [(masksGraph n masks).symm]; exact hadj⟩

/-! ## 2. Direct Expanded-Port Kills (`0/4`, `0/128`, `0/2048`) Directly on `FinGraph` -/

private theorem checkPortChunk_sound (targets : List Nat) :
    ∀ (cfgs : List SplitConfig) (cycs : List (List Nat)),
      checkPortChunk targets cfgs cycs = true →
      ∀ cfg ∈ cfgs, SplitConfigWellFormed cfg ∧ ∃ L ∈ targets, (expandedPortGraph cfg).HasSimpleCycleOfLen L
  | [], [], _, _, hmem => by cases hmem
  | [], _ :: _, h, _, _ => by simp [checkPortChunk] at h
  | _ :: _, [], h, _, _ => by simp [checkPortChunk] at h
  | cfg :: cfgs, cyc :: cycs, h, c, hc => by
    unfold checkPortChunk at h
    cases hok : (splitConfigWellFormed cfg && memNat cyc.length targets && checkCycleDirect cfg cyc)
    · rw [hok] at h; simp at h
    · rw [hok] at h; simp only [↓reduceIte] at h
      simp only [Bool.and_eq_true] at hok
      rcases List.mem_cons.mp hc with rfl | hrest
      · exact ⟨hok.1.1, cyc.length, (memNat_iff_mem _ _).mp hok.1.2, checkCycleDirect_sound c cyc hok.2⟩
      · exact checkPortChunk_sound targets cfgs cycs h c hrest

/-- **Direct Expanded-Port Kill 1 (`deg3_tri` — ALL `4` Split Configurations → `C_8`):** -/
theorem port_kill_deg3_tri_all_4 :
    deg3TriConfigs.length = 4 ∧
    ∀ cfg ∈ deg3TriConfigs, (expandedPortGraph cfg).HasSimpleCycleOfLen 8 := by
  refine ⟨port_config_counts.1, ?_⟩
  intro cfg hcfg
  rcases (checkPortChunk_sound [8] deg3TriConfigs deg3TriCycles deg3Tri_all_4_ok cfg hcfg).2 with ⟨L, hL, hcyc⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hL
  exact hL ▸ hcyc

/-- **Direct Expanded-Port Kill 2 (`K_{2,3}` — ALL `128` Split Configurations → `C_8` or `C_16`):** -/
theorem port_kill_k23_all_128 :
    k23Configs.length = 128 ∧
    ∀ cfg ∈ k23Configs,
      (expandedPortGraph cfg).HasSimpleCycleOfLen 8 ∨
      (expandedPortGraph cfg).HasSimpleCycleOfLen 16 := by
  refine ⟨port_config_counts.2.1, ?_⟩
  intro cfg hcfg
  have hsplit : k23Configs = k23Configs.take 64 ++ k23Configs.drop 64 := (List.take_append_drop 64 k23Configs).symm
  rw [hsplit, List.mem_append] at hcfg
  rcases hcfg with h0 | h1
  · rcases (checkPortChunk_sound [8, 16] _ _ k23_c0_ok cfg h0).2 with ⟨L, hL, hcyc⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hL
    rcases hL with rfl | rfl
    · exact Or.inl hcyc
    · exact Or.inr hcyc
  · rcases (checkPortChunk_sound [8, 16] _ _ k23_c1_ok cfg h1).2 with ⟨L, hL, hcyc⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hL
    rcases hL with rfl | rfl
    · exact Or.inl hcyc
    · exact Or.inr hcyc

private theorem checkPortChunk128_sound (targets : List Nat) (cfgs : List SplitConfig) (cycs : List (List Nat))
    (h : (checkPortChunk targets (cfgs.take 64) (cycs.take 64) &&
          checkPortChunk targets (cfgs.drop 64) (cycs.drop 64)) = true) :
    ∀ cfg ∈ cfgs, SplitConfigWellFormed cfg ∧ ∃ L ∈ targets, (expandedPortGraph cfg).HasSimpleCycleOfLen L := by
  simp only [Bool.and_eq_true] at h
  intro cfg hcfg
  have hsplit : cfgs = cfgs.take 64 ++ cfgs.drop 64 := (List.take_append_drop 64 cfgs).symm
  rw [hsplit, List.mem_append] at hcfg
  rcases hcfg with h0 | h1
  · exact checkPortChunk_sound targets _ _ h.1 cfg h0
  · exact checkPortChunk_sound targets _ _ h.2 cfg h1

private theorem cartProd_cons2 (a b : List SplitChoice) (rest : List (List SplitChoice)) :
    cartProd (a :: b :: rest) =
      a.flatMap fun o0 => b.flatMap fun o1 => (cartProd rest).map fun tl => o0 :: o1 :: tl := by
  simp only [cartProd, List.map_flatMap, List.map_map]
  rfl

private theorem q3MinusVConfigs_eq_flatMap :
    q3MinusVConfigs =
      q3Opt0.flatMap fun o0 =>
        (q3Opt1.flatMap fun o1 => q3Tail128.map fun tl => o0 :: o1 :: tl) := by
  have hgo : allSplitConfigs.go [] 0 q3MinusVRows =
      q3Opt0 :: q3Opt1 :: allSplitConfigs.go [] 0 [[0, 3, 6], [1, 2], [0, 5, 6], [1, 4], [2, 4]] := by
    decide
  change cartProd (allSplitConfigs.go [] 0 q3MinusVRows) =
    q3Opt0.flatMap fun o0 =>
      q3Opt1.flatMap fun o1 =>
        (cartProd (allSplitConfigs.go [] 0 [[0, 3, 6], [1, 2], [0, 5, 6], [1, 4], [2, 4]])).map fun tl => o0 :: o1 :: tl
  rw [hgo, cartProd_cons2]

private theorem q3MinusVConfigs_length_2048 : q3MinusVConfigs.length = 2048 := by
  rw [q3MinusVConfigs_eq_flatMap]
  have htail : ∀ o0 o1, (q3Tail128.map fun tl => o0 :: o1 :: tl).length = 128 := by
    intro o0 o1; rw [List.length_map]; exact port_config_counts.2.2.2.2
  have hlen_flat : ∀ {α β : Type} (xs : List α) (f : α → List β) (k : Nat),
      (∀ x ∈ xs, (f x).length = k) → (xs.flatMap f).length = xs.length * k := by
    intro α β xs f k hf
    induction xs with
    | nil => simp
    | cons x rest ih =>
      simp only [List.flatMap_cons, List.length_append, List.length_cons]
      rw [hf x (List.mem_cons_self ..), ih (fun y hy => hf y (List.mem_cons_of_mem x hy)),
          Nat.add_mul, Nat.one_mul, Nat.add_comm]
  rw [hlen_flat q3Opt0 _ (4 * 128)]
  · rw [port_config_counts.2.2.1]
  · intro o0 _
    rw [hlen_flat q3Opt1 _ 128 (fun o1 _ => htail o0 o1), port_config_counts.2.2.2.1]

private theorem q3MinusV_all_2048_bundle (cfg : SplitConfig) (hcfg : cfg ∈ q3MinusVConfigs) :
    SplitConfigWellFormed cfg ∧
    ∃ L ∈ ([8, 16] : List Nat), (expandedPortGraph cfg).HasSimpleCycleOfLen L := by
  rw [q3MinusVConfigs_eq_flatMap, List.mem_flatMap] at hcfg
  rcases hcfg with ⟨o0, ho0, h1⟩
  rw [List.mem_flatMap] at h1
  rcases h1 with ⟨o1, ho1, h2⟩
  rcases List.mem_iff_getElem.mp ho0 with ⟨i0, hi0, rfl⟩
  rcases List.mem_iff_getElem.mp ho1 with ⟨i1, hi1, rfl⟩
  have hi0_4 : i0 < 4 := port_config_counts.2.2.1 ▸ hi0
  have hi1_4 : i1 < 4 := port_config_counts.2.2.2.1 ▸ hi1
  let c := 4 * i0 + i1
  have hmem : cfg ∈ q3MinusVChunk c := by
    unfold q3MinusVChunk
    have hc0 : c / 4 = i0 := by dsimp only [c]; omega
    have hc1 : c % 4 = i1 := by dsimp only [c]; omega
    rw [hc0, hc1]
    have hg0 : q3Opt0.getD i0 ([], none) = q3Opt0[i0]'hi0 := by simp [List.getD_eq_getElem?_getD, hi0]
    have hg1 : q3Opt1.getD i1 ([], none) = q3Opt1[i1]'hi1 := by simp [List.getD_eq_getElem?_getD, hi1]
    rw [hg0, hg1]
    exact h2
  have hc16 : c < 16 := by dsimp only [c]; omega
  match c with
  | 0 => exact checkPortChunk128_sound [8, 16] _ _ q3MinusV_c0_ok cfg hmem
  | 1 => exact checkPortChunk128_sound [8, 16] _ _ q3MinusV_c1_ok cfg hmem
  | 2 => exact checkPortChunk128_sound [8, 16] _ _ q3MinusV_c2_ok cfg hmem
  | 3 => exact checkPortChunk128_sound [8, 16] _ _ q3MinusV_c3_ok cfg hmem
  | 4 => exact checkPortChunk128_sound [8, 16] _ _ q3MinusV_c4_ok cfg hmem
  | 5 => exact checkPortChunk128_sound [8, 16] _ _ q3MinusV_c5_ok cfg hmem
  | 6 => exact checkPortChunk128_sound [8, 16] _ _ q3MinusV_c6_ok cfg hmem
  | 7 => exact checkPortChunk128_sound [8, 16] _ _ q3MinusV_c7_ok cfg hmem
  | 8 => exact checkPortChunk128_sound [8, 16] _ _ q3MinusV_c8_ok cfg hmem
  | 9 => exact checkPortChunk128_sound [8, 16] _ _ q3MinusV_c9_ok cfg hmem
  | 10 => exact checkPortChunk128_sound [8, 16] _ _ q3MinusV_c10_ok cfg hmem
  | 11 => exact checkPortChunk128_sound [8, 16] _ _ q3MinusV_c11_ok cfg hmem
  | 12 => exact checkPortChunk128_sound [8, 16] _ _ q3MinusV_c12_ok cfg hmem
  | 13 => exact checkPortChunk128_sound [8, 16] _ _ q3MinusV_c13_ok cfg hmem
  | 14 => exact checkPortChunk128_sound [8, 16] _ _ q3MinusV_c14_ok cfg hmem
  | 15 => exact checkPortChunk128_sound [8, 16] _ _ q3MinusV_c15_ok cfg hmem
  | n + 16 => omega

/-- **Direct Expanded-Port Kill 3 (`Q_3 - v^*` — ALL `2,048` Split Configurations → `C_8` or `C_16`):** -/
theorem port_kill_q3_minus_v_all_2048 :
    q3MinusVConfigs.length = 2048 ∧
    ∀ cfg ∈ q3MinusVConfigs,
      (expandedPortGraph cfg).HasSimpleCycleOfLen 8 ∨
      (expandedPortGraph cfg).HasSimpleCycleOfLen 16 := by
  refine ⟨q3MinusVConfigs_length_2048, ?_⟩
  intro cfg hcfg
  rcases (q3MinusV_all_2048_bundle cfg hcfg).2 with ⟨L, hL, hcyc⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hL
  rcases hL with rfl | rfl
  · exact Or.inl hcyc
  · exact Or.inr hcyc

/-- **Well-Formedness of ALL `4 + 128 + 2,048` Expanded-Port Configurations & `f11G39SplitConfig`:**
Every split configuration checked by the port-expansion engine satisfies `SplitConfigWellFormed`
(symmetric duplicate-free loopless incidence, split side lengths `≤ 2` / unsplit `≤ 3`, valid
partners, pairwise-disjoint bowtie pairs, and vertex indices strictly below the `1000` sentinel). -/
theorem port_configs_wellFormed :
    (∀ cfg ∈ deg3TriConfigs, SplitConfigWellFormed cfg) ∧
    (∀ cfg ∈ k23Configs, SplitConfigWellFormed cfg) ∧
    (∀ cfg ∈ q3MinusVConfigs, SplitConfigWellFormed cfg) ∧
    SplitConfigWellFormed f11G39SplitConfig := by
  refine ⟨fun cfg hcfg => (checkPortChunk_sound [8] deg3TriConfigs deg3TriCycles deg3Tri_all_4_ok cfg hcfg).1,
          ?_,
          fun cfg hcfg => (q3MinusV_all_2048_bundle cfg hcfg).1,
          f11G39_wellFormed_bool⟩
  intro cfg hcfg
  have hsplit : k23Configs = k23Configs.take 64 ++ k23Configs.drop 64 := (List.take_append_drop 64 k23Configs).symm
  rw [hsplit, List.mem_append] at hcfg
  rcases hcfg with h0 | h1
  · exact (checkPortChunk_sound [8, 16] _ _ k23_c0_ok cfg h0).1
  · exact (checkPortChunk_sound [8, 16] _ _ k23_c1_ok cfg h1).1

/-- Parallel-edge lift-window `C_8` exclusion (`[5, 8]` and `[6, 10]` both contain `2^3 = 8`). -/
theorem parallel_edge_hits_c8 : ¬AvoidsPow2 5 8 ∧ ¬AvoidsPow2 6 10 :=
  ⟨fun h => h 3 (by decide) ⟨by decide, by decide⟩,
   fun h => h 3 (by decide) ⟨by decide, by decide⟩⟩

/-! ## 3. Sharp Non-Planar `K_5`-Minor Witness `G_39` (`F_11`, `H_14`, `G_39`) -/

/-- The 11-vertex bowtie-contracted simple quotient `F_11` (`18` edges, `tw(F_11) = 3`). -/
def F11 : FinGraph 11 := masksGraph 11 f11Masks

/-- The 14-vertex cubic triangle quotient `H_14` (`3` independent bowties, `K_5`-minor). -/
def H14 : FinGraph 14 := masksGraph 14 h14Masks

/-- The sharp 39-vertex non-planar claw-free witness `G_39 = T(H_14)/B`. -/
def G39 : FinGraph 39 := masksGraph 39 g39Masks

/-- Explicit spanning 3-tree `T_11` containing `F_11` as a spanning subgraph:
base `K_4 = {0, 1, 2, 7}`, then simplicial additions `3 ~ {0,1,2}`, `4 ~ {0,1,3}`,
`5 ~ {1,2,3}`, `6 ~ {0,2,3}`, `8 ~ {0,1,7}`, `9 ~ {1,2,7}`, `10 ~ {0,2,7}`. -/
def t11Edges : List (Nat × Nat) :=
  [(0, 1), (0, 2), (1, 2), (0, 7), (1, 7), (2, 7),
   (3, 0), (3, 1), (3, 2),
   (4, 0), (4, 1), (4, 3),
   (5, 1), (5, 2), (5, 3),
   (6, 0), (6, 2), (6, 3),
   (8, 0), (8, 1), (8, 7),
   (9, 1), (9, 2), (9, 7),
   (10, 0), (10, 2), (10, 7)]

def T11 : FinGraph 11 := masksGraph 11 (masksFromEdges 11 t11Edges)

/-- Helper to build one `Is3TreeOn.addSimplicial` step by `decide` on `Fin 11`. -/
private def sList (xs : List Nat) (u : Fin 11) : Bool := xs.contains u.val

private theorem addSimp11 {S_new S_old : List Nat} (v a b c : Fin 11)
    (hprev : Is3TreeOn T11 (sList S_old))
    (hcheck :
      (sList S_old v == false) &&
      ((List.finRange 11).all fun u => sList S_new u == (sList S_old u || (u == v))) &&
      sList S_old a && sList S_old b && sList S_old c &&
      (a != b) && (a != c) && (b != c) &&
      T11.adj a b && T11.adj a c && T11.adj b c &&
      ((List.finRange 11).all fun u =>
        if sList S_old u then (T11.adj v u == ((u == a) || (u == b) || (u == c))) else true) = true) :
    Is3TreeOn T11 (sList S_new) := by
  simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne] at hcheck
  rcases hcheck with ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hv, hS⟩, ha⟩, hb⟩, hc⟩, hab⟩, hac⟩, hbc⟩, h1⟩, h2⟩, h3⟩, hnb⟩
  refine Is3TreeOn.addSimplicial (sList S_new) (sList S_old) v a b c hprev hv
    (fun u => by have := List.all_eq_true.mp hS u (List.mem_finRange u); simpa using this)
    ha hb hc hab hac hbc ⟨h1, h2, h3⟩ ?_
  intro u hu
  have h := List.all_eq_true.mp hnb u (List.mem_finRange u)
  simp only [hu, ↓reduceIte, beq_iff_eq] at h
  rw [h]; simp [or_assoc]

/-- **`tw(F_11) ≤ 3` Directly on `FinGraph`:**
`F_11` is a spanning subgraph of the explicit spanning 3-tree `T_11` (`IsSpanning3Tree T11`),
AND satisfies the explicit 8-bag width-3 tree decomposition (`f11_tw3_decomp_ok`)! -/
theorem f11_tw3_certified :
    F11.IsSubgraphOf T11 ∧
    IsSpanning3Tree T11 ∧
    checkTw3DecompBool 11 f11Edges f11Tw3Bags f11Tw3TreeEdges = true := by
  have hsub_b : ((List.finRange 11).all fun u =>
      (List.finRange 11).all fun v => if F11.adj u v then T11.adj u v else true) = true := by decide
  have hsub : F11.IsSubgraphOf T11 := by
    intro u v huv
    have h1 := List.all_eq_true.mp hsub_b u (List.mem_finRange u)
    have h2 := List.all_eq_true.mp h1 v (List.mem_finRange v)
    simp only [huv, ↓reduceIte] at h2; exact h2
  have hbase_clq : ((List.finRange 11).all fun u => (List.finRange 11).all fun v =>
      if sList [0, 1, 2, 7] u && sList [0, 1, 2, 7] v && (u != v) then T11.adj u v else true) = true := by decide
  have h0 : Is3TreeOn T11 (sList [0, 1, 2, 7]) := by
    apply Is3TreeOn.baseK4 (sList [0, 1, 2, 7]) (by decide)
    intro u v hu hv huv
    have h1 := List.all_eq_true.mp hbase_clq u (List.mem_finRange u)
    have h2 := List.all_eq_true.mp h1 v (List.mem_finRange v)
    simp only [hu, hv, bne_iff_ne.mpr huv, Bool.and_self, ↓reduceIte] at h2; exact h2
  have h1 := addSimp11 (S_new := [0, 1, 2, 7, 3]) ⟨3, by decide⟩ ⟨0, by decide⟩ ⟨1, by decide⟩ ⟨2, by decide⟩ h0 (by decide)
  have h2 := addSimp11 (S_new := [0, 1, 2, 7, 3, 4]) ⟨4, by decide⟩ ⟨0, by decide⟩ ⟨1, by decide⟩ ⟨3, by decide⟩ h1 (by decide)
  have h3 := addSimp11 (S_new := [0, 1, 2, 7, 3, 4, 5]) ⟨5, by decide⟩ ⟨1, by decide⟩ ⟨2, by decide⟩ ⟨3, by decide⟩ h2 (by decide)
  have h4 := addSimp11 (S_new := [0, 1, 2, 7, 3, 4, 5, 6]) ⟨6, by decide⟩ ⟨0, by decide⟩ ⟨2, by decide⟩ ⟨3, by decide⟩ h3 (by decide)
  have h5 := addSimp11 (S_new := [0, 1, 2, 7, 3, 4, 5, 6, 8]) ⟨8, by decide⟩ ⟨0, by decide⟩ ⟨1, by decide⟩ ⟨7, by decide⟩ h4 (by decide)
  have h6 := addSimp11 (S_new := [0, 1, 2, 7, 3, 4, 5, 6, 8, 9]) ⟨9, by decide⟩ ⟨1, by decide⟩ ⟨2, by decide⟩ ⟨7, by decide⟩ h5 (by decide)
  have h7 := addSimp11 (S_new := [0, 1, 2, 7, 3, 4, 5, 6, 8, 9, 10]) ⟨10, by decide⟩ ⟨0, by decide⟩ ⟨2, by decide⟩ ⟨7, by decide⟩ h6 (by decide)
  have hall_eq : ((List.finRange 11).all fun u => sList [0, 1, 2, 7, 3, 4, 5, 6, 8, 9, 10] u) = true := by decide
  have hspan : IsSpanning3Tree T11 :=
    h7.congr (fun u => List.all_eq_true.mp hall_eq u (List.mem_finRange u))
  exact ⟨hsub, hspan, f11_tw3_decomp_bool⟩

private theorem maskSymm_check (n : Nat) (masks : List Nat)
    (h : ((List.range n).all fun a => (List.range n).all fun b =>
      if (getNat masks a).testBit b then maskAdj masks a b else true) = true) :
    ∀ a b, a < n → b < n → (getNat masks a).testBit b = true → maskAdj masks a b = true := by
  intro a b ha hb hbit
  have h1 := List.all_eq_true.mp h a (List.mem_range.mpr ha)
  have h2 := List.all_eq_true.mp h1 b (List.mem_range.mpr hb)
  simp only [hbit, ↓reduceIte] at h2; exact h2

private theorem h14_masks_symm_bool :
    ((List.range 14).all fun a => (List.range 14).all fun b =>
      if (getNat h14Masks a).testBit b then maskAdj h14Masks a b else true) = true := by decide

private theorem g39_masks_symm_bool :
    ((List.range 39).all fun a => (List.range 39).all fun b =>
      if (getNat g39Masks a).testBit b then maskAdj g39Masks a b else true) = true := by decide

private theorem g39_adj_covers_masks_bool :
    ((List.range 39).all fun u => (List.range 39).all fun v =>
      if maskAdj g39Masks u v then (getAdj g39Adj u).contains v else true) = true := by decide

private theorem g39_adj_covers_masks :
    ∀ u v, u < 39 → v < 39 → maskAdj g39Masks u v = true → v ∈ getAdj g39Adj u := by
  intro u v hu hv hadj
  have h1 := List.all_eq_true.mp g39_adj_covers_masks_bool u (List.mem_range.mpr hu)
  have h2 := List.all_eq_true.mp h1 v (List.mem_range.mpr hv)
  simp only [hadj, ↓reduceIte] at h2
  exact List.contains_iff_mem.mp h2

/-- **Sharp Non-Planar `K_5`-Minor Witness Theorem (`G_39 = T(H_14)/B`):**
Directly kernel-verified on `FinGraph` with ZERO topological axioms:
1. `G_39` equals `expandedPortGraph f11G39SplitConfig` (split of `F_11` with `tw(F_11) ≤ 3`),
2. `G_39` has minimum degree `3`, max degree `4`, and exact degree-4 set `g39V4 = [2, 7, 12]`
   (pairwise non-adjacent: independent bowties),
3. `G_39` is claw-free (`G39.IsClawFree`),
4. `G_39` is sharp for `C_16` vs. `C_8` (with `C_4` also excluded):
   `¬G39.HasSimpleCycleOfLen 4 ∧ ¬G39.HasSimpleCycleOfLen 8 ∧ G39.HasSimpleCycleOfLen 16`,
5. `H_14` is cubic (`H14.IsCubic`), and `H_14` and `G_39` each admit an explicit `K_5`-minor
   model with five nonempty connected pairwise vertex-disjoint branch sets *within each* model
   (`H14.HasK5Minor ∧ G39.HasK5Minor`). -/
theorem g39_sharp_nonplanar_witness :
    (expandedPortCount f11G39SplitConfig = 39 ∧
      ∀ u v : Fin 39, portAdjConfig f11G39SplitConfig u.val v.val = G39.adj u v) ∧
    G39.MinDegreeAtLeast 3 ∧
    (∀ u : Fin 39, G39.deg u = if g39V4.contains u.val then 4 else 3) ∧
    (∀ u v : Fin 39, g39V4.contains u.val = true → g39V4.contains v.val = true → G39.adj u v = false) ∧
    G39.IsClawFree ∧
    ¬G39.HasSimpleCycleOfLen 4 ∧
    ¬G39.HasSimpleCycleOfLen 8 ∧
    G39.HasSimpleCycleOfLen 16 ∧
    H14.IsCubic ∧
    H14.HasK5Minor ∧
    G39.HasK5Minor := by
  have hg39_exp : expandedPortCount f11G39SplitConfig = 39 ∧
      ∀ u v : Fin 39, portAdjConfig f11G39SplitConfig u.val v.val = G39.adj u v := by
    refine ⟨g39_eq_f11_split_expanded.1, fun u v => ?_⟩
    have h1 := List.all_eq_true.mp g39_eq_f11_split_expanded.2 u.val (List.mem_range.mpr u.isLt)
    have h2 := List.all_eq_true.mp h1 v.val (List.mem_range.mpr v.isLt)
    exact beq_iff_eq.mp h2
  have hdeg : ∀ u : Fin 39, G39.deg u = if g39V4.contains u.val then 4 else 3 := by
    intro u
    change (masksGraph 39 g39Masks).deg u = _
    rw [← maskDeg_eq_deg 39 g39Masks u]
    have h1 := List.all_eq_true.mp g39_deg_and_clawfree_ok.1 u.val (List.mem_range.mpr u.isLt)
    exact beq_iff_eq.mp h1
  have hmin3 : G39.MinDegreeAtLeast 3 := by
    refine ⟨by omega, fun u => ?_⟩
    rw [hdeg u]; split <;> omega
  have hv4_ind : ∀ u v : Fin 39, g39V4.contains u.val = true → g39V4.contains v.val = true → G39.adj u v = false := by
    intro u v hu hv
    have h1 := List.all_eq_true.mp g39_deg_and_clawfree_ok.2.1 u.val (List.contains_iff_mem.mp hu)
    have h2 := List.all_eq_true.mp h1 v.val (List.contains_iff_mem.mp hv)
    simpa [G39, masksGraph] using h2
  have hh14_cub : H14.IsCubic := by
    refine ⟨by omega, fun u => ?_⟩
    change (masksGraph 14 h14Masks).deg u = 3
    rw [← maskDeg_eq_deg 14 h14Masks u]
    have h1 := List.all_eq_true.mp h14_cubic_ok u.val (List.mem_range.mpr u.isLt)
    exact beq_iff_eq.mp h1
  refine ⟨hg39_exp, hmin3, hdeg, hv4_ind,
    isClawFreeMasks_sound 39 g39Masks g39_deg_and_clawfree_ok.2.2,
    hasSimpleCycleLenBool_false_sound 39 g39Masks g39Adj 4 (by decide) g39_adj_covers_masks g39_no_c4_bool,
    hasSimpleCycleLenBool_false_sound 39 g39Masks g39Adj 8 (by decide) g39_adj_covers_masks g39_no_c8_bool,
    g39_c16_ok.2 ▸ checkCycleMasks_sound 39 g39Masks g39C16 g39_c16_ok.1,
    hh14_cub,
    checkK5MinorBool_sound 14 h14Masks h14K5BranchSets (maskSymm_check 14 h14Masks h14_masks_symm_bool) h14_k5_minor_bool,
    checkK5MinorBool_sound 39 g39Masks g39K5BranchSets (maskSymm_check 39 g39Masks g39_masks_symm_bool) g39_k5_minor_bool⟩

/-! ## 4. Dyadic-Cycle-Free Independent-Bowtie Order `≥ 120` & Tier-1 Hamiltonian All-Chord-`B` -/

/-- **Dyadic-Cycle-Free Independent-Bowtie 4-Regular Quotient Order Bridge (`|V(G)| = 5 * |V(F)| ≥ 120`):**
For a **dyadic-cycle-free** (EG-counterexample) independent-bowtie claw-free graph `G = T(H)/B`
with `δ(G) ≥ 3` and `Δ(G) ≤ 4` whose bowtie-contracted simple quotient `F = H/H_B` is 4-regular
(`|V(H)| = 2*c`, `|B| = c` where `c = |V(F)|`), we have `|V(G)| = 3*|V(H)| - |B| = 5*c`, hence
`c ≥ 24 → |V(G)| ≥ 120`. (Note: dyadic-cycle avoidance is essential — unconditionally a 25-vertex
`K_5`-quotient independent-bowtie claw-free graph exists and contains `C_16`; the graph-level case
split deriving `c ≥ 24` from dyadic-cycle avoidance is proved in the manuscript + `verify_clawfree_eg.py`.) -/
theorem indep_bowtie_4reg_order_5c (c nH b nG : Nat)
    (hH : nH = 2 * c) (hB : b = c) (hG : nG = 3 * nH - b) :
    nG = 5 * c ∧ (c ≥ 24 → nG ≥ 120) := by
  omega

/-- Computable `AvoidsPow2` checker on finite intervals `[lo, hi]`. -/
private def avoidsPow2Bool (lo hi : Nat) : Bool :=
  let rec go (p : Nat) : Nat → Bool
    | 0 => true
    | fuel + 1 =>
      if Nat.blt hi p then true
      else if Nat.ble lo p then false
      else go (2 * p) fuel
  go 4 (hi + 1)

private theorem avoidsPow2Bool_false_sound (lo hi : Nat) (h : avoidsPow2Bool lo hi = false) :
    ¬AvoidsPow2 lo hi := by
  have hgo : ∀ (fuel p a : Nat), a ≥ 2 → p = 2 ^ a → avoidsPow2Bool.go lo hi p fuel = false → ¬AvoidsPow2 lo hi := by
    intro fuel
    induction fuel with
    | zero => intro p a _ _ hf; simp [avoidsPow2Bool.go] at hf
    | succ f ih =>
      intro p a ha hp hf
      unfold avoidsPow2Bool.go at hf
      cases hhi : Nat.blt hi p
      · rw [hhi] at hf; simp only [Bool.false_eq_true, ↓reduceIte] at hf
        cases hlo : Nat.ble lo p
        · rw [hlo] at hf; simp only [Bool.false_eq_true, ↓reduceIte] at hf
          exact ih (2 * p) (a + 1) (by omega) (by rw [Nat.pow_succ, hp]; omega) hf
        · intro hav
          have hle_lo : lo ≤ 2 ^ a := hp ▸ Nat.le_of_ble_eq_true hlo
          have hle_hi : 2 ^ a ≤ hi := by
            have hnot : ¬(hi < p) := fun hlt => by
              have : Nat.blt hi p = true := Nat.ble_eq_true_of_le (by omega)
              rw [this] at hhi; cases hhi
            omega
          exact hav a ha ⟨hle_lo, hle_hi⟩
      · rw [hhi] at hf; simp at hf
  exact hgo (hi + 1) 4 2 (by decide) rfl h

/-- Exact `allowed_s` table for `r ∈ {3..8}` and `(a, b) ∈ {3,4} × {3..8}` cycle-merge kills +
Moore/distance-3 minimum `24 → 120` (matching `verify_clawfree_eg.py` lines 1687–1703 & 1846–1852).
Note: the `360,612` lifted-`H` configuration sweep + `166` extra-vertex overlap enumeration are
verified zero-float in `cert/verify_clawfree_eg.py`. -/
def allowedSOf : Nat → List Nat
  | 3 => [3]
  | 4 => [1]
  | 5 => [0]
  | 6 => [5, 6]
  | 7 => [3, 4, 5]
  | 8 => [1, 2, 3]
  | _ => []

private theorem allowedS_exact_bool :
    ([3, 4, 5, 6, 7, 8] : List Nat).all (fun r =>
      ((List.range (r + 1)).filter fun s => avoidsPow2Bool (2 * r + s) (3 * r + 2 * s)) == allowedSOf r) = true := by
  decide

private theorem merge_kills_bool :
    ([3, 4] : List Nat).all (fun a =>
      ([3, 4, 5, 6, 7, 8] : List Nat).all fun b =>
        (allowedSOf a).all fun sa =>
          (allowedSOf b).all fun sb =>
            if sa == 0 || sb == 0 then true
            else
              let L := (a + sa) + (b + sb) - 2
              let k := sa + sb - 2
              !(avoidsPow2Bool (2 * L - k) (3 * L - k - 1))) = true := by
  decide

theorem indep_bowtie_120_arithmetic_bundle :
    (([3, 4, 5, 6, 7, 8] : List Nat).all (fun r =>
      ((List.range (r + 1)).filter fun s => avoidsPow2Bool (2 * r + s) (3 * r + 2 * s)) == allowedSOf r) = true) ∧
    (∀ a ∈ ([3, 4] : List Nat), ∀ b ∈ ([3, 4, 5, 6, 7, 8] : List Nat),
      ∀ sa ∈ allowedSOf a, ∀ sb ∈ allowedSOf b, sa ≠ 0 → sb ≠ 0 →
        let L := (a + sa) + (b + sb) - 2
        let k := sa + sb - 2
        ¬AvoidsPow2 (2 * L - k) (3 * L - k - 1)) ∧
    min (min (1 + 4 + 10 + 7 + 7) (1 + 4 + 12 + (36 - 4 + 3) / 4))
        (min (1 + 4 + 11 + (32 - 2 + 3) / 4) (1 + 4 + 10 + 2 + 3 + 2 + 3)) = 24 ∧
    5 * 24 = 120 := by
  refine ⟨allowedS_exact_bool, ?_, by decide, by decide⟩
  intro a ha b hb sa hsa sb hsb hsa0 hsb0
  have h1 := List.all_eq_true.mp merge_kills_bool a ha
  have h2 := List.all_eq_true.mp h1 b hb
  have h3 := List.all_eq_true.mp h2 sa hsa
  have h4 := List.all_eq_true.mp h3 sb hsb
  have hnz : (sa == 0 || sb == 0) = false := by
    rw [beq_false_of_ne hsa0, beq_false_of_ne hsb0]; rfl
  simp only [hnz, Bool.false_eq_true, ↓reduceIte, Bool.not_eq_true'] at h4
  exact avoidsPow2Bool_false_sound _ _ h4

/-- **Hamiltonian All-Chord-`B` 2-Chord Girth `L_2 ≥ 10`:**
Every 2-chord cycle of length `L ∈ {4, 5, 7, 8, 9}` with `0 ≤ m ≤ (L - 4)/2` internal chords
has a lift window `[2*L - 2, 3*L - 2 - m]` hitting a power of two (and `[10, 16]`, `[6, 10]`
both hit `2^4 = 16` / `2^3 = 8`). -/
theorem ham_all_chord_b_L2_ge_10 :
    (∀ L ∈ ([4, 5, 7, 8, 9] : List Nat), ∀ m : Nat, m ≤ (L - 4) / 2 →
      ¬AvoidsPow2 (2 * L - 2) (3 * L - 2 - m)) ∧
    ¬AvoidsPow2 10 16 ∧
    ¬AvoidsPow2 6 10 := by
  refine ⟨?_, fun h => h 4 (by decide) ⟨by decide, by decide⟩,
               fun h => h 3 (by decide) ⟨by decide, by decide⟩⟩
  intro L hL m hm
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hL
  rcases hL with rfl | rfl | rfl | rfl | rfl
  · exact fun h => h 3 (by decide) ⟨by omega, by omega⟩
  · exact fun h => h 3 (by decide) ⟨by omega, by omega⟩
  · exact fun h => h 4 (by decide) ⟨by omega, by omega⟩
  · exact fun h => h 4 (by decide) ⟨by omega, by omega⟩
  · exact fun h => h 4 (by decide) ⟨by omega, by omega⟩

/-- **UNIVERSAL 4-Tier Dyadic-Octave Interval Coverage Theorem (ALL `a ≥ 4`, `P = 2^a ≥ 16`):**
For EVERY power of two `P = 2^a ≥ 16`, the three octave tiers
- Tier A: `[a_lo, a_hi] = [(4*P - 1)/5, P - 1]`,
- Tier B: `[b_lo, b_hi] = [(8*P + 14)/15, (8*P - 2)/12]`,
- Tier C: `[c_lo, c_hi] = [(16*P + 24)/25, (16*P - 2)/20]`
satisfy ALL exact lift-window hits (`2*P`, `4*P`, `8*P`, `16*P`) AND overlap seamlessly across
odd integers (`b_hi` overlaps `c_lo`, `c_hi` overlaps `a_lo`), closing every odd translate
universally across ALL octaves! -/
theorem ham_all_chord_b_4tier_octave_universal (a : Nat) (ha : a ≥ 4) :
    let P := 2 ^ a
    let a_lo := (4 * P - 1) / 5
    let a_hi := P - 1
    let b_lo := (8 * P + 14) / 15
    let b_hi := (8 * P - 2) / 12
    let c_lo := (16 * P + 24) / 25
    let c_hi := (16 * P - 2) / 20
    (∀ j ∈ ([4, 5, 6] : List Nat), 4 * (j + 1) ≤ 5 * j) ∧
    (2 * a_hi + 1 ≤ 2 * P ∧ 2 * P ≤ (5 * a_lo + 5) / 2) ∧
    (4 * a_hi + 2 ≤ 4 * P ∧ 4 * P ≤ 5 * a_lo + 5) ∧
    (12 * b_hi ≤ 8 * P ∧ 8 * P ≤ 15 * b_lo ∧ 12 * b_hi + 2 ≤ 8 * P ∧ 8 * P ≤ 15 * b_lo + 5) ∧
    (20 * c_hi ≤ 16 * P ∧ 16 * P ≤ 25 * c_lo ∧ 20 * c_hi + 2 ≤ 16 * P ∧ 16 * P ≤ 25 * c_lo + 5) ∧
    (b_hi + 1 ≥ c_lo) ∧
    (c_hi ≥ a_lo) := by
  have hP16 : 2 ^ a ≥ 16 := Nat.le_trans (by decide : 16 ≤ 2 ^ 4) (Nat.pow_le_pow_right (by omega) ha)
  have hPmod4 : 2 ^ a % 4 = 0 := by
    obtain ⟨j, rfl⟩ : ∃ j, a = j + 2 := ⟨a - 2, by omega⟩
    rw [Nat.pow_succ, Nat.pow_succ]; omega
  generalize 2 ^ a = P at hP16 hPmod4 ⊢
  dsimp only
  refine ⟨by decide, ⟨by omega, by omega⟩, ⟨by omega, by omega⟩,
          ⟨by omega, by omega, by omega, by omega⟩,
          ⟨by omega, by omega, by omega, by omega⟩,
          by omega, by omega⟩

/-- **Hamiltonian All-Chord-`B` Rim-`C_256` Closure (ALL even `104 ≤ N ≤ 128`):**
For every even `N = 2 * k` with `52 ≤ k ≤ 64`, the rim cycle `C_N` (`k` internal chords) has
lift window `[2*N, 3*N - k] = [4*k, 5*k]` containing `2^8 = 256`! -/
theorem ham_all_chord_b_rim_c256_104_to_128 (k : Nat) (hlo : 52 ≤ k) (hhi : k ≤ 64) :
    ¬AvoidsPow2 (2 * (2 * k)) (3 * (2 * k) - k) :=
  fun hav => hav 8 (by decide) ⟨by omega, by omega⟩

/-- Exact Tier-1 `39` all-order periods (`cert/witnesses/hamiltonian_all_chord_b.json`). -/
def tier1All39Periods : List Nat :=
  [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 17, 19, 21, 23, 25,
   27, 29, 31, 33, 35, 37, 39, 41, 43, 45, 47, 49, 51, 53, 55, 57, 59, 61, 63]

/-- Exact Tier-1 `23` open odd `(g, m)` cases (`n = g*m > 128`) closed by `verify_clawfree_eg.py` (`93,902` visits). -/
def tier1OddOpen23 : List (Nat × Nat) :=
  [(23, 6), (23, 8), (33, 4), (33, 6), (33, 8), (33, 10), (33, 12),
   (35, 4), (37, 4), (39, 4), (41, 4), (43, 4), (43, 6), (43, 8),
   (45, 4), (45, 6), (45, 8), (47, 4), (47, 6), (47, 8), (49, 4), (49, 6), (49, 8)]

private def isOddOpenCase (g m : Nat) : Bool :=
  let n := m * g
  Nat.blt 128 n &&
  avoidsPow2Bool (2 * n) ((5 * n) / 2) &&
  avoidsPow2Bool (2 * (n / 2 + 1) - 1) ((5 * (n / 2 + 1) + 1) / 2) &&
  (List.range (m / 2 - 1)).all fun j0 =>
    let j := j0 + 1
    avoidsPow2Bool (4 * j * g + 2) (5 * j * g + 5)

private def computeOddOpen23 : List (Nat × Nat) :=
  ((List.range 32).map fun i => 2 * i + 1).flatMap fun g =>
    ((List.range 6).map fun j => 2 * j + 2).filterMap fun m =>
      if isOddOpenCase g m then some (g, m) else none

/-- **Tier-1 Hamiltonian All-Chord-`B` Exact Period Classification:**
Kernel-verifies:
1. `tier1All39Periods.length = 39` (all 32 odd periods `1..63`, all 6 short even periods
   `{2, 4, 6, 10, 12, 14}` closed by `W ≤ 31`, and period `8` with `2*56 + 7 + 31 < 168`),
2. `computeOddOpen23 = tier1OddOpen23` (exact `23` open odd `(g, m)` pairs above `N = 128`).
Note: the finite backtracking sweeps (`W ≤ 31` `L_win = 17` [`29,357`], `k = 8`, `23` odd
[`93,902`], and arbitrary matchings even `N ≤ 136` [`641` leaves `≤ 102`, `{130:73, 132:236,
134:242, 136:723}`]) are independently verified zero-float in `cert/verify_clawfree_eg.py`. -/
theorem ham_all_chord_b_tier1_periods_39 :
    tier1All39Periods.length = 39 ∧
    ([2, 4, 6, 10, 12, 14] : List Nat).all (fun k =>
      (List.range 7).any fun j0 =>
        let j := j0 + 1
        Nat.ble (j * k) 31 && !(avoidsPow2Bool (4 * j * k + 2) (5 * j * k + 5))) = true ∧
    2 * 56 + 7 + 31 < 168 ∧
    computeOddOpen23 = tier1OddOpen23 ∧
    tier1OddOpen23.length = 23 := by
  decide

end ClawFreeEG

