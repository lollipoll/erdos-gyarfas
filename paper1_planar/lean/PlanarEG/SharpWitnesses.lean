import PlanarEG.GraphCore
import PlanarEG.SharpData

/-!
# PlanarEG.SharpWitnesses

100% kernel-verified (ZERO `sorry`, ZERO `axiom`, ZERO `native_decide`) formalization
of the three flagship sharpness witnesses for Paper 1:
1. **`G168` (`C24 * [T1 + P + T2]`, 168 vertices):**
   - Cubic `PlaneMap 168`, 252 edges, 86 faces (`48` triangles, `24` pentagons, `12` 17-faces, `2` 18-faces),
     Euler `168 - 252 + 86 = 2`, exact dart-bijection certificate;
   - **3-connected** (via 3-Port Gadget-Inflation 3-Connectivity Theorem over `C24` and `G7`);
   - **ZERO `C_4`, `C_8`, `C_16`** (in fact zero cycles of lengths `4` and `8..16` via 3-Port Gadget-Inflation
     Cycle Dichotomy: `G7` has 7 vertices & no `C_4`, `C24` has girth 5 & min lifted 5-cycle length `17`);
   - **Explicit simple `C_32` cycle verified!**
2. **`C60` (Truncated Icosahedron, 60 vertices):**
   - Cubic `PlaneMap 60`, 90 edges, 32 faces (`12` pentagons, `20` hexagons), Euler `60 - 90 + 32 = 2`,
     exact dart-bijection certificate;
   - **ZERO `C_3`, `C_4`, `C_8`**;
   - **Explicit simple `C_16` cycle verified!**
3. **`TD60` (Truncated Dodecahedron, 60 vertices):**
   - Cubic `PlaneMap 60`, 90 edges, 32 faces (`20` triangles, `12` decagons), Euler `60 - 90 + 32 = 2`,
     exact dart-bijection certificate;
   - **ZERO `C_4, C_5, C_6, C_7, C_8, C_9`** (via 3-Port Gadget-Inflation over girth-5 `D20`);
   - **Explicit simple `C_16` cycle verified!**
-/

namespace PlanarEG

open SharpData

/-! ## 0. Zero-Allocation `allFin` / `foldFin` Combinators for Fast Kernel Checking -/

/-- Allocation-free universal quantifier over `Fin n` (avoids constructing `List.finRange n`
proof terms inside kernel `decide`). -/
def allFinGo (n : Nat) (p : Fin n → Bool) : (k : Nat) → k ≤ n → Bool
  | 0, _ => true
  | k + 1, hk => p ⟨k, hk⟩ && allFinGo n p k (Nat.le_of_lt hk)

def allFin (n : Nat) (p : Fin n → Bool) : Bool :=
  allFinGo n p n (Nat.le_refl n)

theorem allFinGo_eq_true {n : Nat} {p : Fin n → Bool} :
    ∀ {k : Nat} (hk : k ≤ n), allFinGo n p k hk = true →
      ∀ (i : Nat) (hi : i < k), p ⟨i, Nat.lt_of_lt_of_le hi hk⟩ = true
  | 0, _, _, _, hi => absurd hi (Nat.not_lt_zero _)
  | k + 1, hk, h, i, hi => by
    simp only [allFinGo, Bool.and_eq_true] at h
    by_cases heq : i = k
    · subst heq; exact h.1
    · exact allFinGo_eq_true (Nat.le_of_lt hk) h.2 i (by omega)

theorem allFin_eq_true {n : Nat} {p : Fin n → Bool} (h : allFin n p = true) (u : Fin n) :
    p u = true :=
  allFinGo_eq_true (Nat.le_refl n) h u.val u.isLt

/-- Allocation-free fold over `Fin n` (for fast kernel bitmask propagation). -/
def foldFinGo {α : Type} (n : Nat) (f : α → Fin n → α) (acc : α) : (k : Nat) → k ≤ n → α
  | 0, _ => acc
  | k + 1, hk => foldFinGo n f (f acc ⟨k, hk⟩) k (Nat.le_of_lt hk)

def foldFin {α : Type} (n : Nat) (f : α → Fin n → α) (init : α) : α :=
  foldFinGo n f init n (Nat.le_refl n)

theorem foldFin_inv {α : Type} {n : Nat} {P : α → Prop} {f : α → Fin n → α} {init : α}
    (hinit : P init) (hstep : ∀ acc (x : Fin n), P acc → P (f acc x)) :
    P (foldFin n f init) := by
  have hgo : ∀ (k : Nat) (hk : k ≤ n) (acc : α), P acc → P (foldFinGo n f acc k hk) := by
    intro k
    induction k with
    | zero => intro _ acc ha; exact ha
    | succ k ih => intro hk acc ha; exact ih (Nat.le_of_lt hk) (f acc ⟨k, hk⟩) (hstep acc ⟨k, hk⟩ ha)
  exact hgo n (Nat.le_refl n) init hinit

private theorem nodup_map_of_inj {α β : Type} {f : α → β} {l : List α}
    (hnd : l.Nodup) (hinj : ∀ a ∈ l, ∀ b ∈ l, f a = f b → a = b) : (l.map f).Nodup := by
  induction l with
  | nil => exact List.nodup_nil
  | cons x xs ih =>
    rcases List.nodup_cons.mp hnd with ⟨hxnot, hndxs⟩
    rw [List.map_cons, List.nodup_cons]
    refine ⟨?_, ih hndxs (fun a ha b hb => hinj a (List.mem_cons_of_mem x ha) b (List.mem_cons_of_mem x hb))⟩
    intro hmem
    rcases List.mem_map.mp hmem with ⟨y, hy, hfy⟩
    have hyx : y = x := hinj y (List.mem_cons_of_mem x hy) x (List.mem_cons_self ..) hfy
    exact hxnot (hyx ▸ hy)

/-! ## 1. Fast Cubic Graph Specification & Proof-Carrying PlaneMap Builder -/

/-- Exact cubic adjacency specification via 3-neighbor lookup. -/
structure CubicSpec (n : Nat) where
  nbrs : Fin n → Fin n × Fin n × Fin n
  valid : allFin n (fun u =>
    let t := nbrs u
    let a := t.1
    let b := t.2.1
    let c := t.2.2
    let has (x y : Fin n) : Bool :=
      let s := nbrs x
      y == s.1 || y == s.2.1 || y == s.2.2
    a != u && b != u && c != u &&
    a != b && b != c && a != c &&
    has a u && has b u && has c u) = true

namespace CubicSpec

def nbr1 {n : Nat} (S : CubicSpec n) (u : Fin n) : Fin n := (S.nbrs u).1
def nbr2 {n : Nat} (S : CubicSpec n) (u : Fin n) : Fin n := (S.nbrs u).2.1
def nbr3 {n : Nat} (S : CubicSpec n) (u : Fin n) : Fin n := (S.nbrs u).2.2

def nbrList {n : Nat} (S : CubicSpec n) (u : Fin n) : List (Fin n) :=
  [S.nbr1 u, S.nbr2 u, S.nbr3 u]

def adjBool {n : Nat} (S : CubicSpec n) (u v : Fin n) : Bool :=
  v == S.nbr1 u || v == S.nbr2 u || v == S.nbr3 u

theorem valid_at {n : Nat} (S : CubicSpec n) (u : Fin n) :
    S.nbr1 u ≠ u ∧ S.nbr2 u ≠ u ∧ S.nbr3 u ≠ u ∧
    S.nbr1 u ≠ S.nbr2 u ∧ S.nbr2 u ≠ S.nbr3 u ∧ S.nbr1 u ≠ S.nbr3 u ∧
    S.adjBool (S.nbr1 u) u = true ∧ S.adjBool (S.nbr2 u) u = true ∧ S.adjBool (S.nbr3 u) u = true := by
  have h := allFin_eq_true S.valid u
  simp only [Bool.and_eq_true, bne_iff_ne] at h
  rcases h with ⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

theorem adjBool_symm_imp {n : Nat} (S : CubicSpec n) {u v : Fin n}
    (h : S.adjBool u v = true) : S.adjBool v u = true := by
  have hv := S.valid_at u
  unfold adjBool at h
  simp only [Bool.or_eq_true, beq_iff_eq] at h
  rcases h with (rfl | rfl) | rfl
  · exact hv.2.2.2.2.2.2.1
  · exact hv.2.2.2.2.2.2.2.1
  · exact hv.2.2.2.2.2.2.2.2

theorem adjBool_symm {n : Nat} (S : CubicSpec n) (u v : Fin n) :
    S.adjBool u v = S.adjBool v u := by
  cases huv : S.adjBool u v
  · cases hvu : S.adjBool v u
    · rfl
    · have h := S.adjBool_symm_imp hvu
      rw [huv] at h; cases h
  · exact (S.adjBool_symm_imp huv).symm

theorem adjBool_loopless {n : Nat} (S : CubicSpec n) (u : Fin n) :
    S.adjBool u u = false := by
  have hv := S.valid_at u
  unfold adjBool
  have h1 : (u == S.nbr1 u) = false := beq_false_of_ne (Ne.symm hv.1)
  have h2 : (u == S.nbr2 u) = false := beq_false_of_ne (Ne.symm hv.2.1)
  have h3 : (u == S.nbr3 u) = false := beq_false_of_ne (Ne.symm hv.2.2.1)
  simp [h1, h2, h3]

def toFinGraph {n : Nat} (S : CubicSpec n) : FinGraph n where
  adj := S.adjBool
  symm := S.adjBool_symm
  loopless := S.adjBool_loopless

@[simp] theorem toFinGraph_adj {n : Nat} (S : CubicSpec n) (u v : Fin n) :
    S.toFinGraph.adj u v = S.adjBool u v := rfl

theorem mem_nbrList_iff {n : Nat} (S : CubicSpec n) (u v : Fin n) :
    v ∈ S.nbrList u ↔ S.toFinGraph.adj u v = true := by
  simp only [nbrList, toFinGraph_adj, adjBool, List.mem_cons, List.not_mem_nil, or_false,
             Bool.or_eq_true, beq_iff_eq, or_assoc]

private theorem filter_beq_length {α : Type} [BEq α] [LawfulBEq α]
    (l : List α) (hnd : l.Nodup) (a : α) :
    (l.filter (· == a)).length = if a ∈ l then 1 else 0 := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    rcases List.nodup_cons.mp hnd with ⟨hxnot, hndxs⟩
    by_cases hxa : x = a
    · subst hxa
      have htail : xs.filter (· == x) = [] := by
        rw [List.filter_eq_nil_iff]
        intro y hy
        have hyx : y ≠ x := fun h => hxnot (h ▸ hy)
        simp [beq_false_of_ne hyx]
      simp [htail]
    · have hbeq : (x == a) = false := beq_false_of_ne hxa
      simp only [List.filter_cons, hbeq, Bool.false_eq_true, ↓reduceIte, List.mem_cons]
      rw [ih hndxs]
      have hne : (a = x) ↔ False := ⟨fun h => hxa h.symm, False.elim⟩
      simp [hne]

private theorem filter_or_length {α : Type} (l : List α) (p q : α → Bool)
    (hdisj : ∀ x ∈ l, !(p x && q x) = true) :
    (l.filter fun x => p x || q x).length = (l.filter p).length + (l.filter q).length := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    have hx := hdisj x (List.mem_cons_self ..)
    have hxs := ih (fun y hy => hdisj y (List.mem_cons_of_mem x hy))
    cases hpx : p x <;> cases hqx : q x
    · simp [hpx, hqx, hxs]
    · simp [hpx, hqx, hxs]; omega
    · simp [hpx, hqx, hxs]; omega
    · simp [hpx, hqx] at hx

theorem toFinGraph_deg_eq_three {n : Nat} (S : CubicSpec n) : ∀ u : Fin n, S.toFinGraph.deg u = 3 := by
  intro u
  have hv := S.valid_at u
  rcases hv with ⟨_, _, _, hab, hbc, hac, _, _, _⟩
  let a := S.nbr1 u
  let b := S.nbr2 u
  let c := S.nbr3 u
  have hgoal : S.toFinGraph.deg u = ((List.finRange n).filter fun v => (v == a || v == b) || v == c).length := rfl
  rw [hgoal]
  have h1 := filter_or_length (List.finRange n) (fun v => v == a || v == b) (fun v => v == c) (by
    intro x _
    cases hxa : (x == a) <;> cases hxb : (x == b) <;> cases hxc : (x == c) <;> simp
    · exact hbc ((beq_iff_eq.mp hxb).symm.trans (beq_iff_eq.mp hxc))
    · exact hac ((beq_iff_eq.mp hxa).symm.trans (beq_iff_eq.mp hxc))
    · exact hac ((beq_iff_eq.mp hxa).symm.trans (beq_iff_eq.mp hxc)))
  have h2 := filter_or_length (List.finRange n) (fun v => v == a) (fun v => v == b) (by
    intro x _
    cases hxa : (x == a) <;> cases hxb : (x == b) <;> simp
    exact hab ((beq_iff_eq.mp hxa).symm.trans (beq_iff_eq.mp hxb)))
  rw [h1, h2]
  rw [filter_beq_length _ (List.nodup_finRange n) a,
      filter_beq_length _ (List.nodup_finRange n) b,
      filter_beq_length _ (List.nodup_finRange n) c]
  simp [List.mem_finRange]

theorem toFinGraph_isCubic {n : Nat} (S : CubicSpec n) (hn : n ≥ 1) : S.toFinGraph.IsCubic :=
  ⟨hn, S.toFinGraph_deg_eq_three⟩

theorem toFinGraph_handshaking {n : Nat} (S : CubicSpec n) :
    sumNat ((List.finRange n).map S.toFinGraph.deg) = 3 * n := by
  have h : (List.finRange n).map S.toFinGraph.deg = (List.finRange n).map (fun _ => 3) := by
    apply List.map_congr_left
    intro v _
    exact S.toFinGraph_deg_eq_three v
  rw [h, sumNat_map_const, List.length_finRange]
  omega

/-- Look up the directed edge `(f[p], f[(p+1) % f.length])` at `(faceIdx, pos)`. -/
def faceDartAt {n : Nat} (faces : List (List (Fin n))) (loc : Nat × Nat) : Option (Fin n × Fin n) :=
  match faces[loc.1]? with
  | none => none
  | some f =>
    if hlen : loc.2 < f.length then
      let nxt := (loc.2 + 1) % f.length
      have hn : nxt < f.length := Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le _) hlen)
      some (f[loc.2]'hlen, f[nxt]'hn)
    else none

/-- Look up the facial corner `(prev, u, next)` at `(faceIdx, pos)` in `faces`. -/
def faceCornerAt {n : Nat} (faces : List (List (Fin n))) (loc : Nat × Nat) :
    Option (Fin n × Fin n × Fin n) :=
  match faces[loc.1]? with
  | none => none
  | some f =>
    if hlen : loc.2 < f.length then
      let prev := (loc.2 + f.length - 1) % f.length
      let nxt := (loc.2 + 1) % f.length
      have hp : prev < f.length := Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le _) hlen)
      have hn : nxt < f.length := Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le _) hlen)
      some (f[prev]'hp, f[loc.2]'hlen, f[nxt]'hn)
    else none

/-- Computable check that all faces are valid simple cycles in `S`. -/
def facesValidBool {n : Nat} (S : CubicSpec n) (faces : List (List (Fin n))) : Bool :=
  faces.all fun f => S.toFinGraph.isSimpleCycleBool f

/-- Computable dart-bijection certificate: total face-darts = `3*n` and every directed
edge `(u, nbr_k u)` is witnessed at `dartLoc u k` in `faces`. -/
def dartBijectionBool {n : Nat} (S : CubicSpec n) (faces : List (List (Fin n)))
    (dartLoc : Fin n → Fin 3 → Nat × Nat) : Bool :=
  (sumNat (faces.map List.length) == 3 * n) &&
  allFin n (fun u =>
    faceDartAt faces (dartLoc u 0) == some (u, S.nbr1 u) &&
    faceDartAt faces (dartLoc u 1) == some (u, S.nbr2 u) &&
    faceDartAt faces (dartLoc u 2) == some (u, S.nbr3 u))

/-- Propositional statement of the exact dart bijection. -/
def HasExactDartBijection {n : Nat} (S : CubicSpec n) (faces : List (List (Fin n)))
    (dartLoc : Fin n → Fin 3 → Nat × Nat) : Prop :=
  sumNat (faces.map List.length) = 3 * n ∧
  (∀ u v : Fin n, S.toFinGraph.adj u v = true →
    ∃ slot : Fin 3, faceDartAt faces (dartLoc u slot) = some (u, v)) ∧
  (∀ u1 u2 : Fin n, ∀ s1 s2 : Fin 3, dartLoc u1 s1 = dartLoc u2 s2 → u1 = u2 ∧ s1 = s2)

theorem dartBijection_of_bool {n : Nat} (S : CubicSpec n) (faces : List (List (Fin n)))
    (dartLoc : Fin n → Fin 3 → Nat × Nat)
    (h : dartBijectionBool S faces dartLoc = true) :
    HasExactDartBijection S faces dartLoc := by
  simp only [dartBijectionBool, Bool.and_eq_true, beq_iff_eq] at h
  rcases h with ⟨hsum, hall⟩
  have hslot : ∀ u : Fin n,
      faceDartAt faces (dartLoc u 0) = some (u, S.nbr1 u) ∧
      faceDartAt faces (dartLoc u 1) = some (u, S.nbr2 u) ∧
      faceDartAt faces (dartLoc u 2) = some (u, S.nbr3 u) := by
    intro u
    have hu := allFin_eq_true hall u
    simp only [Bool.and_eq_true, beq_iff_eq] at hu
    exact ⟨hu.1.1, hu.1.2, hu.2⟩
  refine ⟨hsum, ?_, ?_⟩
  · intro u v huv
    have hs := hslot u
    simp only [toFinGraph_adj, adjBool, Bool.or_eq_true, beq_iff_eq] at huv
    rcases huv with (rfl | rfl) | rfl
    · exact ⟨0, hs.1⟩
    · exact ⟨1, hs.2.1⟩
    · exact ⟨2, hs.2.2⟩
  · intro u1 u2 s1 s2 heq
    have hs1 := hslot u1
    have hs2 := hslot u2
    have hval1 : ∃ v1, faceDartAt faces (dartLoc u1 s1) = some (u1, v1) := by
      match s1 with
      | ⟨0, _⟩ => exact ⟨S.nbr1 u1, hs1.1⟩
      | ⟨1, _⟩ => exact ⟨S.nbr2 u1, hs1.2.1⟩
      | ⟨2, _⟩ => exact ⟨S.nbr3 u1, hs1.2.2⟩
    have hval2 : ∃ v2, faceDartAt faces (dartLoc u2 s2) = some (u2, v2) := by
      match s2 with
      | ⟨0, _⟩ => exact ⟨S.nbr1 u2, hs2.1⟩
      | ⟨1, _⟩ => exact ⟨S.nbr2 u2, hs2.2.1⟩
      | ⟨2, _⟩ => exact ⟨S.nbr3 u2, hs2.2.2⟩
    rcases hval1 with ⟨v1, hv_1⟩
    rcases hval2 with ⟨v2, hv_2⟩
    rw [heq] at hv_1
    rw [hv_1] at hv_2
    have hu : u1 = u2 := (Prod.mk.inj (Option.some.inj hv_2)).1
    subst hu
    refine ⟨rfl, ?_⟩
    rcases S.valid_at u1 with ⟨_, _, _, hab, hbc, hac, _, _, _⟩
    match s1, s2, heq with
    | ⟨0, _⟩, ⟨0, _⟩, _ => rfl
    | ⟨1, _⟩, ⟨1, _⟩, _ => rfl
    | ⟨2, _⟩, ⟨2, _⟩, _ => rfl
    | ⟨0, _⟩, ⟨1, _⟩, heq =>
      have h01 := hs1.1
      change faceDartAt faces (dartLoc u1 ⟨0, by decide⟩) = some (u1, S.nbr1 u1) at h01
      rw [heq] at h01
      change faceDartAt faces (dartLoc u1 1) = some (u1, S.nbr1 u1) at h01
      rw [hs1.2.1] at h01
      exact absurd (Prod.mk.inj (Option.some.inj h01)).2.symm hab
    | ⟨0, _⟩, ⟨2, _⟩, heq =>
      have h02 := hs1.1
      change faceDartAt faces (dartLoc u1 ⟨0, by decide⟩) = some (u1, S.nbr1 u1) at h02
      rw [heq] at h02
      change faceDartAt faces (dartLoc u1 2) = some (u1, S.nbr1 u1) at h02
      rw [hs1.2.2] at h02
      exact absurd (Prod.mk.inj (Option.some.inj h02)).2.symm hac
    | ⟨1, _⟩, ⟨0, _⟩, heq =>
      have h10 := hs1.2.1
      change faceDartAt faces (dartLoc u1 ⟨1, by decide⟩) = some (u1, S.nbr2 u1) at h10
      rw [heq] at h10
      change faceDartAt faces (dartLoc u1 0) = some (u1, S.nbr2 u1) at h10
      rw [hs1.1] at h10
      exact absurd (Prod.mk.inj (Option.some.inj h10)).2 hab
    | ⟨1, _⟩, ⟨2, _⟩, heq =>
      have h12 := hs1.2.1
      change faceDartAt faces (dartLoc u1 ⟨1, by decide⟩) = some (u1, S.nbr2 u1) at h12
      rw [heq] at h12
      change faceDartAt faces (dartLoc u1 2) = some (u1, S.nbr2 u1) at h12
      rw [hs1.2.2] at h12
      exact absurd (Prod.mk.inj (Option.some.inj h12)).2.symm hbc
    | ⟨2, _⟩, ⟨0, _⟩, heq =>
      have h20 := hs1.2.2
      change faceDartAt faces (dartLoc u1 ⟨2, by decide⟩) = some (u1, S.nbr3 u1) at h20
      rw [heq] at h20
      change faceDartAt faces (dartLoc u1 0) = some (u1, S.nbr3 u1) at h20
      rw [hs1.1] at h20
      exact absurd (Prod.mk.inj (Option.some.inj h20)).2 hac
    | ⟨2, _⟩, ⟨1, _⟩, heq =>
      have h21 := hs1.2.2
      change faceDartAt faces (dartLoc u1 ⟨2, by decide⟩) = some (u1, S.nbr3 u1) at h21
      rw [heq] at h21
      change faceDartAt faces (dartLoc u1 1) = some (u1, S.nbr3 u1) at h21
      rw [hs1.2.1] at h21
      exact absurd (Prod.mk.inj (Option.some.inj h21)).2 hbc

/-- Computable single-cyclic-rotation-per-vertex checker: around every vertex `u` with
neighbors `(a, b, c)`, the three facial corners `(pred, u, succ)` at `dartLoc u 0..2`
induce a single 3-cycle permutation (`(c,u,a),(a,u,b),(b,u,c)` or `(b,u,a),(c,u,b),(a,u,c)`). -/
def singleVertexRotationBool {n : Nat} (S : CubicSpec n) (faces : List (List (Fin n)))
    (dartLoc : Fin n → Fin 3 → Nat × Nat) : Bool :=
  allFin n fun u =>
    let a := S.nbr1 u
    let b := S.nbr2 u
    let c := S.nbr3 u
    let c0 := faceCornerAt faces (dartLoc u 0)
    let c1 := faceCornerAt faces (dartLoc u 1)
    let c2 := faceCornerAt faces (dartLoc u 2)
    (c0 == some (c, u, a) && c1 == some (a, u, b) && c2 == some (b, u, c)) ||
    (c0 == some (b, u, a) && c1 == some (c, u, b) && c2 == some (a, u, c))

/-- Propositional single-cyclic-rotation-per-vertex certificate:
coupled with `HasExactDartBijection` (so total face corners = `3*n`), at every vertex `u`
the three incident facial corners induce a single 3-cycle cyclic rotation of `u`'s 3 neighbors. -/
def HasSingleVertexRotation {n : Nat} (S : CubicSpec n) (faces : List (List (Fin n)))
    (dartLoc : Fin n → Fin 3 → Nat × Nat) : Prop :=
  HasExactDartBijection S faces dartLoc ∧
  ∀ u : Fin n,
    let a := S.nbr1 u
    let b := S.nbr2 u
    let c := S.nbr3 u
    (faceCornerAt faces (dartLoc u 0) = some (c, u, a) ∧
     faceCornerAt faces (dartLoc u 1) = some (a, u, b) ∧
     faceCornerAt faces (dartLoc u 2) = some (b, u, c)) ∨
    (faceCornerAt faces (dartLoc u 0) = some (b, u, a) ∧
     faceCornerAt faces (dartLoc u 1) = some (c, u, b) ∧
     faceCornerAt faces (dartLoc u 2) = some (a, u, c))

theorem singleVertexRotation_of_bool {n : Nat} (S : CubicSpec n) (faces : List (List (Fin n)))
    (dartLoc : Fin n → Fin 3 → Nat × Nat)
    (hb : HasExactDartBijection S faces dartLoc)
    (hrot : singleVertexRotationBool S faces dartLoc = true) :
    HasSingleVertexRotation S faces dartLoc := by
  refine ⟨hb, fun u => ?_⟩
  have hu := allFin_eq_true hrot u
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at hu
  rcases hu with ⟨⟨h0, h1⟩, h2⟩ | ⟨⟨h0, h1⟩, h2⟩
  · exact Or.inl ⟨h0, h1, h2⟩
  · exact Or.inr ⟨h0, h1, h2⟩

/-- Build a kernel-verified `PlaneMap n` from a `CubicSpec n` and face list. -/
def buildPlaneMap {n : Nat} (S : CubicSpec n) (faces : List (List (Fin n))) (numEdges : Nat)
    (hfaces : facesValidBool S faces = true)
    (hsumF : sumNat (faces.map List.length) = 2 * numEdges)
    (h3n : 3 * n = 2 * numEdges)
    (heuler : (n : Int) - (numEdges : Int) + (faces.length : Int) = 2) : PlaneMap n where
  graph := S.toFinGraph
  faces := faces
  numEdges := numEdges
  faces_len_ge3 := fun f hf =>
    (S.toFinGraph.isSimpleCycle_of_bool f (List.all_eq_true.mp hfaces f hf)).1
  faces_nodup := fun f hf =>
    (S.toFinGraph.isSimpleCycle_of_bool f (List.all_eq_true.mp hfaces f hf)).2.1
  faces_walk := fun f hf =>
    (S.toFinGraph.isSimpleCycle_of_bool f (List.all_eq_true.mp hfaces f hf)).2.2
  handshaking_verts := by rw [S.toFinGraph_handshaking, h3n]
  handshaking_faces := hsumF
  euler_formula := heuler

/-! ## 2. Fast Short-Cycle Exclusion Checkers on Cubic Graphs (`C_3`, `C_4`, `C_5`, `C_8`) -/

def noC3Bool {n : Nat} (S : CubicSpec n) : Bool :=
  allFin n fun v0 =>
    (S.nbrList v0).all fun v1 =>
      (S.nbrList v1).all fun v2 =>
        v2 == v0 || !(S.adjBool v2 v0)

theorem no_C3_of_bool {n : Nat} (S : CubicSpec n) (h : S.noC3Bool = true) :
    ¬ S.toFinGraph.HasSimpleCycleOfLen 3 := by
  rintro ⟨cyc, ⟨_, hnd, hadj⟩, hlen⟩
  match cyc, hlen, hnd, hadj with
  | [v0, v1, v2], _, hnd, hadj =>
    have h01 : S.toFinGraph.adj v0 v1 = true := hadj 0 (by simp)
    have h12 : S.toFinGraph.adj v1 v2 = true := hadj 1 (by simp)
    have h20 : S.adjBool v2 v0 = true := by simpa using hadj 2 (by simp)
    have hv1 : v1 ∈ S.nbrList v0 := (S.mem_nbrList_iff v0 v1).mpr h01
    have hv2 : v2 ∈ S.nbrList v1 := (S.mem_nbrList_iff v1 v2).mpr h12
    have hchk := List.all_eq_true.mp (List.all_eq_true.mp (allFin_eq_true h v0) v1 hv1) v2 hv2
    have hne : v2 ≠ v0 := by
      rcases List.nodup_cons.mp hnd with ⟨h0n, _⟩
      intro heq; subst heq; exact h0n (by simp)
    rw [beq_false_of_ne hne, h20] at hchk
    cases hchk

def noC4Bool {n : Nat} (S : CubicSpec n) : Bool :=
  allFin n fun v0 =>
    (S.nbrList v0).all fun v1 =>
      (S.nbrList v1).all fun v2 =>
        v2 == v0 ||
        (S.nbrList v2).all fun v3 =>
          v3 == v0 || v3 == v1 || !(S.adjBool v3 v0)

theorem no_C4_of_bool {n : Nat} (S : CubicSpec n) (h : S.noC4Bool = true) :
    ¬ S.toFinGraph.HasSimpleCycleOfLen 4 := by
  rintro ⟨cyc, ⟨_, hnd, hadj⟩, hlen⟩
  match cyc, hlen, hnd, hadj with
  | [v0, v1, v2, v3], _, hnd, hadj =>
    have h01 : S.toFinGraph.adj v0 v1 = true := hadj 0 (by simp)
    have h12 : S.toFinGraph.adj v1 v2 = true := hadj 1 (by simp)
    have h23 : S.toFinGraph.adj v2 v3 = true := hadj 2 (by simp)
    have h30 : S.adjBool v3 v0 = true := by simpa using hadj 3 (by simp)
    have hv1 : v1 ∈ S.nbrList v0 := (S.mem_nbrList_iff v0 v1).mpr h01
    have hv2 : v2 ∈ S.nbrList v1 := (S.mem_nbrList_iff v1 v2).mpr h12
    have hv3 : v3 ∈ S.nbrList v2 := (S.mem_nbrList_iff v2 v3).mpr h23
    have hchk2 := List.all_eq_true.mp (List.all_eq_true.mp (allFin_eq_true h v0) v1 hv1) v2 hv2
    rcases List.nodup_cons.mp hnd with ⟨h0n, hnd1⟩
    rcases List.nodup_cons.mp hnd1 with ⟨h1n, _⟩
    have h20 : v2 ≠ v0 := fun heq => h0n (by rw [← heq]; simp)
    have h30ne : v3 ≠ v0 := fun heq => h0n (by rw [← heq]; simp)
    have h31ne : v3 ≠ v1 := fun heq => h1n (by rw [← heq]; simp)
    rw [beq_false_of_ne h20, Bool.false_or] at hchk2
    have hchk3 := List.all_eq_true.mp hchk2 v3 hv3
    rw [beq_false_of_ne h30ne, beq_false_of_ne h31ne, h30] at hchk3
    cases hchk3

/-- Weighted 5-cycle lower bound checker on a cubic graph. -/
def c5MinWeightBool {n : Nat} (S : CubicSpec n) (w : Fin n → Fin n → Fin n → Nat) (bound : Nat) : Bool :=
  allFin n fun v0 =>
    (S.nbrList v0).all fun v1 =>
      (S.nbrList v1).all fun v2 =>
        v2 == v0 ||
        (S.nbrList v2).all fun v3 =>
          v3 == v0 || v3 == v1 ||
          (S.nbrList v3).all fun v4 =>
            v4 == v0 || v4 == v1 || v4 == v2 || !(S.adjBool v4 v0) ||
            (bound ≤ w v4 v0 v1 + w v0 v1 v2 + w v1 v2 v3 + w v2 v3 v4 + w v3 v4 v0)

theorem c5_min_weight_of_bool {n : Nat} (S : CubicSpec n) (w : Fin n → Fin n → Fin n → Nat)
    (bound : Nat) (h : S.c5MinWeightBool w bound = true)
    (v0 v1 v2 v3 v4 : Fin n) (hcyc : S.toFinGraph.IsSimpleCycle [v0, v1, v2, v3, v4]) :
    bound ≤ w v4 v0 v1 + w v0 v1 v2 + w v1 v2 v3 + w v2 v3 v4 + w v3 v4 v0 := by
  rcases hcyc with ⟨_, hnd, hadj⟩
  have h01 : S.toFinGraph.adj v0 v1 = true := hadj 0 (by simp)
  have h12 : S.toFinGraph.adj v1 v2 = true := hadj 1 (by simp)
  have h23 : S.toFinGraph.adj v2 v3 = true := hadj 2 (by simp)
  have h34 : S.toFinGraph.adj v3 v4 = true := hadj 3 (by simp)
  have h40 : S.adjBool v4 v0 = true := by simpa using hadj 4 (by simp)
  have hv1 : v1 ∈ S.nbrList v0 := (S.mem_nbrList_iff v0 v1).mpr h01
  have hv2 : v2 ∈ S.nbrList v1 := (S.mem_nbrList_iff v1 v2).mpr h12
  have hv3 : v3 ∈ S.nbrList v2 := (S.mem_nbrList_iff v2 v3).mpr h23
  have hv4 : v4 ∈ S.nbrList v3 := (S.mem_nbrList_iff v3 v4).mpr h34
  rcases List.nodup_cons.mp hnd with ⟨h0n, hnd1⟩
  rcases List.nodup_cons.mp hnd1 with ⟨h1n, hnd2⟩
  rcases List.nodup_cons.mp hnd2 with ⟨h2n, _⟩
  have h20 : v2 ≠ v0 := fun heq => h0n (by rw [← heq]; simp)
  have h30 : v3 ≠ v0 := fun heq => h0n (by rw [← heq]; simp)
  have h31 : v3 ≠ v1 := fun heq => h1n (by rw [← heq]; simp)
  have h40ne : v4 ≠ v0 := fun heq => h0n (by rw [← heq]; simp)
  have h41 : v4 ≠ v1 := fun heq => h1n (by rw [← heq]; simp)
  have h42 : v4 ≠ v2 := fun heq => h2n (by rw [← heq]; simp)
  have c2 := List.all_eq_true.mp (List.all_eq_true.mp (allFin_eq_true h v0) v1 hv1) v2 hv2
  rw [beq_false_of_ne h20, Bool.false_or] at c2
  have c3 := List.all_eq_true.mp c2 v3 hv3
  rw [beq_false_of_ne h30, beq_false_of_ne h31, Bool.false_or, Bool.false_or] at c3
  have c4 := List.all_eq_true.mp c3 v4 hv4
  rw [beq_false_of_ne h40ne, beq_false_of_ne h41, beq_false_of_ne h42, h40] at c4
  simp only [Bool.false_or, Bool.not_true, decide_eq_true_eq] at c4
  exact c4

/-- All simple 4-paths starting at `u` in a cubic graph (at most 24 entries). -/
def paths4From {n : Nat} (S : CubicSpec n) (u : Fin n) : List (Fin n × Fin n × Fin n × Fin n) :=
  (S.nbrList u).flatMap fun a =>
    ((S.nbrList a).filter (· != u)).flatMap fun b =>
      ((S.nbrList b).filter (fun c => c != u && c != a)).flatMap fun c =>
        ((S.nbrList c).filter (fun w => w != u && w != a && w != b)).map fun w =>
          (a, b, c, w)

theorem mem_paths4From {n : Nat} (S : CubicSpec n) {u a b c w : Fin n}
    (h1 : S.toFinGraph.adj u a = true) (h2 : S.toFinGraph.adj a b = true)
    (h3 : S.toFinGraph.adj b c = true) (h4 : S.toFinGraph.adj c w = true)
    (hbu : b ≠ u) (hcu : c ≠ u) (hca : c ≠ a) (hwu : w ≠ u) (hwa : w ≠ a) (hwb : w ≠ b) :
    (a, b, c, w) ∈ S.paths4From u := by
  unfold paths4From
  rw [List.mem_flatMap]
  refine ⟨a, (S.mem_nbrList_iff u a).mpr h1, ?_⟩
  rw [List.mem_flatMap]
  refine ⟨b, List.mem_filter.mpr ⟨(S.mem_nbrList_iff a b).mpr h2, bne_iff_ne.mpr hbu⟩, ?_⟩
  rw [List.mem_flatMap]
  refine ⟨c, List.mem_filter.mpr ⟨(S.mem_nbrList_iff b c).mpr h3, by simp [hcu, hca]⟩, ?_⟩
  rw [List.mem_map]
  exact ⟨w, List.mem_filter.mpr ⟨(S.mem_nbrList_iff c w).mpr h4, by simp [hwu, hwa, hwb]⟩, rfl⟩

/-- Computable check that no two internally disjoint simple 4-paths from a single vertex `u`
share an endpoint (i.e. no simple `C_8` passes through `u`). -/
def noC8At {n : Nat} (S : CubicSpec n) (u : Fin n) : Bool :=
  let ps := S.paths4From u
  ps.all fun (a1, b1, c1, w1) =>
    ps.all fun (a2, b2, c2, w2) =>
      !(a1.val < a2.val) || w1 != w2 ||
      a1 == b2 || a1 == c2 ||
      b1 == a2 || b1 == b2 || b1 == c2 ||
      c1 == a2 || c1 == b2 || c1 == c2

theorem no_C8_at_of_bool {n : Nat} (S : CubicSpec n) (v0 : Fin n) (h : S.noC8At v0 = true)
    (v1 v2 v3 v4 v5 v6 v7 : Fin n)
    (hcyc : S.toFinGraph.IsSimpleCycle [v0, v1, v2, v3, v4, v5, v6, v7]) : False := by
  rcases hcyc with ⟨_, hnd, hadj⟩
  have h01 : S.toFinGraph.adj v0 v1 = true := hadj 0 (by simp)
  have h12 : S.toFinGraph.adj v1 v2 = true := hadj 1 (by simp)
  have h23 : S.toFinGraph.adj v2 v3 = true := hadj 2 (by simp)
  have h34 : S.toFinGraph.adj v3 v4 = true := hadj 3 (by simp)
  have h45 : S.toFinGraph.adj v4 v5 = true := hadj 4 (by simp)
  have h56 : S.toFinGraph.adj v5 v6 = true := hadj 5 (by simp)
  have h67 : S.toFinGraph.adj v6 v7 = true := hadj 6 (by simp)
  have h70 : S.toFinGraph.adj v7 v0 = true := by simpa using hadj 7 (by simp)
  have h07 : S.toFinGraph.adj v0 v7 = true := by rw [S.toFinGraph.symm]; exact h70
  have h76 : S.toFinGraph.adj v7 v6 = true := by rw [S.toFinGraph.symm]; exact h67
  have h65 : S.toFinGraph.adj v6 v5 = true := by rw [S.toFinGraph.symm]; exact h56
  have h54 : S.toFinGraph.adj v5 v4 = true := by rw [S.toFinGraph.symm]; exact h45
  rcases List.nodup_cons.mp hnd with ⟨h0n, hnd1⟩
  rcases List.nodup_cons.mp hnd1 with ⟨h1n, hnd2⟩
  rcases List.nodup_cons.mp hnd2 with ⟨h2n, hnd3⟩
  rcases List.nodup_cons.mp hnd3 with ⟨h3n, hnd4⟩
  rcases List.nodup_cons.mp hnd4 with ⟨h4n, hnd5⟩
  rcases List.nodup_cons.mp hnd5 with ⟨h5n, hnd6⟩
  rcases List.nodup_cons.mp hnd6 with ⟨_, _⟩
  have hp1 : (v1, v2, v3, v4) ∈ S.paths4From v0 :=
    S.mem_paths4From h01 h12 h23 h34
      (fun e => h0n (by rw [← e]; simp))
      (fun e => h0n (by rw [← e]; simp))
      (fun e => h1n (by rw [← e]; simp))
      (fun e => h0n (by rw [← e]; simp))
      (fun e => h1n (by rw [← e]; simp))
      (fun e => h2n (by rw [← e]; simp))
  have hp2 : (v7, v6, v5, v4) ∈ S.paths4From v0 :=
    S.mem_paths4From h07 h76 h65 h54
      (fun e => h0n (by rw [← e]; simp))
      (fun e => h0n (by rw [← e]; simp))
      (fun e => h5n (by rw [← e]; simp))
      (fun e => h0n (by rw [← e]; simp))
      (fun e => h4n (by rw [e]; simp))
      (fun e => h4n (by rw [e]; simp))
  have hv17 : v1 ≠ v7 := fun e => h1n (by rw [e]; simp)
  have hord : v1.val < v7.val ∨ v7.val < v1.val := Nat.lt_or_gt_of_ne (fun e => hv17 (Fin.ext e))
  rcases hord with hlt | hlt
  · have hchk := List.all_eq_true.mp (List.all_eq_true.mp h _ hp1) _ hp2
    simp only [hlt, decide_true, Bool.not_true, bne_self_eq_false, Bool.false_or, Bool.or_eq_true, beq_iff_eq] at hchk
    rcases hchk with ((((((h | h) | h) | h) | h) | h) | h) | h
    · exact h1n (by rw [h]; simp)
    · exact h1n (by rw [h]; simp)
    · exact h2n (by rw [h]; simp)
    · exact h2n (by rw [h]; simp)
    · exact h2n (by rw [h]; simp)
    · exact h3n (by rw [h]; simp)
    · exact h3n (by rw [h]; simp)
    · exact h3n (by rw [h]; simp)
  · have hchk := List.all_eq_true.mp (List.all_eq_true.mp h _ hp2) _ hp1
    simp only [hlt, decide_true, Bool.not_true, bne_self_eq_false, Bool.false_or, Bool.or_eq_true, beq_iff_eq] at hchk
    rcases hchk with ((((((h | h) | h) | h) | h) | h) | h) | h
    · exact h2n (by rw [← h]; simp)
    · exact h3n (by rw [← h]; simp)
    · exact h1n (by rw [← h]; simp)
    · exact h2n (by rw [← h]; simp)
    · exact h3n (by rw [← h]; simp)
    · exact h1n (by rw [← h]; simp)
    · exact h2n (by rw [← h]; simp)
    · exact h3n (by rw [← h]; simp)

/-- Computable check that no two internally disjoint simple 4-paths from any `u` share an endpoint. -/
def noC8Bool {n : Nat} (S : CubicSpec n) : Bool :=
  allFin n (S.noC8At)

theorem no_C8_of_bool {n : Nat} (S : CubicSpec n) (h : S.noC8Bool = true) :
    ¬ S.toFinGraph.HasSimpleCycleOfLen 8 := by
  rintro ⟨cyc, hcyc, hlen⟩
  match cyc, hlen, hcyc with
  | [v0, v1, v2, v3, v4, v5, v6, v7], _, hcyc =>
    exact S.no_C8_at_of_bool v0 (allFin_eq_true h v0) v1 v2 v3 v4 v5 v6 v7 hcyc

end CubicSpec

/-! ## 3. General 3-Port Gadget-Inflation Cycle Dichotomy & 3-Connectivity -/

/-- Projection from inflated vertex `Fin (nb * s)` to base gadget `Fin nb`. -/
def gadgetOf {nb s : Nat} (_hs : s > 0) (v : Fin (nb * s)) : Fin nb :=
  ⟨v.val / s, Nat.div_lt_of_lt_mul (Nat.lt_of_lt_of_eq v.isLt (Nat.mul_comm nb s))⟩

/-- Local offset inside gadget `Fin s`. -/
def localOf {nb s : Nat} (hs : s > 0) (v : Fin (nb * s)) : Fin s :=
  ⟨v.val % s, Nat.mod_lt _ hs⟩

/-- Lift `(g, r)` back to `Fin (nb * s)`. -/
def liftVert {nb s : Nat} (g : Fin nb) (r : Fin s) : Fin (nb * s) :=
  ⟨g.val * s + r.val, by
    have hg : g.val + 1 ≤ nb := g.isLt
    have hr : r.val < s := r.isLt
    have hmul : (g.val + 1) * s ≤ nb * s := Nat.mul_le_mul_right s hg
    rw [Nat.add_mul, Nat.one_mul] at hmul
    omega⟩

theorem gadgetOf_liftVert {nb s : Nat} (hs : s > 0) (g : Fin nb) (r : Fin s) :
    gadgetOf hs (liftVert g r) = g := by
  ext
  simp only [gadgetOf, liftVert]
  rw [Nat.mul_comm g.val s, Nat.mul_add_div hs, Nat.div_eq_of_lt r.isLt]
  omega

theorem localOf_liftVert {nb s : Nat} (hs : s > 0) (g : Fin nb) (r : Fin s) :
    localOf hs (liftVert g r) = r := by
  ext
  simp only [localOf, liftVert]
  rw [Nat.mul_comm g.val s, Nat.mul_add_mod, Nat.mod_eq_of_lt r.isLt]

theorem liftVert_gadgetOf_localOf {nb s : Nat} (hs : s > 0) (v : Fin (nb * s)) :
    liftVert (gadgetOf hs v) (localOf hs v) = v := by
  ext
  simp only [liftVert, gadgetOf, localOf]
  have h := Nat.div_add_mod v.val s
  rw [Nat.mul_comm] at h
  exact h

/-- A 3-port gadget inflation of a cubic base graph `B` (`nb` vertices) by a gadget of size `s`. -/
structure Inflation3Port (nb s : Nat) (hs : s > 0) where
  base : CubicSpec nb
  infl : CubicSpec (nb * s)
  isPort : Fin s → Bool
  portExt : Fin nb → Fin s → Fin (nb * s)
  p0 : Fin s
  p1 : Fin s
  p2 : Fin s
  port_in_three : ∀ r : Fin s, isPort r = true → r = p0 ∨ r = p1 ∨ r = p2
  ext_edge_spec : ∀ x y : Fin (nb * s),
    infl.toFinGraph.adj x y = true →
    gadgetOf hs x ≠ gadgetOf hs y →
    isPort (localOf hs x) = true ∧
    y = portExt (gadgetOf hs x) (localOf hs x) ∧
    base.toFinGraph.adj (gadgetOf hs x) (gadgetOf hs y) = true
  ext_distinct_gadget : ∀ (g : Fin nb) (r1 r2 : Fin s),
    isPort r1 = true → isPort r2 = true → r1 ≠ r2 →
    gadgetOf hs (portExt g r1) ≠ gadgetOf hs (portExt g r2)

/-- Split a list into maximal contiguous runs of equal `proj` value. -/
def splitRuns {α β : Type} [BEq β] (proj : α → β) : List α → List (β × List α)
  | [] => []
  | x :: xs =>
    match splitRuns proj xs with
    | [] => [(proj x, [x])]
    | (b, blk) :: rest =>
      if proj x == b then (b, x :: blk) :: rest
      else (proj x, [x]) :: (b, blk) :: rest

theorem splitRuns_flatMap {α β : Type} [BEq β] (proj : α → β) (xs : List α) :
    (splitRuns proj xs).flatMap Prod.snd = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [splitRuns]
    cases h : splitRuns proj xs with
    | nil =>
      rw [h] at ih
      simp at ih
      subst ih; rfl
    | cons hd tl =>
      rcases hd with ⟨b, blk⟩
      rw [h] at ih
      by_cases heq : proj x == b
      · simp [heq, ← ih]
      · simp [heq, ← ih]

theorem sumNat_splitRuns_length {α β : Type} [BEq β] (proj : α → β) (xs : List α) :
    sumNat ((splitRuns proj xs).map fun r => r.2.length) = xs.length := by
  have hflat := splitRuns_flatMap proj xs
  have hlen : ∀ (rs : List (β × List α)), sumNat (rs.map fun r => r.2.length) = (rs.flatMap Prod.snd).length := by
    intro rs
    induction rs with
    | nil => rfl
    | cons r rs ih =>
      simp only [List.map_cons, sumNat, List.flatMap_cons, List.length_append, ih]
  rw [hlen, hflat]

theorem splitRuns_mem_prop {α β : Type} [BEq β] [LawfulBEq β] (proj : α → β) (xs : List α) :
    ∀ r ∈ splitRuns proj xs, r.2 ≠ [] ∧ ∀ x ∈ r.2, proj x = r.1 := by
  induction xs with
  | nil => intro r hr; cases hr
  | cons x xs ih =>
    simp only [splitRuns]
    cases h : splitRuns proj xs with
    | nil =>
      intro r hr
      simp at hr
      subst hr
      exact ⟨by simp, by intro y hy; simp at hy; subst hy; rfl⟩
    | cons hd tl =>
      rcases hd with ⟨b, blk⟩
      rw [h] at ih
      by_cases heq : proj x == b
      · simp only [heq, ↓reduceIte]
        intro r hr
        rcases List.mem_cons.mp hr with rfl | htl
        · have hhd := ih (b, blk) (List.mem_cons_self ..)
          refine ⟨by simp, ?_⟩
          intro y hy
          rcases List.mem_cons.mp hy with rfl | hyb
          · exact beq_iff_eq.mp heq
          · exact hhd.2 y hyb
        · exact ih r (List.mem_cons_of_mem _ htl)
      · simp only [heq, Bool.false_eq_true, ↓reduceIte]
        intro r hr
        rcases List.mem_cons.mp hr with rfl | hrest
        · exact ⟨by simp, by intro y hy; simp at hy; subst hy; rfl⟩
        · exact ih r hrest

theorem splitRuns_adj_diff {α β : Type} [BEq β] [LawfulBEq β] (proj : α → β) (xs : List α) :
    ∀ (i : Nat) (hi : i + 1 < (splitRuns proj xs).length),
      ((splitRuns proj xs)[i]'(Nat.lt_of_succ_lt hi)).1 ≠
      ((splitRuns proj xs)[i + 1]'hi).1 := by
  induction xs with
  | nil => intro i hi; simp [splitRuns] at hi
  | cons x xs ih =>
    have hstep : ∀ (rs : List (β × List α)),
        (∀ (i : Nat) (hi : i + 1 < rs.length), (rs[i]'(Nat.lt_of_succ_lt hi)).1 ≠ (rs[i + 1]'hi).1) →
        let out := match rs with
          | [] => [(proj x, [x])]
          | (b, blk) :: rest => if proj x == b then (b, x :: blk) :: rest else (proj x, [x]) :: (b, blk) :: rest
        ∀ (i : Nat) (hi : i + 1 < out.length), (out[i]'(Nat.lt_of_succ_lt hi)).1 ≠ (out[i + 1]'hi).1 := by
      intro rs hrs
      cases rs with
      | nil =>
        intro out i hi
        have hi' : i + 1 < ([(proj x, [x])]).length := hi
        simp at hi'
      | cons hd tl =>
        rcases hd with ⟨b, blk⟩
        by_cases heq : proj x == b
        · simp only [heq, ↓reduceIte]
          intro i hi
          cases i with
          | zero => exact hrs 0 hi
          | succ k => exact hrs (k + 1) hi
        · simp only [heq, Bool.false_eq_true, ↓reduceIte]
          intro i hi
          cases i with
          | zero =>
            intro hsame
            exact heq (beq_iff_eq.mpr hsame)
          | succ k => exact hrs k (Nat.lt_of_succ_lt_succ hi)
    simpa only [splitRuns] using hstep (splitRuns proj xs) ih

/-- Cyclic rotation of a list preserves `IsSimpleCycle` and length. -/
def rotateList {α : Type} (xs : List α) (k : Nat) : List α :=
  xs.drop k ++ xs.take k

theorem rotateList_length {α : Type} (xs : List α) (k : Nat) (hk : k ≤ xs.length) :
    (rotateList xs k).length = xs.length := by
  unfold rotateList
  rw [List.length_append, List.length_drop, List.length_take]
  omega

theorem rotateList_getElem {α : Type} (xs : List α) (k : Nat) (hk : k ≤ xs.length)
    (i : Nat) (hi : i < (rotateList xs k).length) :
    (rotateList xs k)[i]'hi =
      xs[(i + k) % xs.length]'(Nat.mod_lt _ (by rw [rotateList_length xs k hk] at hi; omega)) := by
  have hlen := rotateList_length xs k hk
  have hi' : i < xs.length := by omega
  have hi_app : i < (xs.drop k ++ xs.take k).length := hi
  by_cases hlt : i < xs.length - k
  · have hlt_drop : i < (xs.drop k).length := by rw [List.length_drop]; exact hlt
    change (xs.drop k ++ xs.take k)[i]'hi_app = _
    rw [List.getElem_append_left hlt_drop, List.getElem_drop]
    have hmod : (i + k) % xs.length = k + i := by
      rw [Nat.mod_eq_of_lt (by omega)]; omega
    congr 1; omega
  · have hge_drop : (xs.drop k).length ≤ i := by rw [List.length_drop]; omega
    change (xs.drop k ++ xs.take k)[i]'hi_app = _
    rw [List.getElem_append_right hge_drop, List.getElem_take]
    have hmod : (i + k) % xs.length = i - (xs.drop k).length := by
      rw [List.length_drop]
      have h2 : i + k = (i - (xs.length - k)) + xs.length := by omega
      rw [h2, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    congr 1; omega

theorem rotateList_nodup {α : Type} {xs : List α} (hnd : xs.Nodup) (k : Nat) :
    (rotateList xs k).Nodup := by
  unfold rotateList
  have hsplit : xs = xs.take k ++ xs.drop k := (List.take_append_drop k xs).symm
  rw [hsplit] at hnd
  rw [List.nodup_append] at hnd ⊢
  rcases hnd with ⟨ht, hd, hdisj⟩
  exact ⟨hd, ht, fun a ha b hb => Ne.symm (hdisj b hb a ha)⟩

theorem isSimpleCycle_rotate {n : Nat} {G : FinGraph n} {cyc : List (Fin n)}
    (hcyc : G.IsSimpleCycle cyc) (k : Nat) (hk : k ≤ cyc.length) :
    G.IsSimpleCycle (rotateList cyc k) := by
  rcases hcyc with ⟨hlen, hnd, hadj⟩
  have hrlen := rotateList_length cyc k hk
  refine ⟨by omega, rotateList_nodup hnd k, ?_⟩
  intro i hi
  have hi' : i < cyc.length := by omega
  have hpos : cyc.length > 0 := by omega
  rw [rotateList_getElem cyc k hk i hi]
  rw [rotateList_getElem cyc k hk ((i + 1) % (rotateList cyc k).length) (Nat.mod_lt _ (by omega))]
  have hidx : (((i + 1) % (rotateList cyc k).length + k) % cyc.length) =
              (((i + k) % cyc.length) + 1) % cyc.length := by
    rw [hrlen]
    rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
    rw [Nat.add_mod ((i + k) % cyc.length) 1, Nat.mod_mod, ← Nat.add_mod]
    congr 1; omega
  have hstep := hadj ((i + k) % cyc.length) (Nat.mod_lt _ hpos)
  simpa only [hidx] using hstep

/-- Every list of `Fin s` elements with `Nodup` has length `≤ s`. -/
theorem nodup_fin_length_le {s : Nat} (xs : List (Fin s)) (hnd : xs.Nodup) : xs.length ≤ s := by
  have hperm : ∀ (l : List (Fin s)), l.Nodup → ∀ (u : List (Fin s)), (∀ x ∈ l, x ∈ u) → l.length ≤ u.length := by
    intro l
    induction l with
    | nil => intro _ _ _; exact Nat.zero_le _
    | cons a as ih =>
      intro hnda u hmem
      rcases List.nodup_cons.mp hnda with ⟨hanot, hndas⟩
      have hau : a ∈ u := hmem a (List.mem_cons_self ..)
      have hlen_er : (u.erase a).length + 1 = u.length := by
        rw [List.length_erase_of_mem hau]
        have hpos : 0 < u.length := List.length_pos_of_mem hau
        omega
      have hsub_er : ∀ x ∈ as, x ∈ u.erase a := by
        intro x hx
        have hxa : x ≠ a := fun e => hanot (e ▸ hx)
        exact (List.mem_erase_of_ne hxa).mpr (hmem x (List.mem_cons_of_mem a hx))
      have ihle := ih hndas (u.erase a) hsub_er
      simp only [List.length_cons]
      omega
  have h := hperm xs hnd (List.finRange s) (fun x _ => List.mem_finRange x)
  rwa [List.length_finRange] at h

private theorem length_pos_of_ne_nil' {α : Type} {l : List α} (h : l ≠ []) : 0 < l.length := by
  cases l with
  | nil => exact absurd rfl h
  | cons _ _ => exact Nat.zero_lt_succ _

private theorem head_eq_zero {α : Type} {l : List α} (h : l ≠ []) :
    l.head h = l[0]'(length_pos_of_ne_nil' h) := by
  cases l with
  | nil => exact absurd rfl h
  | cons _ _ => rfl

private theorem nodup_getElem_inj {α : Type} {l : List α} (hnd : l.Nodup)
    {i j : Nat} (hi : i < l.length) (hj : j < l.length) (heq : l[i]'hi = l[j]'hj) : i = j := by
  induction l generalizing i j with
  | nil => exact absurd hi (Nat.not_lt_zero _)
  | cons x xs ih =>
    rcases List.nodup_cons.mp hnd with ⟨hxnot, hndxs⟩
    match i, j, hi, hj, heq with
    | 0, 0, _, _, _ => rfl
    | 0, j' + 1, _, hj, heq =>
      simp only [List.getElem_cons_zero, List.getElem_cons_succ] at heq
      exact absurd (heq ▸ List.getElem_mem (Nat.lt_of_succ_lt_succ hj)) hxnot
    | i' + 1, 0, hi, _, heq =>
      simp only [List.getElem_cons_zero, List.getElem_cons_succ] at heq
      exact absurd (heq.symm ▸ List.getElem_mem (Nat.lt_of_succ_lt_succ hi)) hxnot
    | i' + 1, j' + 1, hi, hj, heq =>
      simp only [List.getElem_cons_succ] at heq
      exact congrArg Nat.succ (ih hndxs (Nat.lt_of_succ_lt_succ hi) (Nat.lt_of_succ_lt_succ hj) heq)

private theorem nodup_of_getElem_inj {α : Type} {l : List α}
    (hinj : ∀ (i j : Nat) (hi : i < l.length) (hj : j < l.length), l[i]'hi = l[j]'hj → i = j) :
    l.Nodup := by
  induction l with
  | nil => exact List.nodup_nil
  | cons x xs ih =>
    rw [List.nodup_cons]
    refine ⟨?_, ih (fun i j hi hj heq => ?_)⟩
    · intro hmem
      rcases List.getElem_of_mem hmem with ⟨k, hk, hxk⟩
      have h0 : 0 = k + 1 := hinj 0 (k + 1) (Nat.zero_lt_succ _) (Nat.succ_lt_succ hk) hxk.symm
      omega
    · have h1 := hinj (i + 1) (j + 1) (Nat.succ_lt_succ hi) (Nat.succ_lt_succ hj) heq
      omega

/-- Helper: extracting consecutive adjacencies inside `xs` when `xs = rs.flatMap Prod.snd`. -/
private theorem flatMap_adj_at {n nb : Nat} {G : FinGraph n} {xs : List (Fin n)}
    (hadj : ∀ (i : Nat) (hi : i < xs.length),
      G.adj (xs[i]'hi) (xs[(i + 1) % xs.length]'(Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le i) hi))) = true)
    (rs : List (Fin nb × List (Fin n))) (hflat : rs.flatMap Prod.snd = xs)
    (hne : ∀ r ∈ rs, r.2 ≠ []) :
    (∀ (k : Nat) (hk : k < rs.length),
      let blk := (rs[k]'hk).2
      ∀ (j : Nat) (hj : j + 1 < blk.length),
        G.adj (blk[j]'(Nat.lt_of_succ_lt hj)) (blk[j + 1]'hj) = true) ∧
    (∀ (k : Nat) (hk : k < rs.length),
      let b1 := (rs[k]'hk).2
      let b2 := (rs[(k + 1) % rs.length]'(Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le k) hk))).2
      G.adj (b1.getLast (hne _ (List.getElem_mem hk)))
            (b2.head (hne _ (List.getElem_mem _))) = true) := by
  let pref (k : Nat) : Nat := ((rs.take k).flatMap Prod.snd).length
  have hxs_split : ∀ (k : Nat) (hk : k < rs.length),
      xs = (rs.take k).flatMap Prod.snd ++ (rs[k]'hk).2 ++ (rs.drop (k + 1)).flatMap Prod.snd := by
    intro k hk
    have hsplit : rs = rs.take k ++ [rs[k]'hk] ++ rs.drop (k + 1) := by
      simp [List.take_append_getElem, List.take_append_drop]
    have hfm : rs.flatMap Prod.snd = (rs.take k ++ [rs[k]'hk] ++ rs.drop (k + 1)).flatMap Prod.snd :=
      congrArg (List.flatMap Prod.snd) hsplit
    rw [hflat, List.flatMap_append, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil] at hfm
    exact hfm
  have hget_in : ∀ (k : Nat) (hk : k < rs.length) (j : Nat) (hj : j < (rs[k]'hk).2.length),
      ∃ hpos : pref k + j < xs.length, xs[pref k + j]'hpos = (rs[k]'hk).2[j]'hj := by
    intro k hk j hj
    have hsp := hxs_split k hk
    have hlen : pref k + j < xs.length := by
      rw [hsp]; simp only [List.length_append, pref]; omega
    refine ⟨hlen, ?_⟩
    have heq : xs[pref k + j]'hlen =
        (((rs.take k).flatMap Prod.snd ++ (rs[k]'hk).2) ++ (rs.drop (k + 1)).flatMap Prod.snd)[pref k + j]'(by rw [← hsp]; exact hlen) := by
      congr 1
    rw [heq, List.getElem_append_left (by simp only [List.length_append, pref]; omega)]
    rw [List.getElem_append_right (Nat.le_add_right _ _)]
    simp only [Nat.add_sub_cancel_left]
  constructor
  · intro k hk
    dsimp only
    intro j hj
    rcases hget_in k hk j (Nat.lt_of_succ_lt hj) with ⟨hp1, he1⟩
    rcases hget_in k hk (j + 1) hj with ⟨hp2, he2⟩
    have hstep := hadj (pref k + j) hp1
    have hmod : (pref k + j + 1) % xs.length = pref k + (j + 1) := by
      rw [Nat.mod_eq_of_lt (by omega)]; omega
    rw [← he1, ← he2]
    simpa only [hmod] using hstep
  · intro k hk
    dsimp only
    have hb1_ne := hne (rs[k]'hk) (List.getElem_mem hk)
    have hb1_pos : 0 < (rs[k]'hk).2.length := length_pos_of_ne_nil' hb1_ne
    let jlast := (rs[k]'hk).2.length - 1
    have hjlast : jlast < (rs[k]'hk).2.length := by omega
    rcases hget_in k hk jlast hjlast with ⟨hplast, helast⟩
    have hgl : (rs[k]'hk).2.getLast hb1_ne = (rs[k]'hk).2[jlast]'hjlast := List.getLast_eq_getElem hb1_ne
    rw [hgl, ← helast]
    by_cases hklast : k + 1 < rs.length
    · have hb2_ne := hne (rs[k + 1]'hklast) (List.getElem_mem hklast)
      have hb2_pos : 0 < (rs[k + 1]'hklast).2.length := length_pos_of_ne_nil' hb2_ne
      rcases hget_in (k + 1) hklast 0 hb2_pos with ⟨hpnext, henext⟩
      have hmodk : (k + 1) % rs.length = k + 1 := Nat.mod_eq_of_lt hklast
      have hpref : pref (k + 1) = pref k + (rs[k]'hk).2.length := by
        simp only [pref]
        have htk : rs.take (k + 1) = rs.take k ++ [rs[k]'hk] := List.take_succ_eq_append_getElem hk
        rw [htk, List.flatMap_append]; simp
      have hmodx : (pref k + jlast + 1) % xs.length = pref (k + 1) + 0 := by
        have h1 : pref k + jlast + 1 = pref (k + 1) + 0 := by omega
        rw [h1, Nat.mod_eq_of_lt hpnext]
      have hstep := hadj (pref k + jlast) hplast
      have hhd : (rs[(k + 1) % rs.length]'(Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le k) hk))).2.head
                   (hne _ (List.getElem_mem (Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le k) hk)))) =
                 (rs[k + 1]'hklast).2[0]'hb2_pos := by
        simp only [hmodk, head_eq_zero]
      rw [hhd, ← henext]
      simpa only [hmodx] using hstep
    · have hkeq : k + 1 = rs.length := by omega
      have hmodk : (k + 1) % rs.length = 0 := by rw [hkeq, Nat.mod_self]
      have hpos_rs : 0 < rs.length := by omega
      have hb0_ne := hne (rs[0]'hpos_rs) (List.getElem_mem hpos_rs)
      have hb0_pos : 0 < (rs[0]'hpos_rs).2.length := length_pos_of_ne_nil' hb0_ne
      rcases hget_in 0 hpos_rs 0 hb0_pos with ⟨hp0, he0⟩
      have hpref0 : pref 0 = 0 := by simp [pref]
      have hlast_idx : pref k + jlast + 1 = xs.length := by
        have hsp := hxs_split k hk
        have hdrop : rs.drop (k + 1) = [] := List.drop_eq_nil_of_le (by omega)
        rw [hsp, hdrop]; simp only [List.flatMap_nil, List.append_nil, List.length_append, pref]; omega
      have hmodx : (pref k + jlast + 1) % xs.length = pref 0 + 0 := by
        rw [hlast_idx, Nat.mod_self, hpref0]
      have hstep := hadj (pref k + jlast) hplast
      have hhd : (rs[(k + 1) % rs.length]'(Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le k) hk))).2.head
                   (hne _ (List.getElem_mem (Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le k) hk)))) =
                 (rs[0]'hpos_rs).2[0]'hb0_pos := by
        simp only [hmodk, head_eq_zero]
      rw [hhd, ← he0]
      simpa only [hmodx] using hstep

/-- **General 3-Port Gadget-Inflation Cycle Dichotomy Theorem.** -/
theorem inflation_cycle_dichotomy {nb s : Nat} {hs : s > 0} (I : Inflation3Port nb s hs)
    (cyc : List (Fin (nb * s))) (hcyc : I.infl.toFinGraph.IsSimpleCycle cyc) :
    (∃ g0 : Fin nb, ∀ v ∈ cyc, gadgetOf hs v = g0) ∨
    (∃ runs : List (Fin nb × List (Fin (nb * s))),
      I.base.toFinGraph.IsSimpleCycle (runs.map Prod.fst) ∧
      sumNat (runs.map fun r => r.2.length) = cyc.length ∧
      ∀ (k : Nat) (hk : k < runs.length),
        let g := (runs[k]'hk).1
        let blk := (runs[k]'hk).2
        let gPrev := (runs[(k + runs.length - 1) % runs.length]'(Nat.mod_lt _ (by omega))).1
        let gNext := (runs[(k + 1) % runs.length]'(Nat.mod_lt _ (by omega))).1
        blk.length ≥ 2 ∧
        (∀ v ∈ blk, gadgetOf hs v = g) ∧
        (∀ (j : Nat) (hj : j + 1 < blk.length),
          I.infl.toFinGraph.adj (blk[j]'(Nat.lt_of_succ_lt hj)) (blk[j + 1]'hj) = true) ∧
        (∃ (h0 : 0 < blk.length) (hl : blk.length - 1 < blk.length),
          I.isPort (localOf hs (blk[0]'h0)) = true ∧
          I.isPort (localOf hs (blk[blk.length - 1]'hl)) = true ∧
          gadgetOf hs (I.portExt g (localOf hs (blk[0]'h0))) = gPrev ∧
          gadgetOf hs (I.portExt g (localOf hs (blk[blk.length - 1]'hl))) = gNext)) := by
  by_cases hsingle : ∃ g0 : Fin nb, ∀ v ∈ cyc, gadgetOf hs v = g0
  · exact Or.inl hsingle
  · right
    have hlen_ge3 : cyc.length ≥ 3 := hcyc.1
    have hpos : cyc.length > 0 := by omega
    have hbdry : ∃ k : Nat, ∃ hk : k < cyc.length,
        gadgetOf hs (cyc[k]'hk) ≠
        gadgetOf hs (cyc[(k + cyc.length - 1) % cyc.length]'(Nat.mod_lt _ hpos)) := by
      apply Classical.byContradiction
      intro hnone
      have hall : ∀ (i : Nat) (hi : i < cyc.length),
          gadgetOf hs (cyc[i]'hi) = gadgetOf hs (cyc[0]'hpos) := by
        intro i
        induction i with
        | zero => intro _; rfl
        | succ m ih =>
          intro hm
          have hstep : gadgetOf hs (cyc[m + 1]'hm) =
              gadgetOf hs (cyc[(m + 1 + cyc.length - 1) % cyc.length]'(Nat.mod_lt _ hpos)) :=
            Classical.byContradiction fun hne => hnone ⟨m + 1, hm, hne⟩
          have hprev : (m + 1 + cyc.length - 1) % cyc.length = m := by
            have h1 : m + 1 + cyc.length - 1 = m + cyc.length := by omega
            rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
          simp only [hprev] at hstep
          rw [hstep, ih (by omega)]
      apply hsingle
      refine ⟨gadgetOf hs (cyc[0]'hpos), ?_⟩
      intro v hv
      rcases List.getElem_of_mem hv with ⟨i, hi, rfl⟩
      exact hall i hi
    rcases hbdry with ⟨k0, hk0, hdiff0⟩
    let rcyc := rotateList cyc k0
    have hrcyc : I.infl.toFinGraph.IsSimpleCycle rcyc := isSimpleCycle_rotate hcyc k0 (by omega)
    have hrlen : rcyc.length = cyc.length := rotateList_length cyc k0 (by omega)
    have hr0_ne_last : gadgetOf hs (rcyc[0]'(by omega)) ≠ gadgetOf hs (rcyc[rcyc.length - 1]'(by omega)) := by
      have hk0_le : k0 ≤ cyc.length := by omega
      have h0_lt : 0 < (rotateList cyc k0).length := by rw [hrlen]; omega
      have hl_lt : rcyc.length - 1 < (rotateList cyc k0).length := by rw [hrlen]; omega
      change gadgetOf hs ((rotateList cyc k0)[0]'h0_lt) ≠ gadgetOf hs ((rotateList cyc k0)[rcyc.length - 1]'hl_lt)
      rw [rotateList_getElem cyc k0 hk0_le 0 h0_lt,
          rotateList_getElem cyc k0 hk0_le (rcyc.length - 1) hl_lt]
      have h1 : (0 + k0) % cyc.length = k0 := by rw [Nat.zero_add, Nat.mod_eq_of_lt hk0]
      have h2 : (rcyc.length - 1 + k0) % cyc.length = (k0 + cyc.length - 1) % cyc.length := by
        congr 1; omega
      simpa only [h1, h2] using hdiff0
    let runs := splitRuns (gadgetOf hs) rcyc
    have hflat : runs.flatMap Prod.snd = rcyc := splitRuns_flatMap (gadgetOf hs) rcyc
    have hsum : sumNat (runs.map fun r => r.2.length) = cyc.length := by
      rw [sumNat_splitRuns_length, hrlen]
    have hmem_prop := splitRuns_mem_prop (gadgetOf hs) rcyc
    have hne : ∀ r ∈ runs, r.2 ≠ [] := fun r hr => (hmem_prop r hr).1
    have hruns_ge2 : runs.length ≥ 2 := by
      apply Classical.byContradiction
      intro hlt
      match hrm : runs with
      | [] =>
        rw [hrm] at hflat; simp at hflat
        rw [hflat] at hrlen; simp at hrlen; omega
      | [(g, blk)] =>
        rw [hrm] at hflat; simp at hflat
        have hg0 := (hmem_prop (g, blk) (by change (g, blk) ∈ runs; rw [hrm]; simp)).2
        have h0 : gadgetOf hs (rcyc[0]'(by omega)) = g := hg0 _ (by rw [hflat]; exact List.getElem_mem _)
        have hl : gadgetOf hs (rcyc[rcyc.length - 1]'(by omega)) = g := hg0 _ (by rw [hflat]; exact List.getElem_mem _)
        exact hr0_ne_last (h0.trans hl.symm)
      | _ :: _ :: _ =>
        rw [hrm] at hlt; simp at hlt
    have hcyc_diff : ∀ (k : Nat) (hk : k < runs.length),
        (runs[k]'hk).1 ≠ (runs[(k + 1) % runs.length]'(Nat.mod_lt _ (by omega))).1 := by
      intro k hk
      by_cases hlt : k + 1 < runs.length
      · have hmod : (k + 1) % runs.length = k + 1 := Nat.mod_eq_of_lt hlt
        simpa only [hmod] using splitRuns_adj_diff (gadgetOf hs) rcyc k hlt
      · have hkeq : k + 1 = runs.length := by omega
        have hmod : (k + 1) % runs.length = 0 := by rw [hkeq, Nat.mod_self]
        have hpos_r : 0 < runs.length := by omega
        have hlast_mem : rcyc[rcyc.length - 1]'(by omega) ∈ (runs[k]'hk).2 := by
          have hgl : rcyc.getLast (by intro h; rw [h] at hrlen; simp at hrlen; omega) = rcyc[rcyc.length - 1]'(by omega) :=
            List.getLast_eq_getElem _
          rw [← hgl]
          have hsplit : runs = runs.take k ++ [runs[k]'hk] := by
            have h1 := List.take_append_drop k runs
            have hdrop : runs.drop k = [runs[k]'hk] := by
              rw [List.drop_eq_getElem_cons hk]
              have hnil : runs.drop (k + 1) = [] := List.drop_eq_nil_of_le (by omega)
              rw [hnil]
            rw [hdrop] at h1; exact h1.symm
          have hfl : rcyc = (runs.take k).flatMap Prod.snd ++ (runs[k]'hk).2 := by
            have hfm := congrArg (List.flatMap Prod.snd) hsplit
            rw [hflat, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil] at hfm
            exact hfm
          have hne_k := hne (runs[k]'hk) (List.getElem_mem hk)
          have hgl2 : ((runs.take k).flatMap Prod.snd ++ (runs[k]'hk).2).getLast (by simp [hne_k]) =
                      (runs[k]'hk).2.getLast hne_k := List.getLast_append_of_ne_nil _ hne_k
          have hgl3 : rcyc.getLast (by intro h; rw [h] at hrlen; simp at hrlen; omega) = (runs[k]'hk).2.getLast hne_k := by
            simpa only [hfl] using hgl2
          rw [hgl3]
          exact List.getLast_mem hne_k
        have hfirst_mem : rcyc[0]'(by omega) ∈ (runs[0]'hpos_r).2 := by
          have hsplit : runs = (runs[0]'hpos_r) :: runs.drop 1 := by
            have := List.drop_eq_getElem_cons hpos_r; simpa using this
          have hfl : rcyc = (runs[0]'hpos_r).2 ++ (runs.drop 1).flatMap Prod.snd := by
            have hfm := congrArg (List.flatMap Prod.snd) hsplit
            rw [hflat, List.flatMap_cons] at hfm; exact hfm
          have hne0 := hne (runs[0]'hpos_r) (List.getElem_mem hpos_r)
          have hhd : rcyc[0]'(by omega) = (runs[0]'hpos_r).2[0]'(length_pos_of_ne_nil' hne0) := by
            have h1 : ((runs[0]'hpos_r).2 ++ (runs.drop 1).flatMap Prod.snd)[0]'(by rw [← hfl]; omega) =
                      (runs[0]'hpos_r).2[0]'(length_pos_of_ne_nil' hne0) :=
              List.getElem_append_left (length_pos_of_ne_nil' hne0)
            simpa only [hfl] using h1
          rw [hhd]
          exact List.getElem_mem _
        have hg_k := (hmem_prop (runs[k]'hk) (List.getElem_mem hk)).2 _ hlast_mem
        have hg_0 := (hmem_prop (runs[0]'hpos_r) (List.getElem_mem hpos_r)).2 _ hfirst_mem
        simp only [hmod]
        intro hsame
        exact hr0_ne_last (hg_0.trans (hsame.symm.trans hg_k.symm))
    rcases flatMap_adj_at hrcyc.2.2 runs hflat hne with ⟨hblk_adj, hbdry_adj⟩
    have hbdry_spec : ∀ (k : Nat) (hk : k < runs.length),
        let g := (runs[k]'hk).1
        let blk := (runs[k]'hk).2
        let kPrev := (k + runs.length - 1) % runs.length
        let kNext := (k + 1) % runs.length
        have hkP : kPrev < runs.length := Nat.mod_lt _ (by omega)
        have hkN : kNext < runs.length := Nat.mod_lt _ (by omega)
        have hne_k := hne (runs[k]'hk) (List.getElem_mem hk)
        I.isPort (localOf hs (blk.head hne_k)) = true ∧
        I.portExt g (localOf hs (blk.head hne_k)) = (runs[kPrev]'hkP).2.getLast (hne _ (List.getElem_mem hkP)) ∧
        I.isPort (localOf hs (blk.getLast hne_k)) = true ∧
        I.portExt g (localOf hs (blk.getLast hne_k)) = (runs[kNext]'hkN).2.head (hne _ (List.getElem_mem hkN)) ∧
        I.base.toFinGraph.adj g (runs[kNext]'hkN).1 = true := by
      intro k hk
      dsimp only
      let kPrev := (k + runs.length - 1) % runs.length
      let kNext := (k + 1) % runs.length
      have hkP : kPrev < runs.length := Nat.mod_lt _ (by omega)
      have hkN : kNext < runs.length := Nat.mod_lt _ (by omega)
      have hne_k := hne (runs[k]'hk) (List.getElem_mem hk)
      have hne_P := hne (runs[kPrev]'hkP) (List.getElem_mem hkP)
      have hne_N := hne (runs[kNext]'hkN) (List.getElem_mem hkN)
      have hadjN := hbdry_adj k hk
      have hg_last : gadgetOf hs ((runs[k]'hk).2.getLast hne_k) = (runs[k]'hk).1 :=
        (hmem_prop _ (List.getElem_mem hk)).2 _ (List.getLast_mem hne_k)
      have hg_headN : gadgetOf hs ((runs[kNext]'hkN).2.head hne_N) = (runs[kNext]'hkN).1 :=
        (hmem_prop _ (List.getElem_mem hkN)).2 _ (List.head_mem hne_N)
      have hdiffN : gadgetOf hs ((runs[k]'hk).2.getLast hne_k) ≠ gadgetOf hs ((runs[kNext]'hkN).2.head hne_N) := by
        rw [hg_last, hg_headN]; exact hcyc_diff k hk
      have hspN := I.ext_edge_spec _ _ hadjN hdiffN
      rw [hg_last, hg_headN] at hspN
      have hP_next : (kPrev + 1) % runs.length = k := by
        simp only [kPrev]
        rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
        have h1 : k + runs.length - 1 + 1 = k + runs.length := by omega
        rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt hk]
      have hadjP_raw := hbdry_adj kPrev hkP
      have hadjP : I.infl.toFinGraph.adj ((runs[k]'hk).2.head hne_k) ((runs[kPrev]'hkP).2.getLast hne_P) = true := by
        rw [I.infl.toFinGraph.symm]
        simpa only [hP_next] using hadjP_raw
      have hg_head : gadgetOf hs ((runs[k]'hk).2.head hne_k) = (runs[k]'hk).1 :=
        (hmem_prop _ (List.getElem_mem hk)).2 _ (List.head_mem hne_k)
      have hg_lastP : gadgetOf hs ((runs[kPrev]'hkP).2.getLast hne_P) = (runs[kPrev]'hkP).1 :=
        (hmem_prop _ (List.getElem_mem hkP)).2 _ (List.getLast_mem hne_P)
      have hdiffP : gadgetOf hs ((runs[k]'hk).2.head hne_k) ≠ gadgetOf hs ((runs[kPrev]'hkP).2.getLast hne_P) := by
        rw [hg_head, hg_lastP]
        have hne_pk := hcyc_diff kPrev hkP
        simp only [hP_next] at hne_pk
        exact Ne.symm hne_pk
      have hspP := I.ext_edge_spec _ _ hadjP hdiffP
      rw [hg_head] at hspP
      exact ⟨hspP.1, hspP.2.1.symm, hspN.1, hspN.2.1.symm, hspN.2.2⟩
    have hblk_ge2 : ∀ (k : Nat) (hk : k < runs.length), (runs[k]'hk).2.length ≥ 2 := by
      intro k hk
      have hne_k := hne (runs[k]'hk) (List.getElem_mem hk)
      apply Classical.byContradiction
      intro hlt
      have hlen1 : (runs[k]'hk).2.length = 1 := by
        have hpos_k := length_pos_of_ne_nil' hne_k; omega
      have hhead_eq_last : (runs[k]'hk).2.head hne_k = (runs[k]'hk).2.getLast hne_k := by
        rw [head_eq_zero, List.getLast_eq_getElem]
        congr 1; omega
      have hsp := hbdry_spec k hk
      have hprev_eq_next :
          (runs[(k + runs.length - 1) % runs.length]'(Nat.mod_lt _ (by omega))).2.getLast
            (hne _ (List.getElem_mem (Nat.mod_lt _ (by omega)))) =
          (runs[(k + 1) % runs.length]'(Nat.mod_lt _ (by omega))).2.head
            (hne _ (List.getElem_mem (Nat.mod_lt _ (by omega)))) := by
        rw [← hsp.2.1, ← hsp.2.2.2.1, hhead_eq_last]
      let pref (m : Nat) : Nat := ((runs.take m).flatMap Prod.snd).length
      have hidx_get : ∀ (m : Nat) (hm : m < runs.length) (j : Nat) (hj : j < (runs[m]'hm).2.length),
          ∃ hp : pref m + j < rcyc.length, rcyc[pref m + j]'hp = (runs[m]'hm).2[j]'hj := by
        intro m hm j hj
        have hsp_m : rcyc = (runs.take m).flatMap Prod.snd ++ (runs[m]'hm).2 ++ (runs.drop (m + 1)).flatMap Prod.snd := by
          have h1 : runs = runs.take m ++ [runs[m]'hm] ++ runs.drop (m + 1) := by
            simp [List.take_append_getElem, List.take_append_drop]
          have hfm := congrArg (List.flatMap Prod.snd) h1
          rw [hflat, List.flatMap_append, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil] at hfm
          exact hfm
        have hp : pref m + j < rcyc.length := by rw [hsp_m]; simp only [List.length_append, pref]; omega
        refine ⟨hp, ?_⟩
        have heq : rcyc[pref m + j]'hp =
            (((runs.take m).flatMap Prod.snd ++ (runs[m]'hm).2) ++ (runs.drop (m + 1)).flatMap Prod.snd)[pref m + j]'(by rw [← hsp_m]; exact hp) := by
          congr 1
        rw [heq, List.getElem_append_left (by simp only [List.length_append, pref]; omega),
            List.getElem_append_right (Nat.le_add_right _ _)]
        simp only [Nat.add_sub_cancel_left]
      have hpk_lt : pref k < rcyc.length := (hidx_get k hk 0 (by omega)).1
      have hpred_eq : rcyc[(pref k + rcyc.length - 1) % rcyc.length]'(Nat.mod_lt _ (by omega)) =
          (runs[(k + runs.length - 1) % runs.length]'(Nat.mod_lt _ (by omega))).2.getLast
            (hne _ (List.getElem_mem (Nat.mod_lt _ (by omega)))) := by
        let kP := (k + runs.length - 1) % runs.length
        have hkP : kP < runs.length := Nat.mod_lt _ (by omega)
        have hneP := hne (runs[kP]'hkP) (List.getElem_mem hkP)
        have hposP := length_pos_of_ne_nil' hneP
        rcases hidx_get kP hkP ((runs[kP]'hkP).2.length - 1) (by omega) with ⟨hpP, heP⟩
        rw [List.getLast_eq_getElem, ← heP]
        congr 1
        by_cases hk0' : k = 0
        · subst hk0'
          have hpref0 : pref 0 = 0 := by simp [pref]
          have hkP_eq : kP = runs.length - 1 := by
            simp only [kP]; rw [Nat.zero_add, Nat.mod_eq_of_lt (by omega)]
          have hsp_last : rcyc.length = pref kP + (runs[kP]'hkP).2.length := by
            have h1 : runs = runs.take kP ++ [runs[kP]'hkP] := by
              have h2 := List.take_append_drop kP runs
              have hd : runs.drop kP = [runs[kP]'hkP] := by
                rw [List.drop_eq_getElem_cons hkP, List.drop_eq_nil_of_le (by omega)]
              rw [hd] at h2; exact h2.symm
            have h2 : rcyc = (runs.take kP).flatMap Prod.snd ++ (runs[kP]'hkP).2 := by
              have hfm := congrArg (List.flatMap Prod.snd) h1
              rw [hflat, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil] at hfm
              exact hfm
            rw [h2, List.length_append]
          rw [hpref0, Nat.zero_add, Nat.mod_eq_of_lt (by omega)]; omega
        · have hkP_eq : kP = k - 1 := by
            simp only [kP]
            have h1 : k + runs.length - 1 = (k - 1) + runs.length := by omega
            rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
          have hpref_k : pref k = pref kP + (runs[kP]'hkP).2.length := by
            simp only [pref]
            have htk : runs.take k = runs.take kP ++ [runs[kP]'hkP] := by
              have hk' : k = kP + 1 := by omega
              rw [hk']
              exact List.take_succ_eq_append_getElem hkP
            rw [htk, List.flatMap_append]; simp
          have h1 : pref k + rcyc.length - 1 = (pref k - 1) + rcyc.length := by omega
          rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]; omega
      have hsucc_eq : rcyc[(pref k + 1) % rcyc.length]'(Nat.mod_lt _ (by omega)) =
          (runs[(k + 1) % runs.length]'(Nat.mod_lt _ (by omega))).2.head
            (hne _ (List.getElem_mem (Nat.mod_lt _ (by omega)))) := by
        let kN := (k + 1) % runs.length
        have hkN : kN < runs.length := Nat.mod_lt _ (by omega)
        have hneN := hne (runs[kN]'hkN) (List.getElem_mem hkN)
        have hposN := length_pos_of_ne_nil' hneN
        rcases hidx_get kN hkN 0 hposN with ⟨hpN, heN⟩
        rw [head_eq_zero, ← heN]
        congr 1
        by_cases hkl : k + 1 < runs.length
        · have hkN_eq : kN = k + 1 := Nat.mod_eq_of_lt hkl
          have hprefN : pref kN = pref k + 1 := by
            simp only [pref, hkN_eq]
            rw [List.take_succ_eq_append_getElem hk, List.flatMap_append]
            simp [hlen1]
          rw [Nat.add_zero, hprefN, Nat.mod_eq_of_lt (by omega)]
        · have hkN_eq : kN = 0 := by
            have h1 : k + 1 = runs.length := by omega
            simp only [kN, h1, Nat.mod_self]
          have hprefN : pref kN = 0 := by simp [pref, hkN_eq]
          have hsp_last : rcyc.length = pref k + 1 := by
            have h1 : runs = runs.take k ++ [runs[k]'hk] := by
              have h2 := List.take_append_drop k runs
              have hd : runs.drop k = [runs[k]'hk] := by
                rw [List.drop_eq_getElem_cons hk, List.drop_eq_nil_of_le (by omega)]
              rw [hd] at h2; exact h2.symm
            have h2 : rcyc = (runs.take k).flatMap Prod.snd ++ (runs[k]'hk).2 := by
              have hfm := congrArg (List.flatMap Prod.snd) h1
              rw [hflat, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil] at hfm
              exact hfm
            rw [h2, List.length_append, hlen1]
          rw [hprefN, Nat.add_zero, ← hsp_last, Nat.mod_self]
      rw [← hpred_eq, ← hsucc_eq] at hprev_eq_next
      have heq_idx := nodup_getElem_inj hrcyc.2.1 _ _ hprev_eq_next
      have h3 : rcyc.length ≥ 3 := by omega
      by_cases h0 : pref k = 0
      · rw [h0, Nat.zero_add, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at heq_idx; omega
      · by_cases hl : pref k + 1 = rcyc.length
        · have h1 : pref k + rcyc.length - 1 = (pref k - 1) + rcyc.length := by omega
          rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega), hl, Nat.mod_self] at heq_idx; omega
        · have h1 : pref k + rcyc.length - 1 = (pref k - 1) + rcyc.length := by omega
          rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at heq_idx; omega
    have hbase_nodup : (runs.map Prod.fst).Nodup := by
      apply nodup_of_getElem_inj
      intro i j hi hj heqg
      apply Classical.byContradiction
      intro hij
      simp only [List.length_map] at hi hj
      simp only [List.getElem_map] at heqg
      have hbi := hblk_ge2 i hi
      have hbj := hblk_ge2 j hj
      let a1 := (runs[i]'hi).2[0]'(by omega)
      let a2 := (runs[i]'hi).2[(runs[i]'hi).2.length - 1]'(by omega)
      let b1 := (runs[j]'hj).2[0]'(by omega)
      let b2 := (runs[j]'hj).2[(runs[j]'hj).2.length - 1]'(by omega)
      have h4_disj : a1 ≠ a2 ∧ a1 ≠ b1 ∧ a1 ≠ b2 ∧ a2 ≠ b1 ∧ a2 ≠ b2 ∧ b1 ≠ b2 := by
        let pref (m : Nat) : Nat := ((runs.take m).flatMap Prod.snd).length
        have hpos_get : ∀ (m : Nat) (hm : m < runs.length) (p : Nat) (hp : p < (runs[m]'hm).2.length),
            ∃ hlt : pref m + p < rcyc.length, rcyc[pref m + p]'hlt = (runs[m]'hm).2[p]'hp := by
          intro m hm p hp
          have hsp_m : rcyc = (runs.take m).flatMap Prod.snd ++ (runs[m]'hm).2 ++ (runs.drop (m + 1)).flatMap Prod.snd := by
            have h1 : runs = runs.take m ++ [runs[m]'hm] ++ runs.drop (m + 1) := by
              simp [List.take_append_getElem, List.take_append_drop]
            have hfm := congrArg (List.flatMap Prod.snd) h1
            rw [hflat, List.flatMap_append, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil] at hfm
            exact hfm
          have hlt : pref m + p < rcyc.length := by rw [hsp_m]; simp only [List.length_append, pref]; omega
          refine ⟨hlt, ?_⟩
          have heq : rcyc[pref m + p]'hlt =
              (((runs.take m).flatMap Prod.snd ++ (runs[m]'hm).2) ++ (runs.drop (m + 1)).flatMap Prod.snd)[pref m + p]'(by rw [← hsp_m]; exact hlt) := by
            congr 1
          rw [heq, List.getElem_append_left (by simp only [List.length_append, pref]; omega),
              List.getElem_append_right (Nat.le_add_right _ _)]
          simp only [Nat.add_sub_cancel_left]
        have hpref_lt : ∀ {m1 m2 : Nat} (hm1 : m1 < runs.length) (hm2 : m2 < runs.length),
            m1 < m2 → pref m1 + (runs[m1]'hm1).2.length ≤ pref m2 := by
          intro m1 m2 hm1 hm2 hlt
          have htk : runs.take m2 = runs.take m1 ++ [runs[m1]'hm1] ++ (runs.drop (m1 + 1)).take (m2 - m1 - 1) := by
            have h1 : runs.take (m1 + 1) = runs.take m1 ++ [runs[m1]'hm1] := List.take_succ_eq_append_getElem hm1
            have h2 : runs.take m2 = runs.take (m1 + 1) ++ (runs.drop (m1 + 1)).take (m2 - (m1 + 1)) := by
              have h3 := (List.take_append_drop (m1 + 1) (runs.take m2)).symm
              rw [List.take_take, Nat.min_eq_left (by omega)] at h3
              rw [List.drop_take] at h3
              exact h3
            have hsub : m2 - (m1 + 1) = m2 - m1 - 1 := by omega
            rw [h2, h1, hsub]
          simp only [pref]; rw [htk]; simp only [List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.length_append]; omega
        rcases hpos_get i hi 0 (by omega) with ⟨hpa1, hea1⟩
        rcases hpos_get i hi ((runs[i]'hi).2.length - 1) (by omega) with ⟨hpa2, hea2⟩
        rcases hpos_get j hj 0 (by omega) with ⟨hpb1, heb1⟩
        rcases hpos_get j hj ((runs[j]'hj).2.length - 1) (by omega) with ⟨hpb2, heb2⟩
        have hsep : (pref i + (runs[i]'hi).2.length ≤ pref j) ∨ (pref j + (runs[j]'hj).2.length ≤ pref i) := by
          rcases Nat.lt_or_gt_of_ne hij with hlt | hgt
          · exact Or.inl (hpref_lt hi hj hlt)
          · exact Or.inr (hpref_lt hj hi hgt)
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
        · intro e; dsimp only [a1, a2] at e; rw [← hea1, ← hea2] at e; have := nodup_getElem_inj hrcyc.2.1 _ _ e; omega
        · intro e; dsimp only [a1, b1] at e; rw [← hea1, ← heb1] at e; have := nodup_getElem_inj hrcyc.2.1 _ _ e; omega
        · intro e; dsimp only [a1, b2] at e; rw [← hea1, ← heb2] at e; have := nodup_getElem_inj hrcyc.2.1 _ _ e; omega
        · intro e; dsimp only [a2, b1] at e; rw [← hea2, ← heb1] at e; have := nodup_getElem_inj hrcyc.2.1 _ _ e; omega
        · intro e; dsimp only [a2, b2] at e; rw [← hea2, ← heb2] at e; have := nodup_getElem_inj hrcyc.2.1 _ _ e; omega
        · intro e; dsimp only [b1, b2] at e; rw [← heb1, ← heb2] at e; have := nodup_getElem_inj hrcyc.2.1 _ _ e; omega
      have hg_a1 : gadgetOf hs a1 = (runs[i]'hi).1 := (hmem_prop _ (List.getElem_mem hi)).2 a1 (List.getElem_mem _)
      have hg_a2 : gadgetOf hs a2 = (runs[i]'hi).1 := (hmem_prop _ (List.getElem_mem hi)).2 a2 (List.getElem_mem _)
      have hg_b1 : gadgetOf hs b1 = (runs[i]'hi).1 := by
        rw [heqg]; exact (hmem_prop _ (List.getElem_mem hj)).2 b1 (List.getElem_mem _)
      have hg_b2 : gadgetOf hs b2 = (runs[i]'hi).1 := by
        rw [heqg]; exact (hmem_prop _ (List.getElem_mem hj)).2 b2 (List.getElem_mem _)
      have hloc_ne : ∀ {x y : Fin (nb * s)}, gadgetOf hs x = gadgetOf hs y → x ≠ y → localOf hs x ≠ localOf hs y := by
        intro x y hgx hxy hloc
        apply hxy
        rw [← liftVert_gadgetOf_localOf hs x, ← liftVert_gadgetOf_localOf hs y, hgx, hloc]
      have hsp_i := hbdry_spec i hi
      have hsp_j := hbdry_spec j hj
      have hp_a1 : I.isPort (localOf hs a1) = true := by
        have := hsp_i.1; rwa [head_eq_zero] at this
      have hp_a2 : I.isPort (localOf hs a2) = true := by
        have := hsp_i.2.2.1; rwa [List.getLast_eq_getElem] at this
      have hp_b1 : I.isPort (localOf hs b1) = true := by
        have := hsp_j.1; rwa [head_eq_zero] at this
      have hp_b2 : I.isPort (localOf hs b2) = true := by
        have := hsp_j.2.2.1; rwa [List.getLast_eq_getElem] at this
      rcases h4_disj with ⟨d12, d13, d14, d23, d24, d34⟩
      have l12 := hloc_ne (hg_a1.trans hg_a2.symm) d12
      have l13 := hloc_ne (hg_a1.trans hg_b1.symm) d13
      have l14 := hloc_ne (hg_a1.trans hg_b2.symm) d14
      have l23 := hloc_ne (hg_a2.trans hg_b1.symm) d23
      have l24 := hloc_ne (hg_a2.trans hg_b2.symm) d24
      have l34 := hloc_ne (hg_b1.trans hg_b2.symm) d34
      rcases I.port_in_three _ hp_a1 with e1 | e1 | e1 <;>
      rcases I.port_in_three _ hp_a2 with e2 | e2 | e2 <;>
      rcases I.port_in_three _ hp_b1 with e3 | e3 | e3 <;>
      rcases I.port_in_three _ hp_b2 with e4 | e4 | e4 <;>
      first
      | exact l12 (e1.trans e2.symm) | exact l13 (e1.trans e3.symm) | exact l14 (e1.trans e4.symm)
      | exact l23 (e2.trans e3.symm) | exact l24 (e2.trans e4.symm) | exact l34 (e3.trans e4.symm)
    have hruns_ge3 : runs.length ≥ 3 := by
      apply Classical.byContradiction
      intro hlt
      have hlen2 : runs.length = 2 := by omega
      have h0 : 0 < runs.length := by omega
      have h1 : 1 < runs.length := by omega
      have hsp0 := hbdry_spec 0 h0
      have hb0 := hblk_ge2 0 h0
      have hne0 := hne (runs[0]'h0) (List.getElem_mem h0)
      have hprev0 : (0 + runs.length - 1) % runs.length = 1 := by rw [hlen2]
      have hnext0 : (0 + 1) % runs.length = 1 := by rw [hlen2]
      have hkP0 : (0 + runs.length - 1) % runs.length < runs.length := Nat.mod_lt _ (by omega)
      have hkN0 : (0 + 1) % runs.length < runs.length := Nat.mod_lt _ (by omega)
      have hg_hd_ext : gadgetOf hs (I.portExt (runs[0]'h0).1 (localOf hs ((runs[0]'h0).2.head hne0))) = (runs[1]'h1).1 := by
        rw [hsp0.2.1]
        have hmem := (hmem_prop (runs[(0 + runs.length - 1) % runs.length]'hkP0) (List.getElem_mem hkP0)).2
          _ (List.getLast_mem (hne _ (List.getElem_mem hkP0)))
        simpa only [hprev0] using hmem
      have hg_ls_ext : gadgetOf hs (I.portExt (runs[0]'h0).1 (localOf hs ((runs[0]'h0).2.getLast hne0))) = (runs[1]'h1).1 := by
        rw [hsp0.2.2.2.1]
        have hmem := (hmem_prop (runs[(0 + 1) % runs.length]'hkN0) (List.getElem_mem hkN0)).2
          _ (List.head_mem (hne _ (List.getElem_mem hkN0)))
        simpa only [hnext0] using hmem
      have hhd_ne_ls : (runs[0]'h0).2.head hne0 ≠ (runs[0]'h0).2.getLast hne0 := by
        rw [head_eq_zero, List.getLast_eq_getElem]
        have hsp_0 : rcyc = (runs[0]'h0).2 ++ (runs.drop 1).flatMap Prod.snd := by
          have hdt : runs = (runs[0]'h0) :: runs.drop 1 := by
            have := List.drop_eq_getElem_cons h0; simpa using this
          have hfm := congrArg (List.flatMap Prod.snd) hdt
          rw [hflat, List.flatMap_cons] at hfm; exact hfm
        have hnd0 : (runs[0]'h0).2.Nodup := (List.nodup_append.mp (hsp_0 ▸ hrcyc.2.1)).1
        intro e
        have := nodup_getElem_inj hnd0 _ _ e
        omega
      have hloc_ne : localOf hs ((runs[0]'h0).2.head hne0) ≠ localOf hs ((runs[0]'h0).2.getLast hne0) := by
        intro hloc
        apply hhd_ne_ls
        have hg1 := (hmem_prop _ (List.getElem_mem h0)).2 _ (List.head_mem hne0)
        have hg2 := (hmem_prop _ (List.getElem_mem h0)).2 _ (List.getLast_mem hne0)
        rw [← liftVert_gadgetOf_localOf hs ((runs[0]'h0).2.head hne0),
            ← liftVert_gadgetOf_localOf hs ((runs[0]'h0).2.getLast hne0), hg1, hg2, hloc]
      exact I.ext_distinct_gadget _ _ _ hsp0.1 hsp0.2.2.1 hloc_ne (hg_hd_ext.trans hg_ls_ext.symm)
    refine ⟨runs, ?_, hsum, ?_⟩
    · refine ⟨by simp [hruns_ge3], hbase_nodup, ?_⟩
      intro i hi
      simp only [List.length_map] at hi
      simp only [List.getElem_map, List.length_map]
      exact (hbdry_spec i hi).2.2.2.2
    · intro k hk
      have hsp := hbdry_spec k hk
      have hbk := hblk_ge2 k hk
      refine ⟨hbk, (hmem_prop _ (List.getElem_mem hk)).2, hblk_adj k hk, ?_⟩
      refine ⟨by omega, by omega, ?_, ?_, ?_, ?_⟩
      · have := hsp.1; rwa [head_eq_zero] at this
      · have := hsp.2.2.1; rwa [List.getLast_eq_getElem] at this
      · have h1 := hsp.2.1
        rw [head_eq_zero] at h1
        rw [h1]
        have hkP : (k + runs.length - 1) % runs.length < runs.length := Nat.mod_lt _ (by omega)
        exact (hmem_prop (runs[(k + runs.length - 1) % runs.length]'hkP) (List.getElem_mem hkP)).2
          _ (List.getLast_mem (hne _ (List.getElem_mem hkP)))
      · have h1 := hsp.2.2.2.1
        rw [List.getLast_eq_getElem] at h1
        rw [h1]
        have hkN : (k + 1) % runs.length < runs.length := Nat.mod_lt _ (by omega)
        exact (hmem_prop (runs[(k + 1) % runs.length]'hkN) (List.getElem_mem hkN)).2
          _ (List.head_mem (hne _ (List.getElem_mem hkN)))

/-! ## 4. General 3-Port Gadget-Inflation 3-Connectivity Theorem -/

/-- **General 3-Port Gadget-Inflation 3-Connectivity Theorem.** -/
theorem inflation_is3Connected {nb s : Nat} {hs : s > 0} (I : Inflation3Port nb s hs)
    (hnb : nb ≥ 4)
    (hB3 : I.base.toFinGraph.Is3Connected)
    (hport_adj : ∀ (g : Fin nb) (r : Fin s), I.isPort r = true →
      I.infl.toFinGraph.adj (liftVert g r) (I.portExt g r) = true ∧
      gadgetOf hs (I.portExt g r) ≠ g)
    (hbridge : ∀ (g1 g2 : Fin nb), I.base.toFinGraph.adj g1 g2 = true →
      ∃ r1 : Fin s, I.isPort r1 = true ∧ gadgetOf hs (I.portExt g1 r1) = g2)
    (hG_int1 : ∀ (g : Fin nb) (d a b : Fin s), a ≠ d → b ≠ d →
      ∃ p : List (Fin (nb * s)),
        I.infl.toFinGraph.IsWalkAvoiding [liftVert g d] (liftVert g a) (liftVert g b) p ∧
        ∀ v ∈ p, gadgetOf hs v = g)
    (hG_int2 : ∀ (g : Fin nb) (d1 d2 a : Fin s), a ≠ d1 → a ≠ d2 →
      ∃ r : Fin s, I.isPort r = true ∧ r ≠ d1 ∧ r ≠ d2 ∧
        ∃ p : List (Fin (nb * s)),
          I.infl.toFinGraph.IsWalkAvoiding [liftVert g d1, liftVert g d2] (liftVert g a) (liftVert g r) p ∧
          ∀ v ∈ p, gadgetOf hs v = g)
    (h3ports : I.isPort I.p0 = true ∧ I.isPort I.p1 = true ∧ I.isPort I.p2 = true ∧
      I.p0 ≠ I.p1 ∧ I.p1 ≠ I.p2 ∧ I.p0 ≠ I.p2) :
    I.infl.toFinGraph.Is3Connected := by
  refine ⟨by have : nb * s ≥ 4 * 1 := Nat.mul_le_mul hnb hs; omega, ?_⟩
  intro u v x y hx hy
  have hwalk_weaken : ∀ {f1 f2 : List (Fin (nb * s))} {a b : Fin (nb * s)} {p : List (Fin (nb * s))},
      I.infl.toFinGraph.IsWalkAvoiding f1 a b p →
      (a ∉ f2) → (∀ z ∈ p, z ∉ f2) →
      I.infl.toFinGraph.IsWalkAvoiding f2 a b p := by
    intro f1 f2 a b p hw ha hp
    induction p generalizing a with
    | nil => exact ⟨hw.1, ha⟩
    | cons z zs ih =>
      rcases hw with ⟨_, hadj, hrest⟩
      exact ⟨ha, hadj, ih hrest (hp z (List.mem_cons_self ..)) (fun w hw' => hp w (List.mem_cons_of_mem z hw'))⟩
  have hintact : ∀ (g : Fin nb), g ≠ gadgetOf hs u → g ≠ gadgetOf hs v →
      ∀ (a b : Fin s), ∃ p, I.infl.toFinGraph.IsWalkAvoiding [u, v] (liftVert g a) (liftVert g b) p := by
    intro g hgu hgv a b
    rcases h3ports with ⟨_, _, _, h01, h12, h02⟩
    have hex_d : ∃ d : Fin s, a ≠ d ∧ b ≠ d := by
      by_cases h1 : a ≠ I.p0 ∧ b ≠ I.p0
      · exact ⟨I.p0, h1⟩
      · by_cases h2 : a ≠ I.p1 ∧ b ≠ I.p1
        · exact ⟨I.p1, h2⟩
        · by_cases h3 : a ≠ I.p2 ∧ b ≠ I.p2
          · exact ⟨I.p2, h3⟩
          · by_cases ha0 : a = I.p0
            · by_cases hb1 : b = I.p1
              · exact absurd ⟨by rw [ha0]; exact h02, by rw [hb1]; exact h12⟩ h3
              · exact absurd ⟨by rw [ha0]; exact h01, hb1⟩ h2
            · by_cases ha1 : a = I.p1
              · by_cases hb0 : b = I.p0
                · exact absurd ⟨by rw [ha1]; exact h12, by rw [hb0]; exact h02⟩ h3
                · exact absurd ⟨ha0, hb0⟩ h1
              · by_cases hb0 : b = I.p0
                · exact absurd ⟨ha1, by rw [hb0]; exact h01⟩ h2
                · exact absurd ⟨ha0, hb0⟩ h1
    rcases hex_d with ⟨d, had, hbd⟩
    rcases hG_int1 g d a b had hbd with ⟨p, hp, hpg⟩
    refine ⟨p, hwalk_weaken hp ?_ ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨fun e => hgu (by rw [← e, gadgetOf_liftVert]), fun e => hgv (by rw [← e, gadgetOf_liftVert])⟩
    · intro z hz
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨fun e => hgu (by rw [← e, hpg z hz]), fun e => hgv (by rw [← e, hpg z hz])⟩
  have hlift_base : ∀ {g1 g2 : Fin nb} {bp : List (Fin nb)},
      I.base.toFinGraph.IsWalkAvoiding [gadgetOf hs u, gadgetOf hs v] g1 g2 bp →
      ∀ (r1 r2 : Fin s),
        ∃ p, I.infl.toFinGraph.IsWalkAvoiding [u, v] (liftVert g1 r1) (liftVert g2 r2) p := by
    intro g1 g2 bp hbp
    induction bp generalizing g1 with
    | nil =>
      rcases hbp with ⟨rfl, hg1⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hg1
      intro r1 r2
      exact hintact g1 hg1.1 hg1.2 r1 r2
    | cons gn gs ih =>
      rcases hbp with ⟨hg1, hadj, hrest⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hg1
      have hgn_nf : gn ∉ [gadgetOf hs u, gadgetOf hs v] := by
        cases gs with
        | nil => exact hrest.2
        | cons _ _ => exact hrest.1
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hgn_nf
      intro r1 r2
      rcases hbridge g1 gn hadj with ⟨rp, hrp_port, hrp_ext⟩
      rcases hintact g1 hg1.1 hg1.2 r1 rp with ⟨p1, hp1⟩
      let nxtV := I.portExt g1 rp
      have hstep_adj : I.infl.toFinGraph.adj (liftVert g1 rp) nxtV = true := (hport_adj g1 rp hrp_port).1
      have hnxt_eq : nxtV = liftVert gn (localOf hs nxtV) := by
        rw [← hrp_ext, liftVert_gadgetOf_localOf hs nxtV]
      have hstep_w : I.infl.toFinGraph.IsWalkAvoiding [u, v] (liftVert g1 rp) (liftVert gn (localOf hs nxtV)) [liftVert gn (localOf hs nxtV)] := by
        refine ⟨?_, by rw [← hnxt_eq]; exact hstep_adj, rfl, ?_⟩
        · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
          exact ⟨fun e => hg1.1 (by rw [← e, gadgetOf_liftVert]), fun e => hg1.2 (by rw [← e, gadgetOf_liftVert])⟩
        · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
          exact ⟨fun e => hgn_nf.1 (by rw [← e, gadgetOf_liftVert]), fun e => hgn_nf.2 (by rw [← e, gadgetOf_liftVert])⟩
      rcases ih hrest (localOf hs nxtV) r2 with ⟨p2, hp2⟩
      exact ⟨p1 ++ [liftVert gn (localOf hs nxtV)] ++ p2,
        FinGraph.isWalkAvoiding_append _ _ (FinGraph.isWalkAvoiding_append _ _ hp1 hstep_w) hp2⟩
  have hreach_intact : ∀ (z : Fin (nb * s)), z ∉ [u, v] →
      ∃ (g : Fin nb) (r : Fin s) (p : List (Fin (nb * s))),
        g ∉ [gadgetOf hs u, gadgetOf hs v] ∧
        I.infl.toFinGraph.IsWalkAvoiding [u, v] z (liftVert g r) p := by
    intro z hz
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hz
    let gz := gadgetOf hs z
    let rz := localOf hs z
    have hzeq : z = liftVert gz rz := (liftVert_gadgetOf_localOf hs z).symm
    by_cases hgz_intact : gz ≠ gadgetOf hs u ∧ gz ≠ gadgetOf hs v
    · exact ⟨gz, rz, [], by simp [hgz_intact], hzeq, by simp [hz]⟩
    · by_cases hsame : gadgetOf hs u = gadgetOf hs v
      · have hguz : gz = gadgetOf hs u := by
          by_cases h1 : gz = gadgetOf hs u
          · exact h1
          · exact absurd ⟨h1, by rw [← hsame]; exact h1⟩ hgz_intact
        have hgvz : gz = gadgetOf hs v := hguz.trans hsame
        have hrz_u : rz ≠ localOf hs u := fun e => hz.1 (by rw [hzeq, hguz, e, liftVert_gadgetOf_localOf])
        have hrz_v : rz ≠ localOf hs v := fun e => hz.2 (by rw [hzeq, hgvz, e, liftVert_gadgetOf_localOf])
        rcases hG_int2 gz (localOf hs u) (localOf hs v) rz hrz_u hrz_v with ⟨rp, hrp_port, hrp_u, hrp_v, p, hp, _⟩
        have hu_eq : liftVert gz (localOf hs u) = u := by rw [hguz, liftVert_gadgetOf_localOf]
        have hv_eq : liftVert gz (localOf hs v) = v := by rw [hgvz, liftVert_gadgetOf_localOf]
        rw [hu_eq, hv_eq, ← hzeq] at hp
        have hadj := (hport_adj gz rp hrp_port).1
        have hne_g := (hport_adj gz rp hrp_port).2
        have hgn_nf : gadgetOf hs (I.portExt gz rp) ∉ [gadgetOf hs u, gadgetOf hs v] := by
          simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
          exact ⟨by rw [← hguz]; exact hne_g, by rw [← hgvz]; exact hne_g⟩
        have hstep : I.infl.toFinGraph.IsWalkAvoiding [u, v] (liftVert gz rp) (I.portExt gz rp) [I.portExt gz rp] := by
          refine ⟨?_, hadj, rfl, ?_⟩
          · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
            exact ⟨fun e => hrp_u (by rw [← e, localOf_liftVert]), fun e => hrp_v (by rw [← e, localOf_liftVert])⟩
          · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
            exact ⟨fun e => hne_g (by rw [e, ← hguz]), fun e => hne_g (by rw [e, ← hgvz])⟩
        refine ⟨gadgetOf hs (I.portExt gz rp), localOf hs (I.portExt gz rp), p ++ [I.portExt gz rp], hgn_nf, ?_⟩
        rw [liftVert_gadgetOf_localOf]
        exact FinGraph.isWalkAvoiding_append _ _ hp hstep
      · have hex_port : ∃ rp : Fin s, I.isPort rp = true ∧ liftVert gz rp ≠ u ∧ liftVert gz rp ≠ v ∧
            gadgetOf hs (I.portExt gz rp) ≠ gadgetOf hs u ∧ gadgetOf hs (I.portExt gz rp) ≠ gadgetOf hs v := by
          rcases h3ports with ⟨hp0, hp1, hp2, h01, h12, h02⟩
          have hcase : ∀ (d : Fin (nb * s)) (gO : Fin nb),
              gadgetOf hs d = gz → gO ≠ gz →
              ∃ rp : Fin s, I.isPort rp = true ∧ rp ≠ localOf hs d ∧ gadgetOf hs (I.portExt gz rp) ≠ gO := by
            intro d gO _ _
            have hd01 := I.ext_distinct_gadget gz I.p0 I.p1 hp0 hp1 h01
            have hd12 := I.ext_distinct_gadget gz I.p1 I.p2 hp1 hp2 h12
            have hd02 := I.ext_distinct_gadget gz I.p0 I.p2 hp0 hp2 h02
            by_cases c0 : I.p0 ≠ localOf hs d ∧ gadgetOf hs (I.portExt gz I.p0) ≠ gO
            · exact ⟨I.p0, hp0, c0.1, c0.2⟩
            · by_cases c1 : I.p1 ≠ localOf hs d ∧ gadgetOf hs (I.portExt gz I.p1) ≠ gO
              · exact ⟨I.p1, hp1, c1.1, c1.2⟩
              · by_cases c2 : I.p2 ≠ localOf hs d ∧ gadgetOf hs (I.portExt gz I.p2) ≠ gO
                · exact ⟨I.p2, hp2, c2.1, c2.2⟩
                · by_cases e0 : I.p0 = localOf hs d
                  · by_cases g1 : gadgetOf hs (I.portExt gz I.p1) = gO
                    · exact absurd ⟨by rw [← e0]; exact Ne.symm h02, by rw [← g1]; exact Ne.symm hd12⟩ c2
                    · exact absurd ⟨by rw [← e0]; exact Ne.symm h01, g1⟩ c1
                  · have g0 : gadgetOf hs (I.portExt gz I.p0) = gO :=
                      Classical.byContradiction fun hng0 => c0 ⟨e0, hng0⟩
                    by_cases e1 : I.p1 = localOf hs d
                    · exact absurd ⟨by rw [← e1]; exact Ne.symm h12, by rw [← g0]; exact Ne.symm hd02⟩ c2
                    · exact absurd ⟨e1, by rw [← g0]; exact Ne.symm hd01⟩ c1
          by_cases hguz : gz = gadgetOf hs u
          · have hgv_ne : gadgetOf hs v ≠ gz := by rw [hguz]; exact Ne.symm hsame
            rcases hcase u (gadgetOf hs v) hguz.symm hgv_ne with ⟨rp, hrp, hrpu, hrpv⟩
            refine ⟨rp, hrp, ?_, ?_, ?_, hrpv⟩
            · intro e; exact hrpu (by rw [← e, localOf_liftVert])
            · intro e; exact hgv_ne (by rw [← e, gadgetOf_liftVert])
            · rw [← hguz]; exact (hport_adj gz rp hrp).2
          · have hgvz : gz = gadgetOf hs v :=
              Classical.byContradiction fun hgvz => hgz_intact ⟨hguz, hgvz⟩
            have hgu_ne : gadgetOf hs u ≠ gz := Ne.symm hguz
            rcases hcase v (gadgetOf hs u) hgvz.symm hgu_ne with ⟨rp, hrp, hrpv, hrpu⟩
            refine ⟨rp, hrp, ?_, ?_, hrpu, ?_⟩
            · intro e; exact hgu_ne (by rw [← e, gadgetOf_liftVert])
            · intro e; exact hrpv (by rw [← e, localOf_liftVert])
            · rw [← hgvz]; exact (hport_adj gz rp hrp).2
        rcases hex_port with ⟨rp, hrp_port, hrp_u, hrp_v, hgn_u, hgn_v⟩
        have hmem_av : ∀ {d : Fin (nb * s)} {a b : Fin (nb * s)} {q : List (Fin (nb * s))},
            I.infl.toFinGraph.IsWalkAvoiding [d] a b q → ∀ c ∈ q, c ≠ d := by
          intro d a b q hq
          induction q generalizing a with
          | nil => intro c hc; cases hc
          | cons c cs ih =>
            intro w hw
            rcases List.mem_cons.mp hw with rfl | hds
            · cases cs with
              | nil => have := hq.2.2.2; simp at this; exact this
              | cons _ _ => have := hq.2.2.1; simp at this; exact this
            · exact ih hq.2.2 w hds
        have hwalk_gz : ∃ p, I.infl.toFinGraph.IsWalkAvoiding [u, v] z (liftVert gz rp) p := by
          by_cases hguz : gz = gadgetOf hs u
          · have hrz_u : rz ≠ localOf hs u := fun e => hz.1 (by rw [hzeq, hguz, e, liftVert_gadgetOf_localOf])
            have hrp_lu : rp ≠ localOf hs u := fun e => hrp_u (by rw [hguz, e, liftVert_gadgetOf_localOf])
            rcases hG_int1 gz (localOf hs u) rz rp hrz_u hrp_lu with ⟨p, hp, hpg⟩
            have hu_eq : liftVert gz (localOf hs u) = u := by rw [hguz, liftVert_gadgetOf_localOf]
            rw [hu_eq, ← hzeq] at hp
            refine ⟨p, hwalk_weaken hp (by simp [hz]) ?_⟩
            intro w hw
            have hw_ne_u : w ≠ u := hmem_av hp w hw
            have hw_ne_v : w ≠ v := fun e => hsame (by rw [← hguz, ← hpg w hw, e])
            simp [hw_ne_u, hw_ne_v]
          · have hgvz : gz = gadgetOf hs v :=
              Classical.byContradiction fun hgvz => hgz_intact ⟨hguz, hgvz⟩
            have hrz_v : rz ≠ localOf hs v := fun e => hz.2 (by rw [hzeq, hgvz, e, liftVert_gadgetOf_localOf])
            have hrp_lv : rp ≠ localOf hs v := fun e => hrp_v (by rw [hgvz, e, liftVert_gadgetOf_localOf])
            rcases hG_int1 gz (localOf hs v) rz rp hrz_v hrp_lv with ⟨p, hp, hpg⟩
            have hv_eq : liftVert gz (localOf hs v) = v := by rw [hgvz, liftVert_gadgetOf_localOf]
            rw [hv_eq, ← hzeq] at hp
            refine ⟨p, hwalk_weaken hp (by simp [hz]) ?_⟩
            intro w hw
            have hw_ne_v : w ≠ v := hmem_av hp w hw
            have hw_ne_u : w ≠ u := fun e => hguz (by rw [← hpg w hw, e])
            simp [hw_ne_u, hw_ne_v]
        rcases hwalk_gz with ⟨p, hp⟩
        have hadj := (hport_adj gz rp hrp_port).1
        have hstep : I.infl.toFinGraph.IsWalkAvoiding [u, v] (liftVert gz rp) (I.portExt gz rp) [I.portExt gz rp] := by
          refine ⟨by simp [hrp_u, hrp_v], hadj, rfl, ?_⟩
          simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
          exact ⟨fun e => hgn_u (by rw [e]), fun e => hgn_v (by rw [e])⟩
        refine ⟨gadgetOf hs (I.portExt gz rp), localOf hs (I.portExt gz rp), p ++ [I.portExt gz rp], by simp [hgn_u, hgn_v], ?_⟩
        rw [liftVert_gadgetOf_localOf]
        exact FinGraph.isWalkAvoiding_append _ _ hp hstep
  rcases hreach_intact x hx with ⟨gx, rx, px, hgx_nf, hpx⟩
  rcases hreach_intact y hy with ⟨gy, ry, py, hgy_nf, hpy⟩
  rcases hB3.2 (gadgetOf hs u) (gadgetOf hs v) gx gy hgx_nf hgy_nf with ⟨bp, hbp⟩
  rcases hlift_base hbp rx ry with ⟨pmid, hpmid⟩
  rcases FinGraph.isWalkAvoiding_symm _ _ hpy with ⟨pyRev, hpyRev⟩
  exact ⟨px ++ pmid ++ pyRev,
    FinGraph.isWalkAvoiding_append _ _ (FinGraph.isWalkAvoiding_append _ _ hpx hpmid) hpyRev⟩

/-! ## 5. Zero-Bitmask Parent-Pointer Connectivity Certificates (O(diameter) Hops!) -/

/-- Check that `u` reaches `r` in at most `fuel` hops along `parent` avoiding `[d1, d2]`. -/
def reachesRoot2 {n : Nat} (S : CubicSpec n) (d1 d2 r : Fin n) (parent : Fin n → Fin n) :
    Nat → Fin n → Bool
  | 0, u => u == r && u != d1 && u != d2
  | fuel + 1, u =>
    if u == r then u != d1 && u != d2
    else
      let p := parent u
      u != d1 && u != d2 && S.adjBool u p && reachesRoot2 S d1 d2 r parent fuel p

theorem walk_of_reachesRoot2 {n : Nat} (S : CubicSpec n) (d1 d2 r : Fin n) (parent : Fin n → Fin n) :
    ∀ (fuel : Nat) (u : Fin n),
      reachesRoot2 S d1 d2 r parent fuel u = true →
      ∃ p : List (Fin n), S.toFinGraph.IsWalkAvoiding [d1, d2] u r p
  | 0, u, h => by
    simp only [reachesRoot2, Bool.and_eq_true, beq_iff_eq, bne_iff_ne] at h
    rcases h with ⟨⟨rfl, h1⟩, h2⟩
    exact ⟨[], rfl, by simp [h1, h2]⟩
  | fuel + 1, u, h => by
    simp only [reachesRoot2] at h
    by_cases hur : u = r
    · subst hur
      simp only [beq_self_eq_true, ↓reduceIte, Bool.and_eq_true, bne_iff_ne] at h
      exact ⟨[], rfl, by simp [h.1, h.2]⟩
    · rw [beq_false_of_ne hur] at h
      simp only [Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true, bne_iff_ne] at h
      rcases h with ⟨⟨⟨h1, h2⟩, hadj⟩, hrec⟩
      rcases walk_of_reachesRoot2 S d1 d2 r parent fuel (parent u) hrec with ⟨p, hp⟩
      exact ⟨parent u :: p, by simp [h1, h2], hadj, hp⟩

theorem connectedAvoiding_of_parent2 {n : Nat} (S : CubicSpec n) (d1 d2 r : Fin n)
    (parent : Fin n → Fin n) (fuel : Nat)
    (hcert : allFin n (fun u => u == d1 || u == d2 || reachesRoot2 S d1 d2 r parent fuel u) = true) :
    S.toFinGraph.ConnectedAvoiding [d1, d2] := by
  have hreach : ∀ u : Fin n, u ∉ [d1, d2] → ∃ p, S.toFinGraph.IsWalkAvoiding [d1, d2] u r p := by
    intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hu
    have hc := allFin_eq_true hcert u
    rw [beq_false_of_ne hu.1, beq_false_of_ne hu.2, Bool.false_or, Bool.false_or] at hc
    exact walk_of_reachesRoot2 S d1 d2 r parent fuel u hc
  intro a b ha hb
  rcases hreach a ha with ⟨pa, hpa⟩
  rcases hreach b hb with ⟨pb, hpb⟩
  rcases FinGraph.isWalkAvoiding_symm _ _ hpb with ⟨pbRev, hpbRev⟩
  exact ⟨pa ++ pbRev, FinGraph.isWalkAvoiding_append _ _ hpa hpbRev⟩

/-! ## 6. Concrete Sharpness Witness 1: `G168 = C24 * [T1 + P + T2]` -/

def c24Spec : CubicSpec 24 where
  nbrs := c24Nbrs
  valid := by decide

def g168Spec : CubicSpec 168 where
  nbrs := g168Nbrs
  valid := by decide

/-- `G168` as a kernel-verified cubic `PlaneMap 168` (`168 - 252 + 86 = 2`). -/
def g168Map : PlaneMap 168 :=
  g168Spec.buildPlaneMap g168Faces 252 (by decide) (by decide) (by decide) (by decide)

theorem g168_isCubic : g168Map.graph.IsCubic := g168Spec.toFinGraph_isCubic (by decide)

theorem g168_dartBijection :
    CubicSpec.HasExactDartBijection g168Spec g168Faces g168DartLoc :=
  CubicSpec.dartBijection_of_bool g168Spec g168Faces g168DartLoc (by decide)

theorem g168_singleVertexRotation :
    CubicSpec.HasSingleVertexRotation g168Spec g168Faces g168DartLoc :=
  CubicSpec.singleVertexRotation_of_bool g168Spec g168Faces g168DartLoc g168_dartBijection (by decide)

theorem g168_face_counts :
    (g168Faces.filter (fun f => f.length == 3)).length = 48 ∧
    (g168Faces.filter (fun f => f.length == 5)).length = 24 ∧
    (g168Faces.filter (fun f => f.length == 17)).length = 12 ∧
    (g168Faces.filter (fun f => f.length == 18)).length = 2 ∧
    g168Faces.length = 86 := by decide

/-- Explicit simple `C_32` cycle in `G168`, 100% kernel-verified. -/
theorem g168_has_C32 : g168Map.graph.HasSimpleCycleOfLen 32 :=
  ⟨g168C32, g168Map.graph.isSimpleCycle_of_bool g168C32 (by decide), by decide⟩

/-- Explicit vertex lifting for `G168` (`24` gadgets × `7` local vertices). -/
def g168Vert (g : Fin 24) (r : Fin 7) : Fin 168 := liftVert (nb := 24) (s := 7) g r

def g168PortExt (g : Fin 24) (r : Fin 7) : Fin 168 :=
  let v := g168Vert g r
  let a := g168Spec.nbr1 v
  let b := g168Spec.nbr2 v
  let c := g168Spec.nbr3 v
  if a.val / 7 != g.val then a
  else if b.val / 7 != g.val then b
  else c

def g168IsPort (r : Fin 7) : Bool :=
  r.val == 4 || r.val == 5 || r.val == 6

private theorem g168_inflation_check :
    allFin 168 (fun x =>
      let g := gadgetOf (nb := 24) (s := 7) (by decide) x
      let r := localOf (nb := 24) (s := 7) (by decide) x
      (g168Spec.nbrList x).all fun y =>
        let gy := gadgetOf (nb := 24) (s := 7) (by decide) y
        (g == gy) ||
        (g168IsPort r && (y == g168PortExt g r) && c24Spec.adjBool g gy)) = true := by decide

private theorem g168_ext_distinct_check :
    allFin 24 (fun g =>
      let g4 := (g168PortExt g 4).val / 7
      let g5 := (g168PortExt g 5).val / 7
      let g6 := (g168PortExt g 6).val / 7
      g4 != g5 && g5 != g6 && g4 != g6 &&
      g4 != g.val && g5 != g.val && g6 != g.val &&
      g168Spec.adjBool (g168Vert g 4) (g168PortExt g 4) &&
      g168Spec.adjBool (g168Vert g 5) (g168PortExt g 5) &&
      g168Spec.adjBool (g168Vert g 6) (g168PortExt g 6)) = true := by decide

def g168Inflation : Inflation3Port 24 7 (by decide) where
  base := c24Spec
  infl := g168Spec
  isPort := g168IsPort
  portExt := g168PortExt
  p0 := 4
  p1 := 5
  p2 := 6
  port_in_three := by
    intro r hr
    match r, hr with
    | ⟨4, _⟩, _ => exact Or.inl rfl
    | ⟨5, _⟩, _ => exact Or.inr (Or.inl rfl)
    | ⟨6, _⟩, _ => exact Or.inr (Or.inr rfl)
  ext_edge_spec := by
    intro x y hadj hdiff
    have hx := allFin_eq_true g168_inflation_check x
    have hy := List.all_eq_true.mp hx y ((g168Spec.mem_nbrList_iff x y).mpr hadj)
    dsimp only at hy
    have hneq : (gadgetOf (nb := 24) (s := 7) (by decide) x == gadgetOf (nb := 24) (s := 7) (by decide) y) = false :=
      beq_false_of_ne hdiff
    rw [hneq, Bool.false_or] at hy
    simp only [Bool.and_eq_true, beq_iff_eq] at hy
    exact ⟨hy.1.1, hy.1.2, hy.2⟩
  ext_distinct_gadget := by
    intro g r1 r2 hr1 hr2 hne
    have hg := allFin_eq_true g168_ext_distinct_check g
    simp only [Bool.and_eq_true, bne_iff_ne] at hg
    rcases hg with ⟨⟨⟨⟨⟨⟨⟨⟨h45, h56⟩, h46⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩
    match r1, hr1, r2, hr2 with
    | ⟨4, _⟩, _, ⟨4, _⟩, _ => exact absurd rfl hne
    | ⟨5, _⟩, _, ⟨5, _⟩, _ => exact absurd rfl hne
    | ⟨6, _⟩, _, ⟨6, _⟩, _ => exact absurd rfl hne
    | ⟨4, _⟩, _, ⟨5, _⟩, _ => intro e; exact h45 (congrArg Fin.val e)
    | ⟨5, _⟩, _, ⟨4, _⟩, _ => intro e; exact h45 (congrArg Fin.val e).symm
    | ⟨5, _⟩, _, ⟨6, _⟩, _ => intro e; exact h56 (congrArg Fin.val e)
    | ⟨6, _⟩, _, ⟨5, _⟩, _ => intro e; exact h56 (congrArg Fin.val e).symm
    | ⟨4, _⟩, _, ⟨6, _⟩, _ => intro e; exact h46 (congrArg Fin.val e)
    | ⟨6, _⟩, _, ⟨4, _⟩, _ => intro e; exact h46 (congrArg Fin.val e).symm

/-- Direct local adjacency of the 7-vertex gadget `G7` (O(1) table, zero `G168` BST overhead). -/
abbrev g7Adj : Fin 7 → Fin 7 → Bool := g7AdjFast

private theorem g7Adj_symm : ∀ a b : Fin 7, g7Adj a b = g7Adj b a := by decide

private theorem g168_local_gadget_props :
    allFin 24 (fun g =>
      allFin 7 (fun r1 =>
        allFin 7 (fun r2 =>
          g168Spec.adjBool (g168Vert g r1) (g168Vert g r2) == g7Adj r1 r2))) = true := by decide

private theorem g7_no_C4_bool :
    allFin 7 (fun a =>
      allFin 7 (fun b =>
        !(a != b && g7Adj a b) ||
        allFin 7 (fun c =>
          !(a != c && b != c && g7Adj b c) ||
          allFin 7 (fun d =>
            !(a != d && b != d && c != d && g7Adj c d && g7Adj d a))))) = true := by decide

private theorem g7_ports_indep_and_56_dist3 :
    (!g7Adj 4 5 && !g7Adj 5 6 && !g7Adj 4 6 &&
     allFin 7 (fun r => !(g7Adj 5 r && g7Adj r 6))) = true := by decide

/-- Minimum block size inside gadget `g` entering from `gPrev` and exiting to `gNext`. -/
def c24MinBlock (gPrev g gNext : Fin 24) : Nat :=
  let pIn := c24Port g gPrev
  let pOut := c24Port g gNext
  if (pIn == 5 && pOut == 6) || (pIn == 6 && pOut == 5) then 4 else 3

private theorem c24_port_matches_ext :
    allFin 24 (fun g =>
      (c24Spec.nbrList g).all fun gn =>
        let p := c24Port g gn
        (p == 4 && (g168PortExt g 4).val / 7 == gn.val) ||
        (p == 5 && (g168PortExt g 5).val / 7 == gn.val) ||
        (p == 6 && (g168PortExt g 6).val / 7 == gn.val)) = true := by decide

private theorem c24_no_C3 : ¬ c24Spec.toFinGraph.HasSimpleCycleOfLen 3 :=
  c24Spec.no_C3_of_bool (by decide)

private theorem c24_no_C4 : ¬ c24Spec.toFinGraph.HasSimpleCycleOfLen 4 :=
  c24Spec.no_C4_of_bool (by decide)

private theorem c24_c5_min17_bool : c24Spec.c5MinWeightBool c24MinBlock 17 = true := by decide

/-- **Kernel-Verified Absence of `C_4`, `C_8`, and `C_16` in `G168`!** -/
theorem g168_no_C4_C8_C16 :
    ¬ g168Map.graph.HasSimpleCycleOfLen 4 ∧
    ¬ g168Map.graph.HasSimpleCycleOfLen 8 ∧
    ¬ g168Map.graph.HasSimpleCycleOfLen 16 := by
  have hshift : ∀ (g : Fin 24) (a b : Fin 7),
      g168Spec.adjBool (g168Vert g a) (g168Vert g b) = g7Adj a b := fun g a b =>
    beq_iff_eq.mp (allFin_eq_true (allFin_eq_true (allFin_eq_true g168_local_gadget_props g) a) b)
  have hmain : ∀ L : Nat, (L = 4 ∨ (8 ≤ L ∧ L ≤ 16)) → ¬ g168Map.graph.HasSimpleCycleOfLen L := by
    intro L hL ⟨cyc, hcyc, hclen⟩
    rcases inflation_cycle_dichotomy g168Inflation cyc hcyc with ⟨g0, hall⟩ | ⟨runs, hbase, hsum, hruns⟩
    · -- Case 1: Single-gadget cycle inside `g0` -> length ≤ 7, and not 4!
      let locs := cyc.map (localOf (nb := 24) (s := 7) (by decide))
      have hlocs_nd : locs.Nodup := nodup_map_of_inj hcyc.2.1 (fun a ha b hb hloc => by
        rw [← liftVert_gadgetOf_localOf (by decide) a, ← liftVert_gadgetOf_localOf (by decide) b,
            hall a ha, hall b hb, hloc])
      have hle7 : cyc.length ≤ 7 := by
        have h1 := nodup_fin_length_le locs hlocs_nd
        simp only [locs, List.length_map] at h1; exact h1
      rcases hL with rfl | ⟨hge8, _⟩
      · match cyc, hclen, hcyc, hall with
        | [v0, v1, v2, v3], _, ⟨_, hnd, hadj⟩, hall =>
          let r0 := localOf (nb := 24) (s := 7) (by decide) v0
          let r1 := localOf (nb := 24) (s := 7) (by decide) v1
          let r2 := localOf (nb := 24) (s := 7) (by decide) v2
          let r3 := localOf (nb := 24) (s := 7) (by decide) v3
          have hv_eq : ∀ v ∈ [v0, v1, v2, v3], g168Vert g0 (localOf (nb := 24) (s := 7) (by decide) v) = v := fun v hv => by
            unfold g168Vert
            have hg : gadgetOf (nb := 24) (s := 7) (by decide) v = g0 := hall v hv
            rw [← hg, liftVert_gadgetOf_localOf]
          have h01 : g7Adj r0 r1 = true := by
            rw [← hshift g0, hv_eq v0 (by simp), hv_eq v1 (by simp)]; exact hadj 0 (by simp)
          have h12 : g7Adj r1 r2 = true := by
            rw [← hshift g0, hv_eq v1 (by simp), hv_eq v2 (by simp)]; exact hadj 1 (by simp)
          have h23 : g7Adj r2 r3 = true := by
            rw [← hshift g0, hv_eq v2 (by simp), hv_eq v3 (by simp)]; exact hadj 2 (by simp)
          have h30 : g7Adj r3 r0 = true := by
            rw [← hshift g0, hv_eq v3 (by simp), hv_eq v0 (by simp)]
            have h3 := hadj 3 (by simp)
            simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceMod,
                       List.getElem_cons_zero, List.getElem_cons_succ] at h3
            exact h3
          have hne_r : ∀ {x y : Fin 168}, x ∈ [v0, v1, v2, v3] → y ∈ [v0, v1, v2, v3] → x ≠ y →
              localOf (nb := 24) (s := 7) (by decide) x ≠ localOf (nb := 24) (s := 7) (by decide) y := by
            intro x y hx hy hxy hr
            apply hxy; rw [← hv_eq x hx, ← hv_eq y hy, hr]
          rcases List.nodup_cons.mp hnd with ⟨h0n, hnd1⟩
          rcases List.nodup_cons.mp hnd1 with ⟨h1n, hnd2⟩
          rcases List.nodup_cons.mp hnd2 with ⟨h2n, _⟩
          have hchk := allFin_eq_true (allFin_eq_true g7_no_C4_bool r0) r1
          have n01 : (r0 != r1) = true := bne_iff_ne.mpr (hne_r (by simp) (by simp) (fun e => h0n (by rw [e]; simp)))
          have n02 : (r0 != r2) = true := bne_iff_ne.mpr (hne_r (by simp) (by simp) (fun e => h0n (by rw [e]; simp)))
          have n03 : (r0 != r3) = true := bne_iff_ne.mpr (hne_r (by simp) (by simp) (fun e => h0n (by rw [e]; simp)))
          have n12 : (r1 != r2) = true := bne_iff_ne.mpr (hne_r (by simp) (by simp) (fun e => h1n (by rw [e]; simp)))
          have n13 : (r1 != r3) = true := bne_iff_ne.mpr (hne_r (by simp) (by simp) (fun e => h1n (by rw [e]; simp)))
          have n23 : (r2 != r3) = true := bne_iff_ne.mpr (hne_r (by simp) (by simp) (fun e => h2n (by rw [e]; simp)))
          simp only [n01, h01, Bool.and_self, Bool.not_true, Bool.false_or] at hchk
          have hchk2 := allFin_eq_true hchk r2
          simp only [n02, n12, h12, Bool.and_self, Bool.not_true, Bool.false_or] at hchk2
          have hchk3 := allFin_eq_true hchk2 r3
          simp [n03, n13, n23, h23, h30] at hchk3
      · omega
    · -- Case 2: Multi-gadget cycle!
      have hbase_c24 : c24Spec.toFinGraph.IsSimpleCycle (runs.map Prod.fst) := hbase
      have hrun_lb : ∀ (k : Nat) (hk : k < runs.length),
          let g := (runs[k]'hk).1
          let gPrev := (runs[(k + runs.length - 1) % runs.length]'(Nat.mod_lt _ (by omega))).1
          let gNext := (runs[(k + 1) % runs.length]'(Nat.mod_lt _ (by omega))).1
          (runs[k]'hk).2.length ≥ 3 ∧ (runs[k]'hk).2.length ≥ c24MinBlock gPrev g gNext := by
        intro k hk
        rcases hruns k hk with ⟨hge2, hsame_g, hadj_blk, h0, hl, hp_in, hp_out, hgn_in, hgn_out⟩
        dsimp only at hge2 hsame_g hadj_blk hp_in hp_out hgn_in hgn_out ⊢
        let g := (runs[k]'hk).1
        let blk := (runs[k]'hk).2
        have hge2' : blk.length ≥ 2 := hge2
        have hsame_g' : ∀ v ∈ blk, gadgetOf (nb := 24) (s := 7) (by decide) v = g := hsame_g
        have hadj_blk' : ∀ (j : Nat) (hj : j + 1 < blk.length),
            g168Spec.adjBool (blk[j]'(Nat.lt_of_succ_lt hj)) (blk[j + 1]'hj) = true := hadj_blk
        let rIn := localOf (nb := 24) (s := 7) (by decide) (blk[0]'h0)
        let rOut := localOf (nb := 24) (s := 7) (by decide) (blk[blk.length - 1]'hl)
        have hne_g : (runs[(k + runs.length - 1) % runs.length]'(Nat.mod_lt _ (by omega))).1 ≠
                     (runs[(k + 1) % runs.length]'(Nat.mod_lt _ (by omega))).1 := by
          have hbl3 : runs.length ≥ 3 := by have := hbase_c24.1; simp at this; exact this
          intro e
          have hlt1 : (k + runs.length - 1) % runs.length < (runs.map Prod.fst).length := by
            rw [List.length_map]; exact Nat.mod_lt _ (by omega)
          have hlt2 : (k + 1) % runs.length < (runs.map Prod.fst).length := by
            rw [List.length_map]; exact Nat.mod_lt _ (by omega)
          have heq := nodup_getElem_inj hbase_c24.2.1 hlt1 hlt2 (by simpa only [List.getElem_map] using e)
          by_cases hk0 : k = 0
          · subst hk0
            rw [Nat.zero_add, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at heq; omega
          · by_cases hkl : k + 1 = runs.length
            · have h1 : k + runs.length - 1 = (k - 1) + runs.length := by omega
              rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega), hkl, Nat.mod_self] at heq; omega
            · have h1 : k + runs.length - 1 = (k - 1) + runs.length := by omega
              rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at heq; omega
        have hr_ne : rIn ≠ rOut := by
          intro e
          apply hne_g
          rw [← hgn_in, ← hgn_out]
          exact congrArg (fun r => gadgetOf (nb := 24) (s := 7) (by decide) (g168Inflation.portExt g r)) e
        have hg_props := g7_ports_indep_and_56_dist3
        simp only [Bool.and_eq_true, Bool.not_eq_true'] at hg_props
        rcases hg_props with ⟨⟨⟨hno45, hno56⟩, hno46⟩, hno5r6⟩
        have hg7_symm : ∀ a b : Fin 7, g7Adj a b = g7Adj b a := g7Adj_symm
        have hno_adj_ports : g7Adj rIn rOut = false := by
          rcases g168Inflation.port_in_three rIn hp_in with h1 | h1 | h1 <;>
          rcases g168Inflation.port_in_three rOut hp_out with h2 | h2 | h2
          · exact absurd (h1.trans h2.symm) hr_ne
          · rw [h1, h2]; exact hno45
          · rw [h1, h2]; exact hno46
          · rw [h1, h2, hg7_symm]; exact hno45
          · exact absurd (h1.trans h2.symm) hr_ne
          · rw [h1, h2]; exact hno56
          · rw [h1, h2, hg7_symm]; exact hno46
          · rw [h1, h2, hg7_symm]; exact hno56
          · exact absurd (h1.trans h2.symm) hr_ne
        have hge3 : blk.length ≥ 3 := by
          apply Classical.byContradiction
          intro hlt3
          have heq2 : blk.length = 2 := by omega
          have hadj01 := hadj_blk' 0 (by omega)
          have hlift0 : g168Vert g rIn = blk[0]'h0 := by
            unfold g168Vert; rw [← hsame_g' _ (List.getElem_mem h0), liftVert_gadgetOf_localOf]
          have hlift1 : g168Vert g rOut = blk[1]'(by omega) := by
            have h1 : blk[blk.length - 1]'hl = blk[1]'(by omega) := by congr 1; omega
            unfold g168Vert; rw [← h1, ← hsame_g' _ (List.getElem_mem hl), liftVert_gadgetOf_localOf]
          have hbad : g7Adj rIn rOut = true := by
            rw [← hshift g rIn rOut, hlift0, hlift1]; exact hadj01
          rw [hno_adj_ports] at hbad; cases hbad
        refine ⟨hge3, ?_⟩
        change blk.length ≥ c24MinBlock (runs[(k + runs.length - 1) % runs.length]'(Nat.mod_lt _ (by omega))).1 g
          (runs[(k + 1) % runs.length]'(Nat.mod_lt _ (by omega))).1
        unfold c24MinBlock
        dsimp only
        split
        · rename_i h56
          have hport_eq : ∀ (gn : Fin 24) (r : Fin 7),
              g168IsPort r = true →
              c24Spec.toFinGraph.adj g gn = true →
              gadgetOf (nb := 24) (s := 7) (by decide) (g168PortExt g r) = gn →
              c24Port g gn = r.val := by
            intro gn r hr hadj_gn hext_gn
            have hm := List.all_eq_true.mp (allFin_eq_true c24_port_matches_ext g)
              gn ((c24Spec.mem_nbrList_iff g gn).mpr hadj_gn)
            simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at hm
            have hdist := g168Inflation.ext_distinct_gadget g
            rcases hm with (⟨hp, hg4⟩ | ⟨hp, hg5⟩) | ⟨hp, hg6⟩
            · rw [hp]
              apply Classical.byContradiction
              intro hne4
              have hne : r ≠ 4 := fun e => hne4 (congrArg Fin.val e).symm
              exact hdist r 4 hr (by decide) hne (hext_gn.trans (Fin.ext hg4.symm))
            · rw [hp]
              apply Classical.byContradiction
              intro hne5
              have hne : r ≠ 5 := fun e => hne5 (congrArg Fin.val e).symm
              exact hdist r 5 hr (by decide) hne (hext_gn.trans (Fin.ext hg5.symm))
            · rw [hp]
              apply Classical.byContradiction
              intro hne6
              have hne : r ≠ 6 := fun e => hne6 (congrArg Fin.val e).symm
              exact hdist r 6 hr (by decide) hne (hext_gn.trans (Fin.ext hg6.symm))
          have hadj_next : c24Spec.toFinGraph.adj g (runs[(k + 1) % runs.length]'(Nat.mod_lt _ (by omega))).1 = true := by
            have hstep := hbase_c24.2.2 k (by simp [hk])
            simpa only [List.length_map, List.getElem_map] using hstep
          have hadj_prev : c24Spec.toFinGraph.adj g (runs[(k + runs.length - 1) % runs.length]'(Nat.mod_lt _ (by omega))).1 = true := by
            rw [c24Spec.toFinGraph.symm]
            let kP := (k + runs.length - 1) % runs.length
            have hkP : kP < runs.length := Nat.mod_lt _ (by omega)
            have hstep := hbase_c24.2.2 kP (by simp [hkP])
            have hP1 : (kP + 1) % runs.length = k := by
              simp only [kP]; rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
              have h1 : k + runs.length - 1 + 1 = k + runs.length := by omega
              rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt hk]
            simpa only [List.length_map, List.getElem_map, hP1] using hstep
          have hrin_eq := hport_eq _ rIn hp_in hadj_prev hgn_in
          have hrout_eq := hport_eq _ rOut hp_out hadj_next hgn_out
          rw [hrin_eq, hrout_eq] at h56
          apply Classical.byContradiction
          intro hlt4
          have heq3 : blk.length = 3 := by omega
          let rMid := localOf (nb := 24) (s := 7) (by decide) (blk[1]'(by omega))
          have hlift0 : g168Vert g rIn = blk[0]'h0 := by
            unfold g168Vert; rw [← hsame_g' _ (List.getElem_mem h0), liftVert_gadgetOf_localOf]
          have hlift1 : g168Vert g rMid = blk[1]'(by omega) := by
            unfold g168Vert; rw [← hsame_g' (blk[1]'(by omega)) (List.getElem_mem (by omega)), liftVert_gadgetOf_localOf]
          have hlift2 : g168Vert g rOut = blk[2]'(by omega) := by
            have h2 : blk[blk.length - 1]'hl = blk[2]'(by omega) := by congr 1; omega
            unfold g168Vert; rw [← h2, ← hsame_g' _ (List.getElem_mem hl), liftVert_gadgetOf_localOf]
          have ha01 : g7Adj rIn rMid = true := by
            rw [← hshift g rIn rMid, hlift0, hlift1]; exact hadj_blk' 0 (by omega)
          have ha12 : g7Adj rMid rOut = true := by
            rw [← hshift g rMid rOut, hlift1, hlift2]; exact hadj_blk' 1 (by omega)
          have hno := allFin_eq_true hno5r6 rMid
          simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at h56
          rcases h56 with ⟨e5, e6⟩ | ⟨e6, e5⟩
          · have hr5 : rIn = 5 := Fin.ext e5
            have hr6 : rOut = 6 := Fin.ext e6
            rw [hr5] at ha01; rw [hr6] at ha12
            simp [ha01, ha12] at hno
          · have hr6 : rIn = 6 := Fin.ext e6
            have hr5 : rOut = 5 := Fin.ext e5
            rw [hr6] at ha01; rw [hr5] at ha12
            rw [hg7_symm] at ha01 ha12
            simp [ha01, ha12] at hno
        · exact hge3
      have hbl_ge3 : runs.length ≥ 3 := by have := hbase_c24.1; simp at this; exact this
      by_cases hlen5 : runs.length ≥ 6
      · have hge3_all : ∀ r ∈ runs, 3 ≤ r.2.length := by
          intro r hr
          rcases List.getElem_of_mem hr with ⟨k, hk, rfl⟩
          exact (hrun_lb k hk).1
        have hsum_ge := sumNat_le_of_all_le runs (fun _ => 3) (fun r => r.2.length) hge3_all
        rw [sumNat_map_const, hsum] at hsum_ge
        omega
      · have hlen_cases : runs.length = 3 ∨ runs.length = 4 ∨ runs.length = 5 := by omega
        rcases hlen_cases with h3 | h4 | h5
        · exact c24_no_C3 ⟨runs.map Prod.fst, hbase_c24, by simp [h3]⟩
        · exact c24_no_C4 ⟨runs.map Prod.fst, hbase_c24, by simp [h4]⟩
        · match hrm : runs with
          | [r0, r1, r2, r3, r4] =>
            have hbase5 : c24Spec.toFinGraph.IsSimpleCycle [r0.1, r1.1, r2.1, r3.1, r4.1] := by
              simpa [hrm] using hbase_c24
            have hw17 := c24Spec.c5_min_weight_of_bool c24MinBlock 17 c24_c5_min17_bool r0.1 r1.1 r2.1 r3.1 r4.1 hbase5
            have hb0 : r0.2.length ≥ c24MinBlock r4.1 r0.1 r1.1 := by
              have h := (hrun_lb 0 (by omega)).2
              simpa only [hrm, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceSub, Nat.reduceMod,
                List.getElem_cons_zero, List.getElem_cons_succ] using h
            have hb1 : r1.2.length ≥ c24MinBlock r0.1 r1.1 r2.1 := by
              have h := (hrun_lb 1 (by omega)).2
              simpa only [hrm, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceSub, Nat.reduceMod,
                List.getElem_cons_zero, List.getElem_cons_succ] using h
            have hb2 : r2.2.length ≥ c24MinBlock r1.1 r2.1 r3.1 := by
              have h := (hrun_lb 2 (by omega)).2
              simpa only [hrm, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceSub, Nat.reduceMod,
                List.getElem_cons_zero, List.getElem_cons_succ] using h
            have hb3 : r3.2.length ≥ c24MinBlock r2.1 r3.1 r4.1 := by
              have h := (hrun_lb 3 (by omega)).2
              simpa only [hrm, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceSub, Nat.reduceMod,
                List.getElem_cons_zero, List.getElem_cons_succ] using h
            have hb4 : r4.2.length ≥ c24MinBlock r3.1 r4.1 r0.1 := by
              have h := (hrun_lb 4 (by omega)).2
              simpa only [hrm, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceSub, Nat.reduceMod,
                List.getElem_cons_zero, List.getElem_cons_succ] using h
            simp only [hrm, sumNat, List.map_cons, List.map_nil] at hsum
            omega
          | [] | [_] | [_, _] | [_, _, _] | [_, _, _, _] | _ :: _ :: _ :: _ :: _ :: _ :: _ =>
            rw [hrm] at h5; simp at h5
  exact ⟨hmain 4 (Or.inl rfl), hmain 8 (Or.inr ⟨by omega, by omega⟩), hmain 16 (Or.inr ⟨by omega, by omega⟩)⟩

/-! ### 3-Connectivity of `C24` and `G168` -/

def c24Rot (v : Fin 24) : Fin 24 :=
  ⟨6 * (v.val / 6) + (v.val % 6 + 1) % 6, by omega⟩

private theorem c24Rot_is_aut :
    allFin 24 (fun u =>
      (c24Spec.nbrList u).all fun v =>
        c24Spec.adjBool (c24Rot u) (c24Rot v)) = true := by decide

private theorem c24Rot_inj : ∀ u v : Fin 24, c24Rot u = c24Rot v → u = v := by decide

private theorem c24Rot_six : ∀ v : Fin 24, Nat.repeat c24Rot 6 v = v := by decide

private def c24OrbitU (ui : Fin 4) : Fin 24 :=
  match ui.val with
  | 0 => 0
  | 1 => 6
  | 2 => 12
  | _ => 18

private theorem c24_rot_iter_surj_bool :
    allFin 24 (fun u =>
      ([0, 1, 2, 3, 4, 5] : List Nat).any fun k =>
        allFin 4 (fun ui => Nat.repeat c24Rot k (c24OrbitU ui) != u) == false) = true := by decide

private def c24ParentFor (ui : Fin 4) (v : Fin 24) : Fin 24 → Fin 24 :=
  match ui.val with
  | 0 => c24Parent0 v
  | 1 => c24Parent1 v
  | 2 => c24Parent2 v
  | _ => c24Parent3 v

private theorem c24_parent_orbit0 :
    allFin 24 (fun v =>
      let r : Fin 24 := if v != 1 then 1 else 2
      let par := c24Parent0 v
      allFin 24 fun x => x == 0 || x == v || reachesRoot2 c24Spec 0 v r par 7 x) = true := by decide

private theorem c24_parent_orbit1 :
    allFin 24 (fun v =>
      let r : Fin 24 := if v != 1 then 1 else 2
      let par := c24Parent1 v
      allFin 24 fun x => x == 6 || x == v || reachesRoot2 c24Spec 6 v r par 7 x) = true := by decide

private theorem c24_parent_orbit2 :
    allFin 24 (fun v =>
      let r : Fin 24 := if v != 1 then 1 else 2
      let par := c24Parent2 v
      allFin 24 fun x => x == 12 || x == v || reachesRoot2 c24Spec 12 v r par 7 x) = true := by decide

private theorem c24_parent_orbit3 :
    allFin 24 (fun v =>
      let r : Fin 24 := if v != 1 then 1 else 2
      let par := c24Parent3 v
      allFin 24 fun x => x == 18 || x == v || reachesRoot2 c24Spec 18 v r par 7 x) = true := by decide

private theorem c24_rot_walk {u v a b : Fin 24} {p : List (Fin 24)}
    (hw : c24Spec.toFinGraph.IsWalkAvoiding [u, v] a b p) :
    c24Spec.toFinGraph.IsWalkAvoiding [c24Rot u, c24Rot v] (c24Rot a) (c24Rot b) (p.map c24Rot) := by
  have hnf : ∀ x : Fin 24, x ∉ [u, v] → c24Rot x ∉ [c24Rot u, c24Rot v] := by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx ⊢
    exact ⟨fun e => hx.1 (c24Rot_inj _ _ e), fun e => hx.2 (c24Rot_inj _ _ e)⟩
  induction p generalizing a with
  | nil =>
    rcases hw with ⟨rfl, ha⟩
    exact ⟨rfl, hnf a ha⟩
  | cons w ws ih =>
    rcases hw with ⟨ha, hadj, hrest⟩
    have hadj' : c24Spec.toFinGraph.adj (c24Rot a) (c24Rot w) = true :=
      List.all_eq_true.mp (allFin_eq_true c24Rot_is_aut a)
        w ((c24Spec.mem_nbrList_iff a w).mpr hadj)
    exact ⟨hnf a ha, hadj', ih hrest⟩

theorem c24_is3Connected : c24Spec.toFinGraph.Is3Connected := by
  refine ⟨by decide, ?_⟩
  have horbit : ∀ (ui : Fin 4) (v : Fin 24),
      c24Spec.toFinGraph.ConnectedAvoiding [c24OrbitU ui, v] := by
    intro ui v
    let r : Fin 24 := if v != 1 then 1 else 2
    match ui with
    | ⟨0, _⟩ => exact connectedAvoiding_of_parent2 c24Spec 0 v r (c24Parent0 v) 7 (allFin_eq_true c24_parent_orbit0 v)
    | ⟨1, _⟩ => exact connectedAvoiding_of_parent2 c24Spec 6 v r (c24Parent1 v) 7 (allFin_eq_true c24_parent_orbit1 v)
    | ⟨2, _⟩ => exact connectedAvoiding_of_parent2 c24Spec 12 v r (c24Parent2 v) 7 (allFin_eq_true c24_parent_orbit2 v)
    | ⟨3, _⟩ => exact connectedAvoiding_of_parent2 c24Spec 18 v r (c24Parent3 v) 7 (allFin_eq_true c24_parent_orbit3 v)
  have hrot_conn : ∀ (u v : Fin 24), c24Spec.toFinGraph.ConnectedAvoiding [u, v] →
      c24Spec.toFinGraph.ConnectedAvoiding [c24Rot u, c24Rot v] := by
    intro u v hconn x y hx hy
    let inv (z : Fin 24) : Fin 24 := Nat.repeat c24Rot 5 z
    have hinv : ∀ z : Fin 24, c24Rot (inv z) = z := fun z => c24Rot_six z
    have hxin : inv x ∉ [u, v] := by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx ⊢
      exact ⟨fun e => hx.1 (by rw [← hinv x, e]), fun e => hx.2 (by rw [← hinv x, e])⟩
    have hyin : inv y ∉ [u, v] := by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hy ⊢
      exact ⟨fun e => hy.1 (by rw [← hinv y, e]), fun e => hy.2 (by rw [← hinv y, e])⟩
    rcases hconn (inv x) (inv y) hxin hyin with ⟨p, hp⟩
    have hpw := c24_rot_walk hp
    rw [hinv x, hinv y] at hpw
    exact ⟨p.map c24Rot, hpw⟩
  have hrot_iter : ∀ (k : Nat) (u v : Fin 24), c24Spec.toFinGraph.ConnectedAvoiding [u, v] →
      c24Spec.toFinGraph.ConnectedAvoiding [Nat.repeat c24Rot k u, Nat.repeat c24Rot k v] := by
    intro k
    induction k with
    | zero => intro u v h; exact h
    | succ k ih => intro u v h; exact hrot_conn _ _ (ih u v h)
  intro u v
  have hsurj := allFin_eq_true c24_rot_iter_surj_bool u
  rcases List.any_eq_true.mp hsurj with ⟨k, _, hk⟩
  have hex_ui : ∃ ui : Fin 4, Nat.repeat c24Rot k (c24OrbitU ui) = u := by
    apply Classical.byContradiction
    intro hnone
    have hall_ne : allFin 4 (fun ui => Nat.repeat c24Rot k (c24OrbitU ui) != u) = true := by
      have hgo : ∀ (m : Nat) (hm : m ≤ 4), allFinGo 4 (fun ui => Nat.repeat c24Rot k (c24OrbitU ui) != u) m hm = true := by
        intro m
        induction m with
        | zero => intro _; rfl
        | succ m ihm =>
          intro hm
          simp only [allFinGo, Bool.and_eq_true, bne_iff_ne]
          exact ⟨fun e => hnone ⟨⟨m, hm⟩, e⟩, ihm (Nat.le_of_lt hm)⟩
      exact hgo 4 (Nat.le_refl 4)
    rw [hall_ne] at hk; cases hk
  rcases hex_ui with ⟨ui, hu_eq⟩
  rw [← hu_eq]
  let invk (z : Fin 24) : Fin 24 := Nat.repeat c24Rot ((6 - k % 6) % 6) z
  have hinvk : Nat.repeat c24Rot k (invk v) = v := by
    have hadd : ∀ a b (z : Fin 24), Nat.repeat c24Rot (a + b) z = Nat.repeat c24Rot a (Nat.repeat c24Rot b z) := by
      intro a b z
      induction a with
      | zero => simp [Nat.repeat]
      | succ a iha => simp [Nat.succ_add, Nat.repeat, iha]
    have hmul6 : ∀ q (z : Fin 24), Nat.repeat c24Rot (6 * q) z = z := by
      intro q
      induction q with
      | zero => intro z; rfl
      | succ q ihq =>
        intro z
        have h1 : 6 * (q + 1) = 6 + 6 * q := by omega
        rw [h1, hadd, ihq, c24Rot_six]
    dsimp only [invk]
    rw [← hadd]
    have hdiv6 : k + (6 - k % 6) % 6 = 6 * ((k + (6 - k % 6) % 6) / 6) := by omega
    rw [hdiv6, hmul6]
  have hc := hrot_iter k (c24OrbitU ui) (invk v) (horbit ui (invk v))
  rwa [hinvk] at hc

/-- Zero-bitmask parent-pointer check inside 7-vertex gadget `G7`! -/
def g7ReachesRoot1 (d r : Fin 7) : Nat → Fin 7 → Bool
  | 0, x => x == r && x != d
  | fuel + 1, x =>
    if x == r then x != d
    else
      let p := g7Parent1 d x
      x != d && g7Adj x p && g7ReachesRoot1 d r fuel p

def g7ReachesPort2 (d1 d2 : Fin 7) : Nat → Fin 7 → Bool
  | 0, x => g168IsPort x && x != d1 && x != d2
  | fuel + 1, x =>
    if g168IsPort x then x != d1 && x != d2
    else
      let p := g7Parent2 d1 d2 x
      x != d1 && x != d2 && g7Adj x p && g7ReachesPort2 d1 d2 fuel p

private theorem g7_int1_cert :
    allFin 7 (fun d =>
      let r : Fin 7 := if d == 0 then 1 else 0
      allFin 7 (fun a => a == d || g7ReachesRoot1 d r 6 a)) = true := by decide

private theorem g7_int2_cert :
    allFin 7 (fun d1 =>
      allFin 7 (fun d2 =>
        allFin 7 (fun a => a == d1 || a == d2 || g7ReachesPort2 d1 d2 6 a))) = true := by decide

private theorem g7_walk_root1 (g : Fin 24) (d r : Fin 7) :
    ∀ (fuel : Nat) (a : Fin 7), g7ReachesRoot1 d r fuel a = true →
      ∃ p : List (Fin 168),
        g168Spec.toFinGraph.IsWalkAvoiding [g168Vert g d] (g168Vert g a) (g168Vert g r) p ∧
        ∀ v ∈ p, gadgetOf (nb := 24) (s := 7) (by decide) v = g := by
  have hshift : ∀ r1 r2 : Fin 7,
      g168Spec.adjBool (g168Vert g r1) (g168Vert g r2) = g7Adj r1 r2 := fun r1 r2 =>
    beq_iff_eq.mp (allFin_eq_true (allFin_eq_true (allFin_eq_true g168_local_gadget_props g) r1) r2)
  have hne_lift : ∀ x y : Fin 7, x ≠ y → g168Vert g x ≠ g168Vert g y := fun x y hxy he =>
    hxy (by have := congrArg (localOf (nb := 24) (s := 7) (by decide)) he; unfold g168Vert at this; rwa [localOf_liftVert, localOf_liftVert] at this)
  intro fuel
  induction fuel with
  | zero =>
    intro a ha
    simp only [g7ReachesRoot1, Bool.and_eq_true, beq_iff_eq, bne_iff_ne] at ha
    rcases ha with ⟨rfl, had⟩
    exact ⟨[], ⟨rfl, by simp [hne_lift _ _ had]⟩, fun _ h => nomatch h⟩
  | succ k ih =>
    intro a ha
    simp only [g7ReachesRoot1] at ha
    by_cases har : a = r
    · subst har
      simp only [beq_self_eq_true, ↓reduceIte, bne_iff_ne] at ha
      exact ⟨[], ⟨rfl, by simp [hne_lift _ _ ha]⟩, fun _ h => nomatch h⟩
    · rw [beq_false_of_ne har] at ha
      simp only [Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true, bne_iff_ne] at ha
      rcases ha with ⟨⟨had, hadj⟩, hrec⟩
      rcases ih (g7Parent1 d a) hrec with ⟨p, hp, hpg⟩
      have hadj_g : g168Spec.toFinGraph.adj (g168Vert g a) (g168Vert g (g7Parent1 d a)) = true := by
        simp only [CubicSpec.toFinGraph_adj]; rw [hshift]; exact hadj
      refine ⟨g168Vert g (g7Parent1 d a) :: p, ⟨by simp [hne_lift _ _ had], hadj_g, hp⟩, ?_⟩
      intro v hv
      rcases List.mem_cons.mp hv with rfl | hvp
      · exact gadgetOf_liftVert (by decide) g _
      · exact hpg v hvp

private theorem g7_walk_port2 (g : Fin 24) (d1 d2 : Fin 7) :
    ∀ (fuel : Nat) (a : Fin 7), g7ReachesPort2 d1 d2 fuel a = true →
      ∃ r : Fin 7, g168IsPort r = true ∧ r ≠ d1 ∧ r ≠ d2 ∧
        ∃ p : List (Fin 168),
          g168Spec.toFinGraph.IsWalkAvoiding [g168Vert g d1, g168Vert g d2] (g168Vert g a) (g168Vert g r) p ∧
          ∀ v ∈ p, gadgetOf (nb := 24) (s := 7) (by decide) v = g := by
  have hshift : ∀ r1 r2 : Fin 7,
      g168Spec.adjBool (g168Vert g r1) (g168Vert g r2) = g7Adj r1 r2 := fun r1 r2 =>
    beq_iff_eq.mp (allFin_eq_true (allFin_eq_true (allFin_eq_true g168_local_gadget_props g) r1) r2)
  have hne_lift : ∀ x y : Fin 7, x ≠ y → g168Vert g x ≠ g168Vert g y := fun x y hxy he =>
    hxy (by have := congrArg (localOf (nb := 24) (s := 7) (by decide)) he; unfold g168Vert at this; rwa [localOf_liftVert, localOf_liftVert] at this)
  intro fuel
  induction fuel with
  | zero =>
    intro a ha
    simp only [g7ReachesPort2, Bool.and_eq_true, bne_iff_ne] at ha
    rcases ha with ⟨⟨hp, h1⟩, h2⟩
    exact ⟨a, hp, h1, h2, [], ⟨rfl, by simp [hne_lift _ _ h1, hne_lift _ _ h2]⟩, fun _ h => nomatch h⟩
  | succ k ih =>
    intro a ha
    simp only [g7ReachesPort2] at ha
    by_cases hap : g168IsPort a = true
    · simp only [hap, ↓reduceIte, Bool.and_eq_true, bne_iff_ne] at ha
      exact ⟨a, hap, ha.1, ha.2, [], ⟨rfl, by simp [hne_lift _ _ ha.1, hne_lift _ _ ha.2]⟩, fun _ h => nomatch h⟩
    · simp only [hap, Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true, bne_iff_ne] at ha
      rcases ha with ⟨⟨⟨h1, h2⟩, hadj⟩, hrec⟩
      rcases ih (g7Parent2 d1 d2 a) hrec with ⟨r, hrp, hrd1, hrd2, p, hp, hpg⟩
      have hadj_g : g168Spec.toFinGraph.adj (g168Vert g a) (g168Vert g (g7Parent2 d1 d2 a)) = true := by
        simp only [CubicSpec.toFinGraph_adj]; rw [hshift]; exact hadj
      refine ⟨r, hrp, hrd1, hrd2, g168Vert g (g7Parent2 d1 d2 a) :: p,
        ⟨by simp [hne_lift _ _ h1, hne_lift _ _ h2], hadj_g, hp⟩, ?_⟩
      intro v hv
      rcases List.mem_cons.mp hv with rfl | hvp
      · exact gadgetOf_liftVert (by decide) g _
      · exact hpg v hvp

/-- **Kernel-Verified 3-Connectivity of `G168`!** -/
theorem g168_is3Connected : g168Map.graph.Is3Connected := by
  apply inflation_is3Connected g168Inflation (by decide) c24_is3Connected
  · intro g r hr
    have hg := allFin_eq_true g168_ext_distinct_check g
    simp only [Bool.and_eq_true, bne_iff_ne] at hg
    rcases hg with ⟨⟨⟨⟨⟨⟨⟨⟨_, _⟩, _⟩, h4g⟩, h5g⟩, h6g⟩, ha4⟩, ha5⟩, ha6⟩
    match r, hr with
    | ⟨4, _⟩, _ => exact ⟨ha4, fun e => h4g (congrArg Fin.val e)⟩
    | ⟨5, _⟩, _ => exact ⟨ha5, fun e => h5g (congrArg Fin.val e)⟩
    | ⟨6, _⟩, _ => exact ⟨ha6, fun e => h6g (congrArg Fin.val e)⟩
  · intro g1 g2 hadj
    have hm := List.all_eq_true.mp (allFin_eq_true c24_port_matches_ext g1)
      g2 ((c24Spec.mem_nbrList_iff g1 g2).mpr hadj)
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at hm
    rcases hm with (⟨_, h4⟩ | ⟨_, h5⟩) | ⟨_, h6⟩
    · exact ⟨4, by decide, Fin.ext h4⟩
    · exact ⟨5, by decide, Fin.ext h5⟩
    · exact ⟨6, by decide, Fin.ext h6⟩
  · intro g d a b had hbd
    let r : Fin 7 := if d == 0 then 1 else 0
    have ha_ok := allFin_eq_true (allFin_eq_true g7_int1_cert d) a
    have hb_ok := allFin_eq_true (allFin_eq_true g7_int1_cert d) b
    rw [beq_false_of_ne had, Bool.false_or] at ha_ok
    rw [beq_false_of_ne hbd, Bool.false_or] at hb_ok
    rcases g7_walk_root1 g d r 6 a ha_ok with ⟨pa, hpa, hpga⟩
    rcases g7_walk_root1 g d r 6 b hb_ok with ⟨pb, hpb, hpgb⟩
    -- Reverse `pb` while preserving `gadgetOf = g`:
    have hrev : ∀ {u1 u2 : Fin 168} {q : List (Fin 168)},
        g168Spec.toFinGraph.IsWalkAvoiding [g168Vert g d] u1 u2 q →
        gadgetOf (nb := 24) (s := 7) (by decide) u1 = g →
        (∀ v ∈ q, gadgetOf (nb := 24) (s := 7) (by decide) v = g) →
        ∃ qRev : List (Fin 168),
          g168Spec.toFinGraph.IsWalkAvoiding [g168Vert g d] u2 u1 qRev ∧
          ∀ v ∈ qRev, gadgetOf (nb := 24) (s := 7) (by decide) v = g := by
      intro u1 u2 q hq
      induction q generalizing u1 with
      | nil =>
        intro hu1 _
        rcases hq with ⟨rfl, hnf⟩
        exact ⟨[], ⟨rfl, hnf⟩, fun _ h => nomatch h⟩
      | cons w ws ih =>
        intro hu1 hqg
        rcases hq with ⟨hu1nf, hadj, hrest⟩
        have hw_g : gadgetOf (nb := 24) (s := 7) (by decide) w = g := hqg w (List.mem_cons_self ..)
        rcases ih hrest hw_g (fun v hv => hqg v (List.mem_cons_of_mem w hv)) with ⟨qr, hqr, hqrg⟩
        have hwnf : w ∉ [g168Vert g d] := by
          cases ws with
          | nil => exact hrest.2
          | cons _ _ => exact hrest.1
        have hstep : g168Spec.toFinGraph.IsWalkAvoiding [g168Vert g d] w u1 [u1] :=
          ⟨hwnf, by rw [g168Spec.toFinGraph.symm]; exact hadj, rfl, hu1nf⟩
        refine ⟨qr ++ [u1], FinGraph.isWalkAvoiding_append _ _ hqr hstep, ?_⟩
        intro v hv
        rcases List.mem_append.mp hv with hv | hv
        · exact hqrg v hv
        · simp at hv; subst hv; exact hu1
    rcases hrev hpb (gadgetOf_liftVert (by decide) g b) hpgb with ⟨pbRev, hpbRev, hpgbRev⟩
    refine ⟨pa ++ pbRev, FinGraph.isWalkAvoiding_append _ _ hpa hpbRev, ?_⟩
    intro v hv
    rcases List.mem_append.mp hv with hv | hv
    · exact hpga v hv
    · exact hpgbRev v hv
  · intro g d1 d2 a ha1 ha2
    have ha_ok := allFin_eq_true (allFin_eq_true (allFin_eq_true g7_int2_cert d1) d2) a
    rw [beq_false_of_ne ha1, beq_false_of_ne ha2, Bool.false_or, Bool.false_or] at ha_ok
    exact g7_walk_port2 g d1 d2 6 a ha_ok
  · decide

/-! ## 7. Concrete Sharpness Witness 2: `C60` (Truncated Icosahedron, 60 vertices) -/

def c60Spec : CubicSpec 60 where
  nbrs := c60Nbrs
  valid := by decide

/-- `C60` as a kernel-verified cubic `PlaneMap 60` (`60 - 90 + 32 = 2`). -/
def c60Map : PlaneMap 60 :=
  c60Spec.buildPlaneMap c60Faces 90 (by decide) (by decide) (by decide) (by decide)

theorem c60_isCubic : c60Map.graph.IsCubic := c60Spec.toFinGraph_isCubic (by decide)

theorem c60_dartBijection :
    CubicSpec.HasExactDartBijection c60Spec c60Faces c60DartLoc :=
  CubicSpec.dartBijection_of_bool c60Spec c60Faces c60DartLoc (by decide)

theorem c60_singleVertexRotation :
    CubicSpec.HasSingleVertexRotation c60Spec c60Faces c60DartLoc :=
  CubicSpec.singleVertexRotation_of_bool c60Spec c60Faces c60DartLoc c60_dartBijection (by decide)

theorem c60_face_counts :
    (c60Faces.filter (fun f => f.length == 5)).length = 12 ∧
    (c60Faces.filter (fun f => f.length == 6)).length = 20 ∧
    c60Faces.length = 32 := by decide

/-- Explicit simple `C_16` cycle in `C60`, 100% kernel-verified. -/
theorem c60_has_C16 : c60Map.graph.HasSimpleCycleOfLen 16 :=
  ⟨c60C16, c60Map.graph.isSimpleCycle_of_bool c60C16 (by decide), by decide⟩

/-- Apply a word of icosahedral symmetry generators `c60AutA` / `c60AutB` to a vertex of `C60`. -/
def c60ApplyWord : List Bool → Fin 60 → Fin 60
  | [], x => x
  | false :: ws, x => c60ApplyWord ws (c60AutA x)
  | true :: ws, x => c60ApplyWord ws (c60AutB x)

private theorem c60AutA_ok :
    allFin 60 (fun u =>
      c60AutAInv (c60AutA u) == u &&
      (c60Spec.nbrList u).all fun v => c60Spec.adjBool (c60AutA u) (c60AutA v)) = true := by decide

private theorem c60AutB_ok :
    allFin 60 (fun u =>
      c60AutBInv (c60AutB u) == u &&
      (c60Spec.nbrList u).all fun v => c60Spec.adjBool (c60AutB u) (c60AutB v)) = true := by decide

private theorem c60ToZero_ok :
    allFin 60 (fun u => c60ApplyWord (c60ToZeroWord u) u == 0) = true := by decide

private theorem c60_no_C8_at_0 : c60Spec.noC8At 0 = true := by decide

private theorem c60_aut_cycle {f : Fin 60 → Fin 60}
    (hinj : ∀ a b : Fin 60, f a = f b → a = b)
    (hadj : ∀ a b : Fin 60, c60Spec.toFinGraph.adj a b = true → c60Spec.toFinGraph.adj (f a) (f b) = true)
    {cyc : List (Fin 60)} (hcyc : c60Spec.toFinGraph.IsSimpleCycle cyc) :
    c60Spec.toFinGraph.IsSimpleCycle (cyc.map f) := by
  rcases hcyc with ⟨hlen, hnd, hwalk⟩
  refine ⟨by simpa using hlen, nodup_map_of_inj hnd (fun a _ b _ h => hinj a b h), ?_⟩
  intro i hi
  simp only [List.length_map] at hi
  simp only [List.length_map, List.getElem_map]
  exact hadj _ _ (hwalk i hi)

private theorem c60_word_cycle (ws : List Bool) {cyc : List (Fin 60)}
    (hcyc : c60Spec.toFinGraph.IsSimpleCycle cyc) :
    c60Spec.toFinGraph.IsSimpleCycle (cyc.map (c60ApplyWord ws)) := by
  have hA_inj : ∀ a b : Fin 60, c60AutA a = c60AutA b → a = b := fun a b h => by
    have ha := beq_iff_eq.mp (Bool.and_eq_true _ _ |>.mp (allFin_eq_true c60AutA_ok a)).1
    have hb := beq_iff_eq.mp (Bool.and_eq_true _ _ |>.mp (allFin_eq_true c60AutA_ok b)).1
    rw [← ha, ← hb, h]
  have hA_adj : ∀ a b : Fin 60, c60Spec.toFinGraph.adj a b = true →
      c60Spec.toFinGraph.adj (c60AutA a) (c60AutA b) = true := fun a b hab =>
    List.all_eq_true.mp (Bool.and_eq_true _ _ |>.mp (allFin_eq_true c60AutA_ok a)).2
      b ((c60Spec.mem_nbrList_iff a b).mpr hab)
  have hB_inj : ∀ a b : Fin 60, c60AutB a = c60AutB b → a = b := fun a b h => by
    have ha := beq_iff_eq.mp (Bool.and_eq_true _ _ |>.mp (allFin_eq_true c60AutB_ok a)).1
    have hb := beq_iff_eq.mp (Bool.and_eq_true _ _ |>.mp (allFin_eq_true c60AutB_ok b)).1
    rw [← ha, ← hb, h]
  have hB_adj : ∀ a b : Fin 60, c60Spec.toFinGraph.adj a b = true →
      c60Spec.toFinGraph.adj (c60AutB a) (c60AutB b) = true := fun a b hab =>
    List.all_eq_true.mp (Bool.and_eq_true _ _ |>.mp (allFin_eq_true c60AutB_ok a)).2
      b ((c60Spec.mem_nbrList_iff a b).mpr hab)
  induction ws generalizing cyc with
  | nil => simpa [c60ApplyWord] using hcyc
  | cons b ws ih =>
    cases b
    · have h1 := ih (c60_aut_cycle hA_inj hA_adj hcyc)
      rw [List.map_map] at h1
      exact h1
    · have h1 := ih (c60_aut_cycle hB_inj hB_adj hcyc)
      rw [List.map_map] at h1
      exact h1

/-- **Kernel-Verified Absence of `C_3`, `C_4`, and `C_8` in `C60`!**
Uses `C60` vertex-transitivity (`c60AutA`, `c60AutB`) to reduce `C_8`-freeness `60×` to vertex `0`. -/
theorem c60_no_C3_C4_C8 :
    ¬ c60Map.graph.HasSimpleCycleOfLen 3 ∧
    ¬ c60Map.graph.HasSimpleCycleOfLen 4 ∧
    ¬ c60Map.graph.HasSimpleCycleOfLen 8 := by
  refine ⟨c60Spec.no_C3_of_bool (by decide), c60Spec.no_C4_of_bool (by decide), ?_⟩
  rintro ⟨cyc, hcyc, hlen⟩
  match cyc, hlen, hcyc with
  | [v0, v1, v2, v3, v4, v5, v6, v7], _, hcyc =>
    let ws := c60ToZeroWord v0
    have hmapped := c60_word_cycle ws hcyc
    have hv0 : c60ApplyWord ws v0 = 0 := beq_iff_eq.mp (allFin_eq_true c60ToZero_ok v0)
    simp only [List.map_cons, List.map_nil, hv0] at hmapped
    exact c60Spec.no_C8_at_of_bool 0 c60_no_C8_at_0 _ _ _ _ _ _ _ hmapped

/-! ## 8. Concrete Sharpness Witness 3: `TD60` (Truncated Dodecahedron, 60 vertices) -/

def d20Spec : CubicSpec 20 where
  nbrs := d20Nbrs
  valid := by decide

def td60Spec : CubicSpec 60 where
  nbrs := td60Nbrs
  valid := by decide

/-- `TD60` as a kernel-verified cubic `PlaneMap 60` (`60 - 90 + 32 = 2`). -/
def td60Map : PlaneMap 60 :=
  td60Spec.buildPlaneMap td60Faces 90 (by decide) (by decide) (by decide) (by decide)

theorem td60_isCubic : td60Map.graph.IsCubic := td60Spec.toFinGraph_isCubic (by decide)

theorem td60_dartBijection :
    CubicSpec.HasExactDartBijection td60Spec td60Faces td60DartLoc :=
  CubicSpec.dartBijection_of_bool td60Spec td60Faces td60DartLoc (by decide)

theorem td60_singleVertexRotation :
    CubicSpec.HasSingleVertexRotation td60Spec td60Faces td60DartLoc :=
  CubicSpec.singleVertexRotation_of_bool td60Spec td60Faces td60DartLoc td60_dartBijection (by decide)

theorem td60_face_counts :
    (td60Faces.filter (fun f => f.length == 3)).length = 20 ∧
    (td60Faces.filter (fun f => f.length == 10)).length = 12 ∧
    td60Faces.length = 32 := by decide

/-- Explicit simple `C_16` cycle in `TD60`, 100% kernel-verified. -/
theorem td60_has_C16 : td60Map.graph.HasSimpleCycleOfLen 16 :=
  ⟨td60C16, td60Map.graph.isSimpleCycle_of_bool td60C16 (by decide), by decide⟩

def td60Vert (g : Fin 20) (r : Fin 3) : Fin 60 := liftVert (nb := 20) (s := 3) g r

def td60PortExt (g : Fin 20) (r : Fin 3) : Fin 60 :=
  let v := td60Vert g r
  let a := td60Spec.nbr1 v
  let b := td60Spec.nbr2 v
  let c := td60Spec.nbr3 v
  if a.val / 3 != g.val then a
  else if b.val / 3 != g.val then b
  else c

private theorem td60_inflation_check :
    allFin 60 (fun x =>
      let g := gadgetOf (nb := 20) (s := 3) (by decide) x
      let r := localOf (nb := 20) (s := 3) (by decide) x
      (td60Spec.nbrList x).all fun y =>
        let gy := gadgetOf (nb := 20) (s := 3) (by decide) y
        (g == gy) || ((y == td60PortExt g r) && d20Spec.adjBool g gy)) = true := by decide

private theorem td60_ext_distinct_check :
    allFin 20 (fun g =>
      let g0 := (td60PortExt g 0).val / 3
      let g1 := (td60PortExt g 1).val / 3
      let g2 := (td60PortExt g 2).val / 3
      g0 != g1 && g1 != g2 && g0 != g2) = true := by decide

def td60Inflation : Inflation3Port 20 3 (by decide) where
  base := d20Spec
  infl := td60Spec
  isPort := fun _ => true
  portExt := td60PortExt
  p0 := 0
  p1 := 1
  p2 := 2
  port_in_three := fun r _ => by
    match r with
    | ⟨0, _⟩ => exact Or.inl rfl
    | ⟨1, _⟩ => exact Or.inr (Or.inl rfl)
    | ⟨2, _⟩ => exact Or.inr (Or.inr rfl)
  ext_edge_spec := by
    intro x y hadj hdiff
    have hx := allFin_eq_true td60_inflation_check x
    have hy := List.all_eq_true.mp hx y ((td60Spec.mem_nbrList_iff x y).mpr hadj)
    dsimp only at hy
    have hneq : (gadgetOf (nb := 20) (s := 3) (by decide) x == gadgetOf (nb := 20) (s := 3) (by decide) y) = false :=
      beq_false_of_ne hdiff
    rw [hneq, Bool.false_or] at hy
    simp only [Bool.and_eq_true, beq_iff_eq] at hy
    exact ⟨rfl, hy.1, hy.2⟩
  ext_distinct_gadget := by
    intro g r1 r2 _ _ hne
    have hg := allFin_eq_true td60_ext_distinct_check g
    simp only [Bool.and_eq_true, bne_iff_ne] at hg
    rcases hg with ⟨⟨h01, h12⟩, h02⟩
    match r1, r2 with
    | ⟨0, _⟩, ⟨0, _⟩ | ⟨1, _⟩, ⟨1, _⟩ | ⟨2, _⟩, ⟨2, _⟩ => exact absurd rfl hne
    | ⟨0, _⟩, ⟨1, _⟩ => intro e; exact h01 (congrArg Fin.val e)
    | ⟨1, _⟩, ⟨0, _⟩ => intro e; exact h01 (congrArg Fin.val e).symm
    | ⟨1, _⟩, ⟨2, _⟩ => intro e; exact h12 (congrArg Fin.val e)
    | ⟨2, _⟩, ⟨1, _⟩ => intro e; exact h12 (congrArg Fin.val e).symm
    | ⟨0, _⟩, ⟨2, _⟩ => intro e; exact h02 (congrArg Fin.val e)
    | ⟨2, _⟩, ⟨0, _⟩ => intro e; exact h02 (congrArg Fin.val e).symm

private theorem d20_no_C3 : ¬ d20Spec.toFinGraph.HasSimpleCycleOfLen 3 :=
  d20Spec.no_C3_of_bool (by decide)

private theorem d20_no_C4 : ¬ d20Spec.toFinGraph.HasSimpleCycleOfLen 4 :=
  d20Spec.no_C4_of_bool (by decide)

/-- **Kernel-Verified Absence of `C_4, C_5, C_6, C_7, C_8, C_9` in `TD60`!** -/
theorem td60_no_C4_to_C9 (L : Nat) (hlo : 4 ≤ L) (hhi : L ≤ 9) :
    ¬ td60Map.graph.HasSimpleCycleOfLen L := by
  rintro ⟨cyc, hcyc, hclen⟩
  rcases inflation_cycle_dichotomy td60Inflation cyc hcyc with ⟨g0, hall⟩ | ⟨runs, hbase, hsum, hruns⟩
  · let locs := cyc.map (localOf (nb := 20) (s := 3) (by decide))
    have hlocs_nd : locs.Nodup := nodup_map_of_inj hcyc.2.1 (fun a ha b hb hloc => by
      rw [← liftVert_gadgetOf_localOf (by decide) a, ← liftVert_gadgetOf_localOf (by decide) b,
          hall a ha, hall b hb, hloc])
    have hle3 : cyc.length ≤ 3 := by
      have h1 := nodup_fin_length_le locs hlocs_nd
      simp only [locs, List.length_map] at h1; exact h1
    omega
  · have hbl_ge3 : runs.length ≥ 3 := by have := hbase.1; simp at this; exact this
    have hbl_ge5 : runs.length ≥ 5 := by
      apply Classical.byContradiction
      intro hlt
      have h34 : runs.length = 3 ∨ runs.length = 4 := by omega
      rcases h34 with h3 | h4
      · exact d20_no_C3 ⟨runs.map Prod.fst, hbase, by simp [h3]⟩
      · exact d20_no_C4 ⟨runs.map Prod.fst, hbase, by simp [h4]⟩
    have hge2_all : ∀ r ∈ runs, 2 ≤ r.2.length := by
      intro r hr
      rcases List.getElem_of_mem hr with ⟨k, hk, rfl⟩
      exact (hruns k hk).1
    have hsum_ge := sumNat_le_of_all_le runs (fun _ => 2) (fun r => r.2.length) hge2_all
    rw [sumNat_map_const, hsum] at hsum_ge
    omega

end PlanarEG
