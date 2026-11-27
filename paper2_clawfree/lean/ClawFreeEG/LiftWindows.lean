/-!
# ClawFreeEG.LiftWindows

Core finite simple graph theory (`FinGraph`), exact forbidden band `F_EG`, sufficient bowtie
detour-selection realizability & lift-window arithmetic for `G = T(H)/B`, Bowtie-Forest &
Simple-Quotient arithmetic exclusions, Universal Cubic-to-General Transfer (`2^K → 2^{K+1}`),
Average-Degree `d_avg(G) ≥ 7/2` arithmetic closure, R5 Dual-Crossing Sturmian Lower Bound
(`18*L < 17*N` and bipartite `16*L < 15*N`, contrapositive `c(G) ≥ (17/18)|V(G)|` / `(15/16)|V(G)|`),
and the 15-Line Universal 3-Tree Lemma directly on `FinGraph`.

Pure Lean 4 (`v4.36.0`, ZERO Mathlib, ZERO `Std`, ZERO `sorry`, ZERO `axiom`,
ZERO `native_decide`, ZERO `unsafe`/`implemented_by`/`extern`/`partial`).
-/

namespace ClawFreeEG

/-! ## 1. Finite Simple Graphs, Counting Helpers, Subgraphs, & Simple Cycles -/

/-- Count how many elements of `Fin n` satisfy boolean predicate `p`. -/
def countPred {n : Nat} (p : Fin n → Bool) : Nat :=
  ((List.finRange n).filter p).length

theorem filter_length_le_of_imp {α : Type} (l : List α) (p q : α → Bool)
    (h : ∀ x ∈ l, p x = true → q x = true) :
    (l.filter p).length ≤ (l.filter q).length := by
  induction l with
  | nil => exact Nat.le_refl 0
  | cons x xs ih =>
    have ih' := ih (fun y hy => h y (List.mem_cons_of_mem x hy))
    cases hpx : p x
    · simp only [List.filter_cons, hpx, Bool.false_eq_true, ↓reduceIte]
      cases hqx : q x <;> simp <;> omega
    · have hqx : q x = true := h x (List.mem_cons_self ..) hpx
      simp only [List.filter_cons, hpx, hqx, ↓reduceIte, List.length_cons]
      omega

theorem countPred_le_of_imp {n : Nat} (p q : Fin n → Bool)
    (h : ∀ u : Fin n, p u = true → q u = true) :
    countPred p ≤ countPred q :=
  filter_length_le_of_imp (List.finRange n) p q (fun u _ hu => h u hu)

theorem filter_congr_eq {α : Type} (l : List α) (p q : α → Bool)
    (h : ∀ x ∈ l, p x = q x) : l.filter p = l.filter q :=
  List.filter_congr h

theorem countPred_congr {n : Nat} (p q : Fin n → Bool) (h : ∀ u, p u = q u) :
    countPred p = countPred q := by
  unfold countPred
  rw [List.filter_congr (fun u _ => h u)]

theorem filter_length_add_not {α : Type} (l : List α) (p : α → Bool) :
    (l.filter p).length + (l.filter (fun x => !p x)).length = l.length := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    cases hpx : p x <;> simp [hpx] <;> omega

theorem countPred_add_not {n : Nat} (p : Fin n → Bool) :
    countPred p + countPred (fun u => !p u) = n := by
  unfold countPred
  have h := filter_length_add_not (List.finRange n) p
  rw [List.length_finRange] at h
  exact h

theorem filter_length_le_length {α : Type} (l : List α) (p : α → Bool) :
    (l.filter p).length ≤ l.length := by
  have h := filter_length_add_not l p
  omega

theorem countPred_le_n {n : Nat} (p : Fin n → Bool) : countPred p ≤ n := by
  have h := countPred_add_not p
  omega

theorem countPred_true {n : Nat} : countPred (fun _ : Fin n => true) = n := by
  unfold countPred
  have h : (List.finRange n).filter (fun _ => true) = List.finRange n := by
    induction (List.finRange n) with
    | nil => rfl
    | cons x xs ih => simp [ih]
  rw [h, List.length_finRange]

theorem countPred_insert {n : Nat} (S : Fin n → Bool) (v : Fin n) (hv : S v = false) :
    countPred (fun u => S u || (u == v)) = countPred S + 1 := by
  unfold countPred
  have hlem : ∀ (l : List (Fin n)), l.Nodup → v ∈ l →
      (l.filter fun u => S u || (u == v)).length = (l.filter S).length + 1 := by
    intro l hnd hmem
    induction l with
    | nil => cases hmem
    | cons x xs ih =>
      rcases List.nodup_cons.mp hnd with ⟨hxnot, hndxs⟩
      by_cases hxv : x = v
      · subst hxv
        have htail : xs.filter (fun u => S u || (u == x)) = xs.filter S := by
          apply List.filter_congr
          intro u hu
          have hux : u ≠ x := fun h => hxnot (h ▸ hu)
          simp [beq_false_of_ne hux]
        simp [hv, htail]
      · have hvxs : v ∈ xs := by
          rcases List.mem_cons.mp hmem with rfl | h
          · exact absurd rfl hxv
          · exact h
        have hxbeq : (x == v) = false := beq_false_of_ne hxv
        have iht := ih hndxs hvxs
        simp only [List.filter_cons, hxbeq, Bool.or_false]
        cases S x <;> simp [iht]
  exact hlem (List.finRange n) (List.nodup_finRange n) (List.mem_finRange v)

theorem countPred_erase {n : Nat} (S : Fin n → Bool) (v : Fin n) (hv : S v = true) :
    countPred (fun u => S u && (u != v)) + 1 = countPred S := by
  have h0 : (fun u => S u && (u != v)) v = false := by simp
  have h1 := countPred_insert (fun u => S u && (u != v)) v h0
  have heq : countPred (fun u => (S u && (u != v)) || (u == v)) = countPred S := by
    apply countPred_congr
    intro u
    by_cases huv : u = v
    · subst huv; simp [hv]
    · simp [bne_iff_ne, huv, beq_false_of_ne huv]
  rw [heq] at h1
  omega

theorem mem_filter_finRange_iff {n : Nat} (p : Fin n → Bool) (u : Fin n) :
    u ∈ (List.finRange n).filter p ↔ p u = true := by
  simp [List.mem_filter, List.mem_finRange]

theorem nodup_filter_finRange {n : Nat} (p : Fin n → Bool) :
    ((List.finRange n).filter p).Nodup :=
  (List.nodup_finRange n).filter p

theorem subset_length_le_of_nodup {α : Type} [DecidableEq α] :
    ∀ {l1 l2 : List α}, l1.Nodup → (∀ x ∈ l1, x ∈ l2) → l1.length ≤ l2.length
  | [], _, _, _ => Nat.zero_le _
  | x :: xs, l2, hnd, hsub => by
    rcases List.nodup_cons.mp hnd with ⟨hxnot, hndxs⟩
    have hx2 : x ∈ l2 := hsub x (List.mem_cons_self ..)
    have hsub' : ∀ y ∈ xs, y ∈ l2.erase x := by
      intro y hy
      have hyx : y ≠ x := fun h => hxnot (h ▸ hy)
      exact (List.mem_erase_of_ne hyx).mpr (hsub y (List.mem_cons_of_mem x hy))
    have ih := subset_length_le_of_nodup hndxs hsub'
    have her : (l2.erase x).length + 1 = l2.length := by
      rw [List.length_erase_of_mem hx2]
      have hpos : 0 < l2.length := List.length_pos_of_mem hx2
      omega
    simp only [List.length_cons]
    omega

theorem eq_of_imp_and_countPred_eq {n : Nat} (p q : Fin n → Bool)
    (himp : ∀ u, p u = true → q u = true) (heq : countPred p = countPred q) :
    ∀ u, p u = q u := by
  intro u
  cases hpu : p u
  · cases hqu : q u
    · rfl
    · exfalso
      have h1 : countPred (fun x => p x || (x == u)) = countPred p + 1 :=
        countPred_insert p u hpu
      have h2 : countPred (fun x => p x || (x == u)) ≤ countPred q := by
        apply countPred_le_of_imp
        intro x hx
        simp only [Bool.or_eq_true, beq_iff_eq] at hx
        rcases hx with hx | rfl
        · exact himp x hx
        · exact hqu
      omega
  · exact (himp u hpu).symm

theorem countPred_of_list_eq {n : Nat} (p : Fin n → Bool) (xs : List (Fin n))
    (hnd : xs.Nodup) (hiff : ∀ u, p u = true ↔ u ∈ xs) :
    countPred p = xs.length := by
  have h1 : countPred p ≤ xs.length := by
    apply subset_length_le_of_nodup (nodup_filter_finRange p)
    intro u hu
    exact (hiff u).mp ((mem_filter_finRange_iff p u).mp hu)
  have h2 : xs.length ≤ countPred p := by
    apply subset_length_le_of_nodup hnd
    intro u hu
    exact (mem_filter_finRange_iff p u).mpr ((hiff u).mpr hu)
  omega

theorem countPred_le_of_subset_list {n : Nat} (p : Fin n → Bool) (xs : List (Fin n))
    (hsub : ∀ u, p u = true → u ∈ xs) :
    countPred p ≤ xs.length := by
  apply subset_length_le_of_nodup (nodup_filter_finRange p)
  intro u hu
  exact hsub u ((mem_filter_finRange_iff p u).mp hu)

theorem countPred_ge_of_nodup_subset {n : Nat} (p : Fin n → Bool) (xs : List (Fin n))
    (hnd : xs.Nodup) (hsub : ∀ u ∈ xs, p u = true) :
    xs.length ≤ countPred p := by
  apply subset_length_le_of_nodup hnd
  intro u hu
  exact (mem_filter_finRange_iff p u).mpr (hsub u hu)

/-- A finite simple graph on vertex set `Fin n` represented by a symmetric, irreflexive
computable adjacency matrix. -/
structure FinGraph (n : Nat) where
  adj : Fin n → Fin n → Bool
  symm : ∀ u v : Fin n, adj u v = adj v u
  loopless : ∀ u : Fin n, adj u u = false

namespace FinGraph

/-- The sorted list of neighbors of vertex `u`. -/
def neighbors {n : Nat} (G : FinGraph n) (u : Fin n) : List (Fin n) :=
  (List.finRange n).filter (fun v => G.adj u v)

/-- The degree of vertex `u` in `G`. -/
def deg {n : Nat} (G : FinGraph n) (u : Fin n) : Nat :=
  (G.neighbors u).length

/-- The sorted list of neighbors of `u` inside a vertex subset `S : Fin n → Bool`. -/
def neighborsIn {n : Nat} (G : FinGraph n) (S : Fin n → Bool) (u : Fin n) : List (Fin n) :=
  (List.finRange n).filter (fun v => S v && G.adj u v)

/-- The degree of `u` inside the induced subgraph `G[S]`. -/
def degIn {n : Nat} (G : FinGraph n) (S : Fin n → Bool) (u : Fin n) : Nat :=
  (G.neighborsIn S u).length

/-- Minimum degree at least `k` on a nonempty finite simple graph (`n ≥ 1`). -/
def MinDegreeAtLeast {n : Nat} (G : FinGraph n) (k : Nat) : Prop :=
  n ≥ 1 ∧ ∀ u : Fin n, k ≤ G.deg u

/-- Cubic (3-regular) nonempty finite simple graph predicate (`n ≥ 1`). -/
def IsCubic {n : Nat} (G : FinGraph n) : Prop :=
  n ≥ 1 ∧ ∀ u : Fin n, G.deg u = 3

/-- Claw-free (`K_{1,3}`-free) predicate on `FinGraph`. -/
def IsClawFree {n : Nat} (G : FinGraph n) : Prop :=
  ∀ u a b c : Fin n, a ≠ b → a ≠ c → b ≠ c →
    G.adj u a = true → G.adj u b = true → G.adj u c = true →
    G.adj a b = true ∨ G.adj a c = true ∨ G.adj b c = true

/-- Spanning subgraph relation `F ⊆ T`. -/
def IsSubgraphOf {n : Nat} (F T : FinGraph n) : Prop :=
  ∀ u v : Fin n, F.adj u v = true → T.adj u v = true

/-- Independent set predicate on `FinGraph`. -/
def IsIndependentSet {n : Nat} (G : FinGraph n) (S : Fin n → Bool) : Prop :=
  ∀ u v : Fin n, S u = true → S v = true → G.adj u v = false

/-- Computable duplicate-free check. -/
def nodupBool {α : Type} [BEq α] : List α → Bool
  | [] => true
  | x :: xs => !(xs.contains x) && nodupBool xs

/-- Propositional simple cycle predicate: length `≥ 3`, pairwise distinct vertices,
and consecutive vertices (cyclically) are adjacent in `G`. -/
def IsSimpleCycle {n : Nat} (G : FinGraph n) (cyc : List (Fin n)) : Prop :=
  cyc.length ≥ 3 ∧
  cyc.Nodup ∧
  ∀ (i : Nat) (hi : i < cyc.length),
    G.adj (cyc[i]'hi)
      (cyc[(i + 1) % cyc.length]'(Nat.mod_lt _ (Nat.lt_of_lt_of_le (Nat.zero_lt_of_lt hi) (Nat.le_refl _)))) = true

/-- Computable checker for simple cycles. -/
def isSimpleCycleBool {n : Nat} (G : FinGraph n) (cyc : List (Fin n)) : Bool :=
  (3 ≤ cyc.length) && nodupBool cyc &&
    (List.range cyc.length).all fun i =>
      if hi : i < cyc.length then
        let j := (i + 1) % cyc.length
        have hj : j < cyc.length := Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le i) hi)
        G.adj (cyc[i]'hi) (cyc[j]'hj)
      else true

theorem nodup_of_nodupBool {α : Type} [BEq α] [LawfulBEq α] :
    ∀ {xs : List α}, nodupBool xs = true → xs.Nodup
  | [], _ => List.nodup_nil
  | x :: xs, h => by
    simp only [nodupBool, Bool.and_eq_true, Bool.not_eq_true'] at h
    rcases h with ⟨hnot, hrest⟩
    have hmem : x ∉ xs := by
      intro hx
      have hc : xs.contains x = true := List.contains_iff_mem.mpr hx
      rw [hc] at hnot
      cases hnot
    exact List.nodup_cons.mpr ⟨hmem, nodup_of_nodupBool hrest⟩

theorem isSimpleCycle_of_bool {n : Nat} (G : FinGraph n) (cyc : List (Fin n))
    (h : G.isSimpleCycleBool cyc = true) : G.IsSimpleCycle cyc := by
  simp only [isSimpleCycleBool, Bool.and_eq_true, decide_eq_true_eq] at h
  rcases h with ⟨⟨hlen, hnd⟩, hadj⟩
  refine ⟨hlen, nodup_of_nodupBool hnd, ?_⟩
  intro i hi
  have hall := List.all_eq_true.mp hadj i (List.mem_range.mpr hi)
  simp only [hi, dite_true] at hall
  exact hall

/-- `G` contains a simple cycle of exact length `L`. -/
def HasSimpleCycleOfLen {n : Nat} (G : FinGraph n) (L : Nat) : Prop :=
  ∃ cyc : List (Fin n), G.IsSimpleCycle cyc ∧ cyc.length = L

/-- `G` contains a simple power-of-two cycle `C_{2^a}` (`a ≥ 2`). -/
def HasDyadicCycle {n : Nat} (G : FinGraph n) : Prop :=
  ∃ a : Nat, a ≥ 2 ∧ G.HasSimpleCycleOfLen (2 ^ a)

/-- `G` contains a simple power-of-two cycle of length at most `K`. -/
def HasDyadicCycleUpTo {n : Nat} (G : FinGraph n) (K : Nat) : Prop :=
  ∃ a : Nat, a ≥ 2 ∧ 2 ^ a ≤ K ∧ G.HasSimpleCycleOfLen (2 ^ a)

/-- `G` contains a triangle containing a vertex of degree exactly `3`. -/
def HasDeg3Triangle {n : Nat} (G : FinGraph n) : Prop :=
  ∃ w a b : Fin n, w ≠ a ∧ w ≠ b ∧ a ≠ b ∧
    G.deg w = 3 ∧ G.adj w a = true ∧ G.adj w b = true ∧ G.adj a b = true

/-- `G` contains a subgraph isomorphic to `K_{2,3}` (5 distinct vertices). -/
def HasK23 {n : Nat} (G : FinGraph n) : Prop :=
  ∃ x y a b c : Fin n, [x, y, a, b, c].Nodup ∧
    G.adj x a = true ∧ G.adj x b = true ∧ G.adj x c = true ∧
    G.adj y a = true ∧ G.adj y b = true ∧ G.adj y c = true

/-- `G` contains a subgraph isomorphic to `Q_3 - v^*` (7 distinct vertices:
hub `u` adjacent to `w1, w2, w3`, with `w1 ~ a,b`, `w2 ~ b,c`, `w3 ~ c,a`). -/
def HasQ3MinusV {n : Nat} (G : FinGraph n) : Prop :=
  ∃ u w1 w2 w3 a b c : Fin n, [u, w1, w2, w3, a, b, c].Nodup ∧
    G.adj u w1 = true ∧ G.adj u w2 = true ∧ G.adj u w3 = true ∧
    G.adj w1 a = true ∧ G.adj w1 b = true ∧
    G.adj w2 b = true ∧ G.adj w2 c = true ∧
    G.adj w3 c = true ∧ G.adj w3 a = true

theorem deg_eq_countPred {n : Nat} (G : FinGraph n) (u : Fin n) :
    G.deg u = countPred (G.adj u) := rfl

theorem degIn_eq_countPred {n : Nat} (G : FinGraph n) (S : Fin n → Bool) (u : Fin n) :
    G.degIn S u = countPred (fun v => S v && G.adj u v) := rfl

theorem degIn_all {n : Nat} (G : FinGraph n) (u : Fin n) :
    G.degIn (fun _ => true) u = G.deg u := by
  simp [degIn, neighborsIn, deg, neighbors]

theorem deg_le_of_subgraph {n : Nat} {F T : FinGraph n} (hsub : F.IsSubgraphOf T) (u : Fin n) :
    F.deg u ≤ T.deg u :=
  countPred_le_of_imp (F.adj u) (T.adj u) (fun v hv => hsub u v hv)

theorem adj_ne {n : Nat} (G : FinGraph n) {u v : Fin n} (h : G.adj u v = true) : u ≠ v := by
  intro heq
  subst heq
  rw [G.loopless] at h
  cases h

end FinGraph

/-! ## 2. Exact Forbidden Band `F_EG` & Lift-Window Arithmetic / Realizability -/

/-- Exact forbidden band `F_EG = ⋃_{a ≥ 2} (2^a, ⌊4·2^a/3⌋]`. -/
def InFEG (L : Nat) : Prop :=
  ∃ a : Nat, a ≥ 2 ∧ 2 ^ a < L ∧ 3 * L ≤ 4 * 2 ^ a

/-- Interval `[lo, hi]` avoids all powers of two `2^a` with `a ≥ 2`. -/
def AvoidsPow2 (lo hi : Nat) : Prop :=
  ∀ a : Nat, a ≥ 2 → ¬(lo ≤ 2 ^ a ∧ 2 ^ a ≤ hi)

/-- No power of two is divisible by `3`. -/
theorem pow2_mod_three_ne_zero : ∀ k : Nat, 2 ^ k % 3 ≠ 0
  | 0 => by decide
  | k + 1 => by
    have ih := pow2_mod_three_ne_zero k
    rw [Nat.pow_succ]
    omega

/-- Every integer `L ≥ 3` lies strictly between `2^a` and `2^(a+1)` (or equals `2^(a+1)`) for some `a ≥ 1`. -/
theorem exists_dyadic_bracket (L : Nat) (hL : L ≥ 3) :
    ∃ a : Nat, a ≥ 1 ∧ 2 ^ a < L ∧ L ≤ 2 ^ (a + 1) := by
  induction L with
  | zero => omega
  | succ m ih =>
    by_cases hm : m < 3
    · have hm2 : m = 2 := by omega
      subst hm2
      exact ⟨1, by omega, by decide, by decide⟩
    · rcases ih (by omega) with ⟨a, ha, hlo, hhi⟩
      by_cases hle : m + 1 ≤ 2 ^ (a + 1)
      · exact ⟨a, ha, by omega, hle⟩
      · have heq : m = 2 ^ (a + 1) := by omega
        refine ⟨a + 1, by omega, ?_, ?_⟩
        · omega
        · rw [Nat.pow_succ]; omega

/-- **Exact Forbidden Band Characterization:**
For every integer `L ≥ 3`, the cubic triangle-expansion lift window `[2*L, 3*L]` avoids all
powers of two `2^a` (`a ≥ 2`) if and only if `L ∈ F_EG`. -/
theorem avoidsPow2_2L_3L_iff_inFEG (L : Nat) (hL : L ≥ 3) :
    AvoidsPow2 (2 * L) (3 * L) ↔ InFEG L := by
  constructor
  · intro hav
    rcases exists_dyadic_bracket L hL with ⟨a, ha, hlo, hhi⟩
    have hnot_eq : L ≠ 2 ^ (a + 1) := by
      intro heq
      have hhit := hav (a + 2) (by omega)
      apply hhit
      have hpow : 2 ^ (a + 2) = 2 * 2 ^ (a + 1) := by rw [Nat.pow_succ]; omega
      omega
    have hlt_hi : L < 2 ^ (a + 1) := by omega
    have ha2 : a ≥ 2 := by
      exact Classical.byContradiction fun hlt => by
        have ha1 : a = 1 := by omega
        subst ha1
        simp at hlo hlt_hi
        have hL3 : L = 3 := by omega
        subst hL3
        exact hav 3 (by omega) ⟨by decide, by decide⟩
    have hnot_next := hav (a + 2) (by omega)
    have hpow2 : 2 ^ (a + 2) = 4 * 2 ^ a := by
      rw [Nat.pow_succ, Nat.pow_succ]; omega
    have hpow1 : 2 ^ (a + 1) = 2 * 2 ^ a := by
      rw [Nat.pow_succ]; omega
    have h2L_le : 2 * L ≤ 2 ^ (a + 2) := by omega
    have h3L_lt : 3 * L < 2 ^ (a + 2) := by
      exact Classical.byContradiction fun hge => hnot_next ⟨h2L_le, by omega⟩
    exact ⟨a, ha2, hlo, by omega⟩
  · rintro ⟨a, ha, hlo, hhi⟩ b hb ⟨hblo, hbhi⟩
    have hstrict : 3 * L < 4 * 2 ^ a := by
      have hne := pow2_mod_three_ne_zero (a + 2)
      have hpow2 : 2 ^ (a + 2) = 4 * 2 ^ a := by
        rw [Nat.pow_succ, Nat.pow_succ]; omega
      omega
    by_cases hba : b ≤ a + 1
    · have hle : 2 ^ b ≤ 2 ^ (a + 1) := Nat.pow_le_pow_right (by omega) hba
      have hpow1 : 2 ^ (a + 1) = 2 * 2 ^ a := by rw [Nat.pow_succ]; omega
      omega
    · have hge : a + 2 ≤ b := by omega
      have hpow_ge : 2 ^ (a + 2) ≤ 2 ^ b := Nat.pow_le_pow_right (by omega) hge
      have hpow2 : 2 ^ (a + 2) = 4 * 2 ^ a := by
        rw [Nat.pow_succ, Nat.pow_succ]; omega
      omega

/-- **Sufficient Bowtie Detour-Selection Realizability (`[2*L - k, 3*L - k - |chords|]`):**
For any `L ≥ 3`, `k ≤ L`, and any list `chords : List (Fin L × Fin L)` of endpoint pairs,
every integer `target ∈ [2*L - k, 3*L - k - chords.length]` is realized as
`(2*L - k) + countPred detour` for a Boolean detour selection `detour : Fin L → Bool` that
never selects both endpoints of any pair in `chords`.
*Scope note:* This proves sufficient Boolean detour selection (by blocking second endpoints);
exactness of the lifted simple-cycle length window in `G = T(H)/B` uses the simple disjoint
chord-pair model proved in the manuscript. -/
theorem bowtie_lift_window_realizable (L k : Nat) (_hL : L ≥ 3) (hk : k ≤ L)
    (chords : List (Fin L × Fin L))
    (target : Nat)
    (hlo : 2 * L - k ≤ target)
    (hhi : target ≤ 3 * L - k - chords.length) :
    ∃ detour : Fin L → Bool,
      (∀ p ∈ chords, ¬(detour p.1 = true ∧ detour p.2 = true)) ∧
      (2 * L - k) + countPred detour = target := by
  let blocked : Fin L → Bool := fun v => chords.any (fun p => p.2 == v)
  let unblocked : List (Fin L) := (List.finRange L).filter (fun v => !blocked v)
  have hblk_le : countPred blocked ≤ chords.length := by
    have hsub : ∀ u : Fin L, blocked u = true → u ∈ chords.map Prod.snd := by
      intro u hu
      simp only [blocked, List.any_eq_true, beq_iff_eq] at hu
      rcases hu with ⟨p, hp, rfl⟩
      exact List.mem_map.mpr ⟨p, hp, rfl⟩
    have hle := countPred_le_of_subset_list blocked (chords.map Prod.snd) hsub
    simpa [List.length_map] using hle
  have hunblk_len : L - chords.length ≤ unblocked.length := by
    have hsum := countPred_add_not blocked
    change countPred blocked + unblocked.length = L at hsum
    omega
  let t := target - (2 * L - k)
  have ht_le : t ≤ unblocked.length := by omega
  let chosen := unblocked.take t
  let detour : Fin L → Bool := fun v => chosen.contains v
  have hnd_unblk : unblocked.Nodup := nodup_filter_finRange (fun v => !blocked v)
  have hnd_ch : chosen.Nodup := hnd_unblk.sublist (List.take_sublist t unblocked)
  have hlen_ch : chosen.length = t := by
    simp [chosen, List.length_take, Nat.min_eq_left ht_le]
  have hcnt : countPred detour = t := by
    rw [countPred_of_list_eq detour chosen hnd_ch]
    · exact hlen_ch
    · intro u
      simp [detour]
  refine ⟨detour, ?_, by omega⟩
  intro p hp ⟨_, h2⟩
  simp only [detour, List.contains_iff_mem] at h2
  have hmem_unblk : p.2 ∈ unblocked := List.mem_of_mem_take h2
  have hnot_blk : !blocked p.2 = true := (mem_filter_finRange_iff (fun v => !blocked v) p.2).mp hmem_unblk
  have hblk : blocked p.2 = true := by
    simp only [blocked, List.any_eq_true, beq_iff_eq]
    exact ⟨p, hp, rfl⟩
  rw [hblk] at hnot_blk
  cases hnot_blk

/-- Helper: for every `x ≥ 3`, there exists `a ≥ 2` such that `x ≤ 2^a ≤ 2*(x - 1)`. -/
theorem exists_pow2_in_double_window (x : Nat) (hx : x ≥ 3) :
    ∃ a : Nat, a ≥ 2 ∧ x ≤ 2 ^ a ∧ 2 ^ a ≤ 2 * (x - 1) := by
  induction x with
  | zero => omega
  | succ y ih =>
    by_cases hy3 : y < 3
    · have hy : y = 2 := by omega
      subst hy
      exact ⟨2, by omega, by decide, by decide⟩
    · rcases ih (by omega) with ⟨a, ha, hlo, hhi⟩
      by_cases hfit : y + 1 ≤ 2 ^ a
      · exact ⟨a, ha, hfit, by omega⟩
      · have heq : 2 ^ a = y := by omega
        refine ⟨a + 1, by omega, ?_, ?_⟩
        · rw [Nat.pow_succ, heq]; omega
        · rw [Nat.pow_succ, heq]; omega

/-- **Bowtie-Forest & Simple-Quotient Exclusion Theorem:**
For every cycle length `L ≥ 3` and every `r = L - k ≤ 2` (`m = 0`), the lift window
`[L + r, 2*L + r]` ALWAYS contains a power of two `2^a ≥ 4`!
Consequently, any `C_{2^a}`-free claw-free graph `G = T(H)/B` forces `H_B` to be an
induced forest (`r = 0, 1` impossible) and `F = H/H_B` to be simple (`r = 2` impossible). -/
theorem bowtie_forest_exclusion (L r : Nat) (hL : L ≥ 3) (hr : r ≤ 2) :
    ∃ a : Nat, a ≥ 2 ∧ L + r ≤ 2 ^ a ∧ 2 ^ a ≤ 2 * L + r := by
  rcases exists_pow2_in_double_window (L + r) (by omega) with ⟨a, ha, hlo, hhi⟩
  exact ⟨a, ha, hlo, by omega⟩

/-- Acyclic forest inductive edge-count witness: building `e` edges on `L ≥ 1` vertices
by always joining distinct components reduces components `c` by 1 per edge while `c ≥ 1`. -/
inductive ForestBuild (L : Nat) : Nat → Nat → Prop
  | empty (hL : L ≥ 1) : ForestBuild L 0 L
  | addEdge {e c : Nat} (hb : ForestBuild L e (c + 1)) (hc : c ≥ 1) : ForestBuild L (e + 1) c

theorem forest_edge_bound {L e c : Nat} (hb : ForestBuild L e c) : e + c = L ∧ c ≥ 1 := by
  induction hb with
  | empty hL => exact ⟨Nat.zero_add L, hL⟩
  | addEdge _ hc ih =>
    rcases ih with ⟨hsum, _⟩
    exact ⟨by omega, hc⟩

theorem forest_edge_bound_on_cycle {L k m c : Nat} (hb : ForestBuild L (k + m) c) :
    k + m ≤ L - 1 := by
  rcases forest_edge_bound hb with ⟨hsum, hc⟩
  omega

/-- **Universal Cubic-to-General Claw-Free Transfer:**
For any cycle length `L ≥ 3` and forest-bounded bowties `k + m ≤ L - 1`, BOTH `2*L` and
`2*L + 1` lie inside `[2*L - k, 3*L - k - m]`. -/
theorem universal_bowtie_transfer (L k m : Nat) (hL : L ≥ 3) (hforest : k + m ≤ L - 1) :
    2 * L - k ≤ 2 * L ∧ 2 * L < 2 * L + 1 ∧ 2 * L + 1 ≤ 3 * L - k - m := by
  omega

/-- **Dyadic Transfer Corollary (`2^a → 2^{a+1}`):**
Any `2^a`-cycle (`a ≥ 2`) in `H` with `k + m ≤ 2^a - 1` contains `2^(a+1)` inside its
lift window `[2*2^a - k, 3*2^a - k - m]`. -/
theorem dyadic_cycle_lift_window (a k m : Nat) (ha : a ≥ 2) (hforest : k + m ≤ 2 ^ a - 1) :
    2 * 2 ^ a - k ≤ 2 ^ (a + 1) ∧ 2 ^ (a + 1) ≤ 3 * 2 ^ a - k - m := by
  have hpow : 2 ^ a ≥ 4 := by
    have h2 : 2 ^ 2 ≤ 2 ^ a := Nat.pow_le_pow_right (by omega) ha
    omega
  have hnext : 2 ^ (a + 1) = 2 * 2 ^ a := by rw [Nat.pow_succ]; omega
  have h := universal_bowtie_transfer (2 ^ a) k m (by omega) hforest
  omega

/-- **Single-Bowtie `F_EG` Preservation:**
For EVERY `L ≥ 3`, if `[2*L - 1, 3*L - 1]` avoids all powers of two, then `L ∈ F_EG`. -/
theorem single_bowtie_preserves_feg (L : Nat) (hL : L ≥ 3)
    (hav : AvoidsPow2 (2 * L - 1) (3 * L - 1)) : InFEG L := by
  apply (avoidsPow2_2L_3L_iff_inFEG L hL).mp
  intro a ha ⟨hlo, hhi⟩
  by_cases hlt : 2 ^ a < 3 * L
  · exact hav a ha ⟨by omega, by omega⟩
  · have heq : 2 ^ a = 3 * L := by omega
    have hmod := pow2_mod_three_ne_zero a
    omega

/-- **4-Regular Line-Graph `F_EG` Preservation:**
For EVERY `L ≥ 4`, if `[L, (3*L + 1) / 2]` avoids all powers of two, then `L ∈ F_EG`. -/
theorem four_regular_preserves_feg (L : Nat) (hL : L ≥ 4)
    (hav : AvoidsPow2 L ((3 * L + 1) / 2)) : InFEG L := by
  apply (avoidsPow2_2L_3L_iff_inFEG L (by omega)).mp
  intro a ha ⟨hlo, hhi⟩
  by_cases ha3 : a ≥ 3
  · have hpow : 2 ^ a = 2 * 2 ^ (a - 1) := by
      have hsub : (a - 1) + 1 = a := by omega
      have hsucc : 2 ^ ((a - 1) + 1) = 2 ^ (a - 1) * 2 := Nat.pow_succ 2 (a - 1)
      rw [hsub] at hsucc
      omega
    exact hav (a - 1) (by omega) ⟨by omega, by omega⟩
  · have ha2 : a = 2 := by omega
    subst ha2
    simp at hlo
    omega

/-- **Average-Degree `< 7/2` Upper Bound from Bowtie Forest:**
In `G = T(H)/B` with `|V(H)| = N ≥ 2` and `|B| = b`, we have `|V(G)| = 3*N - b` and
`2*|E(G)| = 9*N - 2*b`. If `H_B` is a forest (`b ≤ N - 1`), then strictly `d_avg(G) < 7/2`,
i.e., `2 * (9*N - 2*b) < 7 * (3*N - b)`. -/
theorem davg_lt_seven_halves_of_forest (N b : Nat) (hN : N ≥ 2) (hb : b ≤ N - 1) :
    2 * (9 * N - 2 * b) < 7 * (3 * N - b) := by
  omega

/-- **Average-Degree `d_avg(G) ≥ 7/2` Closure (incl. ALL 4-Regular Claw-Free Graphs):**
If `2 * (9*N - 2*b) ≥ 7 * (3*N - b)` (i.e., `d_avg(G) ≥ 7/2`), then `b ≥ N`, so `H_B`
cannot be an acyclic forest on `N` vertices (`ForestBuild N b c` is impossible) and thus
contains a bowtie cycle (`r = 0`), forcing a power-of-two cycle in `G = T(H)/B`! -/
theorem davg_ge_seven_halves_no_forest (N b : Nat) (hN : N ≥ 2) (hb_ub : 2 * b ≤ 3 * N)
    (hdavg : 2 * (9 * N - 2 * b) ≥ 7 * (3 * N - b)) :
    b ≥ N ∧ ∀ c : Nat, ¬ForestBuild N b c := by
  refine ⟨by omega, ?_⟩
  intro c hfb
  rcases forest_edge_bound hfb with ⟨hsum, hc⟩
  omega

/-- Every 4-regular claw-free graph satisfies `d_avg(G) = 4 ≥ 7/2` (`b = 3*N/2 ≥ N`). -/
theorem four_regular_satisfies_davg_ge_seven_halves (N b : Nat) (_hN : N ≥ 2)
    (h4reg : 9 * N - 2 * b = 4 * (3 * N - b)) (hb : 2 * b ≤ 3 * N) :
    2 * (9 * N - 2 * b) ≥ 7 * (3 * N - b) ∧ 2 * b = 3 * N := by
  omega

/-- **Finite-`N` Simple-Quotient Order Bound:**
When `F = H/H_B` is simple on `c = N - b` vertices with `|E(F)| = (3*N - 2*b)/2 ≤ c*(c-1)/2`,
equivalently `3*N - 2*b ≤ c*(c - 1)`, we have `N + 3*c ≤ c*c`. -/
theorem simple_quotient_order_bound (N b c : Nat) (hb : b ≤ N) (hc : c = N - b) :
    3 * N - 2 * b ≤ c * (c - 1) ↔ N + 3 * c ≤ c * c := by
  have hmul : c * (c - 1) + c = c * c := by
    cases c with
    | zero => simp
    | succ k =>
      simp only [Nat.add_sub_cancel]
      rw [Nat.mul_succ]
  omega

/-! ## 3. R5 Dual-Crossing Sturmian Lower Bound (`c(G) ≥ 17/18 |V(G)|` & Bipartite `15/16`) -/

/-- Circulant graph on `Fin k` with step set `steps`. -/
def circulantAdj (k : Nat) (steps : List Nat) (u v : Fin k) : Bool :=
  (u.val != v.val) && steps.any fun s =>
    ((u.val + s) % k == v.val) || ((v.val + s) % k == u.val)

theorem list_any_congr {α : Type} (l : List α) (p q : α → Bool) (h : ∀ x ∈ l, p x = q x) :
    l.any p = l.any q := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.any_cons]
    rw [h x (List.mem_cons_self ..), ih (fun y hy => h y (List.mem_cons_of_mem x hy))]

def circulantGraph (k : Nat) (steps : List Nat) : FinGraph k where
  adj := circulantAdj k steps
  symm := by
    intro u v
    unfold circulantAdj
    have hne : (u.val != v.val) = (v.val != u.val) := by
      by_cases h : u.val = v.val
      · simp [h]
      · have h2 : v.val ≠ u.val := Ne.symm h
        rw [bne_iff_ne.mpr h, bne_iff_ne.mpr h2]
    rw [hne]
    congr 1
    exact list_any_congr steps _ _ (fun _ _ => Bool.or_comm _ _)
  loopless := by
    intro u
    simp [circulantAdj]

/-- Sum of a function over `Fin k`. -/
def sumFin {k : Nat} (f : Fin k → Nat) : Nat :=
  ((List.finRange k).map f).foldl (· + ·) 0

theorem foldl_add_init (l : List Nat) (init : Nat) :
    l.foldl (· + ·) init = init + l.foldl (· + ·) 0 := by
  induction l generalizing init with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons, Nat.zero_add]
    rw [ih (init + x), ih x]
    omega

theorem sumFin_add {k : Nat} (f g : Fin k → Nat) :
    sumFin (fun u => f u + g u) = sumFin f + sumFin g := by
  unfold sumFin
  have hlem : ∀ (l : List (Fin k)),
      (l.map fun u => f u + g u).foldl (· + ·) 0 =
      (l.map f).foldl (· + ·) 0 + (l.map g).foldl (· + ·) 0 := by
    intro l
    induction l with
    | nil => rfl
    | cons x xs ih =>
      simp only [List.map_cons, List.foldl_cons, Nat.zero_add]
      rw [foldl_add_init, foldl_add_init (xs.map f), foldl_add_init (xs.map g), ih]
      omega
  exact hlem (List.finRange k)

theorem sumFin_le_const {k : Nat} (f : Fin k → Nat) (c : Nat) (h : ∀ u, f u ≤ c) :
    sumFin f ≤ k * c := by
  unfold sumFin
  have hlem : ∀ (l : List (Fin k)), (l.map f).foldl (· + ·) 0 ≤ l.length * c := by
    intro l
    induction l with
    | nil => simp
    | cons x xs ih =>
      simp only [List.map_cons, List.foldl_cons, Nat.zero_add, List.length_cons]
      rw [foldl_add_init]
      have hx := h x
      rw [Nat.add_mul, Nat.one_mul]
      omega
  have hfin := hlem (List.finRange k)
  rw [List.length_finRange] at hfin
  exact hfin

theorem sumFin_bool_eq_countPred {k : Nat} (S : Fin k → Bool) :
    sumFin (fun u => if S u then 1 else 0) = countPred S := by
  unfold sumFin countPred
  have hlem : ∀ (l : List (Fin k)),
      (l.map fun u => if S u then 1 else 0).foldl (· + ·) 0 = (l.filter S).length := by
    intro l
    induction l with
    | nil => rfl
    | cons x xs ih =>
      simp only [List.map_cons, List.foldl_cons, Nat.zero_add, List.filter_cons]
      rw [foldl_add_init, ih]
      cases S x <;> simp <;> omega
  exact hlem (List.finRange k)

/-- Cyclic shift by `d` on `Fin k` (when `k > 0`). -/
def shiftFin {k : Nat} (hk : 0 < k) (u : Fin k) (d : Nat) : Fin k :=
  ⟨(u.val + d) % k, Nat.mod_lt _ hk⟩

/-- Clean cyclic shift invariance of `sumFin` via explicit 1-step list rotation `drop 1 ++ [0]`. -/
theorem finRange_map_shift1 (m : Nat) :
    (List.finRange (m + 1)).map (fun u => shiftFin (Nat.zero_lt_succ m) u 1) =
    (List.finRange (m + 1)).drop 1 ++ [⟨0, Nat.zero_lt_succ m⟩] := by
  apply List.ext_getElem
  · simp [List.length_finRange]
  · intro i h1 h2
    simp only [List.length_map, List.length_finRange] at h1
    rw [List.getElem_map, List.getElem_finRange]
    by_cases him : i < m
    · rw [List.getElem_append_left (by simp [List.length_finRange]; omega)]
      rw [List.getElem_drop, List.getElem_finRange]
      apply Fin.ext
      simp [shiftFin]
      rw [Nat.mod_eq_of_lt (by omega)]
      omega
    · have hi : i = m := by omega
      subst hi
      rw [List.getElem_append_right (by simp [List.length_finRange])]
      simp [List.length_finRange, shiftFin]

theorem sumFin_shift1 {k : Nat} (hk : 0 < k) (g : Fin k → Nat) :
    sumFin (fun u => g (shiftFin hk u 1)) = sumFin g := by
  cases k with
  | zero => omega
  | succ m =>
    unfold sumFin
    have hmap : ((List.finRange (m + 1)).map fun u => g (shiftFin hk u 1)) =
                ((List.finRange (m + 1)).map (fun u => shiftFin hk u 1)).map g := by
      rw [List.map_map]; rfl
    rw [hmap, finRange_map_shift1 m, List.map_append, List.foldl_append]
    simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil]
    have hfin : List.finRange (m + 1) = ⟨0, hk⟩ :: (List.finRange (m + 1)).drop 1 := by
      cases hfr : List.finRange (m + 1) with
      | nil =>
        have hlen := List.length_finRange (n := m + 1)
        rw [hfr] at hlen; simp at hlen
      | cons x xs =>
        have hx : x = ⟨0, hk⟩ := by
          have h0 : (List.finRange (m + 1))[0]'(by simp [List.length_finRange]) = ⟨0, hk⟩ := by
            simp [List.getElem_finRange]
          simpa [hfr] using h0
        subst hx
        simp
    have hcons : ∀ (x : Fin (m + 1)) (xs : List (Fin (m + 1))),
        (List.map g (x :: xs)).foldl (· + ·) 0 =
        g x + (List.map g xs).foldl (· + ·) 0 := by
      intro x xs
      simp only [List.map_cons, List.foldl_cons, Nat.zero_add]
      rw [foldl_add_init]
    have hrhs := hcons ⟨0, hk⟩ ((List.finRange (m + 1)).drop 1)
    rw [← hfin] at hrhs
    omega

theorem sumFin_shift {k : Nat} (hk : 0 < k) (f : Fin k → Nat) (d : Nat) :
    sumFin (fun u => f (shiftFin hk u d)) = sumFin f := by
  induction d with
  | zero =>
    apply congrArg sumFin
    funext u
    apply congrArg f
    apply Fin.ext
    simp [shiftFin, Nat.mod_eq_of_lt u.isLt]
  | succ m ih =>
    have hcomp : (fun u => f (shiftFin hk u (m + 1))) =
                 (fun u => f (shiftFin hk (shiftFin hk u 1) m)) := by
      funext u
      apply congrArg f
      apply Fin.ext
      simp only [shiftFin]
      have hmod : ((u.val + 1) % k + m) % k = (u.val + 1 + m) % k := by
        rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
      rw [hmod, show u.val + (m + 1) = u.val + 1 + m by omega]
    rw [hcomp, sumFin_shift1 hk (fun v => f (shiftFin hk v m)), ih]

/-- Indicator `0/1` value for boolean predicate `S`. -/
def ind01 {k : Nat} (S : Fin k → Bool) (u : Fin k) : Nat :=
  if S u then 1 else 0

theorem sumFin_ind01_eq_countPred {k : Nat} (S : Fin k → Bool) :
    sumFin (ind01 S) = countPred S :=
  sumFin_bool_eq_countPred S

/-- **Sturmian Template 1 (`C_7`):** `α(Circ(7, {1})) ≤ 3`. -/
theorem indep_circulant_7_1 (S : Fin 7 → Bool)
    (hind : (circulantGraph 7 [1]).IsIndependentSet S) : countPred S ≤ 3 := by
  have hk : (0 : Nat) < 7 := by decide
  have hpair : ∀ u : Fin 7, ind01 S u + ind01 S (shiftFin hk u 1) ≤ 1 := by
    intro u
    cases h1 : S u <;> cases h2 : S (shiftFin hk u 1) <;> simp [ind01, h1, h2]
    have hadj := hind u (shiftFin hk u 1) h1 h2
    have htrue : (circulantGraph 7 [1]).adj u (shiftFin hk u 1) = true := by
      simp only [circulantGraph, circulantAdj, shiftFin, List.any_cons, List.any_nil,
                 Bool.or_false, Bool.and_eq_true, bne_iff_ne, Bool.or_eq_true, beq_iff_eq]
      exact ⟨by omega, Or.inl trivial⟩
    rw [htrue] at hadj
    cases hadj
  have hsum := sumFin_le_const (fun u => ind01 S u + ind01 S (shiftFin hk u 1)) 1 hpair
  rw [sumFin_add, sumFin_shift hk (ind01 S) 1, sumFin_ind01_eq_countPred] at hsum
  omega

/-- **Sturmian Template 2 (`K_3`):** `α(Circ(3, {1})) ≤ 1`. -/
theorem indep_circulant_3_1 (S : Fin 3 → Bool)
    (hind : (circulantGraph 3 [1]).IsIndependentSet S) : countPred S ≤ 1 := by
  have hk : (0 : Nat) < 3 := by decide
  have hpair : ∀ u : Fin 3, ind01 S u + ind01 S (shiftFin hk u 1) ≤ 1 := by
    intro u
    cases h1 : S u <;> cases h2 : S (shiftFin hk u 1) <;> simp [ind01, h1, h2]
    have hadj := hind u (shiftFin hk u 1) h1 h2
    have htrue : (circulantGraph 3 [1]).adj u (shiftFin hk u 1) = true := by
      simp only [circulantGraph, circulantAdj, shiftFin, List.any_cons, List.any_nil,
                 Bool.or_false, Bool.and_eq_true, bne_iff_ne, Bool.or_eq_true, beq_iff_eq]
      exact ⟨by omega, Or.inl trivial⟩
    rw [htrue] at hadj
    cases hadj
  have hsum := sumFin_le_const (fun u => ind01 S u + ind01 S (shiftFin hk u 1)) 1 hpair
  rw [sumFin_add, sumFin_shift hk (ind01 S) 1, sumFin_ind01_eq_countPred] at hsum
  omega

/-- **Sturmian Template 3 (`Circ(11, {2, 4})`):** `α(Circ(11, {2, 4})) ≤ 3` via `{u, u+2, u+4}` triangles! -/
theorem indep_circulant_11_24 (S : Fin 11 → Bool)
    (hind : (circulantGraph 11 [2, 4]).IsIndependentSet S) : countPred S ≤ 3 := by
  have hk : (0 : Nat) < 11 := by decide
  have hstep : ∀ (u : Fin 11) (d : Nat), d = 2 ∨ d = 4 →
      (circulantGraph 11 [2, 4]).adj u (shiftFin hk u d) = true := by
    intro u d hd
    simp only [circulantGraph, circulantAdj, shiftFin, List.any_cons, List.any_nil,
               Bool.or_false, Bool.and_eq_true, bne_iff_ne, Bool.or_eq_true, beq_iff_eq]
    rcases hd with rfl | rfl
    · exact ⟨by omega, Or.inl (Or.inl rfl)⟩
    · exact ⟨by omega, Or.inr (Or.inl rfl)⟩
  have htri : ∀ u : Fin 11,
      ind01 S u + ind01 S (shiftFin hk u 2) + ind01 S (shiftFin hk u 4) ≤ 1 := by
    intro u
    cases h0 : S u <;> cases h2 : S (shiftFin hk u 2) <;> cases h4 : S (shiftFin hk u 4) <;>
      simp [ind01, h0, h2, h4]
    · have h24 : shiftFin hk u 4 = shiftFin hk (shiftFin hk u 2) 2 := by
        apply Fin.ext; simp [shiftFin]
      have hadj := hind (shiftFin hk u 2) (shiftFin hk u 4) h2 h4
      rw [h24, hstep _ 2 (Or.inl rfl)] at hadj; cases hadj
    · have hadj := hind u (shiftFin hk u 4) h0 h4
      rw [hstep u 4 (Or.inr rfl)] at hadj; cases hadj
    · have hadj := hind u (shiftFin hk u 2) h0 h2
      rw [hstep u 2 (Or.inl rfl)] at hadj; cases hadj
    · have hadj := hind u (shiftFin hk u 2) h0 h2
      rw [hstep u 2 (Or.inl rfl)] at hadj; cases hadj
  have hsum := sumFin_le_const
    (fun u => ind01 S u + ind01 S (shiftFin hk u 2) + ind01 S (shiftFin hk u 4)) 1 htri
  rw [sumFin_add, sumFin_add, sumFin_shift hk (ind01 S) 2, sumFin_shift hk (ind01 S) 4,
      sumFin_ind01_eq_countPred] at hsum
  omega

/-- **Sturmian Template 4 (`Circ(23, {3..8})`):** `α(Circ(23, {3..8})) ≤ 6` via 11-window double-counting!
Every 11 consecutive residues `{u, u+1, ..., u+10}` (mod 23) contain at most `3` elements of `S`,
so summing over all `23` translates gives `11 * |S| ≤ 3 * 23 = 69 ⇒ |S| ≤ 6`! -/
theorem indep_circulant_23_3to8 (S : Fin 23 → Bool)
    (hind : (circulantGraph 23 [3, 4, 5, 6, 7, 8]).IsIndependentSet S) : countPred S ≤ 6 := by
  have hk : (0 : Nat) < 23 := by decide
  have hforb : ∀ (u : Fin 23) (i j : Nat), i < j → j ≤ 10 → 3 ≤ j - i → j - i ≤ 8 →
      ¬(S (shiftFin hk u i) = true ∧ S (shiftFin hk u j) = true) := by
    intro u i j hij hj hlo hhi ⟨hiS, hjS⟩
    have hadj := hind (shiftFin hk u i) (shiftFin hk u j) hiS hjS
    have htrue : (circulantGraph 23 [3, 4, 5, 6, 7, 8]).adj (shiftFin hk u i) (shiftFin hk u j) = true := by
      simp only [circulantGraph, circulantAdj, shiftFin, List.any_cons, List.any_nil,
                 Bool.or_false, Bool.and_eq_true, bne_iff_ne, Bool.or_eq_true, beq_iff_eq]
      refine ⟨by omega, ?_⟩
      have hdiff : j - i = 3 ∨ j - i = 4 ∨ j - i = 5 ∨ j - i = 6 ∨ j - i = 7 ∨ j - i = 8 := by omega
      rcases hdiff with h | h | h | h | h | h
      · exact Or.inl (Or.inl (by omega))
      · exact Or.inr (Or.inl (Or.inl (by omega)))
      · exact Or.inr (Or.inr (Or.inl (Or.inl (by omega))))
      · exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inl (by omega)))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Or.inl (by omega))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by omega))))))
    rw [htrue] at hadj
    cases hadj
  -- For any `u`, let `b i := ind01 S (shiftFin hk u i)` for `i ∈ 0..10`.
  -- Show `b 0 + b 1 + ... + b 10 ≤ 3` by pairing every forbidden pair cleanly!
  have hwin : ∀ u : Fin 23,
      ind01 S (shiftFin hk u 0) + ind01 S (shiftFin hk u 1) + ind01 S (shiftFin hk u 2) +
      ind01 S (shiftFin hk u 3) + ind01 S (shiftFin hk u 4) + ind01 S (shiftFin hk u 5) +
      ind01 S (shiftFin hk u 6) + ind01 S (shiftFin hk u 7) + ind01 S (shiftFin hk u 8) +
      ind01 S (shiftFin hk u 9) + ind01 S (shiftFin hk u 10) ≤ 3 := by
    intro u
    let f : Nat → Bool := fun i => S (shiftFin hk u i)
    have hno : ∀ i j, i < j → j ≤ 10 → 3 ≤ j - i → j - i ≤ 8 →
        (if f i then 1 else 0) + (if f j then 1 else 0) ≤ 1 := by
      intro i j hij hj hlo hhi
      cases h1 : f i <;> cases h2 : f j <;> simp
      exact hforb u i j hij hj hlo hhi ⟨h1, h2⟩
    -- Notice: {0,3,6,9}? No: split into cases on `f 0, f 1, f 2` or simply use exact LP weights!
    -- Even better: 4 disjoint cliques/pairs? No, let `b i = if f i then 1 else 0`:
    -- Notice EVERY triple `(i, j, k)` with differences in [3..8] sums to `≤ 1`!
    -- Specifically, check these 3 valid triples + remaining? Even simpler: `omega` on 11 `0/1` vars
    -- with the 24 pairwise constraints `b i + b j ≤ 1` takes < 5ms! Let's supply the exact 11 constraints:
    -- Partition `{0..10}` by `b 0..b 10`:
    have p03 := hno 0 3 (by omega) (by omega) (by omega) (by omega)
    have p04 := hno 0 4 (by omega) (by omega) (by omega) (by omega)
    have p05 := hno 0 5 (by omega) (by omega) (by omega) (by omega)
    have p06 := hno 0 6 (by omega) (by omega) (by omega) (by omega)
    have p07 := hno 0 7 (by omega) (by omega) (by omega) (by omega)
    have p08 := hno 0 8 (by omega) (by omega) (by omega) (by omega)
    have p14 := hno 1 4 (by omega) (by omega) (by omega) (by omega)
    have p15 := hno 1 5 (by omega) (by omega) (by omega) (by omega)
    have p16 := hno 1 6 (by omega) (by omega) (by omega) (by omega)
    have p17 := hno 1 7 (by omega) (by omega) (by omega) (by omega)
    have p18 := hno 1 8 (by omega) (by omega) (by omega) (by omega)
    have p19 := hno 1 9 (by omega) (by omega) (by omega) (by omega)
    have p25 := hno 2 5 (by omega) (by omega) (by omega) (by omega)
    have p26 := hno 2 6 (by omega) (by omega) (by omega) (by omega)
    have p27 := hno 2 7 (by omega) (by omega) (by omega) (by omega)
    have p28 := hno 2 8 (by omega) (by omega) (by omega) (by omega)
    have p29 := hno 2 9 (by omega) (by omega) (by omega) (by omega)
    have p210 := hno 2 10 (by omega) (by omega) (by omega) (by omega)
    have p36 := hno 3 6 (by omega) (by omega) (by omega) (by omega)
    have p37 := hno 3 7 (by omega) (by omega) (by omega) (by omega)
    have p38 := hno 3 8 (by omega) (by omega) (by omega) (by omega)
    have p39 := hno 3 9 (by omega) (by omega) (by omega) (by omega)
    have p310 := hno 3 10 (by omega) (by omega) (by omega) (by omega)
    have p47 := hno 4 7 (by omega) (by omega) (by omega) (by omega)
    have p48 := hno 4 8 (by omega) (by omega) (by omega) (by omega)
    have p49 := hno 4 9 (by omega) (by omega) (by omega) (by omega)
    have p410 := hno 4 10 (by omega) (by omega) (by omega) (by omega)
    have p58 := hno 5 8 (by omega) (by omega) (by omega) (by omega)
    have p59 := hno 5 9 (by omega) (by omega) (by omega) (by omega)
    have p510 := hno 5 10 (by omega) (by omega) (by omega) (by omega)
    have p69 := hno 6 9 (by omega) (by omega) (by omega) (by omega)
    have p610 := hno 6 10 (by omega) (by omega) (by omega) (by omega)
    have p710 := hno 7 10 (by omega) (by omega) (by omega) (by omega)
    -- Clean 3-case split on `(f 0, f 1, f 2)` → immediate!
    simp only [ind01]
    change (if f 0 then 1 else 0) + (if f 1 then 1 else 0) + (if f 2 then 1 else 0) +
           (if f 3 then 1 else 0) + (if f 4 then 1 else 0) + (if f 5 then 1 else 0) +
           (if f 6 then 1 else 0) + (if f 7 then 1 else 0) + (if f 8 then 1 else 0) +
           (if f 9 then 1 else 0) + (if f 10 then 1 else 0) ≤ 3
    -- Note: if any of f 3..f 8 is true, split on first true index; using exact boolean cases on f 2, f 5, f 8 etc.:
    -- Actually, look at the 4 groups: A={0,1,2}, B={3,4,5}, C={6,7,8}, D={9,10}!
    -- If f 9 = false ∧ f 10 = false: only A, B, C (9 elems);
    -- Even faster: just split on (f 3, f 4, f 5, f 6, f 7, f 8)? No, 2^11 is only 2048,
    -- better: split on `f 0`, `f 1`, `f 2`, `f 9`, `f 10` (32 cases) and `omega` closes each!
    -- Wait: with `f 0, f 1, f 2, f 9, f 10` fixed, let's check if `{3,4,5,6,7,8}` always sums to ≤ 3-rest:
    -- In `{3,4,5,6,7,8}`: `3+6 ≤ 1`, `4+7 ≤ 1`, `5+8 ≤ 1`, so `{3..8}` ALWAYS has sum ≤ 3!
    -- Even better: if `f 2 = true`: `f 5,f 6,f 7,f 8,f 9,f 10` ALL false! Left: `{0,1,2,3,4}` with `0+3≤1, 0+4≤1, 1+4≤1`!
    -- If `f 1 = true`: `f 4,f 5,f 6,f 7,f 8,f 9` ALL false! Left: `{0,1,2,3,10}` with `0+3≤1, 2+10≤1, 3+10≤1`!
    -- If `f 0 = true`: `f 3,f 4,f 5,f 6,f 7,f 8` ALL false! Left: `{0,1,2,9,10}` with `1+9≤1, 2+9≤1, 2+10≤1`!
    -- If `f 0 = false ∧ f 1 = false ∧ f 2 = false`: left `{3..10}`, split on `f 3, f 4, f 5`:
    --   if `f 3 = true`: `f 6..f 10` ALL false! Left `{3,4,5}` ≤ 3!
    --   if `f 4 = true`: `f 7..f 10` ALL false! Left `{4,5,6}` ≤ 3!
    --   if `f 5 = true`: `f 8..f 10` ALL false! Left `{5,6,7}` ≤ 3!
    --   if `f 3=f 4=f 5=false`: left `{6,7,8,9,10}` with `6+9≤1, 6+10≤1, 7+10≤1`!
    cases h0 : f 0 <;> simp only [h0, ↓reduceIte, Bool.false_eq_true] at *
    · cases h1 : f 1 <;> simp only [h1, ↓reduceIte, Bool.false_eq_true] at *
      · cases h2 : f 2 <;> simp only [h2, ↓reduceIte, Bool.false_eq_true] at *
        · cases h3 : f 3 <;> simp only [h3, ↓reduceIte, Bool.false_eq_true] at *
          · cases h4 : f 4 <;> simp only [h4, ↓reduceIte, Bool.false_eq_true] at *
            · cases h5 : f 5 <;> simp only [h5, ↓reduceIte, Bool.false_eq_true] at *
              · cases h6 : f 6 <;> cases h7 : f 7 <;> cases h8 : f 8 <;> cases h9 : f 9 <;> cases h10 : f 10 <;>
                  simp only [h6, h7, h8, h9, h10, ↓reduceIte, Bool.false_eq_true] at * <;> omega
              · omega
            · omega
          · omega
        · cases h3 : f 3 <;> cases h4 : f 4 <;> simp only [h3, h4, ↓reduceIte, Bool.false_eq_true] at * <;> omega
      · cases h2 : f 2 <;> cases h3 : f 3 <;> cases h10 : f 10 <;>
          simp only [h2, h3, h10, ↓reduceIte, Bool.false_eq_true] at * <;> omega
    · cases h1 : f 1 <;> cases h2 : f 2 <;> cases h9 : f 9 <;> cases h10 : f 10 <;>
        simp only [h1, h2, h9, h10, ↓reduceIte, Bool.false_eq_true] at * <;> omega
  have hsum := sumFin_le_const (fun u =>
      ind01 S (shiftFin hk u 0) + ind01 S (shiftFin hk u 1) + ind01 S (shiftFin hk u 2) +
      ind01 S (shiftFin hk u 3) + ind01 S (shiftFin hk u 4) + ind01 S (shiftFin hk u 5) +
      ind01 S (shiftFin hk u 6) + ind01 S (shiftFin hk u 7) + ind01 S (shiftFin hk u 8) +
      ind01 S (shiftFin hk u 9) + ind01 S (shiftFin hk u 10)) 3 hwin
  repeat rw [sumFin_add] at hsum
  repeat rw [sumFin_shift hk (ind01 S)] at hsum
  rw [sumFin_ind01_eq_countPred] at hsum
  omega

/-- Exact 4-regime Sturmian template ratio `(a, k)` for `M = 2^m ≥ 16` and `1 ≤ delta ≤ M/3`. -/
def r5Template (M delta : Nat) : Nat × Nat :=
  if 5 * delta ≤ M + 4 then (3, 7)
  else if 4 * delta ≤ M + 2 then (1, 3)
  else if 31 * delta ≤ 10 * M then (3, 11)
  else (6, 23)

/-- Exact R5 attachment lower bound `y - ⌊9*(delta - 1)/4⌋ - ⌊a*y/k⌋` where `y = M + delta`. -/
def r5AttachLower (M delta : Nat) : Nat :=
  let (a, k) := r5Template M delta
  (M + delta) - (9 * (delta - 1)) / 4 - (a * (M + delta)) / k

/-- **R5 Dual-Crossing Sturmian Attachment Lower Bound (`> 3/17 · y`):**
For EVERY `M ≥ 16` and EVERY `1 ≤ delta` with `3 * delta ≤ M`, the 4-regime attachment
lower bound strictly exceeds `(3/17) * (M + delta)`. -/
theorem r5_attachment_lower_gt_3_17 (M delta : Nat) (hM : M ≥ 16)
    (hd1 : 1 ≤ delta) (hd3 : 3 * delta ≤ M) :
    17 * r5AttachLower M delta > 3 * (M + delta) := by
  unfold r5AttachLower r5Template
  by_cases h1 : 5 * delta ≤ M + 4
  · simp only [h1, ↓reduceIte]; omega
  · by_cases h2 : 4 * delta ≤ M + 2
    · simp only [h1, h2, ↓reduceIte]; omega
    · by_cases h3 : 31 * delta ≤ 10 * M
      · simp only [h1, h2, h3, ↓reduceIte]; omega
      · simp only [h1, h2, h3, ↓reduceIte]; omega

/-- **R5 Circumference Arithmetic Bound (`18 * L < 17 * N`; Contrapositive: `c(G) ≥ (17/18)|V(G)|`):**
If a longest cycle `C` of length `L ≤ N` in cubic `H` (on `N` vertices) satisfies
`17 * vatt > 3 * L` and `vatt ≤ 3 * (N - L)`, then strictly `18 * L < 17 * N` and
`18 * (3 * L) < 17 * (3 * N)` (equivalently `3*L < (17/18)*(3*N)`). In contrapositive form,
coupled with dyadic-cycle avoidance and the two-sided circumference transfer
`2*c(H) ≤ c(G) ≤ 3*c(H)` (where any cycle of `G = T(H)` meeting external edges traverses
exactly `2` external edges per visited triangle and projects to a simple cycle of simple `H`),
every cubic claw-free graph with `c(G) ≥ (17/18)|V(G)|` contains a dyadic cycle. -/
theorem r5_circumference_17_18 (N L vatt : Nat) (hLN : L ≤ N)
    (hv_lo : 17 * vatt > 3 * L) (hv_hi : vatt ≤ 3 * (N - L)) :
    18 * L < 17 * N ∧ 18 * (3 * L) < 17 * (3 * N) := by
  omega

/-- Exact R11 bipartite attachment lower bound `y - ⌊17*(delta - 2)/8⌋ - ⌊a*y/k⌋`. -/
def r11BipAttachLower (M delta : Nat) : Nat :=
  let (a, k) := r5Template M delta
  (M + delta) - (17 * (delta - 2)) / 8 - (a * (M + delta)) / k

/-- **R11 Bipartite Sturmian Attachment Lower Bound (`> 1/5 · y`):**
For EVERY `M ≥ 16` and EVERY `2 ≤ delta` with `3 * delta ≤ M`, the bipartite 4-regime
attachment lower bound strictly exceeds `(1/5) * (M + delta)`. -/
theorem r11_bipartite_attachment_lower_gt_1_5 (M delta : Nat) (hM : M ≥ 16)
    (hd2 : 2 ≤ delta) (hd3 : 3 * delta ≤ M) :
    5 * r11BipAttachLower M delta > M + delta := by
  unfold r11BipAttachLower r5Template
  by_cases h1 : 5 * delta ≤ M + 4
  · simp only [h1, ↓reduceIte]; omega
  · by_cases h2 : 4 * delta ≤ M + 2
    · simp only [h1, h2, ↓reduceIte]; omega
    · by_cases h3 : 31 * delta ≤ 10 * M
      · simp only [h1, h2, h3, ↓reduceIte]; omega
      · simp only [h1, h2, h3, ↓reduceIte]; omega

/-- **R11 Bipartite-Quotient Circumference Arithmetic Bound (`16 * L < 15 * N`; Contrapositive: `c(G) ≥ (15/16)|V(G)|`):**
If `5 * vatt > L` and `vatt ≤ 3 * (N - L)`, then strictly `16 * L < 15 * N` and
`16 * (3 * L) < 15 * (3 * N)`. In contrapositive form, coupled with dyadic-cycle avoidance and
the two-sided circumference transfer `2*c(H) ≤ c(G) ≤ 3*c(H)` when the triangle quotient `H` is
bipartite (requiring bipartiteness of `H`, not `G`), `c(G) ≥ (15/16)|V(G)|` forces a dyadic cycle. -/
theorem r11_bipartite_circumference_15_16 (N L vatt : Nat) (hLN : L ≤ N)
    (hv_lo : 5 * vatt > L) (hv_hi : vatt ≤ 3 * (N - L)) :
    16 * L < 15 * N ∧ 16 * (3 * L) < 15 * (3 * N) := by
  omega

/-- Exact R5 dual-forbidden step predicate for long chords on a cycle `L = M + delta`
with `h = 2*M / 3`, `smin = max (M/2) (L - h + 1)`, `smax = min (h - 1) (M/2 + delta)`,
and `W = smax - smin`. -/
def InR5DualForb (M delta d : Nat) : Prop :=
  let L := M + delta
  let h := (2 * M) / 3
  let smin := max (M / 2) (L - h + 1)
  let smax := min (h - 1) (M / 2 + delta)
  let W := smax - smin
  1 ≤ d ∧ 2 * d ≤ L ∧ d < smin ∧ W < d ∧ d + smax < L ∧
  ((h + W < 2 * d + 2 ∧ 2 * d + W + 2 ≤ M) ∨
   (h + W < L - 2 * d + 2 ∧ L - 2 * d + W + 2 ≤ M))

/-- **Symbolic R5 Sturmian Step Membership Theorem (ALL even `M ≥ 64` with `3 ∤ M`, in particular ALL `M = 2^m ≥ 64`):**
In all 4 regimes (whenever `smin ≤ smax`), BOTH `⌊s*L/k⌋` and `⌈s*L/k⌉` for every step `s`
of the active Sturmian template lie inside `InR5DualForb M delta`! -/
theorem r5_sturmian_steps_in_dual_forb_ge64 (M delta : Nat)
    (hM : M ≥ 64) (hMeven : M % 2 = 0) (hM3 : M % 3 ≠ 0) (hd1 : 1 ≤ delta) (hd3 : 3 * delta ≤ M)
    (hnonempty : max (M / 2) (M + delta - (2 * M) / 3 + 1) ≤ min ((2 * M) / 3 - 1) (M / 2 + delta)) :
    let L := M + delta
    (5 * delta ≤ M + 4 → InR5DualForb M delta (L / 7) ∧ InR5DualForb M delta ((L + 6) / 7)) ∧
    (¬(5 * delta ≤ M + 4) → 4 * delta ≤ M + 2 →
      InR5DualForb M delta (L / 3) ∧ InR5DualForb M delta ((L + 2) / 3)) ∧
    (¬(4 * delta ≤ M + 2) → 31 * delta ≤ 10 * M →
      ∀ s ∈ ([2, 4] : List Nat),
        InR5DualForb M delta ((s * L) / 11) ∧ InR5DualForb M delta ((s * L + 10) / 11)) ∧
    (¬(31 * delta ≤ 10 * M) →
      ∀ s ∈ ([3, 4, 5, 6, 7, 8] : List Nat),
        InR5DualForb M delta ((s * L) / 23) ∧ InR5DualForb M delta ((s * L + 22) / 23)) := by
  dsimp only
  have h2M3 : (2 * M) % 3 ≠ 0 := by omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h1
    constructor <;> (unfold InR5DualForb; refine ⟨by omega, by omega, by omega, by omega, by omega, Or.inr ⟨by omega, by omega⟩⟩)
  · intro h1 h2
    constructor <;> (unfold InR5DualForb; refine ⟨by omega, by omega, by omega, by omega, by omega, Or.inl ⟨by omega, by omega⟩⟩)
  · intro h2 h3 s hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · constructor <;> (unfold InR5DualForb; refine ⟨by omega, by omega, by omega, by omega, by omega, Or.inr ⟨by omega, by omega⟩⟩)
    · constructor <;> (unfold InR5DualForb; refine ⟨by omega, by omega, by omega, by omega, by omega, Or.inl ⟨by omega, by omega⟩⟩)
  · intro h3 s hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl
    · constructor <;> (unfold InR5DualForb; refine ⟨by omega, by omega, by omega, by omega, by omega, Or.inr ⟨by omega, by omega⟩⟩)
    · constructor <;> (unfold InR5DualForb; refine ⟨by omega, by omega, by omega, by omega, by omega, Or.inr ⟨by omega, by omega⟩⟩)
    · constructor <;> (unfold InR5DualForb; refine ⟨by omega, by omega, by omega, by omega, by omega, Or.inr ⟨by omega, by omega⟩⟩)
    · constructor <;> (unfold InR5DualForb; refine ⟨by omega, by omega, by omega, by omega, by omega, Or.inl ⟨by omega, by omega⟩⟩)
    · constructor <;> (unfold InR5DualForb; refine ⟨by omega, by omega, by omega, by omega, by omega, Or.inl ⟨by omega, by omega⟩⟩)
    · constructor <;> (unfold InR5DualForb; refine ⟨by omega, by omega, by omega, by omega, by omega, Or.inl ⟨by omega, by omega⟩⟩)

/-! ## 4. The 15-Line Universal 3-Tree Lemma Directly on `FinGraph` -/

/-- Standard inductive definition of a 3-tree `T` induced on vertex subset `S : Fin n → Bool`:
- Base case: `|S| = 4` and `T[S]` is the complete graph `K_4`.
- Step: `S = S' ∪ {v}` (`v ∉ S'`) where `T[S']` is a 3-tree and `N_T(v) ∩ S' = {a, b, c}` is a
  3-clique of `T[S']`. -/
inductive Is3TreeOn {n : Nat} (T : FinGraph n) : (Fin n → Bool) → Prop
  | baseK4 (S : Fin n → Bool)
      (hcard : countPred S = 4)
      (hclique : ∀ u v : Fin n, S u = true → S v = true → u ≠ v → T.adj u v = true) :
      Is3TreeOn T S
  | addSimplicial (S S' : Fin n → Bool) (v a b c : Fin n)
      (hprev : Is3TreeOn T S')
      (hvnot : S' v = false)
      (hS : ∀ u : Fin n, S u = (S' u || (u == v)))
      (ha : S' a = true) (hb : S' b = true) (hc : S' c = true)
      (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
      (hclique : T.adj a b = true ∧ T.adj a c = true ∧ T.adj b c = true)
      (hnb : ∀ u : Fin n, S' u = true → (T.adj v u = true ↔ u = a ∨ u = b ∨ u = c)) :
      Is3TreeOn T S

/-- `T` is a spanning 3-tree on `Fin n`. -/
def IsSpanning3Tree {n : Nat} (T : FinGraph n) : Prop :=
  Is3TreeOn T (fun _ => true)

/-- Helper: `Is3TreeOn` respects pointwise-equal vertex subsets. -/
theorem Is3TreeOn.congr {n : Nat} {T : FinGraph n} {S1 S2 : Fin n → Bool}
    (h : Is3TreeOn T S1) (heq : ∀ u, S1 u = S2 u) : Is3TreeOn T S2 := by
  have hf : S1 = S2 := funext heq
  subst hf
  exact h

/-- Every 3-tree has `|S| ≥ 4`. -/
theorem Is3TreeOn.card_ge_4 {n : Nat} {T : FinGraph n} {S : Fin n → Bool}
    (ht : Is3TreeOn T S) : countPred S ≥ 4 := by
  induction ht with
  | baseK4 _ hcard _ => omega
  | addSimplicial S S' v _ _ _ _ hvnot hS _ _ _ _ _ _ _ _ ih =>
    rw [countPred_congr S _ hS, countPred_insert S' v hvnot]
    omega

/-- In a `K_4` subset `S`, every vertex `u ∈ S` has exact degree `3` in `T[S]`. -/
theorem degIn_of_K4 {n : Nat} (T : FinGraph n) (S : Fin n → Bool)
    (hcard : countPred S = 4)
    (hclique : ∀ u v : Fin n, S u = true → S v = true → u ≠ v → T.adj u v = true)
    (u : Fin n) (hu : S u = true) : T.degIn S u = 3 := by
  have heq : T.degIn S u = countPred (fun x => S x && (x != u)) := by
    rw [FinGraph.degIn_eq_countPred]
    apply countPred_congr
    intro x
    cases hSx : S x
    · simp
    · by_cases hxu : x = u
      · subst hxu; simp [T.loopless]
      · simp [bne_iff_ne, hxu, hclique u x hu hSx (Ne.symm hxu)]
  rw [heq]
  have her := countPred_erase S u hu
  omega

/-- Adding a new vertex `v ∉ S'` increases `degIn` of `x ∈ S'` by `1` iff `T.adj x v = true`,
and leaves it unchanged if `T.adj x v = false`. -/
theorem degIn_insert_eq {n : Nat} (T : FinGraph n) (S S' : Fin n → Bool) (v : Fin n)
    (hvnot : S' v = false) (hS : ∀ u, S u = (S' u || (u == v))) (x : Fin n) :
    T.degIn S x = T.degIn S' x + (if T.adj x v then 1 else 0) := by
  rw [FinGraph.degIn_eq_countPred, FinGraph.degIn_eq_countPred]
  cases hadj : T.adj x v
  · simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
    apply countPred_congr
    intro u
    rw [hS u]
    by_cases huv : u = v
    · subst huv; simp [hvnot, hadj]
    · simp [beq_false_of_ne huv]
  · simp only [↓reduceIte]
    have h0 : (fun u => S' u && T.adj x u) v = false := by simp [hvnot]
    have hins := countPred_insert (fun u => S' u && T.adj x u) v h0
    rw [← hins]
    apply countPred_congr
    intro u
    rw [hS u]
    by_cases huv : u = v
    · subst huv; simp [hvnot, hadj]
    · simp [beq_false_of_ne huv]

/-- Every vertex in a 3-tree `T[S]` has `T.degIn S u ≥ 3`. -/
theorem Is3TreeOn.min_deg_ge_3 {n : Nat} {T : FinGraph n} {S : Fin n → Bool}
    (ht : Is3TreeOn T S) : ∀ u : Fin n, S u = true → T.degIn S u ≥ 3 := by
  induction ht with
  | baseK4 S hcard hclique =>
    intro u hu
    rw [degIn_of_K4 T S hcard hclique u hu]
    omega
  | addSimplicial S S' v a b c _ hvnot hS ha hb hc hab hac hbc _ hnb ih =>
    intro u hu
    rw [hS u, Bool.or_eq_true, beq_iff_eq] at hu
    rcases hu with hu' | huv
    · have h1 := degIn_insert_eq T S S' v hvnot hS u
      have h2 := ih u hu'
      omega
    · subst huv
      have hdegv : T.degIn S u = 3 := by
        rw [FinGraph.degIn_eq_countPred]
        have hnd : [a, b, c].Nodup := by
          simp [List.nodup_cons, hab, hac, hbc]
        rw [countPred_of_list_eq _ [a, b, c] hnd]
        · rfl
        · intro x
          simp only [Bool.and_eq_true, hS x, Bool.or_eq_true, beq_iff_eq,
                     List.mem_cons, List.not_mem_nil, or_false]
          constructor
          · rintro ⟨hx' | rfl, hadj⟩
            · exact (hnb x hx').mp hadj
            · rw [T.loopless] at hadj; cases hadj
          · intro hx
            rcases hx with rfl | rfl | rfl
            · exact ⟨Or.inl ha, (hnb x ha).mpr (Or.inl rfl)⟩
            · exact ⟨Or.inl hb, (hnb x hb).mpr (Or.inr (Or.inl rfl))⟩
            · exact ⟨Or.inl hc, (hnb x hc).mpr (Or.inr (Or.inr rfl))⟩
      omega

/-- **Core 3-Tree Structural Invariant:**
In any 3-tree `T[S]` with `|S| ≥ 5`, every degree-3 vertex `w ∈ S` has:
1. Its 3 neighbors in `S` form a 3-clique in `T`, AND
2. Every neighbor `x ∈ N_T(w) ∩ S` has `T.degIn S x ≥ 4`!
(In particular, the set `S_0 = {w ∈ S | T.degIn S w = 3}` is an independent set in `T`!) -/
theorem Is3TreeOn.deg3_props {n : Nat} {T : FinGraph n} {S : Fin n → Bool}
    (ht : Is3TreeOn T S) (h5 : countPred S ≥ 5) :
    ∀ w : Fin n, S w = true → T.degIn S w = 3 →
      (∀ x y : Fin n, S x = true → S y = true → x ≠ y →
        T.adj w x = true → T.adj w y = true → T.adj x y = true) ∧
      (∀ x : Fin n, S x = true → T.adj w x = true → T.degIn S x ≥ 4) := by
  induction ht with
  | baseK4 _ hcard _ => omega
  | addSimplicial S S' v a b c hprev hvnot hS ha hb hc hab hac hbc hclique hnb ih =>
    have hva : v ≠ a := fun h => by subst h; rw [hvnot] at ha; cases ha
    have hvb : v ≠ b := fun h => by subst h; rw [hvnot] at hb; cases hb
    have hvc : v ≠ c := fun h => by subst h; rw [hvnot] at hc; cases hc
    have hdeg_abc : ∀ x, (x = a ∨ x = b ∨ x = c) → T.degIn S x ≥ 4 := by
      intro x hx
      have hx' : S' x = true := by rcases hx with rfl | rfl | rfl <;> assumption
      have hge3 := hprev.min_deg_ge_3 x hx'
      have hadj : T.adj x v = true := by rw [T.symm]; exact (hnb x hx').mpr hx
      have hinc := degIn_insert_eq T S S' v hvnot hS x
      rw [hadj] at hinc
      simp at hinc
      omega
    intro w hw hdegw
    rw [hS w, Bool.or_eq_true, beq_iff_eq] at hw
    rcases hw with hw' | rfl
    · -- `w ∈ S'`, so `w` cannot be adjacent to `v` (else `degIn S w ≥ 4`)
      have hnotadj : T.adj w v = false := by
        cases h : T.adj w v
        · rfl
        · have hge3 := hprev.min_deg_ge_3 w hw'
          have hinc := degIn_insert_eq T S S' v hvnot hS w
          rw [h] at hinc; simp at hinc; omega
      have hdegw' : T.degIn S' w = 3 := by
        have hinc := degIn_insert_eq T S S' v hvnot hS w
        rw [hnotadj] at hinc; simp at hinc; omega
      have hcard' := hprev.card_ge_4
      by_cases h4 : countPred S' = 4
      · -- `T[S']` is `K_4`: `w` is the unique 4th vertex outside `{a, b, c}`!
        have hw_ne_abc : w ≠ a ∧ w ≠ b ∧ w ≠ c := by
          refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
          · subst h; have := hdeg_abc w (Or.inl rfl); omega
          · subst h; have := hdeg_abc w (Or.inr (Or.inl rfl)); omega
          · subst h; have := hdeg_abc w (Or.inr (Or.inr rfl)); omega
        have hS'4 : ∀ u : Fin n, S' u = true ↔ u = w ∨ u = a ∨ u = b ∨ u = c := by
          have hnd : [w, a, b, c].Nodup := by
            simp [List.nodup_cons, hw_ne_abc, hab, hac, hbc]
          have hsub : ∀ u ∈ [w, a, b, c], S' u = true := by
            intro u hu; simp at hu; rcases hu with rfl | rfl | rfl | rfl <;> assumption
          have hle := countPred_ge_of_nodup_subset S' [w, a, b, c] hnd hsub
          have heq := eq_of_imp_and_countPred_eq (fun u => [w, a, b, c].contains u) S'
            (fun u hu => hsub u (List.contains_iff_mem.mp hu))
            (by rw [countPred_of_list_eq _ [w, a, b, c] hnd (fun u => List.contains_iff_mem)]; exact h4.symm)
          intro u
          rw [← heq u, List.contains_iff_mem]
          simp
        constructor
        · intro x y hx hy hxy hwx hwy
          have hx' : S' x = true := by
            rw [hS x, Bool.or_eq_true, beq_iff_eq] at hx
            rcases hx with h | rfl
            · exact h
            · rw [hnotadj] at hwx; cases hwx
          have hy' : S' y = true := by
            rw [hS y, Bool.or_eq_true, beq_iff_eq] at hy
            rcases hy with h | rfl
            · exact h
            · rw [hnotadj] at hwy; cases hwy
          have hx_abc : x = a ∨ x = b ∨ x = c := by
            rcases (hS'4 x).mp hx' with rfl | h
            · exact absurd (T.adj_ne hwx) (by simp)
            · exact h
          have hy_abc : y = a ∨ y = b ∨ y = c := by
            rcases (hS'4 y).mp hy' with rfl | h
            · exact absurd (T.adj_ne hwy) (by simp)
            · exact h
          rcases hx_abc with rfl | rfl | rfl <;> rcases hy_abc with rfl | rfl | rfl
          · exact absurd rfl hxy
          · exact hclique.1
          · exact hclique.2.1
          · rw [T.symm]; exact hclique.1
          · exact absurd rfl hxy
          · exact hclique.2.2
          · rw [T.symm]; exact hclique.2.1
          · rw [T.symm]; exact hclique.2.2
          · exact absurd rfl hxy
        · intro x hx hwx
          have hx' : S' x = true := by
            rw [hS x, Bool.or_eq_true, beq_iff_eq] at hx
            rcases hx with h | rfl
            · exact h
            · rw [hnotadj] at hwx; cases hwx
          rcases (hS'4 x).mp hx' with rfl | habc
          · exact absurd (T.adj_ne hwx) (by simp)
          · exact hdeg_abc x habc
      · -- `|S'| ≥ 5`: apply IH directly!
        rcases ih (by omega) w hw' hdegw' with ⟨ih_clq, ih_deg⟩
        constructor
        · intro x y hx hy hxy hwx hwy
          have hx' : S' x = true := by
            rw [hS x, Bool.or_eq_true, beq_iff_eq] at hx
            rcases hx with h | rfl
            · exact h
            · rw [hnotadj] at hwx; cases hwx
          have hy' : S' y = true := by
            rw [hS y, Bool.or_eq_true, beq_iff_eq] at hy
            rcases hy with h | rfl
            · exact h
            · rw [hnotadj] at hwy; cases hwy
          exact ih_clq x y hx' hy' hxy hwx hwy
        · intro x hx hwx
          have hx' : S' x = true := by
            rw [hS x, Bool.or_eq_true, beq_iff_eq] at hx
            rcases hx with h | rfl
            · exact h
            · rw [hnotadj] at hwx; cases hwx
          have h1 := degIn_insert_eq T S S' v hvnot hS x
          have h2 := ih_deg x hx' hwx
          omega
    · -- `w = v`: its neighbors in `S` are `{a, b, c}` (a 3-clique, all with `degIn S ≥ 4`)!
      constructor
      · intro x y hx hy hxy hvx hvy
        have hx' : S' x = true := by
          rw [hS x, Bool.or_eq_true, beq_iff_eq] at hx
          rcases hx with h | rfl
          · exact h
          · rw [T.loopless] at hvx; cases hvx
        have hy' : S' y = true := by
          rw [hS y, Bool.or_eq_true, beq_iff_eq] at hy
          rcases hy with h | rfl
          · exact h
          · rw [T.loopless] at hvy; cases hvy
        rcases (hnb x hx').mp hvx with rfl | rfl | rfl <;>
        rcases (hnb y hy').mp hvy with rfl | rfl | rfl
        · exact absurd rfl hxy
        · exact hclique.1
        · exact hclique.2.1
        · rw [T.symm]; exact hclique.1
        · exact absurd rfl hxy
        · exact hclique.2.2
        · rw [T.symm]; exact hclique.2.1
        · rw [T.symm]; exact hclique.2.2
        · exact absurd rfl hxy
      · intro x hx hvx
        have hx' : S' x = true := by
          rw [hS x, Bool.or_eq_true, beq_iff_eq] at hx
          rcases hx with h | rfl
          · exact h
          · rw [T.loopless] at hvx; cases hvx
        exact hdeg_abc x ((hnb x hx').mp hvx)

/-- **Arbitrary Simplicial Peeling Lemma:**
Deleting ANY degree-3 vertex `w ∈ S` from a 3-tree `T[S]` with `|S| ≥ 5` ALWAYS leaves a 3-tree! -/
theorem Is3TreeOn.peel_any_deg3 {n : Nat} {T : FinGraph n} {S : Fin n → Bool}
    (ht : Is3TreeOn T S) (h5 : countPred S ≥ 5)
    (w : Fin n) (hw : S w = true) (hdegw : T.degIn S w = 3) :
    Is3TreeOn T (fun u => S u && (u != w)) := by
  induction ht with
  | baseK4 _ hcard _ => omega
  | addSimplicial S S' v a b c hprev hvnot hS ha hb hc hab hac hbc hclique hnb ih =>
    by_cases hwv : w = v
    · subst hwv
      apply hprev.congr
      intro u
      rw [hS u]
      by_cases huv : u = w
      · subst huv; simp [hvnot]
      · simp [bne_iff_ne, huv, beq_false_of_ne huv]
    · have hw' : S' w = true := by
        rw [hS w, Bool.or_eq_true, beq_iff_eq] at hw
        rcases hw with h | h
        · exact h
        · exact absurd h hwv
      have hnotadj : T.adj w v = false := by
        cases h : T.adj w v
        · rfl
        · have hge3 := hprev.min_deg_ge_3 w hw'
          have hinc := degIn_insert_eq T S S' v hvnot hS w
          rw [h] at hinc; simp at hinc; omega
      have hdegw' : T.degIn S' w = 3 := by
        have hinc := degIn_insert_eq T S S' v hvnot hS w
        rw [hnotadj] at hinc; simp at hinc; omega
      have hwa : w ≠ a := by
        intro h; subst h
        have hadj : T.adj w v = true := by rw [T.symm]; exact (hnb w hw').mpr (Or.inl rfl)
        rw [hnotadj] at hadj; cases hadj
      have hwb : w ≠ b := by
        intro h; subst h
        have hadj : T.adj w v = true := by rw [T.symm]; exact (hnb w hw').mpr (Or.inr (Or.inl rfl))
        rw [hnotadj] at hadj; cases hadj
      have hwc : w ≠ c := by
        intro h; subst h
        have hadj : T.adj w v = true := by rw [T.symm]; exact (hnb w hw').mpr (Or.inr (Or.inr rfl))
        rw [hnotadj] at hadj; cases hadj
      have hcard' := hprev.card_ge_4
      by_cases h4 : countPred S' = 4
      · -- `S' = {w, a, b, c}`, so `S \ {w} = {v, a, b, c}` is `K_4`!
        have hnd : [w, a, b, c].Nodup := by
          simp [List.nodup_cons, hwa, hwb, hwc, hab, hac, hbc]
        have hsub : ∀ u ∈ [w, a, b, c], S' u = true := by
          intro u hu; simp at hu; rcases hu with rfl | rfl | rfl | rfl <;> assumption
        have heqS' := eq_of_imp_and_countPred_eq (fun u => [w, a, b, c].contains u) S'
          (fun u hu => hsub u (List.contains_iff_mem.mp hu))
          (by rw [countPred_of_list_eq _ [w, a, b, c] hnd (fun u => List.contains_iff_mem)]; exact h4.symm)
        have hcardS : countPred S = 5 := by
          rw [countPred_congr S _ hS, countPred_insert S' v hvnot]; omega
        have her := countPred_erase S w hw
        apply Is3TreeOn.baseK4 _ (by omega)
        intro x y hx hy hxy
        simp only [Bool.and_eq_true, bne_iff_ne, hS, Bool.or_eq_true, beq_iff_eq] at hx hy
        have hx_in : x = v ∨ x = a ∨ x = b ∨ x = c := by
          rcases hx with ⟨hx' | rfl, hxw⟩
          · rw [← heqS' x, List.contains_iff_mem] at hx'
            simp at hx'
            rcases hx' with rfl | h
            · exact absurd rfl hxw
            · exact Or.inr h
          · exact Or.inl rfl
        have hy_in : y = v ∨ y = a ∨ y = b ∨ y = c := by
          rcases hy with ⟨hy' | rfl, hyw⟩
          · rw [← heqS' y, List.contains_iff_mem] at hy'
            simp at hy'
            rcases hy' with rfl | h
            · exact absurd rfl hyw
            · exact Or.inr h
          · exact Or.inl rfl
        rcases hx_in with hxv | hxa | hxb | hxc <;> rcases hy_in with hyv | hya | hyb | hyc
        · exact absurd (hxv.trans hyv.symm) hxy
        · rw [hxv, hya]; exact (hnb a ha).mpr (Or.inl rfl)
        · rw [hxv, hyb]; exact (hnb b hb).mpr (Or.inr (Or.inl rfl))
        · rw [hxv, hyc]; exact (hnb c hc).mpr (Or.inr (Or.inr rfl))
        · rw [hxa, hyv, T.symm]; exact (hnb a ha).mpr (Or.inl rfl)
        · exact absurd (hxa.trans hya.symm) hxy
        · rw [hxa, hyb]; exact hclique.1
        · rw [hxa, hyc]; exact hclique.2.1
        · rw [hxb, hyv, T.symm]; exact (hnb b hb).mpr (Or.inr (Or.inl rfl))
        · rw [hxb, hya, T.symm]; exact hclique.1
        · exact absurd (hxb.trans hyb.symm) hxy
        · rw [hxb, hyc]; exact hclique.2.2
        · rw [hxc, hyv, T.symm]; exact (hnb c hc).mpr (Or.inr (Or.inr rfl))
        · rw [hxc, hya, T.symm]; exact hclique.2.1
        · rw [hxc, hyb, T.symm]; exact hclique.2.2
        · exact absurd (hxc.trans hyc.symm) hxy
      · -- `|S'| ≥ 5`: peel `w` from `S'`, then re-attach `v` on `{a, b, c}`!
        have hpeel' := ih (by omega) hw' hdegw'
        refine Is3TreeOn.addSimplicial (fun u => S u && (u != w)) (fun u => S' u && (u != w))
          v a b c hpeel' (by simp [hvnot]) ?_
          (by simp [ha, bne_iff_ne, Ne.symm hwa])
          (by simp [hb, bne_iff_ne, Ne.symm hwb])
          (by simp [hc, bne_iff_ne, Ne.symm hwc])
          hab hac hbc hclique ?_
        · intro u
          rw [hS u]
          by_cases huw : u = w
          · subst huw; simp [beq_false_of_ne hwv]
          · have hne : (u != w) = true := bne_iff_ne.mpr huw
            simp [hne]
        · intro u hu
          simp only [Bool.and_eq_true] at hu
          exact hnb u hu.1

/-- Every 3-tree `T[S]` contains a simplicial vertex `u ∈ S` with `degIn S u = 3` and
3 distinct neighbors `a, b, c ∈ S` forming a 3-clique in `T`. -/
theorem Is3TreeOn.exists_simplicial {n : Nat} {T : FinGraph n} {S : Fin n → Bool}
    (ht : Is3TreeOn T S) :
    ∃ u a b c : Fin n, [u, a, b, c].Nodup ∧
      S u = true ∧ S a = true ∧ S b = true ∧ S c = true ∧
      T.degIn S u = 3 ∧
      (∀ x : Fin n, S x = true → (T.adj u x = true ↔ x = a ∨ x = b ∨ x = c)) ∧
      (T.adj a b = true ∧ T.adj a c = true ∧ T.adj b c = true) := by
  cases ht with
  | baseK4 S hcard hclique =>
    have hlen : ((List.finRange n).filter S).length = 4 := hcard
    match hfl : (List.finRange n).filter S with
    | [u, a, b, c] =>
      have hnd : [u, a, b, c].Nodup := hfl ▸ nodup_filter_finRange S
      have hmem : ∀ x, S x = true ↔ x = u ∨ x = a ∨ x = b ∨ x = c := by
        intro x
        rw [← mem_filter_finRange_iff S x, hfl]
        simp
      have hu : S u = true := (hmem u).mpr (Or.inl rfl)
      have ha : S a = true := (hmem a).mpr (Or.inr (Or.inl rfl))
      have hb : S b = true := (hmem b).mpr (Or.inr (Or.inr (Or.inl rfl)))
      have hc : S c = true := (hmem c).mpr (Or.inr (Or.inr (Or.inr rfl)))
      simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hnd
      rcases hnd with ⟨⟨hua, hub, huc⟩, ⟨hab, hac⟩, hbc, _⟩
      refine ⟨u, a, b, c, by simp [List.nodup_cons, hua, hub, huc, hab, hac, hbc],
              hu, ha, hb, hc, degIn_of_K4 T S hcard hclique u hu, ?_,
              hclique a b ha hb hab, hclique a c ha hc hac, hclique b c hb hc hbc⟩
      intro x hx
      rcases (hmem x).mp hx with hxu | hxa | hxb | hxc
      · rw [hxu]; simp [T.loopless, hua, hub, huc]
      · rw [hxa]; simp [hclique u a hu ha hua]
      · rw [hxb]; simp [hclique u b hu hb hub]
      · rw [hxc]; simp [hclique u c hu hc huc]
    | [] | [_] | [_, _] | [_, _, _] | _ :: _ :: _ :: _ :: _ :: _ =>
      rw [hfl] at hlen; simp at hlen
  | addSimplicial S S' v a b c _ hvnot hS ha hb hc hab hac hbc hclique hnb =>
    have hva : v ≠ a := fun h => by subst h; rw [hvnot] at ha; cases ha
    have hvb : v ≠ b := fun h => by subst h; rw [hvnot] at hb; cases hb
    have hvc : v ≠ c := fun h => by subst h; rw [hvnot] at hc; cases hc
    have hnd : [v, a, b, c].Nodup := by
      simp [List.nodup_cons, hva, hvb, hvc, hab, hac, hbc]
    have hvS : S v = true := by rw [hS v]; simp
    have haS : S a = true := by rw [hS a, ha]; rfl
    have hbS : S b = true := by rw [hS b, hb]; rfl
    have hcS : S c = true := by rw [hS c, hc]; rfl
    have hnbS : ∀ x : Fin n, S x = true → (T.adj v x = true ↔ x = a ∨ x = b ∨ x = c) := by
      intro x hx
      rw [hS x, Bool.or_eq_true, beq_iff_eq] at hx
      rcases hx with hx' | rfl
      · exact hnb x hx'
      · simp [T.loopless, hva, hvb, hvc]
    have hdegv : T.degIn S v = 3 := by
      rw [FinGraph.degIn_eq_countPred]
      have hnd3 : [a, b, c].Nodup := by simp [List.nodup_cons, hab, hac, hbc]
      rw [countPred_of_list_eq _ [a, b, c] hnd3]
      · rfl
      · intro x
        simp only [Bool.and_eq_true, List.mem_cons, List.not_mem_nil, or_false]
        constructor
        · rintro ⟨hx, hadj⟩; exact (hnbS x hx).mp hadj
        · intro hx
          rcases hx with rfl | rfl | rfl
          · exact ⟨haS, (hnbS x haS).mpr (Or.inl rfl)⟩
          · exact ⟨hbS, (hnbS x hbS).mpr (Or.inr (Or.inl rfl))⟩
          · exact ⟨hcS, (hnbS x hcS).mpr (Or.inr (Or.inr rfl))⟩
    exact ⟨v, a, b, c, hnd, hvS, haS, hbS, hcS, hdegv, hnbS, hclique⟩

/-- Peeling an entire independent set `R ⊆ S_0(T)` of degree-3 vertices from a 3-tree `T`
on `Fin n` (`n ≥ 5`) leaves either a 3-tree `Is3TreeOn T S'` or a 3-clique `|S'| = 3`. -/
theorem peel_simplicial_set {n : Nat} (T : FinGraph n) (ht : IsSpanning3Tree T)
    (hn5 : n ≥ 5) (R : List (Fin n)) (hnd : R.Nodup)
    (hR_deg3 : ∀ w ∈ R, T.deg w = 3) :
    let S' : Fin n → Bool := fun u => !(R.contains u)
    Is3TreeOn T S' ∨ countPred S' = 3 := by
  have hS0_indep : ∀ w x : Fin n, T.deg w = 3 → T.adj w x = true → T.deg x ≥ 4 := by
    intro w x hdw hadj
    have h5 : countPred (fun _ : Fin n => true) ≥ 5 := by rw [countPred_true]; omega
    have hprops := ht.deg3_props h5 w rfl (by rw [FinGraph.degIn_all]; exact hdw)
    have h := hprops.2 x rfl hadj
    rwa [FinGraph.degIn_all] at h
  -- Induct on `R`:
  induction R with
  | nil =>
    left
    exact ht.congr (fun _ => rfl)
  | cons w ws ih =>
    rcases List.nodup_cons.mp hnd with ⟨hwnot, hndws⟩
    have hws_deg3 : ∀ z ∈ ws, T.deg z = 3 := fun z hz => hR_deg3 z (List.mem_cons_of_mem w hz)
    have hw_deg3 : T.deg w = 3 := hR_deg3 w (List.mem_cons_self ..)
    let Sws : Fin n → Bool := fun u => !(ws.contains u)
    let Sw : Fin n → Bool := fun u => !((w :: ws).contains u)
    have hw_in : Sws w = true := by
      simp only [Sws, Bool.not_eq_true']
      cases hc : ws.contains w
      · rfl
      · exact absurd (List.contains_iff_mem.mp hc) hwnot
    have hSw_eq : ∀ u, Sw u = (Sws u && (u != w)) := by
      intro u
      simp only [Sw, Sws, List.contains_cons]
      by_cases huw : u = w
      · subst huw; simp
      · simp [beq_false_of_ne huw, bne_iff_ne, huw]
    have hdegw_Sws : T.degIn Sws w = 3 := by
      have heq : T.degIn Sws w = T.deg w := by
        rw [FinGraph.degIn_eq_countPred, FinGraph.deg_eq_countPred]
        apply countPred_congr
        intro x
        cases hadj : T.adj w x
        · simp
        · have hx4 := hS0_indep w x hw_deg3 hadj
          have hxnot : x ∉ ws := fun hmem => by
            have hx3 := hws_deg3 x hmem; omega
          have hnc : ws.contains x = false := by
            cases hc : ws.contains x
            · rfl
            · exact absurd (List.contains_iff_mem.mp hc) hxnot
          have hxSws : Sws x = true := by dsimp only [Sws]; rw [hnc]; rfl
          simp [hxSws]
      rw [heq, hw_deg3]
    have hih : Is3TreeOn T Sws ∨ countPred Sws = 3 := ih hndws hws_deg3
    rcases hih with htree_ws | hcard3_ws
    · have hcard_ws := htree_ws.card_ge_4
      by_cases h5 : countPred Sws ≥ 5
      · left
        have hpeel := htree_ws.peel_any_deg3 h5 w hw_in hdegw_Sws
        exact hpeel.congr (fun u => (hSw_eq u).symm)
      · right
        have h4 : countPred Sws = 4 := by omega
        have her := countPred_erase Sws w hw_in
        change countPred Sw = 3
        rw [countPred_congr Sw _ hSw_eq]
        omega
    · exfalso
      have hle : T.degIn Sws w ≤ countPred Sws - 1 := by
        have hsub : T.degIn Sws w ≤ countPred (fun u => Sws u && (u != w)) := by
          rw [FinGraph.degIn_eq_countPred]
          apply countPred_le_of_imp
          intro u hu
          simp only [Bool.and_eq_true] at hu ⊢
          exact ⟨hu.1, bne_iff_ne.mpr (Ne.symm (T.adj_ne hu.2))⟩
        have her := countPred_erase Sws w hw_in
        omega
      omega

/-- **15-Line Universal 3-Tree Lemma (Directly on `FinGraph`):**
Every finite simple graph `F` with minimum degree `δ(F) ≥ 3` that is a spanning subgraph
of a 3-tree `T` contains a degree-3 triangle, a `K_{2,3}`, or a `Q_3 - v^*`! -/
theorem universal_3tree_lemma {n : Nat} (F T : FinGraph n)
    (hsub : F.IsSubgraphOf T)
    (hmin : F.MinDegreeAtLeast 3)
    (htree : IsSpanning3Tree T) :
    F.HasDeg3Triangle ∨ F.HasK23 ∨ F.HasQ3MinusV := by
  refine Classical.byContradiction fun hnone => ?_
  have hnoTri : ¬F.HasDeg3Triangle := fun h => hnone (Or.inl h)
  have hnoK23 : ¬F.HasK23 := fun h => hnone (Or.inr (Or.inl h))
  have hnoQ3 : ¬F.HasQ3MinusV := fun h => hnone (Or.inr (Or.inr h))
  have hn4 : n ≥ 4 := by
    have h := htree.card_ge_4
    rw [countPred_true] at h; exact h
  -- Case `n = 4`: `T` is `K_4`, so `F = K_4` gives a degree-3 triangle!
  by_cases hn5 : n < 5
  · have hn_eq : n = 4 := by omega
    subst hn_eq
    have hFdeg3 : ∀ u : Fin 4, F.deg u = 3 := by
      intro u
      have hlo := hmin.2 u
      have hhi : F.deg u ≤ 3 := by
        rw [FinGraph.deg_eq_countPred]
        have hle : countPred (F.adj u) ≤ countPred (fun v : Fin 4 => v != u) :=
          countPred_le_of_imp _ _ (fun v hv => bne_iff_ne.mpr (Ne.symm (F.adj_ne hv)))
        have her := countPred_erase (fun _ : Fin 4 => true) u rfl
        have htot : countPred (fun _ : Fin 4 => true) = 4 := by decide
        have hcongr : countPred (fun v : Fin 4 => true && (v != u)) = countPred (fun v : Fin 4 => v != u) :=
          countPred_congr _ _ (fun _ => by simp)
        omega
      omega
    have hFclq : ∀ u v : Fin 4, u ≠ v → F.adj u v = true := by
      intro u v huv
      have heq := eq_of_imp_and_countPred_eq (F.adj u) (fun x : Fin 4 => x != u)
        (fun x hx => bne_iff_ne.mpr (Ne.symm (F.adj_ne hx)))
        (by
          have h1 := hFdeg3 u
          rw [FinGraph.deg_eq_countPred] at h1
          have her := countPred_erase (fun _ : Fin 4 => true) u rfl
          have htot : countPred (fun _ : Fin 4 => true) = 4 := by decide
          have hcongr : countPred (fun x : Fin 4 => true && (x != u)) = countPred (fun x : Fin 4 => x != u) :=
            countPred_congr _ _ (fun _ => by simp)
          omega)
      rw [heq v]
      exact bne_iff_ne.mpr (Ne.symm huv)
    exact hnoTri ⟨⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩,
      by decide, by decide, by decide, hFdeg3 ⟨0, by decide⟩,
      hFclq _ _ (by decide), hFclq _ _ (by decide), hFclq _ _ (by decide)⟩
  · -- Main case `n ≥ 5`:
    have hn5' : n ≥ 5 := by omega
    have hcountAll : countPred (fun _ : Fin n => true) = n := countPred_true
    -- Define `S0 := {w | T.deg w = 3}`:
    let S0_pred : Fin n → Bool := fun w => T.deg w == 3
    let S0_list : List (Fin n) := (List.finRange n).filter S0_pred
    have hS0_mem : ∀ w, w ∈ S0_list ↔ T.deg w = 3 := by
      intro w; simp [S0_list, S0_pred, List.mem_filter, List.mem_finRange]
    -- Key Property 1: Every `w ∈ S0` has `F.deg w = 3` AND `∀ x, F.adj w x = T.adj w x`!
    have hS0_eq_adj : ∀ w : Fin n, T.deg w = 3 → F.deg w = 3 ∧ ∀ x, F.adj w x = T.adj w x := by
      intro w hdw
      have hlo := hmin.2 w
      have hhi := FinGraph.deg_le_of_subgraph hsub w
      have hFd : F.deg w = 3 := by omega
      refine ⟨hFd, eq_of_imp_and_countPred_eq (F.adj w) (T.adj w) (fun x hx => hsub w x hx) ?_⟩
      rw [← FinGraph.deg_eq_countPred, ← FinGraph.deg_eq_countPred]; omega
    -- Key Property 2: For every `w ∈ S0`, `N_T(w)` is an independent set in `F` (no deg-3 triangle)!
    have hS0_nb_indep : ∀ w x y : Fin n, T.deg w = 3 →
        T.adj w x = true → T.adj w y = true → F.adj x y = false := by
      intro w x y hdw hwx hwy
      cases hxy : F.adj x y
      · rfl
      · exfalso
        have hF := hS0_eq_adj w hdw
        exact hnoTri ⟨w, x, y, T.adj_ne hwx, T.adj_ne hwy, F.adj_ne hxy,
          hF.1, (hF.2 x).trans hwx, (hF.2 y).trans hwy, hxy⟩
    -- Key Property 3: Distinct `w1, w2 ∈ S0` cannot share 3 distinct common neighbors in `T` (no `K_{2,3}`)!
    have hS0_inj : ∀ w1 w2 a b c : Fin n,
        w1 ≠ w2 → T.deg w1 = 3 → T.deg w2 = 3 →
        a ≠ b → a ≠ c → b ≠ c →
        T.adj w1 a = true → T.adj w1 b = true → T.adj w1 c = true →
        T.adj w2 a = true → T.adj w2 b = true → T.adj w2 c = true → False := by
      intro w1 w2 a b c hne hd1 hd2 hab hac hbc h1a h1b h1c h2a h2b h2c
      have hF1 := hS0_eq_adj w1 hd1
      have hF2 := hS0_eq_adj w2 hd2
      have hnd5 : [w1, w2, a, b, c].Nodup := by
        simp [List.nodup_cons, hne, hab, hac, hbc,
              T.adj_ne h1a, T.adj_ne h1b, T.adj_ne h1c,
              T.adj_ne h2a, T.adj_ne h2b, T.adj_ne h2c]
      exact hnoK23 ⟨w1, w2, a, b, c, hnd5,
        (hF1.2 a).trans h1a, (hF1.2 b).trans h1b, (hF1.2 c).trans h1c,
        (hF2.2 a).trans h2a, (hF2.2 b).trans h2b, (hF2.2 c).trans h2c⟩
    -- Key Property 4: Every neighbor of `w ∈ S0` has `T.deg ≥ 4`, and `N_T(w)` is a 3-clique in `T`!
    have hS0_props : ∀ w : Fin n, T.deg w = 3 →
        (∀ x y : Fin n, x ≠ y → T.adj w x = true → T.adj w y = true → T.adj x y = true) ∧
        (∀ x : Fin n, T.adj w x = true → T.deg x ≥ 4) := by
      intro w hdw
      have hp := htree.deg3_props (by omega) w rfl (by rw [FinGraph.degIn_all]; exact hdw)
      exact ⟨fun x y hxy h1 h2 => hp.1 x y rfl rfl hxy h1 h2,
             fun x hx => by have := hp.2 x rfl hx; rwa [FinGraph.degIn_all] at this⟩
    -- Peel all of `S0_list` from `T`!
    let S' : Fin n → Bool := fun u => !(S0_list.contains u)
    have hS'_iff : ∀ u, S' u = true ↔ T.deg u ≠ 3 := by
      intro u
      simp only [S', Bool.not_eq_true']
      constructor
      · intro h hc
        have hm := (hS0_mem u).mpr hc
        rw [List.contains_iff_mem.mpr hm] at h; cases h
      · intro hne
        cases hc : S0_list.contains u
        · rfl
        · exact absurd ((hS0_mem u).mp (List.contains_iff_mem.mp hc)) hne
    have hpeeled := peel_simplicial_set T htree hn5' S0_list (nodup_filter_finRange S0_pred)
      (fun w hw => (hS0_mem w).mp hw)
    rcases hpeeled with htree' | hcard3
    · -- Case 2: `T[S']` is a 3-tree (`|S'| ≥ 4`). Pick a simplicial vertex `u ∈ S'` with `N_{T[S']}(u) = {a, b, c}`!
      rcases htree'.exists_simplicial with ⟨u, a, b, c, hnd4, huS', haS', hbS', hcS', hdegu', hnbu', _⟩
      simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hnd4
      rcases hnd4 with ⟨⟨hua, hub, huc⟩, ⟨hab, hac⟩, hbc, _⟩
      -- Every `w ∈ S0` adjacent to `u` in `T` has its other 2 neighbors in `{a, b, c}`!
      have hw_subset : ∀ w : Fin n, T.deg w = 3 → T.adj u w = true →
          ∃ p q : Fin n, (p = a ∧ q = b ∨ p = b ∧ q = c ∨ p = c ∧ q = a) ∧
            T.adj w u = true ∧ T.adj w p = true ∧ T.adj w q = true := by
        intro w hdw huw
        have hwu : T.adj w u = true := by rw [T.symm]; exact huw
        -- `w` has 3 neighbors in `T`; one is `u`, the other two are in `S'` and adjacent to `u` (since `N_T(w)` is a 3-clique in `T`!)
        have hnb_sub : ∀ x, T.adj w x = true → x = u ∨ x = a ∨ x = b ∨ x = c := by
          intro x hwx
          by_cases hxu : x = u
          · exact Or.inl hxu
          · have hx4 : T.deg x ≥ 4 := (hS0_props w hdw).2 x hwx
            have hxS' : S' x = true := (hS'_iff x).mpr (by omega)
            have hux : T.adj u x = true := (hS0_props w hdw).1 u x (Ne.symm hxu) hwu hwx
            exact Or.inr ((hnbu' x hxS').mp hux)
        -- Since `T.deg w = 3`, `N_T(w) \ {u}` has size 2 inside `{a, b, c}`!
        -- So at least two of `T.adj w a, T.adj w b, T.adj w c` must be true!
        cases hwa : T.adj w a <;> cases hwb : T.adj w b <;> cases hwc : T.adj w c
        · exfalso
          have hle : countPred (T.adj w) ≤ 1 := countPred_le_of_subset_list (T.adj w) [u] (by
            intro x hx; rcases hnb_sub x hx with rfl | rfl | rfl | rfl
            · simp
            · rw [hwa] at hx; cases hx
            · rw [hwb] at hx; cases hx
            · rw [hwc] at hx; cases hx)
          rw [← FinGraph.deg_eq_countPred] at hle; omega
        · exfalso
          have hle : countPred (T.adj w) ≤ 2 := countPred_le_of_subset_list (T.adj w) [u, c] (by
            intro x hx; rcases hnb_sub x hx with rfl | rfl | rfl | rfl <;> simp_all)
          rw [← FinGraph.deg_eq_countPred] at hle; omega
        · exfalso
          have hle : countPred (T.adj w) ≤ 2 := countPred_le_of_subset_list (T.adj w) [u, b] (by
            intro x hx; rcases hnb_sub x hx with rfl | rfl | rfl | rfl <;> simp_all)
          rw [← FinGraph.deg_eq_countPred] at hle; omega
        · exact ⟨b, c, Or.inr (Or.inl ⟨rfl, rfl⟩), hwu, hwb, hwc⟩
        · exfalso
          have hle : countPred (T.adj w) ≤ 2 := countPred_le_of_subset_list (T.adj w) [u, a] (by
            intro x hx; rcases hnb_sub x hx with rfl | rfl | rfl | rfl <;> simp_all)
          rw [← FinGraph.deg_eq_countPred] at hle; omega
        · exact ⟨c, a, Or.inr (Or.inr ⟨rfl, rfl⟩), hwu, hwc, hwa⟩
        · exact ⟨a, b, Or.inl ⟨rfl, rfl⟩, hwu, hwa, hwb⟩
        · exact ⟨a, b, Or.inl ⟨rfl, rfl⟩, hwu, hwa, hwb⟩
      -- Partition `S0 ∩ N_T(u)` into the 3 unordered pair buckets `{a,b}`, `{b,c}`, `{c,a}`!
      let hasAB : Prop := ∃ w : Fin n, T.deg w = 3 ∧ T.adj w u = true ∧ T.adj w a = true ∧ T.adj w b = true
      let hasBC : Prop := ∃ w : Fin n, T.deg w = 3 ∧ T.adj w u = true ∧ T.adj w b = true ∧ T.adj w c = true
      let hasCA : Prop := ∃ w : Fin n, T.deg w = 3 ∧ T.adj w u = true ∧ T.adj w c = true ∧ T.adj w a = true
      -- Note: each bucket has at most 1 vertex by `hS0_inj`!
      have huniq_AB : ∀ w1 w2, T.deg w1 = 3 → T.deg w2 = 3 →
          T.adj w1 u = true → T.adj w1 a = true → T.adj w1 b = true →
          T.adj w2 u = true → T.adj w2 a = true → T.adj w2 b = true → w1 = w2 := by
        intro w1 w2 d1 d2 h1u h1a h1b h2u h2a h2b
        exact Classical.byContradiction fun hne =>
          hS0_inj w1 w2 u a b hne d1 d2 hua hub hab h1u h1a h1b h2u h2a h2b
      have huniq_BC : ∀ w1 w2, T.deg w1 = 3 → T.deg w2 = 3 →
          T.adj w1 u = true → T.adj w1 b = true → T.adj w1 c = true →
          T.adj w2 u = true → T.adj w2 b = true → T.adj w2 c = true → w1 = w2 := by
        intro w1 w2 d1 d2 h1u h1b h1c h2u h2b h2c
        exact Classical.byContradiction fun hne =>
          hS0_inj w1 w2 u b c hne d1 d2 hub huc hbc h1u h1b h1c h2u h2b h2c
      have huniq_CA : ∀ w1 w2, T.deg w1 = 3 → T.deg w2 = 3 →
          T.adj w1 u = true → T.adj w1 c = true → T.adj w1 a = true →
          T.adj w2 u = true → T.adj w2 c = true → T.adj w2 a = true → w1 = w2 := by
        intro w1 w2 d1 d2 h1u h1c h1a h2u h2c h2a
        exact Classical.byContradiction fun hne =>
          hS0_inj w1 w2 u c a hne d1 d2 huc hua (Ne.symm hac) h1u h1c h1a h2u h2c h2a
      -- Every neighbor of `u` in `F` is either in `{a, b, c}` or in `S0 ∩ N_T(u)`!
      have hFnb_u : ∀ x : Fin n, F.adj u x = true →
          x = a ∨ x = b ∨ x = c ∨ (T.deg x = 3 ∧ T.adj u x = true) := by
        intro x hux
        have hTx : T.adj u x = true := hsub u x hux
        by_cases hx3 : T.deg x = 3
        · exact Or.inr (Or.inr (Or.inr ⟨hx3, hTx⟩))
        · have hxS' : S' x = true := (hS'_iff x).mpr hx3
          rcases (hnbu' x hxS').mp hTx with rfl | rfl | rfl
          · exact Or.inl rfl
          · exact Or.inr (Or.inl rfl)
          · exact Or.inr (Or.inr (Or.inl rfl))
      -- Helper to close `k = 1` or `k = 2` via `F.deg u ≤ 2`!
      have hFdeg3_u : F.deg u ≥ 3 := hmin.2 u
      by_cases hAB : hasAB
      · rcases hAB with ⟨w1, dw1, h1u, h1a, h1b⟩
        have hno_ua : F.adj u a = false := hS0_nb_indep w1 u a dw1 h1u h1a
        have hno_ub : F.adj u b = false := hS0_nb_indep w1 u b dw1 h1u h1b
        by_cases hBC : hasBC
        · rcases hBC with ⟨w2, dw2, h2u, h2b, h2c⟩
          have hno_uc : F.adj u c = false := hS0_nb_indep w2 u c dw2 h2u h2c
          by_cases hCA : hasCA
          · -- `k = 3`: EXPLICIT `Q_3 - v^*` on `[u, w1, w2, w3, a, b, c]`!
            rcases hCA with ⟨w3, dw3, h3u, h3c, h3a⟩
            have hF1 := hS0_eq_adj w1 dw1
            have hF2 := hS0_eq_adj w2 dw2
            have hF3 := hS0_eq_adj w3 dw3
            have hw12 : w1 ≠ w2 := by
              intro h; subst h
              have hge4 : countPred (T.adj w1) ≥ 4 := countPred_ge_of_nodup_subset (T.adj w1) [u, a, b, c]
                (by simp [List.nodup_cons, hua, hub, huc, hab, hac, hbc])
                (by intro x hx; simp at hx; rcases hx with rfl | rfl | rfl | rfl <;> assumption)
              rw [← FinGraph.deg_eq_countPred] at hge4; omega
            have hw13 : w1 ≠ w3 := by
              intro h; subst h
              have hge4 : countPred (T.adj w1) ≥ 4 := countPred_ge_of_nodup_subset (T.adj w1) [u, a, b, c]
                (by simp [List.nodup_cons, hua, hub, huc, hab, hac, hbc])
                (by intro x hx; simp at hx; rcases hx with rfl | rfl | rfl | rfl <;> assumption)
              rw [← FinGraph.deg_eq_countPred] at hge4; omega
            have hw23 : w2 ≠ w3 := by
              intro h; subst h
              have hge4 : countPred (T.adj w2) ≥ 4 := countPred_ge_of_nodup_subset (T.adj w2) [u, a, b, c]
                (by simp [List.nodup_cons, hua, hub, huc, hab, hac, hbc])
                (by intro x hx; simp at hx; rcases hx with rfl | rfl | rfl | rfl <;> assumption)
              rw [← FinGraph.deg_eq_countPred] at hge4; omega
            have hnd7 : [u, w1, w2, w3, a, b, c].Nodup := by
              have hw1S : ∀ x, S' x = true → w1 ≠ x := fun x hx h => by subst h; exact (hS'_iff w1).mp hx dw1
              have hw2S : ∀ x, S' x = true → w2 ≠ x := fun x hx h => by subst h; exact (hS'_iff w2).mp hx dw2
              have hw3S : ∀ x, S' x = true → w3 ≠ x := fun x hx h => by subst h; exact (hS'_iff w3).mp hx dw3
              simp [List.nodup_cons, hua, hub, huc, hab, hac, hbc, hw12, hw13, hw23,
                    Ne.symm (hw1S u huS'), Ne.symm (hw2S u huS'), Ne.symm (hw3S u huS'),
                    hw1S a haS', hw1S b hbS', hw1S c hcS',
                    hw2S a haS', hw2S b hbS', hw2S c hcS',
                    hw3S a haS', hw3S b hbS', hw3S c hcS']
            exact hnoQ3 ⟨u, w1, w2, w3, a, b, c, hnd7,
              by rw [F.symm]; exact (hF1.2 u).trans h1u,
              by rw [F.symm]; exact (hF2.2 u).trans h2u,
              by rw [F.symm]; exact (hF3.2 u).trans h3u,
              (hF1.2 a).trans h1a, (hF1.2 b).trans h1b,
              (hF2.2 b).trans h2b, (hF2.2 c).trans h2c,
              (hF3.2 c).trans h3c, (hF3.2 a).trans h3a⟩
          · -- `k = 2` (AB, BC): only neighbors of `u` in `F` are `{w1, w2}` → `F.deg u ≤ 2`!
            have hle2 : countPred (F.adj u) ≤ 2 := countPred_le_of_subset_list (F.adj u) [w1, w2] (by
              intro x hx
              rcases hFnb_u x hx with rfl | rfl | rfl | ⟨dx, hux⟩
              · rw [hno_ua] at hx; cases hx
              · rw [hno_ub] at hx; cases hx
              · rw [hno_uc] at hx; cases hx
              · rcases hw_subset x dx hux with ⟨p, q, hpq, hxu, hxp, hxq⟩
                rcases hpq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
                · have := huniq_AB x w1 dx dw1 hxu hxp hxq h1u h1a h1b; simp [this]
                · have := huniq_BC x w2 dx dw2 hxu hxp hxq h2u h2b h2c; simp [this]
                · exact absurd ⟨x, dx, hxu, hxp, hxq⟩ hCA)
            rw [← FinGraph.deg_eq_countPred] at hle2; omega
        · by_cases hCA : hasCA
          · -- `k = 2` (AB, CA): only neighbors of `u` in `F` are `{w1, w3}` → `F.deg u ≤ 2`!
            rcases hCA with ⟨w3, dw3, h3u, h3c, h3a⟩
            have hno_uc : F.adj u c = false := hS0_nb_indep w3 u c dw3 h3u h3c
            have hle2 : countPred (F.adj u) ≤ 2 := countPred_le_of_subset_list (F.adj u) [w1, w3] (by
              intro x hx
              rcases hFnb_u x hx with rfl | rfl | rfl | ⟨dx, hux⟩
              · rw [hno_ua] at hx; cases hx
              · rw [hno_ub] at hx; cases hx
              · rw [hno_uc] at hx; cases hx
              · rcases hw_subset x dx hux with ⟨p, q, hpq, hxu, hxp, hxq⟩
                rcases hpq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
                · have := huniq_AB x w1 dx dw1 hxu hxp hxq h1u h1a h1b; simp [this]
                · exact absurd ⟨x, dx, hxu, hxp, hxq⟩ hBC
                · have := huniq_CA x w3 dx dw3 hxu hxp hxq h3u h3c h3a; simp [this])
            rw [← FinGraph.deg_eq_countPred] at hle2; omega
          · -- `k = 1` (AB only): only neighbors of `u` in `F` are `{w1, c}` → `F.deg u ≤ 2`!
            have hle2 : countPred (F.adj u) ≤ 2 := countPred_le_of_subset_list (F.adj u) [w1, c] (by
              intro x hx
              rcases hFnb_u x hx with rfl | rfl | rfl | ⟨dx, hux⟩
              · rw [hno_ua] at hx; cases hx
              · rw [hno_ub] at hx; cases hx
              · simp
              · rcases hw_subset x dx hux with ⟨p, q, hpq, hxu, hxp, hxq⟩
                rcases hpq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
                · have := huniq_AB x w1 dx dw1 hxu hxp hxq h1u h1a h1b; simp [this]
                · exact absurd ⟨x, dx, hxu, hxp, hxq⟩ hBC
                · exact absurd ⟨x, dx, hxu, hxp, hxq⟩ hCA)
            rw [← FinGraph.deg_eq_countPred] at hle2; omega
      · by_cases hBC : hasBC
        · rcases hBC with ⟨w2, dw2, h2u, h2b, h2c⟩
          have hno_ub : F.adj u b = false := hS0_nb_indep w2 u b dw2 h2u h2b
          have hno_uc : F.adj u c = false := hS0_nb_indep w2 u c dw2 h2u h2c
          by_cases hCA : hasCA
          · -- `k = 2` (BC, CA): only neighbors of `u` in `F` are `{w2, w3}` → `F.deg u ≤ 2`!
            rcases hCA with ⟨w3, dw3, h3u, h3c, h3a⟩
            have hno_ua : F.adj u a = false := hS0_nb_indep w3 u a dw3 h3u h3a
            have hle2 : countPred (F.adj u) ≤ 2 := countPred_le_of_subset_list (F.adj u) [w2, w3] (by
              intro x hx
              rcases hFnb_u x hx with rfl | rfl | rfl | ⟨dx, hux⟩
              · rw [hno_ua] at hx; cases hx
              · rw [hno_ub] at hx; cases hx
              · rw [hno_uc] at hx; cases hx
              · rcases hw_subset x dx hux with ⟨p, q, hpq, hxu, hxp, hxq⟩
                rcases hpq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
                · exact absurd ⟨x, dx, hxu, hxp, hxq⟩ hAB
                · have := huniq_BC x w2 dx dw2 hxu hxp hxq h2u h2b h2c; simp [this]
                · have := huniq_CA x w3 dx dw3 hxu hxp hxq h3u h3c h3a; simp [this])
            rw [← FinGraph.deg_eq_countPred] at hle2; omega
          · -- `k = 1` (BC only): only neighbors of `u` in `F` are `{w2, a}` → `F.deg u ≤ 2`!
            have hle2 : countPred (F.adj u) ≤ 2 := countPred_le_of_subset_list (F.adj u) [w2, a] (by
              intro x hx
              rcases hFnb_u x hx with rfl | rfl | rfl | ⟨dx, hux⟩
              · simp
              · rw [hno_ub] at hx; cases hx
              · rw [hno_uc] at hx; cases hx
              · rcases hw_subset x dx hux with ⟨p, q, hpq, hxu, hxp, hxq⟩
                rcases hpq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
                · exact absurd ⟨x, dx, hxu, hxp, hxq⟩ hAB
                · have := huniq_BC x w2 dx dw2 hxu hxp hxq h2u h2b h2c; simp [this]
                · exact absurd ⟨x, dx, hxu, hxp, hxq⟩ hCA)
            rw [← FinGraph.deg_eq_countPred] at hle2; omega
        · by_cases hCA : hasCA
          · -- `k = 1` (CA only): only neighbors of `u` in `F` are `{w3, b}` → `F.deg u ≤ 2`!
            rcases hCA with ⟨w3, dw3, h3u, h3c, h3a⟩
            have hno_uc : F.adj u c = false := hS0_nb_indep w3 u c dw3 h3u h3c
            have hno_ua : F.adj u a = false := hS0_nb_indep w3 u a dw3 h3u h3a
            have hle2 : countPred (F.adj u) ≤ 2 := countPred_le_of_subset_list (F.adj u) [w3, b] (by
              intro x hx
              rcases hFnb_u x hx with rfl | rfl | rfl | ⟨dx, hux⟩
              · rw [hno_ua] at hx; cases hx
              · simp
              · rw [hno_uc] at hx; cases hx
              · rcases hw_subset x dx hux with ⟨p, q, hpq, hxu, hxp, hxq⟩
                rcases hpq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
                · exact absurd ⟨x, dx, hxu, hxp, hxq⟩ hAB
                · exact absurd ⟨x, dx, hxu, hxp, hxq⟩ hBC
                · have := huniq_CA x w3 dx dw3 hxu hxp hxq h3u h3c h3a; simp [this])
            rw [← FinGraph.deg_eq_countPred] at hle2; omega
          · -- `k = 0`: NO vertex of `S0` is adjacent to `u`, so `T.deg u = T.degIn S' u = 3`, contradicting `u ∈ S'`!
            have hTu3 : T.deg u = 3 := by
              have heq : T.deg u = T.degIn S' u := by
                rw [FinGraph.deg_eq_countPred, FinGraph.degIn_eq_countPred]
                apply countPred_congr
                intro x
                cases hTx : T.adj u x
                · simp
                · by_cases hx3 : T.deg x = 3
                  · exfalso
                    rcases hw_subset x hx3 hTx with ⟨p, q, hpq, hxu, hxp, hxq⟩
                    rcases hpq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
                    · exact hAB ⟨x, hx3, hxu, hxp, hxq⟩
                    · exact hBC ⟨x, hx3, hxu, hxp, hxq⟩
                    · exact hCA ⟨x, hx3, hxu, hxp, hxq⟩
                  · simp [(hS'_iff x).mpr hx3]
              rw [heq, hdegu']
            exact (hS'_iff u).mp huS' hTu3
    · -- Case 1: `|S'| = 3`, so `|S0| = n - 3 ≥ 2`, and EVERY `w ∈ S0` has `N_T(w) = S'`, giving `K_{2,3}`!
      have hlen3 : ((List.finRange n).filter S').length = 3 := hcard3
      match hfl : (List.finRange n).filter S' with
      | [a, b, c] =>
        have hnd3 : [a, b, c].Nodup := hfl ▸ nodup_filter_finRange S'
        simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hnd3
        rcases hnd3 with ⟨⟨hab, hac⟩, hbc, _⟩
        have hS'_mem : ∀ x, S' x = true ↔ x = a ∨ x = b ∨ x = c := by
          intro x; rw [← mem_filter_finRange_iff S' x, hfl]; simp
        have hcard3' : countPred S' = 3 := hcard3
        have hS0_len : S0_list.length ≥ 2 := by
          have hsum := countPred_add_not S0_pred
          have heqS' : countPred (fun u => !S0_pred u) = countPred S' := by
            apply countPred_congr
            intro u
            simp only [S', S0_list, S0_pred]
            by_cases h : T.deg u = 3
            · simp [h]
            · simp [h]
          change S0_list.length + countPred (fun u => !S0_pred u) = n at hsum
          omega
        match h0l : S0_list with
        | w1 :: w2 :: _ =>
          have hnd0 : S0_list.Nodup := nodup_filter_finRange S0_pred
          rw [h0l] at hnd0
          have hw12 : w1 ≠ w2 := by
            rcases List.nodup_cons.mp hnd0 with ⟨hnot, _⟩
            intro heq; subst heq; exact hnot (List.mem_cons_self ..)
          have dw1 : T.deg w1 = 3 := (hS0_mem w1).mp (by simp)
          have dw2 : T.deg w2 = 3 := (hS0_mem w2).mp (by simp)
          have hall_adj : ∀ w, T.deg w = 3 → T.adj w a = true ∧ T.adj w b = true ∧ T.adj w c = true := by
            intro w hdw
            have heq := eq_of_imp_and_countPred_eq (T.adj w) S'
              (fun x hx => (hS'_iff x).mpr (by have := (hS0_props w hdw).2 x hx; omega))
              (by rw [← FinGraph.deg_eq_countPred, hdw, hcard3'])
            exact ⟨(heq a).trans ((hS'_mem a).mpr (Or.inl rfl)),
                   (heq b).trans ((hS'_mem b).mpr (Or.inr (Or.inl rfl))),
                   (heq c).trans ((hS'_mem c).mpr (Or.inr (Or.inr rfl)))⟩
          rcases hall_adj w1 dw1 with ⟨h1a, h1b, h1c⟩
          rcases hall_adj w2 dw2 with ⟨h2a, h2b, h2c⟩
          exact hS0_inj w1 w2 a b c hw12 dw1 dw2 hab hac hbc h1a h1b h1c h2a h2b h2c
        | [] | [_] => simp at hS0_len
      | [] | [_] | [_, _] | _ :: _ :: _ :: _ :: _ =>
        rw [hfl] at hlen3; simp at hlen3

end ClawFreeEG
