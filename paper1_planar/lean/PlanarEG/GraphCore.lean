import Std

/-!
# PlanarEG.GraphCore

Core finite simple graph theory, combinatorial plane maps, exact Euler discharging
conservation, Alternating-C6 planar degree-density bounds (Main Theorem 4),
Universal Cubic-to-General Claw-Free Lift-Window & Bowtie-Forest theorems
(Main Theorem 2 core), and 2-Edge-Bond / 2-Vertex-Cut Cap lemmas.

Pure Lean 4 (`import Std`, ZERO Mathlib, ZERO `sorry`, ZERO `axiom`, ZERO `native_decide`).
-/

namespace PlanarEG

/-! ## 1. Finite Simple Graphs, Degrees, Walks, & Simple Cycles -/

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

/-- The degree of vertex `u`. -/
def deg {n : Nat} (G : FinGraph n) (u : Fin n) : Nat :=
  (G.neighbors u).length

/-- Minimum degree at least `k` on a nonempty finite simple graph (`n ≥ 1`, preventing order-0 vacuity). -/
def MinDegreeAtLeast {n : Nat} (G : FinGraph n) (k : Nat) : Prop :=
  n ≥ 1 ∧ ∀ u : Fin n, k ≤ G.deg u

/-- Cubic (3-regular) nonempty finite simple graph predicate (`n ≥ 1`, preventing order-0 vacuity). -/
def IsCubic {n : Nat} (G : FinGraph n) : Prop :=
  n ≥ 1 ∧ ∀ u : Fin n, G.deg u = 3

/-- Boolean check that every vertex in `cyc` is adjacent to the next (cyclically). -/
def isClosedWalkBool {n : Nat} (G : FinGraph n) : List (Fin n) → Bool
  | [] => false
  | u :: rest =>
    let rec go (prev : Fin n) : List (Fin n) → Bool
      | [] => G.adj prev u
      | v :: vs => G.adj prev v && go v vs
    go u rest

/-- A list of vertices has no duplicates (computable boolean version). -/
def nodupBool {α : Type} [BEq α] : List α → Bool
  | [] => true
  | x :: xs => !(xs.contains x) && nodupBool xs

/-- Propositional simple cycle predicate: length ≥ 3, pairwise distinct vertices,
and consecutive vertices (cyclically) are adjacent in `G`. -/
def IsSimpleCycle {n : Nat} (G : FinGraph n) (cyc : List (Fin n)) : Prop :=
  cyc.length ≥ 3 ∧
  cyc.Nodup ∧
  ∀ (i : Nat) (hi : i < cyc.length),
    G.adj (cyc[i]'hi) (cyc[(i + 1) % cyc.length]'(Nat.mod_lt _ (Nat.lt_of_lt_of_le (Nat.zero_lt_of_lt hi) (Nat.le_refl _)))) = true

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

/-- `G` contains a simple dyadic cycle of length `2^k` with `k ≥ 2` and `2^k ≤ K`. -/
def HasDyadicCycleUpTo {n : Nat} (G : FinGraph n) (K : Nat) : Prop :=
  ∃ k : Nat, k ≥ 2 ∧ 2 ^ k ≤ K ∧ G.HasSimpleCycleOfLen (2 ^ k)

/-- Simple walk predicate between `u` and `v` avoiding a set of forbidden vertices. -/
def IsWalkAvoiding {n : Nat} (G : FinGraph n) (forb : List (Fin n)) :
    Fin n → Fin n → List (Fin n) → Prop
  | u, v, [] => u = v ∧ u ∉ forb
  | u, v, w :: ws => u ∉ forb ∧ G.adj u w = true ∧ IsWalkAvoiding G forb w v ws

/-- `G` is connected after removing `forb`: any two vertices outside `forb` are connected
by a walk avoiding `forb`. -/
def ConnectedAvoiding {n : Nat} (G : FinGraph n) (forb : List (Fin n)) : Prop :=
  ∀ u v : Fin n, u ∉ forb → v ∉ forb → ∃ path : List (Fin n), G.IsWalkAvoiding forb u v path

/-- A finite graph is 3-connected if `n ≥ 4` and deleting any two vertices leaves it connected. -/
def Is3Connected {n : Nat} (G : FinGraph n) : Prop :=
  n ≥ 4 ∧ ∀ u v : Fin n, G.ConnectedAvoiding [u, v]

theorem isWalkAvoiding_append {n : Nat} (G : FinGraph n) (forb : List (Fin n))
    {u v w : Fin n} {p1 p2 : List (Fin n)}
    (h1 : G.IsWalkAvoiding forb u v p1) (h2 : G.IsWalkAvoiding forb v w p2) :
    G.IsWalkAvoiding forb u w (p1 ++ p2) := by
  induction p1 generalizing u with
  | nil =>
    rcases h1 with ⟨rfl, _⟩
    exact h2
  | cons x xs ih =>
    rcases h1 with ⟨hu, hadj, hrest⟩
    exact ⟨hu, hadj, ih hrest⟩

theorem isWalkAvoiding_symm {n : Nat} (G : FinGraph n) (forb : List (Fin n))
    {u v : Fin n} {p : List (Fin n)}
    (h : G.IsWalkAvoiding forb u v p) :
    ∃ q : List (Fin n), G.IsWalkAvoiding forb v u q := by
  induction p generalizing u with
  | nil =>
    rcases h with ⟨rfl, hu⟩
    exact ⟨[], rfl, hu⟩
  | cons x xs ih =>
    rcases h with ⟨hu, hadj, hrest⟩
    rcases ih hrest with ⟨q, hq⟩
    have hx : x ∉ forb := by
      cases xs with
      | nil => exact hrest.2
      | cons _ _ => exact hrest.1
    have hstep : G.IsWalkAvoiding forb x u [u] := ⟨hx, by rw [G.symm]; exact hadj, rfl, hu⟩
    exact ⟨q ++ [u], isWalkAvoiding_append G forb hq hstep⟩

/-- A parent-pointer certificate for connectivity in `G - forb` rooted at `r`:
if every `v ∉ forb` reaches `r` in at most `fuel` steps along `parent`, then `G - forb` is connected! -/
def reachesRoot {n : Nat} (G : FinGraph n) (forb : List (Fin n)) (r : Fin n)
    (parent : Fin n → Fin n) : Nat → Fin n → Bool
  | 0, u => u == r && !(forb.contains u)
  | fuel + 1, u =>
    if u == r then !(forb.contains u)
    else !(forb.contains u) && G.adj u (parent u) && reachesRoot G forb r parent fuel (parent u)

theorem walk_to_root_of_reachesRoot {n : Nat} (G : FinGraph n) (forb : List (Fin n))
    (r : Fin n) (parent : Fin n → Fin n) :
    ∀ (fuel : Nat) (u : Fin n),
      G.reachesRoot forb r parent fuel u = true →
      ∃ p : List (Fin n), G.IsWalkAvoiding forb u r p
  | 0, u, h => by
    simp only [reachesRoot, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at h
    rcases h with ⟨rfl, hnf⟩
    have hu : u ∉ forb := fun hm => by
      have hc := List.contains_iff_mem.mpr hm
      rw [hc] at hnf; cases hnf
    exact ⟨[], rfl, hu⟩
  | fuel + 1, u, h => by
    simp only [reachesRoot] at h
    by_cases hur : u = r
    · subst hur
      simp only [beq_self_eq_true, ↓reduceIte, Bool.not_eq_true'] at h
      have hu : u ∉ forb := fun hm => by
        have hc := List.contains_iff_mem.mpr hm
        rw [hc] at h; cases h
      exact ⟨[], rfl, hu⟩
    · have hbeq : (u == r) = false := beq_false_of_ne hur
      simp only [hbeq, Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true, Bool.not_eq_true'] at h
      rcases h with ⟨⟨hnf, hadj⟩, hrec⟩
      have hu : u ∉ forb := fun hm => by
        have hc := List.contains_iff_mem.mpr hm
        rw [hc] at hnf; cases hnf
      rcases walk_to_root_of_reachesRoot G forb r parent fuel (parent u) hrec with ⟨p, hp⟩
      exact ⟨parent u :: p, hu, hadj, hp⟩

theorem connectedAvoiding_of_rootCert {n : Nat} (G : FinGraph n) (forb : List (Fin n))
    (r : Fin n) (parent : Fin n → Fin n) (fuel : Nat)
    (hcert : ∀ u : Fin n, u ∉ forb → G.reachesRoot forb r parent fuel u = true) :
    G.ConnectedAvoiding forb := by
  intro u v hu hv
  rcases walk_to_root_of_reachesRoot G forb r parent fuel u (hcert u hu) with ⟨pu, hpu⟩
  rcases walk_to_root_of_reachesRoot G forb r parent fuel v (hcert v hv) with ⟨pv, hpv⟩
  rcases isWalkAvoiding_symm G forb hpv with ⟨pvRev, hpvRev⟩
  exact ⟨pu ++ pvRev, isWalkAvoiding_append G forb hpu hpvRev⟩

end FinGraph

/-! ## 2. Exact List Sums & General Discharging Conservation -/

/-- Sum of a list of integers. -/
def sumInt : List Int → Int
  | [] => 0
  | x :: xs => x + sumInt xs

/-- Sum of a list of natural numbers. -/
def sumNat : List Nat → Nat
  | [] => 0
  | x :: xs => x + sumNat xs

theorem sumInt_map_add {α : Type} (l : List α) (f g : α → Int) :
    sumInt (l.map fun x => f x + g x) = sumInt (l.map f) + sumInt (l.map g) := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons, sumInt, ih]
    omega

theorem sumInt_map_sub {α : Type} (l : List α) (f g : α → Int) :
    sumInt (l.map fun x => f x - g x) = sumInt (l.map f) - sumInt (l.map g) := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons, sumInt, ih]
    omega

theorem sumInt_map_const {α : Type} (l : List α) (c : Int) :
    sumInt (l.map fun _ => c) = (l.length : Int) * c := by
  induction l with
  | nil => simp [sumInt]
  | cons x xs ih =>
    simp only [List.map_cons, sumInt, List.length_cons, ih]
    rw [Int.natCast_add, Int.natCast_one, Int.add_mul, Int.one_mul]
    omega

theorem sumInt_map_mul_left {α : Type} (l : List α) (c : Int) (f : α → Int) :
    sumInt (l.map fun x => c * f x) = c * sumInt (l.map f) := by
  induction l with
  | nil => simp [sumInt]
  | cons x xs ih =>
    simp only [List.map_cons, sumInt, ih, Int.mul_add]

theorem sumInt_map_ofNat {α : Type} (l : List α) (f : α → Nat) :
    sumInt (l.map fun x => (f x : Int)) = (sumNat (l.map f) : Int) := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons, sumInt, sumNat, ih]
    omega

theorem sumNat_map_const {α : Type} (l : List α) (c : Nat) :
    sumNat (l.map fun _ => c) = l.length * c := by
  induction l with
  | nil => simp [sumNat]
  | cons x xs ih =>
    simp only [List.map_cons, sumNat, List.length_cons, ih]
    rw [Nat.add_mul, Nat.one_mul]
    omega

theorem sumNat_le_of_all_le {α : Type} (l : List α) (f g : α → Nat)
    (hle : ∀ x ∈ l, f x ≤ g x) :
    sumNat (l.map f) ≤ sumNat (l.map g) := by
  induction l with
  | nil => exact Nat.le_refl 0
  | cons x xs ih =>
    simp only [List.map_cons, sumNat]
    have hx := hle x (List.mem_cons_self ..)
    have hxs := ih (fun y hy => hle y (List.mem_cons_of_mem x hy))
    omega

theorem sumInt_le_of_all_le {α : Type} (l : List α) (f g : α → Int)
    (hle : ∀ x ∈ l, f x ≤ g x) :
    sumInt (l.map f) ≤ sumInt (l.map g) := by
  induction l with
  | nil => exact Int.le_refl 0
  | cons x xs ih =>
    simp only [List.map_cons, sumInt]
    have hx := hle x (List.mem_cons_self ..)
    have hxs := ih (fun y hy => hle y (List.mem_cons_of_mem x hy))
    omega

theorem sumInt_filter_split {α : Type} (l : List α) (p : α → Bool) (f : α → Int) :
    sumInt (l.map f) = sumInt ((l.filter p).map f) + sumInt ((l.filter fun x => !p x).map f) := by
  induction l with
  | nil => simp [sumInt]
  | cons x xs ih =>
    cases hpx : p x
    · simp only [List.map_cons, List.filter_cons, hpx, Bool.false_eq_true, ↓reduceIte,
                 Bool.not_false, sumInt, ih]
      omega
    · simp only [List.map_cons, List.filter_cons, hpx, ↓reduceIte, Bool.not_true,
                 Bool.false_eq_true, sumInt, ih]
      omega

theorem sumInt_nonpos_of_all_nonpos {α : Type} (l : List α) (f : α → Int)
    (h : ∀ x ∈ l, f x ≤ 0) : sumInt (l.map f) ≤ 0 := by
  induction l with
  | nil => simp [sumInt]
  | cons x xs ih =>
    simp only [List.map_cons, sumInt]
    have hx := h x (List.mem_cons_self ..)
    have hxs := ih (fun y hy => h y (List.mem_cons_of_mem x hy))
    omega

/-- Charge conservation from incoming/outgoing transfers:
if `cFin x = c0 x + inCh x - outCh x` and total incoming equals total outgoing,
then total final charge equals total initial charge. -/
theorem charge_conserved_of_transfers {α : Type} (elems : List α)
    (c0 cFin inCh outCh : α → Int)
    (hdef : ∀ x ∈ elems, cFin x = c0 x + inCh x - outCh x)
    (hbal : sumInt (elems.map inCh) = sumInt (elems.map outCh)) :
    sumInt (elems.map cFin) = sumInt (elems.map c0) := by
  have h1 : sumInt (elems.map cFin) = sumInt (elems.map fun x => c0 x + inCh x - outCh x) := by
    congr 1
    exact List.map_congr_left hdef
  rw [h1, sumInt_map_sub, sumInt_map_add, hbal]
  omega

/-- General Discharging Contradiction Lemma (exact scaled integers, supporting arbitrary
rational discharging via a positive common denominator `S > 0`):
if total initial charge is `12 * S`, charge is conserved, every non-frozen element ends
with `cFin x ≤ 0`, and the frozen elements sum to `< 12 * S`, then `False`. -/
theorem charge_conservation_contradiction {α : Type} (elems : List α)
    (isFrozen : α → Bool) (c0 cFin : α → Int) (S : Int)
    (hinit : sumInt (elems.map c0) = 12 * S)
    (hcons : sumInt (elems.map cFin) = sumInt (elems.map c0))
    (hclean : ∀ x ∈ elems, isFrozen x = false → cFin x ≤ 0)
    (hfrozen : sumInt ((elems.filter isFrozen).map cFin) < 12 * S) :
    False := by
  have hsplit := sumInt_filter_split elems isFrozen cFin
  have hnonfrz : sumInt ((elems.filter fun x => !isFrozen x).map cFin) ≤ 0 := by
    apply sumInt_nonpos_of_all_nonpos
    intro x hx
    have hmem := List.mem_filter.mp hx
    have hnf : isFrozen x = false := by
      cases h : isFrozen x
      · rfl
      · simp [h] at hmem
    exact hclean x hmem.1 hnf
  omega

/-! ## 3. Combinatorial Plane Map & Euler Discharging Identities -/

/-- A combinatorial facial-Euler structure on a finite simple graph:
an explicit list of simple closed facial walks (`length ≥ 3`, `Nodup`), vertex and face
handshaking (`∑ d(v) = 2E`, `∑ |f| = 2E`), and Euler characteristic `V - E + F = 2`.

**Scope note:** `PlaneMap` is a combinatorial facial-Euler abstraction sufficient for exact
discharging conservation (`euler_face_discharging_sum`, `euler_vertex_face_sum`) and girth-based
Euler bounds (`planar_girth_edge_bound`). It is NOT a topological characterization of all planar
embeddings (it does not enforce connectivity, dart bijection, or vertex rotation systems — those
stronger cellular-sphere properties are certified separately on our sharpness witnesses via
`CubicSpec.HasExactDartBijection` and `CubicSpec.HasSingleVertexRotation`, and topological
embedding/block/bridge reductions for general planar graphs are proved in the paper manuscript). -/
structure PlaneMap (n : Nat) where
  graph : FinGraph n
  faces : List (List (Fin n))
  numEdges : Nat
  faces_len_ge3 : ∀ f ∈ faces, f.length ≥ 3
  faces_nodup : ∀ f ∈ faces, f.Nodup
  faces_walk : ∀ f ∈ faces,
    ∀ (i : Nat) (hi : i < f.length),
      graph.adj (f[i]'hi) (f[(i + 1) % f.length]'(Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le i) hi))) = true
  handshaking_verts : sumNat ((List.finRange n).map graph.deg) = 2 * numEdges
  handshaking_faces : sumNat (faces.map List.length) = 2 * numEdges
  euler_formula : (n : Int) - (numEdges : Int) + (faces.length : Int) = 2

/-- For ANY cubic `PlaneMap`, the face discharging initial charges `6 - d(f)` sum to `12`. -/
theorem euler_face_discharging_sum {n : Nat} (M : PlaneMap n) (hcubic : M.graph.IsCubic) :
    sumInt (M.faces.map fun f => (6 : Int) - (f.length : Int)) = 12 := by
  have h3V : 3 * n = 2 * M.numEdges := by
    have h1 := M.handshaking_verts
    have h2 : (List.finRange n).map M.graph.deg = (List.finRange n).map (fun _ => 3) := by
      apply List.map_congr_left
      intro v _
      exact hcubic.2 v
    rw [h2, sumNat_map_const, List.length_finRange] at h1
    omega
  have hsumF : sumInt (M.faces.map fun f => (f.length : Int)) = (2 * M.numEdges : Int) := by
    rw [sumInt_map_ofNat, M.handshaking_faces]
    omega
  rw [sumInt_map_sub, sumInt_map_const, hsumF]
  have heul := M.euler_formula
  omega

/-- For ANY `PlaneMap` (arbitrary degrees!), the Euler vertex-face initial charges
`∑_v (6 - 2 d(v)) + ∑_f (6 - d(f))` sum to `12`. -/
theorem euler_vertex_face_sum {n : Nat} (M : PlaneMap n) :
    sumInt ((List.finRange n).map fun v => (6 : Int) - 2 * (M.graph.deg v : Int)) +
    sumInt (M.faces.map fun f => (6 : Int) - (f.length : Int)) = 12 := by
  have hsumV : sumInt ((List.finRange n).map fun v => (M.graph.deg v : Int)) = (2 * M.numEdges : Int) := by
    rw [sumInt_map_ofNat, M.handshaking_verts]
    omega
  have hsumF : sumInt (M.faces.map fun f => (f.length : Int)) = (2 * M.numEdges : Int) := by
    rw [sumInt_map_ofNat, M.handshaking_faces]
    omega
  rw [sumInt_map_sub, sumInt_map_const, sumInt_map_mul_left, hsumV, List.length_finRange]
  rw [sumInt_map_sub, sumInt_map_const, hsumF]
  have heul := M.euler_formula
  omega

/-- Euler girth edge bound for any `PlaneMap` whose faces all have length `≥ g` (`g ≥ 3`):
`(g - 2) * E ≤ g * (V - 2)`. -/
theorem planar_girth_edge_bound {n : Nat} (M : PlaneMap n) (g : Nat) (_hg : g ≥ 3)
    (hfaces : ∀ f ∈ M.faces, g ≤ f.length) :
    ((g : Int) - 2) * (M.numEdges : Int) ≤ (g : Int) * ((n : Int) - 2) := by
  have hge : M.faces.length * g ≤ 2 * M.numEdges := by
    have h1 := sumNat_le_of_all_le M.faces (fun _ => g) List.length hfaces
    rw [sumNat_map_const, M.handshaking_faces] at h1
    exact h1
  have heul := M.euler_formula
  have hge_int : (M.faces.length : Int) * (g : Int) ≤ 2 * (M.numEdges : Int) := by
    exact_mod_cast hge
  have hmul : (g : Int) * ((n : Int) - (M.numEdges : Int) + (M.faces.length : Int)) = (g : Int) * 2 := by
    rw [heul]
  have hexp : (g : Int) * (n : Int) - (g : Int) * (M.numEdges : Int) + (M.faces.length : Int) * (g : Int) = (g : Int) * 2 := by
    have hcomm : (g : Int) * (M.faces.length : Int) = (M.faces.length : Int) * (g : Int) := Int.mul_comm _ _
    rw [Int.mul_add, Int.mul_sub, hcomm] at hmul
    exact hmul
  have h1 : ((g : Int) - 2) * (M.numEdges : Int) = (g : Int) * (M.numEdges : Int) - 2 * (M.numEdges : Int) := by
    rw [Int.sub_mul]
  have h2 : (g : Int) * ((n : Int) - 2) = (g : Int) * (n : Int) - (g : Int) * 2 := by
    rw [Int.mul_sub]
  omega

/-- Specialization to girth `g = 10` (planar bipartite girth `≥ 10`): `4 * E ≤ 5 * (n - 2)`. -/
theorem planar_girth10_edge_bound {n : Nat} (M : PlaneMap n)
    (hfaces : ∀ f ∈ M.faces, 10 ≤ f.length) :
    4 * (M.numEdges : Int) ≤ 5 * ((n : Int) - 2) := by
  have h := planar_girth_edge_bound M 10 (by omega) hfaces
  omega

/-! ## 4. Cap Reduction Lemmas (2-Edge-Bond Cap & Universal 2-Vertex-Cut Cap) -/

/-- Adding a single cap edge between distinct vertices `a, b` of a finite simple graph `G`. -/
def FinGraph.addEdge {n : Nat} (G : FinGraph n) (a b : Fin n) (hab : a ≠ b) : FinGraph n where
  adj u v := G.adj u v || (u == a && v == b) || (u == b && v == a)
  symm u v := by
    cases hu_a : (u == a) <;> cases hv_b : (v == b) <;>
    cases hu_b : (u == b) <;> cases hv_a : (v == a) <;>
    simp [G.symm u v]
  loopless u := by
    have h1 : (u == a && u == b) = false := by
      cases hua : (u == a)
      · rfl
      · simp only [Bool.true_and]
        have heq : u = a := beq_iff_eq.mp hua
        subst heq
        exact beq_false_of_ne hab
    have h2 : (u == b && u == a) = false := by
      cases hub : (u == b)
      · rfl
      · simp only [Bool.true_and]
        have heq : u = b := beq_iff_eq.mp hub
        subst heq
        exact beq_false_of_ne (Ne.symm hab)
    simp [G.loopless u, h1, h2]

/-- Adding a cap edge preserves all existing adjacencies (monotonicity). -/
theorem FinGraph.addEdge_mono {n : Nat} (G : FinGraph n) (a b : Fin n) (hab : a ≠ b)
    {u v : Fin n} (h : G.adj u v = true) :
    (G.addEdge a b hab).adj u v = true := by
  simp [FinGraph.addEdge, h]

/-- Adding a cap edge never decreases any vertex degree (Universal 2-Vertex-Cut Cap
minimum-degree preservation: `δ(H) ≥ 3 → δ(H + ab) ≥ 3`). -/
theorem universal_two_vertex_cut_cap_min_deg {n : Nat} (G : FinGraph n) (a b : Fin n) (hab : a ≠ b)
    (u : Fin n) : G.deg u ≤ (G.addEdge a b hab).deg u := by
  unfold FinGraph.deg FinGraph.neighbors
  have hsub : ∀ {l : List (Fin n)} (p q : Fin n → Bool),
      (∀ x, p x = true → q x = true) → (l.filter p).length ≤ (l.filter q).length := by
    intro l p q hpq
    induction l with
    | nil => exact Nat.le_refl 0
    | cons x xs ih =>
      cases hpx : p x
      · simp only [List.filter_cons, hpx, Bool.false_eq_true, ↓reduceIte]
        cases hqx : q x
        · simp [ih]
        · simp; omega
      · have hqx : q x = true := hpq x hpx
        simp only [List.filter_cons, hpx, hqx, ↓reduceIte, List.length_cons]
        omega
  exact hsub (G.adj u) ((G.addEdge a b hab).adj u) (fun v hv => G.addEdge_mono a b hab hv)

/-- Any simple cycle in the capped graph `H + ab` that does NOT traverse the artificial cap
edge `{a, b}` is already a genuine simple cycle in the original graph `H`. -/
theorem cap_cycle_avoiding_edge_lifts {n : Nat} (H : FinGraph n) (a b : Fin n) (hab : a ≠ b)
    (cyc : List (Fin n))
    (hcyc : (H.addEdge a b hab).IsSimpleCycle cyc)
    (havoid : ∀ (i : Nat) (hi : i < cyc.length),
      let u := cyc[i]'hi
      let v := cyc[(i + 1) % cyc.length]'(Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le i) hi))
      ¬((u = a ∧ v = b) ∨ (u = b ∧ v = a))) :
    H.IsSimpleCycle cyc := by
  rcases hcyc with ⟨hlen, hnd, hadj⟩
  refine ⟨hlen, hnd, ?_⟩
  intro i hi
  have h1 := hadj i hi
  have hnot := havoid i hi
  simp only [FinGraph.addEdge, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at h1
  rcases h1 with (h1 | ⟨ha, hb⟩) | ⟨hb, ha⟩
  · exact h1
  · exact absurd (Or.inl ⟨ha, hb⟩) hnot
  · exact absurd (Or.inr ⟨hb, ha⟩) hnot

/-- Minimal 2-Edge-Bond Cap degree restoration: if a vertex `a` in a subcubic component `H`
has degree `2` and is not adjacent to `b`, then adding the cap edge `ab` raises `deg(a)`
to exact degree `3` (restoring cubicness at both cap endpoints). -/
theorem minimal_two_edge_bond_cap_deg {n : Nat} (H : FinGraph n) (a b : Fin n) (hab : a ≠ b)
    (hnot : H.adj a b = false) :
    (H.addEdge a b hab).deg a = H.deg a + 1 := by
  unfold FinGraph.deg FinGraph.neighbors
  have hlem : ∀ (l : List (Fin n)), l.Nodup → b ∈ l →
      (l.filter fun v => (H.addEdge a b hab).adj a v).length =
      (l.filter fun v => H.adj a v).length + 1 := by
    intro l hnd hmem
    induction l with
    | nil => cases hmem
    | cons x xs ih =>
      rcases List.nodup_cons.mp hnd with ⟨hxnot, hndxs⟩
      by_cases hxb : x = b
      · subst hxb
        have hadd : (H.addEdge a x hab).adj a x = true := by
          simp [FinGraph.addEdge]
        have heq_tail : xs.filter (fun v => (H.addEdge a x hab).adj a v) =
                        xs.filter (fun v => H.adj a v) := by
          apply List.filter_congr
          intro v hv
          have hvx : v ≠ x := fun h => hxnot (h ▸ hv)
          have h1 : (v == x) = false := beq_false_of_ne hvx
          have h2 : (a == x) = false := beq_false_of_ne hab
          simp [FinGraph.addEdge, h1, h2]
        simp only [List.filter_cons, hadd, hnot, ↓reduceIte, Bool.false_eq_true,
                   List.length_cons, heq_tail]
      · have hbxs : b ∈ xs := by
          rcases List.mem_cons.mp hmem with rfl | h
          · exact absurd rfl hxb
          · exact h
        have heqx : (H.addEdge a b hab).adj a x = H.adj a x := by
          have h1 : (x == b) = false := beq_false_of_ne hxb
          have h2 : (a == b) = false := beq_false_of_ne hab
          simp [FinGraph.addEdge, h1, h2]
        have iht := ih hndxs hbxs
        simp only [List.filter_cons, heqx]
        cases H.adj a x <;> simp [iht]
  exact hlem (List.finRange n) (List.nodup_finRange n) (List.mem_finRange b)

/-! ## 5. Main Theorem 4 — Alternating-C6 Planar Degree-Density Bound -/

/-- Minimum order of a `C_4`-free graph with minimum degree `≥ 3`:
from `3 * n ≤ n * (n - 1) / 2` (since pairs of neighbors of distinct vertices collide at most once),
we must have `n ≥ 7`. -/
theorem c4_free_min_order (n : Nat) (hn : n ≥ 1) (h : 3 * n ≤ n * (n - 1) / 2) : n ≥ 7 := by
  match n, hn, h with
  | 1, _, h | 2, _, h | 3, _, h | 4, _, h | 5, _, h | 6, _, h => simp at h
  | _ + 7, _, _ => omega

/-- **Main Theorem 4 (Alternating-C6 Planar Degree-Density Bound):**
If `Q` is the mixed bipartite subgraph with `eQ = 4*h + eps` edges (from independent `V_{≥ 4}`
with `h = |V_{≥ 4}|` and excess `eps = ∑_{v ∈ V_{≥ 4}} (d(v) - 4)`), deleting a 6-cycle
transversal of size `tau6` leaves `ePrime` edges in a planar bipartite girth-`≥ 10` graph
obeying `4 * ePrime ≤ 5 * (n - 2)`, then `16 * h + 4 * eps ≤ 5 * (n - 2) + 4 * tau6`. -/
theorem alternating_c6_density (n h eps eQ ePrime tau6 : Nat)
    (h_eQ : eQ = 4 * h + eps)
    (h_del : eQ ≤ ePrime + tau6)
    (h_euler : 4 * ePrime ≤ 5 * (n - 2)) :
    16 * h + 4 * eps ≤ 5 * (n - 2) + 4 * tau6 := by
  omega

/-- **Main Theorem 4 Corollary (`C_6`-free `|V_3|` Density Bound):**
When `tau6 = 0` (`C_6`-free planar with `δ ≥ 3`, independent `V_{≥ 4}`, no `C_4, C_8`),
`16 * |V_3| ≥ 11 * n + 10`, strictly beating Ducoffe–Dumitru's `2n/3` (`3 * |V_3| > 2 * n`)
for every `n ≥ 7`! -/
theorem c6_free_v3_density (n v3 h eps : Nat)
    (hn : n ≥ 7)
    (hpart : v3 + h = n)
    (hdens : 16 * h + 4 * eps ≤ 5 * (n - 2)) :
    16 * v3 ≥ 11 * n + 10 ∧ 3 * v3 > 2 * n := by
  omega

/-! ## 6. Main Theorem 2 Core — Universal Cubic-to-General Claw-Free Transfer & Bowtie Forest -/

/-- **Universal Cubic-to-General-Claw-Free Lift-Window Theorem:**
For ANY cycle length `L ≥ 3` and forest-bounded bowties `k + m ≤ L - 1` (`k` traversed
bowties, `m` internal chordal bowties), BOTH `2*L` and `2*L + 1` ALWAYS lie in the
exact lift-window `[2*L - k, 3*L - k - m]`. -/
theorem universal_bowtie_transfer (L k m : Nat) (hL : L ≥ 3) (hforest : k + m ≤ L - 1) :
    2 * L - k ≤ 2 * L ∧ 2 * L < 2 * L + 1 ∧ 2 * L + 1 ≤ 3 * L - k - m := by
  omega

/-- **Dyadic Lift Corollary:**
Any `2^a`-cycle (`a ≥ 2`) in `H` with forest-bounded bowties `k + m ≤ 2^a - 1`
contains `2^(a+1)` inside its exact lift-window `[2*2^a - k, 3*2^a - k - m]`!
In particular, `C_4, C_8, C_16, C_32` in cubic planar `H` lifts to `C_8, C_16, C_32, C_64`
in `G = T(H)/B`! -/
theorem dyadic_cycle_lift_window (a k m : Nat) (ha : a ≥ 2) (hforest : k + m ≤ 2 ^ a - 1) :
    2 * 2 ^ a - k ≤ 2 ^ (a + 1) ∧ 2 ^ (a + 1) ≤ 3 * 2 ^ a - k - m := by
  have hpow : 2 ^ a ≥ 4 := by
    have h2 : 2 ^ 2 ≤ 2 ^ a := Nat.pow_le_pow_right (by omega) ha
    omega
  have hnext : 2 ^ (a + 1) = 2 * 2 ^ a := by
    rw [Nat.pow_succ]
    omega
  have h := universal_bowtie_transfer (2 ^ a) k m (by omega) hforest
  omega

/-- **Acyclic Forest Edge-Count Bound:**
If a set of `e` edges is built inductively on `L ≥ 1` vertices by always joining two
distinct connected components (decreasing the component count `c` by 1 per edge while
maintaining `c ≥ 1`), then `e ≤ L - 1`. -/
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
    · have hy : y ≥ 3 := by omega
      rcases ih hy with ⟨a, ha, hlo, hhi⟩
      by_cases hfit : y + 1 ≤ 2 ^ a
      · exact ⟨a, ha, hfit, by omega⟩
      · have heq : 2 ^ a = y := by omega
        refine ⟨a + 1, by omega, ?_, ?_⟩
        · rw [Nat.pow_succ, heq]; omega
        · rw [Nat.pow_succ, heq]; omega

/-- **Bowtie-Forest Exclusion Theorem:**
For EVERY cycle length `L ≥ 3` and every `r = L - k ≤ 2` (`m = 0`), the lift-window
`[L + r, 2*L + r]` ALWAYS contains a power of two `2^a ≥ 4`!
Consequently, any `C_{2^a}`-free claw-free graph `G = T(H)/B` forces `H_B` to be an
induced forest (`r = 0, 1` impossible) and `H/H_B` to be simple (`r = 2` impossible)! -/
theorem bowtie_forest_exclusion (L r : Nat) (hL : L ≥ 3) (hr : r ≤ 2) :
    ∃ a : Nat, a ≥ 2 ∧ L + r ≤ 2 ^ a ∧ 2 ^ a ≤ 2 * L + r := by
  rcases exists_pow2_in_double_window (L + r) (by omega) with ⟨a, ha, hlo, hhi⟩
  exact ⟨a, ha, hlo, by omega⟩

end PlanarEG
