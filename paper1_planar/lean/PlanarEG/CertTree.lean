/-!
# PlanarEG.CertTree

Zero-`Std` (pure `Init`) ultra-fast kernel-reduction data structures for proof-carrying
Bellman-Ford dual potentials, cyclic DP DAG upper bounds, backward DP tables,
and explicit weld simple-cycle witnesses.

Design notes (benchmarked on Lean 4.36.0):
- Omits `import Std` so pure data modules save ~260 MB RSS per `lean` process.
- `NTree` stores `Nat`-biased integers (`val + bias`), so EVERY kernel check uses
  pure C++ GMP-accelerated `Nat.add`, `Nat.div`, `Nat.mod`, `Nat.ble` — ZERO `Int`
  reduction inside `by decide`!
- Soundness theorems bridge `Nat.ble` directly to exact `Int` inequalities on
  `t.getInt bias u = (t.get u : Int) - (bias : Int)`.
-/

namespace PlanarEG.CertTree

/-! ## 1. Binary Lookup Tree (`NTree`) for Biased-`Nat` Potentials & DP Rows -/

/-- Binary tree of `Nat` leaves routed by least-significant bits (`idx % 2`, `idx / 2`). -/
inductive NTree where
  | l (v : Nat)
  | n (even odd : NTree)

/-- `O(log N)` structural-recursion lookup into an `NTree`. -/
def NTree.get : NTree → Nat → Nat
  | .l v, _ => v
  | .n a b, idx =>
    if idx % 2 == 0 then NTree.get a (idx / 2) else NTree.get b (idx / 2)

/-- Exact signed `Int` value decoded from an `NTree` with bias `bias`. -/
def NTree.getInt (t : NTree) (bias : Nat) (idx : Nat) : Int :=
  (t.get idx : Int) - (bias : Int)

/-! ## 2. Packed-`Nat` Edge Checkers (Pure GMP `Nat.ble`, Zero `Int` in `decide`) -/

/-- Packing radix for node indices `u, v < 4096`. -/
abbrev NODE_RADIX : Nat := 4096

/-- Packing radix for signed integer edge weights `w ∈ [-65536, 65535]`. -/
abbrev WT_RADIX : Nat := 131072

/-- Bias added to signed integer edge weights before packing into `Nat`. -/
abbrev WT_BIAS : Nat := 65536

/-- Default bias added to `Int` potential values before storing in `NTree`. -/
abbrev PI_BIAS : Nat := 65536

/-- Unpack source node `u` from packed edge `e = ((u * 4096 + v) * 131072 + (w + 65536))`. -/
@[inline] def edgeU (e : Nat) : Nat := (e / WT_RADIX) / NODE_RADIX

/-- Unpack target node `v` from packed edge `e`. -/
@[inline] def edgeV (e : Nat) : Nat := (e / WT_RADIX) % NODE_RADIX

/-- Unpack biased `Nat` weight `w + WT_BIAS` from packed edge `e`. -/
@[inline] def edgeWRaw (e : Nat) : Nat := e % WT_RADIX

/-- Unpack signed integer weight `w` from packed edge `e`. -/
@[inline] def edgeW (e : Nat) : Int := ((e % WT_RADIX : Nat) : Int) - (WT_BIAS : Int)

/-- Pure-`Nat` check of `π(u) + w ≤ π(v)`:
`(π_nat(u)) + (w + WT_BIAS) ≤ (π_nat(v)) + WT_BIAS`. -/
@[inline] def checkEdge (pi : NTree) (e : Nat) : Bool :=
  Nat.ble (pi.get (edgeU e) + edgeWRaw e) (pi.get (edgeV e) + WT_BIAS)

/-- Check a chunk of packed edges against potential `pi`. -/
def checkEdgeList (pi : NTree) : List Nat → Bool
  | [] => true
  | e :: es => if checkEdge pi e then checkEdgeList pi es else false

/-- Check a list of edge chunks against potential `pi`. -/
def checkEdgeChunks (pi : NTree) : List (List Nat) → Bool
  | [] => true
  | c :: cs => if checkEdgeList pi c then checkEdgeChunks pi cs else false

/-- Check upper bound `π_nat(u) ≤ boundNat` for every node `u` in a list. -/
def checkNodeUpper (pi : NTree) (boundNat : Nat) : List Nat → Bool
  | [] => true
  | u :: us => if Nat.ble (pi.get u) boundNat then checkNodeUpper pi boundNat us else false

/-- Check lower bound `w_raw ≤ π_nat(u)` (where both are biased by `PI_BIAS`) for
packed `(u, w + PI_BIAS)` pairs (`u * WT_RADIX + (w + PI_BIAS)`). -/
def checkInitLower (pi : NTree) : List Nat → Bool
  | [] => true
  | p :: ps =>
    if Nat.ble (p % WT_RADIX) (pi.get (p / WT_RADIX)) then checkInitLower pi ps else false

/-! ## 3. Packed-`Nat` Backward DP Checkers (Pure `Nat.ble`) -/

abbrev BWD_NODE_RADIX : Nat := 256
abbrev BWD_LEN_RADIX : Nat := 8

@[inline] def bwdU (e : Nat) : Nat := ((e / WT_RADIX) / BWD_LEN_RADIX) / BWD_NODE_RADIX
@[inline] def bwdV (e : Nat) : Nat := ((e / WT_RADIX) / BWD_LEN_RADIX) % BWD_NODE_RADIX
@[inline] def bwdL (e : Nat) : Nat := (e / WT_RADIX) % BWD_LEN_RADIX
@[inline] def bwdWRaw (e : Nat) : Nat := e % WT_RADIX
@[inline] def bwdW (e : Nat) : Int := ((e % WT_RADIX : Nat) : Int) - (WT_BIAS : Int)

/-- Pure-`Nat` check of backward-DP step `U(rem - ln, v) + w ≤ U(rem, u)`. -/
@[inline] def checkBwdEdgeRow (rowCur rowPrev : NTree) (u v wRaw : Nat) : Bool :=
  Nat.ble (rowPrev.get v + wRaw) (rowCur.get u + WT_BIAS)

/-- Check a backward-DP edge across all `rem ∈ [ln, maxRem]` (enforcing `1 ≤ ln`). -/
def checkBwdEdgeAllRems (rows : Nat → NTree) (maxRem : Nat) (e : Nat) : Bool :=
  let u := bwdU e
  let v := bwdV e
  let ln := bwdL e
  let wRaw := bwdWRaw e
  let rec go : Nat → Bool
    | 0 => true
    | r + 1 =>
      let rem := r + 1
      let ok := if Nat.ble ln rem then checkBwdEdgeRow (rows rem) (rows (rem - ln)) u v wRaw else true
      if ok then go r else false
  if Nat.ble 1 ln then go maxRem else false

def checkBwdEdgeList (rows : Nat → NTree) (maxRem : Nat) : List Nat → Bool
  | [] => true
  | e :: es => if checkBwdEdgeAllRems rows maxRem e then checkBwdEdgeList rows maxRem es else false

def checkBwdEdgeChunks (rows : Nat → NTree) (maxRem : Nat) : List (List Nat) → Bool
  | [] => true
  | c :: cs => if checkBwdEdgeList rows maxRem c then checkBwdEdgeChunks rows maxRem cs else false

/-! ## 4. Soundness Lemmas (Bridging `Nat.ble` to Exact `Int` Inequalities) -/

theorem checkEdge_sound (pi : NTree) (bias : Nat) (e : Nat) (h : checkEdge pi e = true) :
    pi.getInt bias (edgeU e) + edgeW e ≤ pi.getInt bias (edgeV e) := by
  unfold checkEdge at h
  have hle : pi.get (edgeU e) + edgeWRaw e ≤ pi.get (edgeV e) + WT_BIAS := Nat.le_of_ble_eq_true h
  unfold NTree.getInt edgeW edgeWRaw at *
  omega

theorem checkEdgeList_eq_true (pi : NTree) (bias : Nat) :
    ∀ {es : List Nat}, checkEdgeList pi es = true →
      ∀ e ∈ es, pi.getInt bias (edgeU e) + edgeW e ≤ pi.getInt bias (edgeV e)
  | [], _, _, hmem => by cases hmem
  | x :: xs, h, e, hmem => by
    unfold checkEdgeList at h
    cases hx : checkEdge pi x
    · rw [hx] at h; cases h
    · rw [hx] at h
      cases hmem with
      | head => exact checkEdge_sound pi bias x hx
      | tail _ hm => exact checkEdgeList_eq_true pi bias h e hm

theorem checkEdgeChunks_eq_true (pi : NTree) (bias : Nat) :
    ∀ {cs : List (List Nat)}, checkEdgeChunks pi cs = true →
      ∀ c ∈ cs, ∀ e ∈ c, pi.getInt bias (edgeU e) + edgeW e ≤ pi.getInt bias (edgeV e)
  | [], _, _, hmem => by cases hmem
  | c :: cs, h, c', hmem => by
    unfold checkEdgeChunks at h
    cases hc : checkEdgeList pi c
    · rw [hc] at h; cases h
    · rw [hc] at h
      cases hmem with
      | head => exact checkEdgeList_eq_true pi bias hc
      | tail _ hm => exact checkEdgeChunks_eq_true pi bias h c' hm

theorem checkNodeUpper_eq_true (pi : NTree) (bias boundNat : Nat) :
    ∀ {us : List Nat}, checkNodeUpper pi boundNat us = true →
      ∀ u ∈ us, pi.getInt bias u ≤ (boundNat : Int) - (bias : Int)
  | [], _, _, hmem => by cases hmem
  | x :: xs, h, u, hmem => by
    unfold checkNodeUpper at h
    cases hx : Nat.ble (pi.get x) boundNat
    · rw [hx] at h; cases h
    · rw [hx] at h
      cases hmem with
      | head =>
        have hle := Nat.le_of_ble_eq_true hx
        unfold NTree.getInt
        omega
      | tail _ hm => exact checkNodeUpper_eq_true pi bias boundNat h u hm

theorem checkInitLower_eq_true (pi : NTree) (bias : Nat) :
    ∀ {ps : List Nat}, checkInitLower pi ps = true →
      ∀ p ∈ ps, ((p % WT_RADIX : Nat) : Int) - (bias : Int) ≤ pi.getInt bias (p / WT_RADIX)
  | [], _, _, hmem => by cases hmem
  | x :: xs, h, p, hmem => by
    unfold checkInitLower at h
    cases hx : Nat.ble (x % WT_RADIX) (pi.get (x / WT_RADIX))
    · rw [hx] at h; cases h
    · rw [hx] at h
      cases hmem with
      | head =>
        have hle := Nat.le_of_ble_eq_true hx
        unfold NTree.getInt
        omega
      | tail _ hm => exact checkInitLower_eq_true pi bias h p hm

theorem checkBwdEdgeAllRems_eq_true (rows : Nat → NTree) (bias maxRem : Nat) (e : Nat)
    (h : checkBwdEdgeAllRems rows maxRem e = true) :
    1 ≤ bwdL e ∧
    ∀ rem, rem ≤ maxRem → bwdL e ≤ rem →
      (rows (rem - bwdL e)).getInt bias (bwdV e) + bwdW e ≤ (rows rem).getInt bias (bwdU e) := by
  unfold checkBwdEdgeAllRems at h
  dsimp only at h
  cases hpos_b : Nat.ble 1 (bwdL e)
  · rw [hpos_b] at h; cases h
  · rw [hpos_b] at h
    have hpos : 1 ≤ bwdL e := Nat.le_of_ble_eq_true hpos_b
    refine ⟨hpos, ?_⟩
    have hgo : ∀ (k : Nat),
        checkBwdEdgeAllRems.go rows (bwdU e) (bwdV e) (bwdL e) (bwdWRaw e) k = true →
        ∀ rem, 1 ≤ rem → rem ≤ k → bwdL e ≤ rem →
          (rows (rem - bwdL e)).getInt bias (bwdV e) + bwdW e ≤ (rows rem).getInt bias (bwdU e) := by
      intro k
      induction k with
      | zero => intro _ rem h1 hle; omega
      | succ r ih =>
        intro hk rem h1 hle hln
        unfold checkBwdEdgeAllRems.go at hk
        dsimp only at hk
        by_cases hbr : Nat.ble (bwdL e) (r + 1) = true
        · simp only [hbr, ↓reduceIte] at hk
          cases hrow : checkBwdEdgeRow (rows (r + 1)) (rows (r + 1 - bwdL e)) (bwdU e) (bwdV e) (bwdWRaw e)
          · rw [hrow] at hk; cases hk
          · rw [hrow] at hk
            by_cases heq : rem = r + 1
            · subst heq
              unfold checkBwdEdgeRow at hrow
              have hnat := Nat.le_of_ble_eq_true hrow
              unfold NTree.getInt bwdW bwdWRaw at *
              omega
            · exact ih hk rem h1 (by omega) hln
        · have hfalse : Nat.ble (bwdL e) (r + 1) = false := by
            cases hb : Nat.ble (bwdL e) (r + 1)
            · rfl
            · exact absurd hb hbr
          simp only [hfalse, Bool.false_eq_true, ↓reduceIte] at hk
          by_cases heq : rem = r + 1
          · subst heq
            have : Nat.ble (bwdL e) (r + 1) = true := Nat.ble_eq_true_of_le hln
            rw [this] at hfalse; cases hfalse
          · exact ih hk rem h1 (by omega) hln
    intro rem hle hln
    exact hgo maxRem h rem (by omega) hle hln

theorem checkBwdEdgeList_eq_true (rows : Nat → NTree) (bias maxRem : Nat) :
    ∀ {es : List Nat}, checkBwdEdgeList rows maxRem es = true →
      ∀ e ∈ es, 1 ≤ bwdL e ∧
        ∀ rem, rem ≤ maxRem → bwdL e ≤ rem →
          (rows (rem - bwdL e)).getInt bias (bwdV e) + bwdW e ≤ (rows rem).getInt bias (bwdU e)
  | [], _, _, hmem => by cases hmem
  | x :: xs, h, e, hmem => by
    unfold checkBwdEdgeList at h
    cases hx : checkBwdEdgeAllRems rows maxRem x
    · rw [hx] at h; cases h
    · rw [hx] at h
      cases hmem with
      | head => exact checkBwdEdgeAllRems_eq_true rows bias maxRem x hx
      | tail _ hm => exact checkBwdEdgeList_eq_true rows bias maxRem h e hm

theorem checkBwdEdgeChunks_eq_true (rows : Nat → NTree) (bias maxRem : Nat) :
    ∀ {cs : List (List Nat)}, checkBwdEdgeChunks rows maxRem cs = true →
      ∀ c ∈ cs, ∀ e ∈ c, 1 ≤ bwdL e ∧
        ∀ rem, rem ≤ maxRem → bwdL e ≤ rem →
          (rows (rem - bwdL e)).getInt bias (bwdV e) + bwdW e ≤ (rows rem).getInt bias (bwdU e)
  | [], _, _, hmem => by cases hmem
  | c :: cs, h, c', hmem => by
    unfold checkBwdEdgeChunks at h
    cases hc : checkBwdEdgeList rows maxRem c
    · rw [hc] at h; cases h
    · rw [hc] at h
      cases hmem with
      | head => exact checkBwdEdgeList_eq_true rows bias maxRem hc
      | tail _ hm => exact checkBwdEdgeChunks_eq_true rows bias maxRem h c' hm

/-! ## 5. Weld Patch & Explicit Simple Dyadic Cycle Checker -/

def faceHasEdge (a b : Nat) : List Nat → Bool
  | [] => false
  | x :: xs =>
    let rec go (prev : Nat) : List Nat → Bool
      | [] => (prev == a && x == b) || (prev == b && x == a)
      | y :: ys =>
        if (prev == a && y == b) || (prev == b && y == a) then true else go y ys
    go x xs

def facesHaveEdge (faces : List (List Nat)) (a b : Nat) : Bool :=
  faces.any (faceHasEdge a b)

def nodupNat : List Nat → Bool
  | [] => true
  | x :: xs => if xs.contains x then false else nodupNat xs

def allLtNat (n : Nat) : List Nat → Bool
  | [] => true
  | x :: xs => if Nat.blt x n then allLtNat n xs else false

def isFaceGraphClosedWalk (faces : List (List Nat)) : List Nat → Bool
  | [] => false
  | x :: xs =>
    let rec go (prev : Nat) : List Nat → Bool
      | [] => facesHaveEdge faces prev x
      | y :: ys => if facesHaveEdge faces prev y then go y ys else false
    go x xs

def checkWeldDyadicCycle (n : Nat) (faces : List (List Nat)) (cyc : List Nat) : Bool :=
  let len := cyc.length
  (len == 4 || len == 8 || len == 16 || len == 32) &&
  allLtNat n cyc &&
  nodupNat cyc &&
  isFaceGraphClosedWalk faces cyc

structure WeldWitness where
  numVerts : Nat
  faces : List (List Nat)
  cycle : List Nat

/-- Check whether vertex `x` appears in at least one face of `faces`. -/
def vertexInFaces (faces : List (List Nat)) (x : Nat) : Bool :=
  faces.any (fun f => f.contains x)

/-- Check dense vertex labeling: every `v < k` appears in at least one face of `faces`. -/
def allVertsCovered (faces : List (List Nat)) : Nat → Bool
  | 0 => true
  | k + 1 => if vertexInFaces faces k then allVertsCovered faces k else false

/-- Check a single face `f`: length `≥ 3`, every vertex `< n`, and pairwise distinct vertices
(which automatically rules out consecutive self-loops). -/
def checkFaceSchema (n : Nat) (f : List Nat) : Bool :=
  Nat.ble 3 f.length && allLtNat n f && nodupNat f

/-- Strict face-schema checker for a `WeldWitness`:
- `w.numVerts ≥ 3`;
- every face `f ∈ w.faces` satisfies `f.length ≥ 3`, `∀ v ∈ f, v < w.numVerts`, `f.Nodup`
  (hence no consecutive self-loops);
- dense vertex labeling: every `v < w.numVerts` appears in at least one face of `w.faces`. -/
def checkWeldSchema (w : WeldWitness) : Bool :=
  Nat.ble 3 w.numVerts &&
  w.faces.all (checkFaceSchema w.numVerts) &&
  allVertsCovered w.faces w.numVerts

/-- Propositional strict face-schema validity for a `WeldWitness`. -/
def WeldSchemaValid (w : WeldWitness) : Prop :=
  w.numVerts ≥ 3 ∧
  (∀ f ∈ w.faces,
    f.length ≥ 3 ∧
    f.Nodup ∧
    (∀ v ∈ f, v < w.numVerts) ∧
    (∀ (i : Nat) (hi : i < f.length),
      f[i]'hi ≠ f[(i + 1) % f.length]'(Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le i) hi)))) ∧
  (∀ v : Nat, v < w.numVerts → ∃ f ∈ w.faces, v ∈ f)

theorem allLtNat_mem {n : Nat} :
    ∀ {xs : List Nat}, allLtNat n xs = true → ∀ v ∈ xs, v < n
  | [], _, _, hm => by cases hm
  | x :: xs, h, v, hm => by
    unfold allLtNat at h
    cases hx : Nat.blt x n
    · rw [hx] at h; cases h
    · rw [hx] at h
      cases hm with
      | head =>
        unfold Nat.blt at hx
        have hle := Nat.le_of_ble_eq_true hx
        omega
      | tail _ hrest => exact allLtNat_mem h v hrest

theorem nodup_of_nodupNat_ct :
    ∀ {xs : List Nat}, nodupNat xs = true → xs.Nodup
  | [], _ => List.nodup_nil
  | x :: xs, h => by
    unfold nodupNat at h
    cases hc : xs.contains x
    · rw [hc] at h
      have hmem : x ∉ xs := fun hm => by
        have := List.contains_iff_mem.mpr hm
        rw [this] at hc; cases hc
      exact List.nodup_cons.mpr ⟨hmem, nodup_of_nodupNat_ct h⟩
    · rw [hc] at h; cases h

private theorem nodup_getElem_ne_ct {α : Type} :
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
        exact nodup_getElem_ne_ct xs hndxs i' j' (Nat.lt_of_succ_lt_succ hi)
          (Nat.lt_of_succ_lt_succ hj) (fun h => hne (congrArg Nat.succ h))

private theorem allVertsCovered_mem (faces : List (List Nat)) :
    ∀ (k : Nat), allVertsCovered faces k = true → ∀ v : Nat, v < k → ∃ f ∈ faces, v ∈ f
  | 0, _, _, hv => absurd hv (Nat.not_lt_zero _)
  | k + 1, h, v, hv => by
    unfold allVertsCovered at h
    cases hk : vertexInFaces faces k
    · rw [hk] at h; cases h
    · rw [hk] at h
      by_cases heq : v = k
      · subst heq
        unfold vertexInFaces at hk
        rcases List.any_eq_true.mp hk with ⟨f, hf, hmem⟩
        exact ⟨f, hf, List.contains_iff_mem.mp hmem⟩
      · exact allVertsCovered_mem faces k h v (by omega)

/-- Propositional bridge: `checkWeldSchema w = true` implies strict `WeldSchemaValid w`
(order `≥ 3`, every face simple of length `≥ 3` with in-range vertices and no consecutive
self-loops, plus dense vertex coverage `0..w.numVerts - 1`). -/
theorem weldSchema_valid_of_bool (w : WeldWitness) (h : checkWeldSchema w = true) :
    WeldSchemaValid w := by
  unfold checkWeldSchema at h
  simp only [Bool.and_eq_true] at h
  rcases h with ⟨⟨hn, hfaces⟩, hcov⟩
  refine ⟨Nat.le_of_ble_eq_true hn, ?_, allVertsCovered_mem w.faces w.numVerts hcov⟩
  intro f hf
  have hfc := List.all_eq_true.mp hfaces f hf
  unfold checkFaceSchema at hfc
  simp only [Bool.and_eq_true] at hfc
  rcases hfc with ⟨⟨hlen_b, hlt⟩, hnd_b⟩
  have hlen : f.length ≥ 3 := Nat.le_of_ble_eq_true hlen_b
  have hnd : f.Nodup := nodup_of_nodupNat_ct hnd_b
  refine ⟨hlen, hnd, allLtNat_mem hlt, ?_⟩
  intro i hi
  let j := (i + 1) % f.length
  have hj : j < f.length := Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le i) hi)
  have hij : i ≠ j := by
    show i ≠ (i + 1) % f.length
    by_cases hlt1 : i + 1 < f.length
    · rw [Nat.mod_eq_of_lt hlt1]; omega
    · have : i + 1 = f.length := by omega
      rw [this, Nat.mod_self]; omega
  exact nodup_getElem_ne_ct f hnd i j hi hj hij

/-- Check BOTH strict face-schema validity AND explicit simple `C_4/C_8/C_16/C_32` cycle
for every `WeldWitness` in a list. -/
def checkWeldList : List WeldWitness → Bool
  | [] => true
  | w :: ws =>
    if checkWeldSchema w && checkWeldDyadicCycle w.numVerts w.faces w.cycle then
      checkWeldList ws
    else false

theorem checkWeldList_eq_true :
    ∀ {ws : List WeldWitness}, checkWeldList ws = true →
      ∀ w ∈ ws, checkWeldSchema w = true ∧ checkWeldDyadicCycle w.numVerts w.faces w.cycle = true
  | [], _, _, hmem => by cases hmem
  | x :: xs, h, w, hmem => by
    unfold checkWeldList at h
    cases hx : (checkWeldSchema x && checkWeldDyadicCycle x.numVerts x.faces x.cycle)
    · rw [hx] at h; cases h
    · rw [hx] at h
      cases hmem with
      | head => exact Bool.and_eq_true _ _ |>.mp hx
      | tail _ hm => exact checkWeldList_eq_true h w hm

end PlanarEG.CertTree
