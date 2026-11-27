/-!
# ClawFreeEG.Treewidth3Data

Zero-`Std` (pure `Init`) proof-carrying data & certificate module for
`ClawFreeEG.Treewidth3AndBowties`:
1. Direct bounded-instance port-graph adjacency engine (`portAdjConfig`, `rawPortAdj`, `unrelabel`)
   100% isomorphic to `split_quotient` + `expanded_ports` from `cert/verify_clawfree_eg.py`,
   guarded by the explicit well-formedness predicate `splitConfigWellFormed` (symmetric
   duplicate-free loopless incidence rows, split lengths `≤ 3`, valid partners, disjoint
   bowtie pairs, and vertex indices `< 1000`), with kernel verification of ALL `4` `deg3_tri`
   and ALL `128` `K_{2,3}` cycle witnesses (the `2,048` `Q_3 - v^*` witnesses are split evenly
   across `Treewidth3Q3DataA` & `Treewidth3Q3DataB` to keep every module fast and low-RSS).
2. Exact sharp non-planar witness graphs `F_11` (11v, 18e), `H_14` (14v, 3-regular, 3 bowties),
   and `G_39` (39v, 36 deg-3 + 3 independent deg-4 vertices), together with:
   - `F_11` width-3 tree decomposition (`8` bags, `7` tree edges),
   - `G_39` exact equality with `expandedPortGraph f11G39SplitConfig` on all `39 × 39` pairs,
   - `G_39` claw-freeness, degree profile, independent deg-4 vertices, exact `C_16` witness,
   - `G_39` exact absence of `C_4` (326 DFS nodes) and `C_8` (2,138 DFS nodes),
   - Explicit connected vertex-disjoint `K_5`-minor branch sets in BOTH `H_14` and `G_39`.

Omits `import Std` to keep peak RSS low during compilation.
-/

namespace ClawFreeEG.Treewidth3Data

/-! ## 1. Pure-`Init` Bitmask Graph & Direct Bounded-Instance Port-Expansion Engine -/

abbrev SplitChoice := List Nat × Option (List Nat)
abbrev SplitConfig := List SplitChoice

/-- Safe list lookup with default `0`. -/
@[inline] def getNat (xs : List Nat) (i : Nat) : Nat :=
  match xs, i with
  | [], _ => 0
  | x :: _, 0 => x
  | _ :: rest, k + 1 => getNat rest k

/-- Pure-`Nat.beq` membership test (zero `BEq` typeclass overhead in kernel reduction). -/
def memNat (x : Nat) : List Nat → Bool
  | [] => false
  | y :: ys => if Nat.beq x y then true else memNat x ys

/-- Safe `Nat` list duplicate-free check. -/
def nodupNat : List Nat → Bool
  | [] => true
  | x :: xs => if memNat x xs then false else nodupNat xs

/-- Pure-`Nat.blt` bound check `∀ v ∈ xs, v < n`. -/
def allLt (n : Nat) : List Nat → Bool
  | [] => true
  | v :: vs => if Nat.blt v n then allLt n vs else false

/-- Exact bitmask adjacency check (manifestly symmetric and irreflexive). -/
@[inline] def maskAdj (masks : List Nat) (u v : Nat) : Bool :=
  (u != v) && (getNat masks u).testBit v && (getNat masks v).testBit u

/-- Check that `cyc` is a simple cycle in the bitmask graph `(n, masks)` with length `≥ 3`. -/
def checkCycleMasks (n : Nat) (masks : List Nat) (cyc : List Nat) : Bool :=
  let len := cyc.length
  if Nat.blt len 3 then false
  else if !(cyc.all fun v => Nat.blt v n) then false
  else if !(nodupNat cyc) then false
  else
    let rec go (first : Nat) : List Nat → Bool
      | [] => true
      | [last] => maskAdj masks last first
      | a :: b :: rest => if maskAdj masks a b then go first (b :: rest) else false
    match cyc with
    | [] => false
    | first :: _ => go first cyc

/-- Build symmetric loopless bitmask array of length `n` from an undirected edge list (O(n + |E|) depth). -/
def masksFromEdges (n : Nat) (edges : List (Nat × Nat)) : List Nat :=
  (List.range n).map fun u =>
    edges.foldl (fun m (a, b) =>
      if a == u && b != u then m ||| (1 <<< b)
      else if b == u && a != u then m ||| (1 <<< a)
      else m) 0

/-- Build bitmask array directly from a symmetric adjacency list `adj : List (List Nat)` (O(n) depth). -/
def masksFromAdj (adj : List (List Nat)) : List Nat :=
  adj.map fun row => row.foldl (fun m v => m ||| (1 <<< v)) 0

/-- Split options for one vertex row matching `verify_clawfree_eg.py` lines 1579–1586. -/
def vertexSplitOptions (isFixed : Bool) (row : List Nat) : List SplitChoice :=
  let base : List SplitChoice := if Nat.ble row.length 3 then [(row, none)] else []
  if isFixed then base
  else
    match row with
    | [a, b] => base ++ [([a], some [b])]
    | [a, b, c] => base ++ [([a], some [b, c]), ([a, b], some [c]), ([a, c], some [b])]
    | _ => base

/-- Cartesian product of vertex split options in exact `itertools.product` order. -/
def cartProd : List (List SplitChoice) → List SplitConfig
  | [] => [[]]
  | opts :: rest =>
    let tail := cartProd rest
    opts.flatMap fun o => tail.map fun cfg => o :: cfg

/-- Enumerate all split configurations of a base graph `(fixed, rows)`. -/
def allSplitConfigs (fixed : List Nat) (rows : List (List Nat)) : List SplitConfig :=
  let rec go (u : Nat) : List (List Nat) → List (List SplitChoice)
    | [] => []
    | r :: rs => vertexSplitOptions (memNat u fixed) r :: go (Nat.add u 1) rs
  cartProd (go 0 rows)

/-- Find index of source `(u, side)` containing `v`. -/
def findPartner (u v : Nat) : Nat → List (Nat × List Nat) → Nat
  | _, [] => 0
  | idx, (su, side) :: rest =>
    if Nat.beq su u then
      if memNat v side then idx else findPartner u v (Nat.add idx 1) rest
    else findPartner u v (Nat.add idx 1) rest

def hasBt1 (i : Nat) : List (Nat × Nat) → Bool
  | [] => false
  | (a, _) :: rest => if Nat.beq a i then true else hasBt1 i rest

def hasBt2 (i : Nat) : List (Nat × Nat) → Bool
  | [] => false
  | (_, b) :: rest => if Nat.beq b i then true else hasBt2 i rest

def isBtPair (lo hi : Nat) : List (Nat × Nat) → Bool
  | [] => false
  | (a, b) :: rest =>
    if Nat.beq a lo then (if Nat.beq b hi then true else isBtPair lo hi rest)
    else isBtPair lo hi rest

def buildSources (u idx : Nat) :
    SplitConfig → List (Nat × List Nat) → List (Nat × Nat) →
    List (Nat × List Nat) × List (Nat × Nat)
  | [], srcs, bts => (srcs.reverse, bts.reverse)
  | (first, none) :: rest, srcs, bts =>
    buildSources (Nat.add u 1) (Nat.add idx 1) rest ((u, first) :: srcs) bts
  | (first, some second) :: rest, srcs, bts =>
    buildSources (Nat.add u 1) (Nat.add idx 2) rest
      ((u, second) :: (u, first) :: srcs) ((idx, Nat.add idx 1) :: bts)

def pad3 : List Nat → List Nat
  | [] => [1000, 1001, 1002]
  | [a] => [a, 1000, 1001]
  | [a, b] => [a, b, 1000]
  | row => row

def mapPartners (sources : List (Nat × List Nat)) (u : Nat) : List Nat → List Nat
  | [] => []
  | v :: vs => findPartner v u 0 sources :: mapPartners sources u vs

def buildRows (sources : List (Nat × List Nat)) (bowties : List (Nat × Nat)) (i : Nat) :
    List (Nat × List Nat) → List (List Nat)
  | [] => []
  | (u, side) :: rest =>
    let base := mapPartners sources u side
    let withBt :=
      if hasBt1 i bowties then base ++ [Nat.add i 1]
      else if hasBt2 i bowties then base ++ [Nat.sub i 1]
      else base
    pad3 withBt :: buildRows sources bowties (Nat.add i 1) rest

/-- Build `(rows_h, bowties)` from a `SplitConfig` (matching `split_quotient` with sentinels `1000+k`). -/
def splitQuotient (cfg : SplitConfig) : List (List Nat) × List (Nat × Nat) :=
  let (sources, bowties) := buildSources 0 0 cfg [] []
  (buildRows sources bowties 0 sources, bowties)

def getRow : Nat → List (List Nat) → List Nat
  | _, [] => []
  | 0, r :: _ => r
  | k + 1, _ :: rs => getRow k rs

@[inline] def get3 (row : List Nat) (pos : Nat) : Nat :=
  match row, pos with
  | a :: _, 0 => a
  | _ :: b :: _, 1 => b
  | _ :: _ :: c :: _, _ => c
  | _, _ => 1000

@[inline] def findPos3 (row : List Nat) (v : Nat) : Nat :=
  match row with
  | [a, b, _] => if Nat.beq a v then 0 else if Nat.beq b v then 1 else 2
  | [a, _] => if Nat.beq a v then 0 else 1
  | _ => 0

/-- Strictly increasing list of raw port labels removed by bowtie contractions `(i, j)`. -/
def mkRemoved (rowsH : List (List Nat)) : List (Nat × Nat) → List Nat
  | [] => []
  | (i, j) :: rest => Nat.add (Nat.mul 3 j) (findPos3 (getRow j rowsH) i) :: mkRemoved rowsH rest

/-- Exact inverse of compact port relabeling on a strictly increasing `removed` list. -/
def unrelabel (p : Nat) : List Nat → Nat
  | [] => p
  | r :: rs => if Nat.ble r p then unrelabel (Nat.add p 1) rs else p

/-- Manifestly symmetric, irreflexive bounded-instance adjacency on raw kept ports `(x, y)` of `(rowsH, bowties)`:
adjacent iff `x ≠ y` and either same `H`-vertex (`x/3 = y/3`, triangle edge), or cross edge
(`wx = v ∧ wy = u`), or merged bowtie port (`(wx = v ∧ (u,v) ∈ B) ∨ (wy = u ∧ (v,u) ∈ B)`). -/
def rawPortAdj (rowsH : List (List Nat)) (bowties : List (Nat × Nat)) (x y : Nat) : Bool :=
  if Nat.beq x y then false
  else
    let u := Nat.div x 3
    let v := Nat.div y 3
    if Nat.beq u v then true
    else
      let wx := get3 (getRow u rowsH) (Nat.mod x 3)
      let wy := get3 (getRow v rowsH) (Nat.mod y 3)
      (Nat.beq wx v && Nat.beq wy u) ||
      (Nat.beq wx v && isBtPair u v bowties) ||
      (Nat.beq wy u && isBtPair v u bowties)

/-- Compact relabeled port adjacency for `(rowsH, bowties, removed)`. -/
@[inline] def portAdj (rowsH : List (List Nat)) (bowties : List (Nat × Nat)) (removed : List Nat) (a b : Nat) : Bool :=
  rawPortAdj rowsH bowties (unrelabel a removed) (unrelabel b removed)

/-- Number of vertices `3*|V(H)| - |B|` in the expanded port graph of `cfg`. -/
def expandedPortCount (cfg : SplitConfig) : Nat :=
  let (rowsH, bowties) := splitQuotient cfg
  Nat.sub (Nat.mul 3 rowsH.length) bowties.length

/-- Direct adjacency predicate of the expanded port graph of `cfg` (bounded-instance cost;
recomputes split tables per query). -/
def portAdjConfig (cfg : SplitConfig) (a b : Nat) : Bool :=
  let (rowsH, bowties) := splitQuotient cfg
  let removed := mkRemoved rowsH bowties
  portAdj rowsH bowties removed a b

/-- Combined incident neighbor list of one vertex choice `(first, opt)`. -/
@[inline] def choiceNeighbors : SplitChoice → List Nat
  | (first, none) => first
  | (first, some second) => first ++ second

/-- Fast pure-`Init` index lookup into a `SplitConfig` (zero `Option`/`GetElem?` overhead). -/
def getChoice : Nat → SplitConfig → SplitChoice
  | _, [] => ([], none)
  | 0, c :: _ => c
  | k + 1, _ :: rest => getChoice k rest

private def allSym (cfg : SplitConfig) (u : Nat) : List Nat → Bool
  | [] => true
  | v :: vs => if memNat u (choiceNeighbors (getChoice v cfg)) then allSym cfg u vs else false

private def allRowsLen3 : List (List Nat) → Bool
  | [] => true
  | r :: rs => if Nat.beq r.length 3 then allRowsLen3 rs else false

private def flattenBowties : List (Nat × Nat) → List Nat
  | [] => []
  | (a, b) :: rest => a :: b :: flattenBowties rest

/-- Explicit well-formedness checker for a `SplitConfig` before applying the port-expansion engine:
1. Order `n = cfg.length < 1000` and `rowsH.length < 1000` (strictly below the `1000` padding sentinel),
2. Every vertex `u < n` has duplicate-free, loopless, in-range neighbors with unsplit length `≤ 3`
   or split side lengths each `≤ 2` (ensuring every split `H`-vertex has degree `≤ 3`),
3. Symmetric incidence (`v ∈ N(u) → u ∈ N(v)`), guaranteeing every partner lookup succeeds,
4. All padded rows have length `3` and all bowtie pairs in `bowties` are pairwise disjoint and in range. -/
def splitConfigWellFormed (cfg : SplitConfig) : Bool :=
  let n := cfg.length
  let (rowsH, bowties) := splitQuotient cfg
  let rec checkVerts (u : Nat) : List SplitChoice → Bool
    | [] => true
    | (first, none) :: rest =>
      if Nat.ble first.length 3 && allLt n first && nodupNat first && !(memNat u first) &&
         allSym cfg u first then checkVerts (Nat.add u 1) rest
      else false
    | (first, some second) :: rest =>
      if Nat.ble first.length 2 && Nat.ble second.length 2 then
        let comb := first ++ second
        if allLt n comb && nodupNat comb && !(memNat u comb) && allSym cfg u comb then
          checkVerts (Nat.add u 1) rest
        else false
      else false
  let btFlat := flattenBowties bowties
  Nat.blt n 1000 && Nat.blt rowsH.length 1000 &&
  checkVerts 0 cfg &&
  allRowsLen3 rowsH &&
  nodupNat btFlat && allLt rowsH.length btFlat

/-- Propositional well-formedness predicate for a `SplitConfig`. -/
def SplitConfigWellFormed (cfg : SplitConfig) : Prop :=
  splitConfigWellFormed cfg = true

def mapUnrelabel (removed : List Nat) : List Nat → List Nat
  | [] => []
  | v :: vs => unrelabel v removed :: mapUnrelabel removed vs

def checkRawCycleGo (rowsH : List (List Nat)) (bowties : List (Nat × Nat)) (first : Nat) : List Nat → Bool
  | [] => true
  | [last] => rawPortAdj rowsH bowties last first
  | a :: b :: rest =>
    if rawPortAdj rowsH bowties a b then checkRawCycleGo rowsH bowties first (b :: rest) else false

/-- O(L) cycle checker on the expanded port graph of `cfg` (zero edge-list / bitmask allocation). -/
def checkCycleDirect (cfg : SplitConfig) (cyc : List Nat) : Bool :=
  if Nat.blt cyc.length 3 then false
  else
    let (rowsH, bowties) := splitQuotient cfg
    let nVerts := Nat.sub (Nat.mul 3 rowsH.length) bowties.length
    if allLt nVerts cyc then
      if nodupNat cyc then
        let removed := mkRemoved rowsH bowties
        match mapUnrelabel removed cyc with
        | [] => false
        | first :: rest => checkRawCycleGo rowsH bowties first (first :: rest)
      else false
    else false

/-- Check a chunk of `(cfg, cyc)` pairs for BOTH `splitConfigWellFormed cfg` and valid cycle in `targets`. -/
def checkPortChunk (targets : List Nat) : List SplitConfig → List (List Nat) → Bool
  | [], [] => true
  | cfg :: cfgs, cyc :: cycs =>
    if splitConfigWellFormed cfg && memNat cyc.length targets && checkCycleDirect cfg cyc then
      checkPortChunk targets cfgs cycs
    else false
  | _, _ => false

/-! ## 2. Direct Expanded-Port Kill Certificates (`0/4`, `0/128`, & `Q_3 - v^*` Chunking) -/

def deg3TriRows : List (List Nat) := [[1, 2], [0, 2], [0, 1]]
def k23Rows : List (List Nat) := [[2, 3, 4], [2, 3, 4], [0, 1], [0, 1], [0, 1]]
def q3MinusVRows : List (List Nat) := [[1, 2, 4], [0, 3, 5], [0, 3, 6], [1, 2], [0, 5, 6], [1, 4], [2, 4]]

def deg3TriConfigs : List SplitConfig := allSplitConfigs [0] deg3TriRows
def k23Configs : List SplitConfig := allSplitConfigs [] k23Rows
def q3MinusVConfigs : List SplitConfig := allSplitConfigs [] q3MinusVRows

/-- Direct bounded-offset chunking of `q3MinusVConfigs` into `16` chunks of `128` configs by the
`4 × 4 = 16` split choices of vertices `0` and `1` (avoids deep `List.drop` recursion). -/
def q3Opt0 : List SplitChoice := vertexSplitOptions false [1, 2, 4]
def q3Opt1 : List SplitChoice := vertexSplitOptions false [0, 3, 5]
def q3Tail128 : List SplitConfig :=
  allSplitConfigs [] [[0, 3, 6], [1, 2], [0, 5, 6], [1, 4], [2, 4]]

def q3MinusVChunk (c : Nat) : List SplitConfig :=
  let o0 := q3Opt0.getD (c / 4) ([], none)
  let o1 := q3Opt1.getD (c % 4) ([], none)
  q3Tail128.map fun tl => o0 :: o1 :: tl

private theorem list_flatMap_length {α β : Type} (xs : List α) (f : α → List β) (k : Nat)
    (hf : ∀ x ∈ xs, (f x).length = k) : (xs.flatMap f).length = xs.length * k := by
  induction xs with
  | nil => simp
  | cons x rest ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    rw [hf x (List.mem_cons_self ..), ih (fun y hy => hf y (List.mem_cons_of_mem x hy)),
        Nat.add_mul, Nat.one_mul, Nat.add_comm]

private theorem cartProd_length : ∀ (xss : List (List SplitChoice)),
    (cartProd xss).length = xss.foldr (fun o acc => o.length * acc) 1
  | [] => rfl
  | opts :: rest => by
    unfold cartProd
    dsimp only [List.foldr]
    rw [list_flatMap_length opts _ (cartProd rest).length (fun _ _ => List.length_map ..),
        cartProd_length rest]

theorem port_config_counts :
    deg3TriConfigs.length = 4 ∧
    k23Configs.length = 128 ∧
    q3Opt0.length = 4 ∧
    q3Opt1.length = 4 ∧
    q3Tail128.length = 128 := by
  refine ⟨?_, ?_, by decide, by decide, ?_⟩
  · unfold deg3TriConfigs allSplitConfigs; rw [cartProd_length]; decide
  · unfold k23Configs allSplitConfigs; rw [cartProd_length]; decide
  · unfold q3Tail128 allSplitConfigs; rw [cartProd_length]; decide

def deg3TriCycles : List (List Nat) := [
  [0, 2, 1, 6, 8, 7, 4, 3], [0, 2, 1, 6, 7, 9, 4, 3],
  [0, 2, 1, 8, 9, 6, 4, 3], [0, 1, 8, 9, 11, 6, 4, 3]
]
theorem deg3Tri_all_4_ok : checkPortChunk [8] deg3TriConfigs deg3TriCycles = true := by decide

def k23Cycles_0 : List (List Nat) := [
  [0, 2, 12, 13, 5, 3, 7, 6], [0, 1, 9, 10, 4, 3, 7, 6],
  [0, 2, 14, 15, 5, 3, 7, 6], [0, 1, 9, 11, 10, 13, 12, 4, 3, 5, 17, 18, 15, 16, 14, 2],
  [1, 2, 14, 15, 5, 4, 12, 11], [0, 1, 2, 14, 16, 15, 18, 17, 5, 4, 3, 9, 10, 7, 8, 6],
  [0, 2, 1, 11, 13, 12, 15, 14, 4, 5, 3, 9, 10, 7, 8, 6], [0, 2, 1, 11, 13, 12, 15, 14, 4, 5, 3, 9, 10, 7, 8, 6],
  [1, 2, 14, 15, 7, 6, 12, 11], [0, 1, 2, 14, 16, 15, 18, 17, 7, 6, 4, 5, 3, 9, 10, 8],
  [0, 2, 1, 11, 13, 12, 15, 14, 6, 7, 4, 5, 3, 9, 10, 8], [0, 2, 1, 11, 13, 12, 15, 14, 6, 7, 4, 5, 3, 9, 10, 8],
  [0, 2, 1, 13, 15, 14, 6, 7, 4, 5, 3, 11, 12, 9, 10, 8], [0, 2, 16, 18, 17, 20, 19, 7, 6, 4, 5, 3, 11, 12, 9, 8],
  [0, 2, 1, 13, 15, 14, 17, 16, 6, 7, 4, 5, 3, 11, 9, 8], [0, 2, 18, 20, 19, 22, 21, 7, 6, 4, 5, 3, 11, 12, 9, 8],
  [0, 1, 11, 12, 4, 3, 9, 8], [0, 1, 11, 13, 12, 4, 3, 5, 7, 6, 17, 18, 15, 16, 14, 2],
  [0, 1, 11, 13, 12, 15, 14, 4, 3, 5, 7, 6, 17, 18, 16, 2], [0, 1, 11, 13, 12, 15, 14, 4, 5, 7, 6, 19, 20, 17, 16, 2],
  [0, 1, 2, 16, 18, 17, 6, 7, 5, 4, 3, 11, 12, 9, 10, 8], [0, 2, 16, 18, 17, 20, 19, 6, 7, 5, 4, 3, 11, 12, 9, 8],
  [0, 2, 1, 13, 15, 14, 17, 16, 4, 5, 3, 11, 12, 9, 10, 8], [0, 2, 18, 20, 19, 22, 21, 6, 7, 5, 4, 3, 11, 12, 9, 8],
  [0, 2, 14, 15, 4, 3, 9, 8], [0, 1, 11, 13, 12, 6, 7, 5, 3, 4, 17, 18, 15, 16, 14, 2],
  [0, 2, 16, 17, 4, 3, 9, 8], [0, 2, 1, 11, 13, 12, 15, 14, 6, 7, 5, 4, 3, 9, 10, 8],
  [0, 2, 1, 13, 15, 14, 6, 7, 5, 4, 3, 11, 12, 9, 10, 8], [0, 2, 1, 13, 15, 14, 6, 7, 5, 4, 3, 11, 12, 9, 10, 8],
  [0, 2, 1, 13, 15, 14, 17, 16, 6, 7, 5, 4, 3, 11, 9, 8], [0, 2, 1, 13, 15, 14, 17, 16, 6, 7, 5, 4, 3, 11, 9, 8],
  [3, 4, 14, 15, 7, 6, 12, 11], [0, 2, 1, 3, 4, 14, 16, 15, 18, 17, 7, 6, 5, 9, 10, 8],
  [0, 2, 1, 4, 3, 11, 13, 12, 15, 14, 6, 7, 5, 9, 10, 8], [0, 2, 1, 4, 3, 11, 13, 12, 15, 14, 6, 7, 5, 9, 10, 8],
  [0, 2, 1, 4, 3, 13, 15, 14, 6, 7, 5, 11, 12, 9, 10, 8], [0, 2, 1, 4, 16, 18, 17, 20, 19, 7, 6, 5, 11, 12, 9, 8],
  [0, 2, 1, 4, 3, 13, 15, 14, 17, 16, 6, 7, 5, 11, 9, 8], [0, 2, 1, 4, 18, 20, 19, 22, 21, 7, 6, 5, 11, 12, 9, 8],
  [0, 2, 1, 4, 3, 13, 15, 14, 8, 9, 6, 7, 5, 11, 12, 10], [0, 2, 1, 4, 16, 18, 17, 20, 19, 9, 8, 6, 7, 5, 11, 10],
  [0, 2, 1, 4, 3, 13, 15, 14, 17, 16, 8, 9, 6, 5, 11, 10], [0, 2, 1, 4, 18, 20, 19, 22, 21, 9, 8, 6, 7, 5, 11, 10],
  [0, 2, 1, 4, 18, 20, 19, 9, 8, 6, 7, 5, 13, 14, 11, 10], [0, 2, 1, 4, 18, 20, 19, 22, 21, 9, 8, 6, 5, 13, 11, 10],
  [0, 2, 1, 4, 20, 22, 21, 9, 8, 6, 7, 5, 13, 14, 11, 10], [0, 2, 1, 4, 20, 22, 21, 24, 23, 9, 8, 6, 5, 13, 11, 10],
  [0, 2, 1, 3, 4, 16, 18, 17, 8, 9, 7, 6, 5, 11, 12, 10], [0, 2, 1, 4, 16, 18, 17, 20, 19, 8, 9, 7, 6, 5, 11, 10],
  [0, 2, 1, 4, 3, 13, 15, 14, 17, 16, 6, 7, 5, 11, 12, 10], [0, 2, 1, 4, 18, 20, 19, 22, 21, 8, 9, 7, 6, 5, 11, 10],
  [0, 2, 1, 4, 18, 20, 19, 8, 9, 7, 6, 5, 13, 14, 11, 10], [0, 2, 1, 4, 18, 20, 19, 22, 21, 8, 9, 7, 5, 13, 11, 10],
  [0, 2, 1, 4, 20, 22, 21, 8, 9, 7, 6, 5, 13, 14, 11, 10], [0, 2, 1, 4, 20, 22, 21, 24, 23, 8, 9, 7, 5, 13, 11, 10],
  [0, 2, 1, 4, 3, 13, 15, 14, 8, 9, 7, 6, 5, 11, 12, 10], [0, 2, 1, 4, 3, 13, 15, 14, 8, 9, 7, 6, 5, 11, 12, 10],
  [0, 2, 1, 4, 3, 13, 15, 14, 17, 16, 8, 9, 7, 5, 11, 10], [0, 2, 1, 4, 3, 13, 15, 14, 17, 16, 8, 9, 7, 5, 11, 10],
  [0, 2, 1, 4, 3, 15, 17, 16, 8, 9, 7, 6, 5, 13, 11, 10], [0, 2, 1, 4, 18, 20, 19, 22, 21, 6, 7, 5, 13, 14, 11, 10],
  [0, 2, 1, 4, 3, 15, 17, 16, 19, 18, 8, 7, 5, 13, 11, 10], [0, 2, 1, 4, 20, 22, 21, 24, 23, 6, 7, 5, 13, 14, 11, 10]
]
def k23Cycles_1 : List (List Nat) := [
  [0, 1, 11, 12, 6, 5, 9, 8], [0, 1, 11, 13, 12, 6, 5, 7, 17, 18, 15, 16, 14, 3, 4, 2],
  [0, 1, 11, 13, 12, 15, 14, 6, 5, 7, 17, 18, 16, 3, 4, 2], [0, 1, 11, 13, 12, 15, 14, 6, 7, 19, 20, 17, 18, 16, 3, 2],
  [0, 1, 2, 4, 3, 16, 18, 17, 7, 6, 5, 11, 12, 9, 10, 8], [0, 2, 4, 3, 16, 18, 17, 20, 19, 7, 6, 5, 11, 12, 9, 8],
  [0, 2, 1, 13, 15, 14, 17, 16, 6, 7, 5, 11, 12, 9, 10, 8], [0, 2, 4, 3, 18, 20, 19, 22, 21, 7, 6, 5, 11, 12, 9, 8],
  [0, 1, 2, 4, 3, 16, 18, 17, 9, 8, 6, 7, 5, 11, 12, 10], [0, 2, 4, 3, 16, 18, 17, 20, 19, 9, 8, 6, 7, 5, 11, 10],
  [0, 2, 1, 13, 15, 14, 17, 16, 8, 9, 6, 7, 5, 11, 12, 10], [0, 2, 4, 3, 18, 20, 19, 22, 21, 9, 8, 6, 7, 5, 11, 10],
  [0, 2, 4, 3, 18, 20, 19, 9, 8, 6, 7, 5, 13, 14, 11, 10], [0, 2, 4, 3, 18, 20, 19, 22, 21, 9, 8, 6, 5, 13, 11, 10],
  [0, 2, 4, 3, 20, 22, 21, 9, 8, 6, 7, 5, 13, 14, 11, 10], [0, 2, 4, 3, 20, 22, 21, 24, 23, 9, 8, 6, 5, 13, 11, 10],
  [0, 1, 13, 15, 14, 6, 5, 7, 9, 8, 17, 18, 16, 3, 4, 2], [0, 2, 4, 3, 16, 18, 17, 20, 19, 8, 9, 7, 6, 5, 11, 10],
  [0, 1, 13, 15, 14, 17, 16, 6, 7, 9, 8, 19, 20, 18, 3, 2], [0, 2, 4, 3, 18, 20, 19, 22, 21, 8, 9, 7, 6, 5, 11, 10],
  [0, 2, 4, 3, 18, 20, 19, 8, 9, 7, 6, 5, 13, 14, 11, 10], [0, 2, 4, 3, 18, 20, 19, 22, 21, 8, 9, 7, 5, 13, 11, 10],
  [0, 2, 4, 3, 20, 22, 21, 8, 9, 7, 6, 5, 13, 14, 11, 10], [0, 2, 4, 3, 20, 22, 21, 24, 23, 8, 9, 7, 5, 13, 11, 10],
  [0, 1, 13, 15, 14, 8, 9, 7, 5, 6, 17, 18, 16, 3, 4, 2], [0, 1, 13, 15, 14, 8, 9, 7, 6, 19, 20, 17, 18, 16, 3, 2],
  [0, 2, 1, 13, 15, 14, 17, 16, 8, 9, 7, 6, 5, 11, 12, 10], [0, 2, 1, 13, 15, 14, 17, 16, 8, 9, 7, 6, 5, 11, 12, 10],
  [0, 2, 1, 15, 17, 16, 8, 9, 7, 6, 5, 13, 14, 11, 12, 10], [0, 2, 4, 3, 18, 20, 19, 22, 21, 6, 7, 5, 13, 14, 11, 10],
  [0, 2, 1, 15, 17, 16, 19, 18, 8, 9, 7, 6, 5, 13, 11, 10], [0, 2, 4, 3, 20, 22, 21, 24, 23, 6, 7, 5, 13, 14, 11, 10],
  [0, 1, 14, 15, 7, 5, 9, 8], [0, 1, 14, 16, 15, 18, 17, 7, 5, 6, 12, 13, 11, 3, 4, 2],
  [0, 1, 16, 18, 17, 7, 5, 6, 14, 15, 12, 13, 11, 3, 4, 2], [0, 1, 16, 18, 17, 20, 19, 7, 6, 14, 15, 12, 13, 11, 3, 2],
  [0, 1, 2, 4, 3, 13, 15, 14, 6, 7, 5, 11, 12, 9, 10, 8], [0, 2, 1, 16, 18, 17, 20, 19, 7, 6, 5, 11, 12, 9, 10, 8],
  [0, 2, 4, 3, 13, 15, 14, 17, 16, 6, 7, 5, 11, 12, 9, 8], [0, 2, 4, 3, 13, 15, 14, 17, 16, 6, 7, 5, 11, 12, 9, 8],
  [0, 1, 2, 4, 3, 13, 15, 14, 8, 9, 6, 7, 5, 11, 12, 10], [0, 2, 1, 16, 18, 17, 20, 19, 9, 8, 6, 7, 5, 11, 12, 10],
  [0, 2, 4, 3, 13, 15, 14, 17, 16, 8, 9, 6, 7, 5, 11, 10], [0, 2, 4, 3, 13, 15, 14, 17, 16, 8, 9, 6, 7, 5, 11, 10],
  [0, 2, 4, 3, 15, 17, 16, 8, 9, 6, 7, 5, 13, 14, 11, 10], [0, 2, 4, 3, 15, 17, 16, 8, 9, 6, 7, 5, 13, 14, 11, 10],
  [0, 2, 4, 3, 15, 17, 16, 19, 18, 8, 9, 6, 5, 13, 11, 10], [0, 2, 4, 3, 15, 17, 16, 19, 18, 8, 9, 6, 5, 13, 11, 10],
  [0, 1, 16, 18, 17, 8, 9, 7, 5, 6, 14, 15, 13, 3, 4, 2], [0, 2, 1, 16, 18, 17, 20, 19, 8, 9, 7, 6, 5, 11, 12, 10],
  [0, 1, 18, 20, 19, 8, 9, 7, 6, 16, 17, 14, 15, 13, 3, 2], [0, 2, 1, 18, 20, 19, 22, 21, 8, 9, 7, 6, 5, 11, 12, 10],
  [0, 2, 1, 18, 20, 19, 8, 9, 7, 6, 5, 13, 14, 11, 12, 10], [0, 2, 1, 18, 20, 19, 22, 21, 8, 9, 7, 6, 5, 13, 11, 10],
  [0, 2, 4, 3, 15, 17, 16, 19, 18, 6, 7, 5, 13, 14, 11, 10], [0, 2, 4, 3, 15, 17, 16, 19, 18, 6, 7, 5, 13, 14, 11, 10],
  [0, 1, 16, 18, 17, 6, 5, 7, 9, 8, 14, 15, 13, 3, 4, 2], [0, 1, 16, 18, 17, 20, 19, 6, 7, 9, 8, 14, 15, 13, 3, 2],
  [0, 2, 4, 3, 13, 15, 14, 17, 16, 8, 9, 7, 6, 5, 11, 10], [0, 2, 4, 3, 13, 15, 14, 17, 16, 8, 9, 7, 6, 5, 11, 10],
  [0, 2, 4, 3, 15, 17, 16, 8, 9, 7, 6, 5, 13, 14, 11, 10], [0, 2, 4, 3, 15, 17, 16, 8, 9, 7, 6, 5, 13, 14, 11, 10],
  [0, 2, 4, 3, 15, 17, 16, 19, 18, 8, 9, 7, 5, 13, 11, 10], [0, 2, 4, 3, 15, 17, 16, 19, 18, 8, 9, 7, 5, 13, 11, 10]
]
def k23Cycles : List (List Nat) := k23Cycles_0 ++ k23Cycles_1
theorem k23_c0_ok : checkPortChunk [8, 16] (k23Configs.take 64) k23Cycles_0 = true := by decide
theorem k23_c1_ok : checkPortChunk [8, 16] (k23Configs.drop 64) k23Cycles_1 = true := by decide

/-! ## 3. Sharp Non-Planar Witness `G_39 = T(H_14)/B` (`F_11`, `H_14`, `G_39`, `K_5`-Minor, `tw(F_11) = 3`) -/

def f11Edges : List (Nat × Nat) := [(3, 4), (3, 5), (3, 6), (4, 0), (4, 1), (5, 1), (5, 2), (6, 2), (6, 0), (7, 8), (7, 9), (7, 10), (8, 0), (8, 1), (9, 1), (9, 2), (10, 2), (10, 0)]
def f11Tw3Bags : List (List Nat) := [
  [0, 1, 2, 3],
  [0, 1, 3, 4],
  [1, 2, 3, 5],
  [0, 2, 3, 6],
  [0, 1, 2, 7],
  [0, 1, 7, 8],
  [1, 2, 7, 9],
  [0, 2, 7, 10]
]
def f11Tw3TreeEdges : List (Nat × Nat) := [(0, 1), (0, 2), (0, 3), (0, 4), (4, 5), (4, 6), (4, 7)]
def h14Adj : List (List Nat) := [
  [1, 7, 11],
  [0, 9, 13],
  [3, 7, 12],
  [2, 8, 11],
  [5, 8, 13],
  [4, 9, 12],
  [7, 8, 9],
  [0, 2, 6],
  [3, 4, 6],
  [1, 5, 6],
  [11, 12, 13],
  [0, 3, 10],
  [2, 5, 10],
  [1, 4, 10]
]
def h14Bowties : List (Nat × Nat) := [(0, 1), (2, 3), (4, 5)]
def h14K5BranchSets : List (List Nat) := [
  [0, 2, 7],
  [3, 6, 8, 9],
  [4, 5, 12],
  [10, 11],
  [1, 13]
]
def g39Adj : List (List Nat) := [
  [1, 2, 18],
  [0, 2, 30],
  [0, 1, 3, 4],
  [2, 4, 24],
  [2, 3, 36],
  [6, 7, 19],
  [5, 7, 33],
  [5, 6, 8, 9],
  [7, 9, 21],
  [7, 8, 31],
  [11, 12, 22],
  [10, 12, 37],
  [10, 11, 13, 14],
  [12, 14, 25],
  [12, 13, 34],
  [16, 17, 20],
  [15, 17, 23],
  [15, 16, 26],
  [0, 19, 20],
  [5, 18, 20],
  [15, 18, 19],
  [8, 22, 23],
  [10, 21, 23],
  [16, 21, 22],
  [3, 25, 26],
  [13, 24, 26],
  [17, 24, 25],
  [28, 29, 32],
  [27, 29, 35],
  [27, 28, 38],
  [1, 31, 32],
  [9, 30, 32],
  [27, 30, 31],
  [6, 34, 35],
  [14, 33, 35],
  [28, 33, 34],
  [4, 37, 38],
  [11, 36, 38],
  [29, 36, 37]
]
def g39V4 : List Nat := [2, 7, 12]
def g39C16 : List Nat := [0, 2, 4, 36, 38, 37, 11, 12, 14, 34, 35, 33, 6, 5, 19, 18]
def g39K5BranchSets : List (List Nat) := [
  [0, 1, 2, 5, 6, 7, 18, 19, 20],
  [8, 9, 15, 16, 17, 21, 22, 23, 24, 25, 26],
  [10, 11, 12, 13, 14, 33, 34, 35],
  [27, 28, 29, 30, 31, 32],
  [3, 4, 36, 37, 38]
]
def f11G39SplitConfig : SplitConfig := [
  ([4, 8], some [6, 10]),
  ([4, 9], some [5, 8]),
  ([5, 10], some [6, 9]),
  ([4, 5, 6], none),
  ([0, 1, 3], none),
  ([1, 2, 3], none),
  ([0, 2, 3], none),
  ([8, 9, 10], none),
  ([0, 1, 7], none),
  ([1, 2, 7], none),
  ([0, 2, 7], none)
]

def f11Masks : List Nat := masksFromEdges 11 f11Edges
def h14Masks : List Nat := masksFromAdj h14Adj
def g39Masks : List Nat := masksFromAdj g39Adj

theorem g39_eq_f11_split_expanded :
    expandedPortCount f11G39SplitConfig = 39 ∧
    (let (rowsH, bowties) := splitQuotient f11G39SplitConfig
     let removed := mkRemoved rowsH bowties
     (List.range 39).all fun u =>
      (List.range 39).all fun v =>
        portAdj rowsH bowties removed u v == maskAdj g39Masks u v) = true := by
  decide

/-- Safe adjacency-row lookup for `List (List Nat)`. -/
@[inline] def getAdj (adj : List (List Nat)) (i : Nat) : List Nat :=
  match adj, i with
  | [], _ => []
  | r :: _, 0 => r
  | _ :: rs, k + 1 => getAdj rs k

/-- Structural neighbor-list DFS helper (iterates ONLY over actual neighbors `nbs`,
reducing `G_39` `C_8` search by `~100×` vs scanning all 39 vertices!). -/
def hasCycleFromNbs (start vis : Nat) (recFn : Nat → Nat → Bool) : List Nat → Bool
  | [] => false
  | w :: ws =>
    let ok :=
      if Nat.blt start w && !(vis.testBit w) then
        recFn w (vis ||| (1 <<< w))
      else false
    if ok then true else hasCycleFromNbs start vis recFn ws

/-- Exact neighbor-list DFS checking whether `adj` contains a simple cycle of length `L ≥ 3`
whose minimum vertex is `start`. -/
def hasCycleFromAdj (adj : List (List Nat)) (start : Nat) : Nat → Nat → Nat → Bool
  | 0, cur, _ => (getAdj adj cur).contains start
  | rem + 1, cur, vis =>
    hasCycleFromNbs start vis (hasCycleFromAdj adj start rem) (getAdj adj cur)

/-- Structural loop over starting vertices `0..k-1`. -/
def hasSimpleCycleLenGo (adj : List (List Nat)) (L : Nat) : Nat → Bool
  | 0 => false
  | s + 1 =>
    if hasCycleFromAdj adj s (L - 1) s (1 <<< s) then true
    else hasSimpleCycleLenGo adj L s

/-- Exact neighbor-list DFS checking whether `adj` contains ANY simple cycle of length `L ≥ 3`. -/
def hasSimpleCycleLenBool (n : Nat) (adj : List (List Nat)) (L : Nat) : Bool :=
  if Nat.blt L 3 then false else hasSimpleCycleLenGo adj L n

theorem g39_no_c4_bool : hasSimpleCycleLenBool 39 g39Adj 4 = false := by decide
theorem g39_no_c8_bool : hasSimpleCycleLenBool 39 g39Adj 8 = false := by decide
theorem g39_c16_ok : checkCycleMasks 39 g39Masks g39C16 = true ∧ g39C16.length = 16 := by decide

/-- Compute degree of vertex `u` in bitmask graph `(n, masks)`. -/
def maskDeg (n : Nat) (masks : List Nat) (u : Nat) : Nat :=
  let rec go (v acc : Nat) : Nat → Nat
    | 0 => acc
    | k + 1 => go (v + 1) (if maskAdj masks u v then acc + 1 else acc) k
  go 0 0 n

/-- Check claw-freeness (`∀ u, ∀ a < b < c ∈ N(u), adj(a,b) ∨ adj(a,c) ∨ adj(b,c)`). -/
def isClawFreeMasks (n : Nat) (masks : List Nat) : Bool :=
  let rec nbsOf (u v : Nat) : Nat → List Nat
    | 0 => []
    | k + 1 => if maskAdj masks u v then v :: nbsOf u (v + 1) k else nbsOf u (v + 1) k
  let rec checkTriples : List Nat → Bool
    | [] => true
    | a :: rest =>
      let rec checkPairs : List Nat → Bool
        | [] => true
        | b :: rest2 =>
          let okB := rest2.all fun c =>
            maskAdj masks a b || maskAdj masks a c || maskAdj masks b c
          okB && checkPairs rest2
      checkPairs rest && checkTriples rest
  let rec go : Nat → Bool
    | 0 => true
    | u + 1 => checkTriples (nbsOf u 0 n) && go u
  go n

theorem g39_deg_and_clawfree_ok :
    (List.range 39).all (fun u =>
      maskDeg 39 g39Masks u == (if g39V4.contains u then 4 else 3)) = true ∧
    g39V4.all (fun u => g39V4.all fun v => !(maskAdj g39Masks u v)) = true ∧
    isClawFreeMasks 39 g39Masks = true := by
  decide

theorem h14_cubic_ok :
    (List.range 14).all (fun u => maskDeg 14 h14Masks u == 3) = true := by
  decide

/-- Check connectivity of an induced subset `S ⊆ [0, n)` via `|S|` rounds of bitmask BFS expansion. -/
def isSubsetConnected (masks : List Nat) (S : List Nat) : Bool :=
  match S with
  | [] => false
  | s0 :: _ =>
    let sMask := S.foldl (fun m v => m ||| (1 <<< v)) 0
    let step (vis : Nat) : Nat :=
      S.foldl (fun acc u =>
        if vis.testBit u then acc ||| ((getNat masks u) &&& sMask) else acc) vis
    let rec iter : Nat → Nat → Nat
      | 0, vis => vis
      | k + 1, vis => iter k (step vis)
    let reached := iter S.length (1 <<< s0)
    S.all fun v => reached.testBit v

/-- Check that `sets` is a valid `K_5`-minor witness on `(n, masks)`:
5 nonempty pairwise-disjoint connected branch sets inside `0..n-1` with at least one edge
between every pair `i < j`. -/
def checkK5MinorBool (n : Nat) (masks : List Nat) (sets : List (List Nat)) : Bool :=
  (sets.length == 5) &&
  sets.all (fun bs => !(bs.isEmpty) && nodupNat bs && bs.all (fun v => Nat.blt v n) && isSubsetConnected masks bs) &&
  (List.range 5).all fun i =>
    (List.range 5).all fun j =>
      if Nat.blt i j then
        let bi := sets.getD i []
        let bj := sets.getD j []
        bi.all (fun u => !(bj.contains u)) &&
        bi.any (fun u => bj.any fun v => maskAdj masks u v)
      else true

theorem h14_k5_minor_bool : checkK5MinorBool 14 h14Masks h14K5BranchSets = true := by decide
theorem g39_k5_minor_bool : checkK5MinorBool 39 g39Masks g39K5BranchSets = true := by decide

/-- Check that `(bags, tEdges)` is a valid tree decomposition of width `≤ 3` for `(n, edges)`. -/
def checkTw3DecompBool (n : Nat) (edges : List (Nat × Nat))
    (bags : List (List Nat)) (tEdges : List (Nat × Nat)) : Bool :=
  let nb := bags.length
  let tMasks := masksFromEdges nb tEdges
  (tEdges.length + 1 == nb) &&
  isSubsetConnected tMasks (List.range nb) &&
  bags.all (fun b => Nat.ble b.length 4 && nodupNat b && b.all fun v => Nat.blt v n) &&
  edges.all (fun (u, v) => bags.any fun b => b.contains u && b.contains v) &&
  (List.range n).all fun v =>
    let sub := (List.range nb).filter fun i => (bags.getD i []).contains v
    isSubsetConnected tMasks sub

theorem f11_tw3_decomp_bool : checkTw3DecompBool 11 f11Edges f11Tw3Bags f11Tw3TreeEdges = true := by decide
theorem f11G39_wellFormed_bool : splitConfigWellFormed f11G39SplitConfig = true := by decide

end ClawFreeEG.Treewidth3Data
