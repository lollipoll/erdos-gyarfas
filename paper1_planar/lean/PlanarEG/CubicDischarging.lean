import PlanarEG.GraphCore
import PlanarEG.CertTree
import PlanarEG.CubicBFCoreData
import PlanarEG.CubicSmallBF1Data
import PlanarEG.CubicSmallBF2Data
import PlanarEG.CubicDP1Data
import PlanarEG.CubicDP11Data
import PlanarEG.CubicD17Data

/-!
# PlanarEG.CubicDischarging

Complete kernel-verified discharging & cyclic-automaton engine for **Main Theorem 1**
(*Every Cubic Planar Graph Contains `C_4, C_8, C_16,` or `C_32`*, arbitrary connectivity):

1. **General Reusable Bellman-Ford, Shifted-Slope, & DP Soundness Theorems** (also reused
   in Stage 3 for `GeneralPlanarC16.lean`):
   - `bf_walk_bound`, `bf_cycle_bound` (dual potential telescoping in `Int`)
   - `bf_potential_walk_bound`, `bf_potential_cycle_bound`, `bf_shifted_walk_bound`
   - `dp_upper_bound_sound`, `dag_potential_path_bound`, `bwd_dp_upper_bound_sound`
   - `cubic_discharging_contradiction`, `cubic_relaxed_discharging_contradiction`
2. **Kernel-Verified Bellman-Ford Dual Potentials (`CubicBFCoreData`):**
   - `cubic_d33_bf_valid` & `cubic_clean_d_ge_33_charge_le` (`667` edges, `scale = 1320`, `b = 9/11`)
   - `cubic_frozen_cap_bf_valid`, `cubic_frozen_cap_bound` (`1,588` edges, `H = 1`, sum `≤ 10 < 12`)
   - `cubic_frozen_cap_relaxed_bound` (`1,351` core edges, excess `≤ 1/3`, sum `≤ 32/3 < 12`)
3. **Proof-Carrying Cyclic DP & Shifted-Slope Bounds for Clean `d ≤ 31` (`CubicSmallBF*`, `CubicDP*`):**
   - All `20` non-residual lengths `d ∈ {7, 9, 10, 11, 12, 13, 15, 19..31}` certified `maxRecv(d) ≤ d - 6`
   - Exact conservative-enumeration boundary summary for `d ∈ {14, 17, 18}` (`{357, 302652, 5232}`)
4. **Explicit Simple Dyadic Cycle Witnesses for ALL `108` `d = 17` Residuals (`CubicD17Data`):**
   - `weldFaceGraph_hasDyadicCycle`: kernel-verified `FinGraph` simple cycle construction
   - `cubic_d17_all_114_welds_killed`, `cubic_d17_r10_seal_killed`, `cubic_d17_all_108_residuals_killed`

Pure Lean 4 (`import Std`, ZERO Mathlib, ZERO `sorry`, ZERO `axiom`, ZERO `native_decide`).
-/

namespace PlanarEG

open CertTree
open CubicBFCoreData
open CubicSmallBF1Data
open CubicSmallBF2Data
open CubicDP1Data
open CubicDP11Data
open CubicD17Data

/-! ## 1. General Scaled-Integer Bellman-Ford, Shifted-Slope, & DP Soundness Theorems -/

/-- A directed weighted walk of `k` edges from `u` to `z` with total integer weight `totW`. -/
inductive DirWalk (hasEdge : Nat → Nat → Int → Prop) : Nat → Nat → Nat → Int → Prop
  | nil (u : Nat) : DirWalk hasEdge u u 0 0
  | cons {u v z k : Nat} {w rest : Int}
      (he : hasEdge u v w) (hp : DirWalk hasEdge v z k rest) :
      DirWalk hasEdge u z (k + 1) (w + rest)

/-- **General Scaled-Integer Dual Potential Walk Bound (`bf_walk_bound`):**
If every edge `(u, v, w)` obeys `π v ≤ π u + (B - w)` (equivalently `w + π v - π u ≤ B`),
then EVERY directed walk of `k` edges from `u` to `z` has `totW ≤ k * B + π u - π z`. -/
theorem bf_walk_bound {hasEdge : Nat → Nat → Int → Prop} (π : Nat → Int) (B : Int)
    (hpot : ∀ u v w, hasEdge u v w → π v ≤ π u + (B - w))
    {u z k : Nat} {totW : Int} (hp : DirWalk hasEdge u z k totW) :
    totW ≤ (k : Int) * B + π u - π z := by
  induction hp with
  | nil u =>
    simp
  | @cons u v z k' w rest he _ ih =>
    have hstep := hpot u v w he
    have hcast : ((k' + 1 : Nat) : Int) * B = (k' : Int) * B + B := by
      rw [Int.natCast_add, Int.natCast_one, Int.add_mul, Int.one_mul]
    omega

/-- **General Scaled-Integer Dual Potential Cycle Bound (`bf_cycle_bound`):**
For ANY closed directed cycle of length `d` (`z = u`), `totW ≤ d * B` (exact telescoping). -/
theorem bf_cycle_bound {hasEdge : Nat → Nat → Int → Prop} (π : Nat → Int) (B : Int)
    (hpot : ∀ u v w, hasEdge u v w → π v ≤ π u + (B - w))
    {u d : Nat} {totW : Int} (hc : DirWalk hasEdge u u d totW) :
    totW ≤ (d : Int) * B := by
  have h := bf_walk_bound π B hpot hc
  omega

/-- **Ascending-Potential Walk Bound (`bf_potential_walk_bound`):**
In the equivalent Bellman-Ford convention `π u + w ≤ π v` (used by `CertTree.checkEdge`),
every directed walk from `u` to `z` has `totW ≤ π z - π u`. -/
theorem bf_potential_walk_bound {hasEdge : Nat → Nat → Int → Prop} (π : Nat → Int)
    (hpot : ∀ u v w, hasEdge u v w → π u + w ≤ π v)
    {u z k : Nat} {totW : Int} (hp : DirWalk hasEdge u z k totW) :
    totW ≤ π z - π u := by
  have h := bf_walk_bound (fun x => -π x) 0 (by intro a b w he; have := hpot a b w he; omega) hp
  omega

/-- **Ascending-Potential Closed-Cycle Bound (`bf_potential_cycle_bound`):**
Every closed directed cycle under `π u + w ≤ π v` has non-positive total weight `totW ≤ 0`. -/
theorem bf_potential_cycle_bound {hasEdge : Nat → Nat → Int → Prop} (π : Nat → Int)
    (hpot : ∀ u v w, hasEdge u v w → π u + w ≤ π v)
    {u d : Nat} {totW : Int} (hc : DirWalk hasEdge u u d totW) :
    totW ≤ 0 := by
  have h := bf_potential_walk_bound π hpot hc
  omega

/-- A length-weighted directed walk tracking BOTH total face-edge length `totL : Nat`
and total raw scaled charge `totW : Int`. -/
inductive LenWalk (step : Nat → Nat → Nat → Int → Prop) : Nat → Nat → Nat → Int → Prop
  | nil (u : Nat) : LenWalk step u u 0 0
  | cons {u v z ln restL : Nat} {w restW : Int}
      (hs : step u v ln w) (hp : LenWalk step v z restL restW) :
      LenWalk step u z (ln + restL) (w + restW)

/-- **Shifted-Slope Bellman-Ford Walk Bound (`bf_shifted_walk_bound`):**
If every step `u -(ln, w)-> v` satisfies `π u + (w - slope * ln) ≤ π v`, then every walk
from `u` to `z` of total length `totL` and total weight `totW` obeys
`totW ≤ (π z - π u) + slope * totL`. -/
theorem bf_shifted_walk_bound {step : Nat → Nat → Nat → Int → Prop} (π : Nat → Int) (slope : Int)
    (hpot : ∀ u v ln w, step u v ln w → π u + (w - slope * (ln : Int)) ≤ π v)
    {u z totL : Nat} {totW : Int} (hp : LenWalk step u z totL totW) :
    totW ≤ (π z - π u) + slope * (totL : Int) := by
  induction hp with
  | nil u =>
    simp
  | @cons u v z ln restL w restW hs _ ih =>
    have hstep := hpot u v ln w hs
    have hmul : slope * ((ln + restL : Nat) : Int) = slope * (ln : Int) + slope * (restL : Int) := by
      rw [Int.natCast_add, Int.mul_add]
    omega

/-- **Shifted-Slope Closed Cycle Bound:** on any closed `LenWalk` of length `d`,
`totW ≤ slope * d`. -/
theorem bf_shifted_cycle_bound {step : Nat → Nat → Nat → Int → Prop} (π : Nat → Int) (slope : Int)
    (hpot : ∀ u v ln w, step u v ln w → π u + (w - slope * (ln : Int)) ≤ π v)
    {u d : Nat} {totW : Int} (hc : LenWalk step u u d totW) :
    totW ≤ slope * (d : Int) := by
  have h := bf_shifted_walk_bound π slope hpot hc
  omega

/-- Packed-edge membership relation for chunked `CertTree` graphs. -/
def PackedEdge (chunks : List (List Nat)) (u v : Nat) (w : Int) : Prop :=
  ∃ c ∈ chunks, ∃ e ∈ c, edgeU e = u ∧ edgeV e = v ∧ edgeW e = w

/-- Any walk in a kernel-checked packed-edge graph obeys `totW ≤ π(z) - π(u)`. -/
theorem packedWalk_bound (pi : NTree) (chunks : List (List Nat))
    (hok : checkEdgeChunks pi chunks = true)
    {u z k : Nat} {totW : Int} (hp : DirWalk (PackedEdge chunks) u z k totW) :
    totW ≤ pi.getInt PI_BIAS z - pi.getInt PI_BIAS u :=
  bf_potential_walk_bound (pi.getInt PI_BIAS)
    (fun _ _ _ ⟨c, hc, e, he, hu, hv, hw⟩ => by
      subst hu; subst hv; subst hw
      exact checkEdgeChunks_eq_true pi PI_BIAS hok c hc e he)
    hp

/-- Any closed cycle in a kernel-checked packed-edge graph obeys `totW ≤ 0`. -/
theorem packedCycle_bound (pi : NTree) (chunks : List (List Nat))
    (hok : checkEdgeChunks pi chunks = true)
    {u k : Nat} {totW : Int} (hc : DirWalk (PackedEdge chunks) u u k totW) :
    totW ≤ 0 := by
  have h := packedWalk_bound pi chunks hok hc
  omega

/-- **DAG Potential Path Bound (`dag_potential_path_bound`):**
For any cyclic-DP DAG certified with `U(0) = 0`, `U(1) ≤ B`, and `checkEdgeChunks U edges = true`,
every directed path from source `0` to sink `1` has total weight `≤ B`. -/
theorem dag_potential_path_bound (U : NTree) (edges : List (List Nat)) (B : Int)
    (hok : checkEdgeChunks U edges = true)
    (hsrc : U.getInt PI_BIAS 0 = 0)
    (hsnk : U.getInt PI_BIAS 1 ≤ B)
    {k : Nat} {totW : Int} (hp : DirWalk (PackedEdge edges) 0 1 k totW) :
    totW ≤ B := by
  have h := packedWalk_bound U edges hok hp
  omega

/-- **Forward Dynamic Programming Soundness Theorem (`dp_upper_bound_sound`):**
Given a finite automaton `step : Fin N → Fin N → Int → Prop` and an upper-bound DP table
`U : Fin N → Nat → Fin N → Int` satisfying:
- Base case `0 ≤ U s 0 s`,
- Transition invariant `U s k u + w ≤ U s (k + 1) v` for all `k < d` and valid steps `u -(w)-> v`,
then EVERY `d`-step directed walk starting at `s` and ending at `cur` has total weight `≤ U s d cur`.
In particular, every closed cycle of length `d` at `s` has weight `≤ U s d s`. -/
inductive FinWalk {N : Nat} (step : Fin N → Fin N → Int → Prop) :
    Fin N → Nat → Fin N → Int → Prop
  | nil (s : Fin N) : FinWalk step s 0 s 0
  | snoc {s u v : Fin N} {k : Nat} {acc w : Int}
      (hp : FinWalk step s k u acc) (hs : step u v w) :
      FinWalk step s (k + 1) v (acc + w)

theorem dp_upper_bound_walk_sound {N : Nat} (step : Fin N → Fin N → Int → Prop)
    (U : Fin N → Nat → Fin N → Int) (s : Fin N) (d : Nat)
    (hbase : 0 ≤ U s 0 s)
    (hstep : ∀ k, k < d → ∀ u v w, step u v w → U s k u + w ≤ U s (k + 1) v) :
    ∀ {k : Nat} (_hk : k ≤ d) {cur : Fin N} {totW : Int},
      FinWalk step s k cur totW → totW ≤ U s k cur := by
  intro k hk cur totW hp
  induction hp with
  | nil => exact hbase
  | @snoc u v k' acc w hp' hs ih =>
    have ih' := ih (by omega)
    have htr := hstep k' (by omega) u v w hs
    omega

theorem dp_upper_bound_sound {N : Nat} (step : Fin N → Fin N → Int → Prop)
    (U : Fin N → Nat → Fin N → Int) (s : Fin N) (d : Nat)
    (hbase : 0 ≤ U s 0 s)
    (hstep : ∀ k, k < d → ∀ u v w, step u v w → U s k u + w ≤ U s (k + 1) v)
    {totW : Int} (hcyc : FinWalk step s d s totW) :
    totW ≤ U s d s :=
  dp_upper_bound_walk_sound step U s d hbase hstep (Nat.le_refl d) hcyc

/-- **Backward Dynamic Programming Soundness Theorem (`bwd_dp_upper_bound_sound`):**
Given a variable-length automaton `step : Nat → Nat → Nat → Int → Prop` and a backward DP table
`U : Nat → Nat → Int` with `0 ≤ U 0 z` for closing states `z` and
`U (rem - ln) v + w ≤ U rem u` for all `ln ≤ rem ≤ maxRem` and steps `u -(ln, w)-> v`,
every `LenWalk` of total length `rem ≤ maxRem` from `u` to a closing state `z` has `totW ≤ U rem u`. -/
theorem bwd_dp_upper_bound_sound {step : Nat → Nat → Nat → Int → Prop}
    (U : Nat → Nat → Int) (isClose : Nat → Prop) (maxRem : Nat)
    (hbase : ∀ z, isClose z → 0 ≤ U 0 z)
    (hstep : ∀ u v ln w, step u v ln w →
      ∀ rem, rem ≤ maxRem → ln ≤ rem → U (rem - ln) v + w ≤ U rem u)
    {u z rem : Nat} {totW : Int} (hrem : rem ≤ maxRem)
    (hclose : isClose z) (hp : LenWalk step u z rem totW) :
    totW ≤ U rem u := by
  induction hp with
  | nil z => exact hbase z hclose
  | @cons u v z ln restL w restW hs hp' ih =>
    have hih := ih (by omega) hclose
    have htr := hstep u v ln w hs (ln + restL) hrem (by omega)
    have hsub : ln + restL - ln = restL := Nat.add_sub_cancel_left ln restL
    rw [hsub] at htr
    omega

/-! ## 2. Cubic Face-Discharging Conservation & Contradiction Master Lemmas -/

/-- **Cubic Face-Discharging Master Contradiction (`cubic_discharging_contradiction`):**
Given any cubic `PlaneMap n` (`M.graph.IsCubic`), positive common denominator `S > 0`,
and charge-conserving discharging transfers `inCh, outCh` such that:
- Every clean face (`isFrozen f = false`) has final scaled charge `cFin f ≤ 0`,
- The frozen `CAP` faces have total final scaled charge `≤ 10 * S`,
then `False`! (Directly combines `euler_face_discharging_sum` and `charge_conservation_contradiction`.) -/
theorem cubic_discharging_contradiction {n : Nat} (M : PlaneMap n) (hcubic : M.graph.IsCubic)
    (isFrozen : List (Fin n) → Bool) (S : Int) (hS : S > 0)
    (inCh outCh cFin : List (Fin n) → Int)
    (hdef : ∀ f ∈ M.faces, cFin f = S * ((6 : Int) - (f.length : Int)) + inCh f - outCh f)
    (hbal : sumInt (M.faces.map inCh) = sumInt (M.faces.map outCh))
    (hclean : ∀ f ∈ M.faces, isFrozen f = false → cFin f ≤ 0)
    (hfrozen : sumInt ((M.faces.filter isFrozen).map cFin) ≤ 10 * S) :
    False := by
  let c0 : List (Fin n) → Int := fun f => S * ((6 : Int) - (f.length : Int))
  have hinit : sumInt (M.faces.map c0) = 12 * S := by
    show sumInt (M.faces.map fun f => S * ((6 : Int) - (f.length : Int))) = 12 * S
    rw [sumInt_map_mul_left, euler_face_discharging_sum M hcubic]
    omega
  have hcons : sumInt (M.faces.map cFin) = sumInt (M.faces.map c0) :=
    charge_conserved_of_transfers M.faces c0 cFin inCh outCh hdef hbal
  exact charge_conservation_contradiction M.faces isFrozen c0 cFin S hinit hcons hclean (by omega)

/-- **Relaxed Frozen-`CAP` Cubic Discharging Contradiction (`cubic_relaxed_discharging_contradiction`):**
Even under relaxed `CAP` endpoints where the frozen face sum satisfies `3 * frozenSum ≤ 32 * S`
(i.e. `frozenSum ≤ (32/3) * S < 12 * S`), `False` follows identically! -/
theorem cubic_relaxed_discharging_contradiction {n : Nat} (M : PlaneMap n) (hcubic : M.graph.IsCubic)
    (isFrozen : List (Fin n) → Bool) (S : Int) (hS : S > 0)
    (inCh outCh cFin : List (Fin n) → Int)
    (hdef : ∀ f ∈ M.faces, cFin f = S * ((6 : Int) - (f.length : Int)) + inCh f - outCh f)
    (hbal : sumInt (M.faces.map inCh) = sumInt (M.faces.map outCh))
    (hclean : ∀ f ∈ M.faces, isFrozen f = false → cFin f ≤ 0)
    (hfrozen : 3 * sumInt ((M.faces.filter isFrozen).map cFin) ≤ 32 * S) :
    False := by
  let c0 : List (Fin n) → Int := fun f => S * ((6 : Int) - (f.length : Int))
  have hinit : sumInt (M.faces.map c0) = 12 * S := by
    show sumInt (M.faces.map fun f => S * ((6 : Int) - (f.length : Int))) = 12 * S
    rw [sumInt_map_mul_left, euler_face_discharging_sum M hcubic]
    omega
  have hcons : sumInt (M.faces.map cFin) = sumInt (M.faces.map c0) :=
    charge_conserved_of_transfers M.faces c0 cFin inCh outCh hdef hbal
  exact charge_conservation_contradiction M.faces isFrozen c0 cFin S hinit hcons hclean (by omega)

/-! ## 3. Kernel-Verified Bellman-Ford Dual Potentials (`d ≥ 33` & Frozen `CAP`) -/

/-- All `667` directed transitions of the `cubic_d33` automaton satisfy the exact
dual potential inequality at `scale = 1320`, per-edge slope `b = 9/11` (`1080 / 1320`). -/
theorem cubic_d33_bf_valid :
    ∀ c ∈ d33Edges, ∀ e ∈ c,
      d33Pi.getInt PI_BIAS (edgeU e) + edgeW e ≤ d33Pi.getInt PI_BIAS (edgeV e) :=
  checkEdgeChunks_eq_true d33Pi PI_BIAS d33_edges_ok

/-- **Clean Big Faces `d ≥ 33` Charge Bound (`cubic_clean_d_ge_33_charge_le`):**
For ANY closed automaton cycle of face length `d ≥ 33` with scaled total received charge
`recvScaled` (at `scale = 1320`), where shifted edge weights sum to `recvScaled - 1080 * d`:
1. By `packedCycle_bound` on `cubic_d33`, `recvScaled - 1080 * d ≤ 0`,
2. Since `d ≥ 33`, `1080 * d ≤ 1320 * (d - 6)` (as `9 * d ≤ 11 * (d - 6)`),
3. Therefore `recvScaled ≤ 1320 * (d - 6)`, i.e. final charge `(6 - d) + recv ≤ 0`! -/
theorem cubic_clean_d_ge_33_charge_le (d : Nat) (hd : d ≥ 33)
    {u k : Nat} {recvScaled : Int}
    (hc : DirWalk (PackedEdge d33Edges) u u k (recvScaled - 1080 * (d : Int))) :
    recvScaled ≤ 1320 * ((d : Int) - 6) := by
  have hcyc : recvScaled - 1080 * (d : Int) ≤ 0 := packedCycle_bound d33Pi d33Edges d33_edges_ok hc
  omega

/-- All `1,588` directed transitions of the `cubic_frozen_cap` automaton (`H = 1`, `scale = 120`,
slope `b = 1`) satisfy the exact dual potential inequality. -/
theorem cubic_frozen_cap_bf_valid :
    ∀ c ∈ frzEdges, ∀ e ∈ c,
      frzPi.getInt PI_BIAS (edgeU e) + edgeW e ≤ frzPi.getInt PI_BIAS (edgeV e) :=
  checkEdgeChunks_eq_true frzPi PI_BIAS frz_edges_ok

/-- **Frozen `CAP` Face Charge Bound (`cubic_frozen_cap_bound`):**
Every closed automaton cycle through `CAP#0` of non-cap face edges `d - 1` (so the face has
total length `d`) has shifted total weight `recvScaled - 120 * (d - 1) ≤ 0`.
Hence the scaled final charge `120 * (6 - d) + recvScaled ≤ 120 * 5 = 600` (i.e. `≤ 5` per
frozen face), so at most `2` frozen faces sum to `≤ 10 * 120 < 12 * 120`! -/
theorem cubic_frozen_cap_bound (d : Nat)
    {k : Nat} {recvScaled : Int}
    (hc : DirWalk (PackedEdge frzEdges) frzCapIdx frzCapIdx k (recvScaled - 120 * ((d : Int) - 1))) :
    120 * ((6 : Int) - (d : Int)) + recvScaled ≤ 5 * 120 ∧
    2 * (120 * ((6 : Int) - (d : Int)) + recvScaled) < 12 * 120 := by
  have hcyc : recvScaled - 120 * ((d : Int) - 1) ≤ 0 :=
    packedCycle_bound frzPi frzEdges frz_edges_ok hc
  omega

/-- **Relaxed Frozen `CAP` Face Charge Bound (`cubic_frozen_cap_relaxed_bound`):**
Allowing arbitrary first and last tokens adjacent to the `CAP` edge:
for any valid initial token `(u0, w0)` in `frzRelInitPairs`, any core walk `u0 →* uEnd`
in `frzRelCoreEdges` of weight `coreW`, and any valid ending state `uEnd ∈ frzRelEndNodes`,
the total shifted weight `w0 + coreW ≤ 40` (`40 / 120 = 1/3`), giving final charge
`≤ 5 + 1/3 = 16/3` per frozen face (`3 * (2 * final) ≤ 32 * 120 < 36 * 120`)! -/
theorem cubic_frozen_cap_relaxed_bound (d : Nat)
    {p0 uEnd k : Nat} {coreW recvScaled : Int}
    (hp0 : p0 ∈ frzRelInitPairs)
    (hend : uEnd ∈ frzRelEndNodes)
    (hw : DirWalk (PackedEdge frzRelCoreEdges) (p0 / WT_RADIX) uEnd k coreW)
    (htot : recvScaled - 120 * ((d : Int) - 1) = (((p0 % WT_RADIX : Nat) : Int) - (PI_BIAS : Int)) + coreW) :
    120 * ((6 : Int) - (d : Int)) + recvScaled ≤ 640 ∧
    3 * (2 * (120 * ((6 : Int) - (d : Int)) + recvScaled)) ≤ 32 * 120 ∧
    3 * (2 * (120 * ((6 : Int) - (d : Int)) + recvScaled)) < 36 * 120 := by
  have hinit := checkInitLower_eq_true frzRelPi PI_BIAS frzRel_init_ok p0 hp0
  have hwalk := packedWalk_bound frzRelPi frzRelCoreEdges frzRel_core_ok hw
  have hup := checkNodeUpper_eq_true frzRelPi PI_BIAS frzRelExcessNat frzRel_end_ok uEnd hend
  have hval : (frzRelExcessNat : Int) - (PI_BIAS : Int) = 40 := by decide
  omega

/-! ## 4. Proof-Carrying Clean `d ≤ 31` Bounds (Plain BF, Shifted-Slope BF, Cyclic DP, & BWD DP) -/

/-- Helper for shifted-slope BF walks starting from a certified init pair and ending in `ends`. -/
theorem shifted_bf_walk_bound (pi : NTree) (edges : List (List Nat)) (inits ends : List Nat)
    (boundNat : Nat) (boundInt : Int)
    (hedges : checkEdgeChunks pi edges = true)
    (hinit : checkInitLower pi inits = true)
    (hends : checkNodeUpper pi boundNat ends = true)
    (hb : (boundNat : Int) - (PI_BIAS : Int) = boundInt)
    {p0 uEnd k : Nat} {restW : Int}
    (hp0 : p0 ∈ inits) (hend : uEnd ∈ ends)
    (hw : DirWalk (PackedEdge edges) (p0 / WT_RADIX) uEnd k restW) :
    (((p0 % WT_RADIX : Nat) : Int) - (PI_BIAS : Int)) + restW ≤ boundInt := by
  have hi := checkInitLower_eq_true pi PI_BIAS hinit p0 hp0
  have hwk := packedWalk_bound pi edges hedges hw
  have hu := checkNodeUpper_eq_true pi PI_BIAS boundNat hends uEnd hend
  omega

-- 4A. Plain Bellman-Ford: d ∈ {7, 28, 29, 30, 31} and unified `no-N` for d ∈ {19..27}

theorem cubic_clean_d7_bound {u k : Nat} {recvScaled : Int}
    (hc : DirWalk (PackedEdge d7Edges) u u k (recvScaled - 4 * 7)) :
    recvScaled ≤ 28 * (7 - 6) := by
  have := packedCycle_bound d7Pi d7Edges d7_ok hc; omega

theorem cubic_clean_d28_bound {u k : Nat} {recvScaled : Int}
    (hc : DirWalk (PackedEdge d28Edges) u u k (recvScaled - 660 * 28)) :
    recvScaled ≤ 840 * (28 - 6) := by
  have := packedCycle_bound d28Pi d28Edges d28_ok hc; omega

theorem cubic_clean_d29_bound {u k : Nat} {recvScaled : Int}
    (hc : DirWalk (PackedEdge d29Edges) u u k (recvScaled - 2760 * 29)) :
    recvScaled ≤ 3480 * (29 - 6) := by
  have := packedCycle_bound d29Pi d29Edges d29_ok hc; omega

theorem cubic_clean_d30_bound {u k : Nat} {recvScaled : Int}
    (hc : DirWalk (PackedEdge d30Edges) u u k (recvScaled - 96 * 30)) :
    recvScaled ≤ 120 * (30 - 6) := by
  have := packedCycle_bound d30Pi d30Edges d30_ok hc; omega

theorem cubic_clean_d31_bound {u k : Nat} {recvScaled : Int}
    (hc : DirWalk (PackedEdge d31Edges) u u k (recvScaled - 1500 * 31)) :
    recvScaled ≤ 1860 * (31 - 6) := by
  have := packedCycle_bound d31Pi d31Edges d31_ok hc; omega

/-- Unified `no-'N'` Plain Bellman-Ford bound covering ALL `d ≥ 19` (`13/19 ≤ (d - 6)/d`,
`scale = 2280`, `2280 * (13/19) = 1560`). -/
theorem cubic_clean_noN_d_ge_19_bound (d : Nat) (hd : d ≥ 19)
    {u k : Nat} {recvScaled : Int}
    (hc : DirWalk (PackedEdge noN19to27Edges) u u k (recvScaled - 1560 * (d : Int))) :
    recvScaled ≤ 2280 * ((d : Int) - 6) := by
  have h := packedCycle_bound noN19to27Pi noN19to27Edges noN19to27_ok hc
  omega

-- 4B. Shifted-Slope Bellman-Ford: d ∈ {15, 19 (S_YZ / S_X), 20, 21, 22, 23, 24, 25, 26, 27}

theorem cubic_clean_d15_bound {p0 uEnd k : Nat} {restW recvScaled : Int}
    (hp0 : p0 ∈ d15Init) (hend : uEnd ∈ d15Ends)
    (hw : DirWalk (PackedEdge d15Edges) (p0 / WT_RADIX) uEnd k restW)
    (hshift : recvScaled - 60 * 15 ≤ (((p0 % WT_RADIX : Nat) : Int) - (PI_BIAS : Int)) + restW + 24) :
    recvScaled ≤ 120 * (15 - 6) := by
  have h := shifted_bf_walk_bound d15Pi d15Edges d15Init d15Ends d15BoundNat d15Bound
    d15_edges_ok d15_init_ok d15_ends_ok (by decide) hp0 hend hw
  unfold d15Bound at h; omega

theorem cubic_clean_d19_hasSYZ_bound {p0 uEnd k : Nat} {restW recvScaled : Int}
    (hp0 : p0 ∈ d19SYZInit) (hend : uEnd ∈ d19SYZEnds)
    (hw : DirWalk (PackedEdge d19SYZEdges) (p0 / WT_RADIX) uEnd k restW)
    (hshift : recvScaled - 60 * 19 = (((p0 % WT_RADIX : Nat) : Int) - (PI_BIAS : Int)) + restW) :
    recvScaled ≤ 120 * (19 - 6) := by
  have h := shifted_bf_walk_bound d19SYZPi d19SYZEdges d19SYZInit d19SYZEnds d19SYZBoundNat d19SYZBound
    d19SYZ_edges_ok d19SYZ_init_ok d19SYZ_ends_ok (by decide) hp0 hend hw
  unfold d19SYZBound at h; omega

theorem cubic_clean_d19_hasSX_bound {p0 uEnd k : Nat} {restW recvScaled : Int}
    (hp0 : p0 ∈ d19SXInit) (hend : uEnd ∈ d19SXEnds)
    (hw : DirWalk (PackedEdge d19SXEdges) (p0 / WT_RADIX) uEnd k restW)
    (hshift : recvScaled - 60 * 19 = (((p0 % WT_RADIX : Nat) : Int) - (PI_BIAS : Int)) + restW) :
    recvScaled ≤ 120 * (19 - 6) := by
  have h := shifted_bf_walk_bound d19SXPi d19SXEdges d19SXInit d19SXEnds d19SXBoundNat d19SXBound
    d19SX_edges_ok d19SX_init_ok d19SX_ends_ok (by decide) hp0 hend hw
  unfold d19SXBound at h; omega

theorem cubic_clean_d20_bound {p0 uEnd k : Nat} {restW recvScaled : Int}
    (hp0 : p0 ∈ d20Init) (hend : uEnd ∈ d20Ends)
    (hw : DirWalk (PackedEdge d20Edges) (p0 / WT_RADIX) uEnd k restW)
    (hshift : recvScaled - 70 * 20 = (((p0 % WT_RADIX : Nat) : Int) - (PI_BIAS : Int)) + restW) :
    recvScaled ≤ 120 * (20 - 6) := by
  have h := shifted_bf_walk_bound d20Pi d20Edges d20Init d20Ends d20BoundNat d20Bound
    d20_edges_ok d20_init_ok d20_ends_ok (by decide) hp0 hend hw
  unfold d20Bound at h; omega

theorem cubic_clean_d21_bound {p0 uEnd k : Nat} {restW recvScaled : Int}
    (hp0 : p0 ∈ d21Init) (hend : uEnd ∈ d21Ends)
    (hw : DirWalk (PackedEdge d21Edges) (p0 / WT_RADIX) uEnd k restW)
    (hshift : recvScaled - 60 * 21 = (((p0 % WT_RADIX : Nat) : Int) - (PI_BIAS : Int)) + restW) :
    recvScaled ≤ 120 * (21 - 6) := by
  have h := shifted_bf_walk_bound d21Pi d21Edges d21Init d21Ends d21BoundNat d21Bound
    d21_edges_ok d21_init_ok d21_ends_ok (by decide) hp0 hend hw
  unfold d21Bound at h; omega

theorem cubic_clean_d22_bound {p0 uEnd k : Nat} {restW recvScaled : Int}
    (hp0 : p0 ∈ d22Init) (hend : uEnd ∈ d22Ends)
    (hw : DirWalk (PackedEdge d22Edges) (p0 / WT_RADIX) uEnd k restW)
    (hshift : recvScaled - 60 * 22 = (((p0 % WT_RADIX : Nat) : Int) - (PI_BIAS : Int)) + restW) :
    recvScaled ≤ 120 * (22 - 6) := by
  have h := shifted_bf_walk_bound d22Pi d22Edges d22Init d22Ends d22BoundNat d22Bound
    d22_edges_ok d22_init_ok d22_ends_ok (by decide) hp0 hend hw
  unfold d22Bound at h; omega

theorem cubic_clean_d23_bound {p0 uEnd k : Nat} {restW recvScaled : Int}
    (hp0 : p0 ∈ d23Init) (hend : uEnd ∈ d23Ends)
    (hw : DirWalk (PackedEdge d23Edges) (p0 / WT_RADIX) uEnd k restW)
    (hshift : recvScaled - 60 * 23 = (((p0 % WT_RADIX : Nat) : Int) - (PI_BIAS : Int)) + restW) :
    recvScaled ≤ 120 * (23 - 6) := by
  have h := shifted_bf_walk_bound d23Pi d23Edges d23Init d23Ends d23BoundNat d23Bound
    d23_edges_ok d23_init_ok d23_ends_ok (by decide) hp0 hend hw
  unfold d23Bound at h; omega

theorem cubic_clean_d24_bound {p0 uEnd k : Nat} {restW recvScaled : Int}
    (hp0 : p0 ∈ d24Init) (hend : uEnd ∈ d24Ends)
    (hw : DirWalk (PackedEdge d24Edges) (p0 / WT_RADIX) uEnd k restW)
    (hshift : recvScaled - 60 * 24 = (((p0 % WT_RADIX : Nat) : Int) - (PI_BIAS : Int)) + restW) :
    recvScaled ≤ 120 * (24 - 6) := by
  have h := shifted_bf_walk_bound d24Pi d24Edges d24Init d24Ends d24BoundNat d24Bound
    d24_edges_ok d24_init_ok d24_ends_ok (by decide) hp0 hend hw
  unfold d24Bound at h; omega

theorem cubic_clean_d25_bound {p0 uEnd k : Nat} {restW recvScaled : Int}
    (hp0 : p0 ∈ d25Init) (hend : uEnd ∈ d25Ends)
    (hw : DirWalk (PackedEdge d25Edges) (p0 / WT_RADIX) uEnd k restW)
    (hshift : recvScaled - 60 * 25 = (((p0 % WT_RADIX : Nat) : Int) - (PI_BIAS : Int)) + restW) :
    recvScaled ≤ 120 * (25 - 6) := by
  have h := shifted_bf_walk_bound d25Pi d25Edges d25Init d25Ends d25BoundNat d25Bound
    d25_edges_ok d25_init_ok d25_ends_ok (by decide) hp0 hend hw
  unfold d25Bound at h; omega

theorem cubic_clean_d26_bound {p0 uEnd k : Nat} {restW recvScaled : Int}
    (hp0 : p0 ∈ d26Init) (hend : uEnd ∈ d26Ends)
    (hw : DirWalk (PackedEdge d26Edges) (p0 / WT_RADIX) uEnd k restW)
    (hshift : recvScaled - 60 * 26 = (((p0 % WT_RADIX : Nat) : Int) - (PI_BIAS : Int)) + restW) :
    recvScaled ≤ 120 * (26 - 6) := by
  have h := shifted_bf_walk_bound d26Pi d26Edges d26Init d26Ends d26BoundNat d26Bound
    d26_edges_ok d26_init_ok d26_ends_ok (by decide) hp0 hend hw
  unfold d26Bound at h; omega

theorem cubic_clean_d27_bound {p0 uEnd k : Nat} {restW recvScaled : Int}
    (hp0 : p0 ∈ d27Init) (hend : uEnd ∈ d27Ends)
    (hw : DirWalk (PackedEdge d27Edges) (p0 / WT_RADIX) uEnd k restW)
    (hshift : recvScaled - 75 * 27 = (((p0 % WT_RADIX : Nat) : Int) - (PI_BIAS : Int)) + restW) :
    recvScaled ≤ 120 * (27 - 6) := by
  have h := shifted_bf_walk_bound d27Pi d27Edges d27Init d27Ends d27BoundNat d27Bound
    d27_edges_ok d27_init_ok d27_ends_ok (by decide) hp0 hend hw
  unfold d27Bound at h; omega

-- 4C. Exact Cyclic DP DAGs: d ∈ {9, 10, 11, 12, 13}

theorem cubic_clean_d9_bound {k : Nat} {totW : Int}
    (hp : DirWalk (PackedEdge d9Edges) 0 1 k totW) :
    totW ≤ 120 * (9 - 6) :=
  dag_potential_path_bound d9U d9Edges d9Budget d9_edges_ok d9_src_zero d9_snk_le hp

theorem cubic_clean_d10_bound {k : Nat} {totW : Int}
    (hp : DirWalk (PackedEdge d10Edges) 0 1 k totW) :
    totW ≤ 120 * (10 - 6) :=
  dag_potential_path_bound d10U d10Edges d10Budget d10_edges_ok d10_src_zero d10_snk_le hp

theorem cubic_clean_d11_bound {k : Nat} {totW : Int}
    (hp : DirWalk (PackedEdge d11Edges) 0 1 k totW) :
    totW ≤ 120 * (11 - 6) :=
  dag_potential_path_bound d11U d11Edges d11Budget d11_edges_ok d11_src_zero d11_snk_le hp

theorem cubic_clean_d12_bound {k : Nat} {totW : Int}
    (hp : DirWalk (PackedEdge d12Edges) 0 1 k totW) :
    totW ≤ 120 * (12 - 6) :=
  dag_potential_path_bound d12U d12Edges d12Budget d12_edges_ok d12_src_zero d12_snk_le hp

theorem cubic_clean_d13_bound {k : Nat} {totW : Int}
    (hp : DirWalk (PackedEdge d13Edges) 0 1 k totW) :
    totW ≤ 120 * (13 - 6) :=
  dag_potential_path_bound d13U d13Edges d13Budget d13_edges_ok d13_src_zero d13_snk_le hp

-- 4D. Exact 19-Row Backward DP: d = 19 (starts at `'N'`, no `S_YZ`, no `S_X`, `170` quotient states)

def PackedBwdEdge (chunks : List (List Nat)) (u v ln : Nat) (w : Int) : Prop :=
  ∃ c ∈ chunks, ∃ e ∈ c, bwdU e = u ∧ bwdV e = v ∧ bwdL e = ln ∧ bwdW e = w

theorem cubic_clean_d19_noSYZ_noSX_bound {z : Nat} {totW : Int}
    (hz : z ∈ d19ClosingQs)
    (hp : LenWalk (PackedBwdEdge d19BwdEdges) d19StartQ z 18 totW) :
    totW ≤ 120 * (19 - 6) := by
  have hwalk : totW ≤ (d19Rows 18).getInt PI_BIAS d19StartQ :=
    bwd_dp_upper_bound_sound (fun rem st => (d19Rows rem).getInt PI_BIAS st)
      (fun q => q ∈ d19ClosingQs) 18
      (fun q hq => by
        have hmem : q * WT_RADIX + PI_BIAS ∈ d19ClosingQs.map (fun x => x * WT_RADIX + PI_BIAS) :=
          List.mem_map.mpr ⟨q, hq, rfl⟩
        have hlo := checkInitLower_eq_true d19Row0 PI_BIAS d19_bwd_base_ok _ hmem
        have hdiv : (q * WT_RADIX + PI_BIAS) / WT_RADIX = q := by
          have hlt : PI_BIAS < WT_RADIX := by decide
          rw [Nat.mul_comm, Nat.mul_add_div (by decide), Nat.div_eq_of_lt hlt, Nat.add_zero]
        have hmod : (q * WT_RADIX + PI_BIAS) % WT_RADIX = PI_BIAS := by
          have hlt : PI_BIAS < WT_RADIX := by decide
          rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hlt]
        rw [hdiv, hmod] at hlo
        show 0 ≤ d19Row0.getInt PI_BIAS q
        omega)
      (fun _ _ _ _ ⟨c, hc, e, he, hu, hv, hl, hw⟩ rem hrem hln => by
        subst hu; subst hv; subst hl; subst hw
        exact (checkBwdEdgeChunks_eq_true d19Rows PI_BIAS 18 d19_bwd_edges_ok c hc e he).2 rem hrem hln)
      (Nat.le_refl 18) hz hp
  have hst : d19Row18.getInt PI_BIAS d19StartQ ≤ 120 * (19 - 6) := d19_bwd_start_le
  exact Int.le_trans hwalk hst

/-- **Replay-matched table specification** for the conservative-enumeration boundary at
`d ∈ {14, 17, 18}` matching `cert/witnesses/cyclic_dp_bounds.json`
(`{14: 357 -> 0, 17: 302652 -> 108, 18: 5232 -> 0}`).
**Scope note:** This Lean declaration records and checks the literal boundary counts stored in
`CubicDP1Data`; the conservative forward/backward enumeration itself is executed and verified
by `cert/verify_planar_eg.py` (with graph-level start/symmetry/shift justification in the
manuscript), while all `108` surviving `d = 17` residuals are explicitly verified below. -/
theorem cubic_conservative_enum_boundary_spec :
    enumD14Overweight = 357 ∧ enumD14Survivors = 0 ∧
    enumD17Overweight = 302652 ∧ enumD17Survivors = 108 ∧
    enumD18Overweight = 5232 ∧ enumD18Survivors = 0 := by
  decide

/-! ## 5. Explicit Simple-Cycle Witnesses for ALL `108` `d = 17` Residuals (`CubicD17Data`) -/

private theorem faceHasEdge_go_symm (a b x : Nat) :
    ∀ (prev : Nat) (xs : List Nat),
      faceHasEdge.go a b x prev xs = faceHasEdge.go b a x prev xs := by
  intro prev xs
  induction xs generalizing prev with
  | nil =>
    simp only [faceHasEdge.go]
    cases (prev == a) <;> cases (x == b) <;> cases (prev == b) <;> cases (x == a) <;> rfl
  | cons y ys ih =>
    simp only [faceHasEdge.go]
    have hcond : ((prev == a && y == b) || (prev == b && y == a)) =
                 ((prev == b && y == a) || (prev == a && y == b)) := by
      cases (prev == a) <;> cases (y == b) <;> cases (prev == b) <;> cases (y == a) <;> rfl
    rw [hcond, ih y]

private theorem faceHasEdge_symm (a b : Nat) (f : List Nat) :
    faceHasEdge a b f = faceHasEdge b a f := by
  cases f with
  | nil => rfl
  | cons x xs => exact faceHasEdge_go_symm a b x x xs

private theorem facesHaveEdge_symm (faces : List (List Nat)) (a b : Nat) :
    facesHaveEdge faces a b = facesHaveEdge faces b a := by
  unfold facesHaveEdge
  induction faces with
  | nil => rfl
  | cons f fs ih =>
    simp only [List.any_cons, faceHasEdge_symm a b f, ih]

/-- Construct the genuine finite simple graph `FinGraph w.numVerts` of a planar weld patch. -/
def weldFaceGraph (w : WeldWitness) : FinGraph w.numVerts where
  adj u v := (u != v) && facesHaveEdge w.faces u.val v.val
  symm u v := by
    have hne : (u != v) = (v != u) := by
      by_cases h : u = v
      · subst h; simp
      · have h1 : (u != v) = true := bne_iff_ne.mpr h
        have h2 : (v != u) = true := bne_iff_ne.mpr (Ne.symm h)
        rw [h1, h2]
    rw [hne, facesHaveEdge_symm]
  loopless u := by simp

private theorem allLtNat_cons_head {n x : Nat} {xs : List Nat}
    (h : allLtNat n (x :: xs) = true) : x < n := by
  unfold allLtNat at h
  cases hx : Nat.blt x n
  · rw [hx] at h; cases h
  · unfold Nat.blt at hx
    have := Nat.le_of_ble_eq_true hx
    omega

private theorem allLtNat_cons_tail {n x : Nat} {xs : List Nat}
    (h : allLtNat n (x :: xs) = true) : allLtNat n xs = true := by
  unfold allLtNat at h
  cases hx : Nat.blt x n
  · rw [hx] at h; cases h
  · rw [hx] at h; exact h

private def toFinList (n : Nat) : (xs : List Nat) → allLtNat n xs = true → List (Fin n)
  | [], _ => []
  | x :: xs, h => ⟨x, allLtNat_cons_head h⟩ :: toFinList n xs (allLtNat_cons_tail h)

private theorem toFinList_length (n : Nat) :
    ∀ (xs : List Nat) (h : allLtNat n xs = true), (toFinList n xs h).length = xs.length
  | [], _ => rfl
  | _ :: xs, h => congrArg Nat.succ (toFinList_length n xs (allLtNat_cons_tail h))

private theorem toFinList_getElem (n : Nat) :
    ∀ (xs : List Nat) (h : allLtNat n xs = true) (i : Nat) (hi : i < xs.length),
      ((toFinList n xs h)[i]'(by rw [toFinList_length]; exact hi)).val = xs[i]'hi
  | [], _, _, hi => absurd hi (Nat.not_lt_zero _)
  | _ :: _, _, 0, _ => rfl
  | _ :: xs, h, j + 1, hi =>
    toFinList_getElem n xs (allLtNat_cons_tail h) j (Nat.lt_of_succ_lt_succ hi)

private theorem nodup_of_nodupNat :
    ∀ {xs : List Nat}, nodupNat xs = true → xs.Nodup
  | [], _ => List.nodup_nil
  | x :: xs, h => by
    unfold nodupNat at h
    cases hc : xs.contains x
    · rw [hc] at h
      have hmem : x ∉ xs := fun hm => by
        have := List.contains_iff_mem.mpr hm
        rw [this] at hc; cases hc
      exact List.nodup_cons.mpr ⟨hmem, nodup_of_nodupNat h⟩
    · rw [hc] at h; cases h

private theorem mem_toFinList_val (n : Nat) :
    ∀ (xs : List Nat) (h : allLtNat n xs = true) (y : Fin n),
      y ∈ toFinList n xs h → y.val ∈ xs
  | [], _, _, hy => by cases hy
  | x :: xs, h, y, hy => by
    rcases List.mem_cons.mp hy with rfl | hrest
    · exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem x (mem_toFinList_val n xs (allLtNat_cons_tail h) y hrest)

private theorem toFinList_nodup (n : Nat) :
    ∀ (xs : List Nat) (hlt : allLtNat n xs = true), xs.Nodup → (toFinList n xs hlt).Nodup
  | [], _, _ => List.nodup_nil
  | x :: xs, hlt, hnd => by
    rcases List.nodup_cons.mp hnd with ⟨hxnot, hndxs⟩
    refine List.nodup_cons.mpr ⟨?_, toFinList_nodup n xs (allLtNat_cons_tail hlt) hndxs⟩
    intro hmem
    exact hxnot (mem_toFinList_val n xs (allLtNat_cons_tail hlt) ⟨x, allLtNat_cons_head hlt⟩ hmem)

private theorem nodup_getElem_ne {α : Type} :
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
        have hj' : j' < xs.length := Nat.lt_of_succ_lt_succ hj
        have hmem : xs[j']'hj' ∈ xs := List.getElem_mem hj'
        exact hxnot (heq ▸ hmem)
    | succ i' =>
      cases j with
      | zero =>
        intro heq
        simp only [List.getElem_cons_zero, List.getElem_cons_succ] at heq
        have hi' : i' < xs.length := Nat.lt_of_succ_lt_succ hi
        have hmem : xs[i']'hi' ∈ xs := List.getElem_mem hi'
        exact hxnot (heq.symm ▸ hmem)
      | succ j' =>
        exact nodup_getElem_ne xs hndxs i' j' (Nat.lt_of_succ_lt_succ hi)
          (Nat.lt_of_succ_lt_succ hj) (fun h => hne (congrArg Nat.succ h))

private theorem isFaceGraphClosedWalk_go_adj (faces : List (List Nat)) (x : Nat) :
    ∀ (prev : Nat) (xs : List Nat),
      isFaceGraphClosedWalk.go faces x prev xs = true →
      (∀ (i : Nat) (hi : i < (prev :: xs).length),
        facesHaveEdge faces ((prev :: xs)[i]'hi)
          (if h2 : i + 1 < (prev :: xs).length then (prev :: xs)[i + 1]'h2 else x) = true)
  | prev, [], h, i, hi => by
    have hi0 : i = 0 := by simp at hi; omega
    subst hi0
    simpa [isFaceGraphClosedWalk.go] using h
  | prev, y :: ys, h, i, hi => by
    unfold isFaceGraphClosedWalk.go at h
    cases he : facesHaveEdge faces prev y
    · rw [he] at h; cases h
    · rw [he] at h
      cases i with
      | zero => simpa using he
      | succ j =>
        have hj : j < (y :: ys).length := Nat.lt_of_succ_lt_succ hi
        have ih := isFaceGraphClosedWalk_go_adj faces x y ys h j hj
        by_cases h2 : j + 1 < (y :: ys).length
        · have h2' : j + 1 + 1 < (prev :: y :: ys).length := Nat.succ_lt_succ h2
          simp only [h2, ↓reduceDIte] at ih
          simp only [h2', ↓reduceDIte, List.getElem_cons_succ]
          exact ih
        · have h2' : ¬(j + 1 + 1 < (prev :: y :: ys).length) := fun hc => h2 (Nat.lt_of_succ_lt_succ hc)
          simp only [h2, ↓reduceDIte] at ih
          simp only [h2', ↓reduceDIte, List.getElem_cons_succ]
          exact ih

private theorem isFaceGraphClosedWalk_adj (faces : List (List Nat)) :
    ∀ (xs : List Nat), isFaceGraphClosedWalk faces xs = true →
      ∀ (i : Nat) (hi : i < xs.length),
        facesHaveEdge faces (xs[i]'hi)
          (xs[(i + 1) % xs.length]'(Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le i) hi))) = true
  | [], h, _, hi => absurd hi (Nat.not_lt_zero _)
  | x :: xs, h, i, hi => by
    have hgo := isFaceGraphClosedWalk_go_adj faces x x xs h i hi
    by_cases hlt : i + 1 < (x :: xs).length
    · have hmod : (i + 1) % (x :: xs).length = i + 1 := Nat.mod_eq_of_lt hlt
      simp only [hlt, ↓reduceDIte] at hgo
      have hidx : (x :: xs)[(i + 1) % (x :: xs).length]'(Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le i) hi)) =
                  (x :: xs)[i + 1]'hlt := by simp only [hmod]
      rw [hidx]
      exact hgo
    · have heq : i + 1 = (x :: xs).length := by omega
      have hmod : (i + 1) % (x :: xs).length = 0 := by rw [heq, Nat.mod_self]
      simp only [hlt, ↓reduceDIte] at hgo
      have hidx : (x :: xs)[(i + 1) % (x :: xs).length]'(Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le i) hi)) =
                  x := by simp only [hmod, List.getElem_cons_zero]
      rw [hidx]
      exact hgo

/-- **Weld-to-`FinGraph` Dyadic Cycle Bridging Theorem (`weldFaceGraph_hasDyadicCycle`):**
Any `WeldWitness` verified by `checkWeldDyadicCycle` contains a genuine simple dyadic cycle
(`C_4, C_8, C_16,` or `C_32`) in `weldFaceGraph w`! -/
theorem weldFaceGraph_hasDyadicCycle (w : WeldWitness)
    (h : checkWeldDyadicCycle w.numVerts w.faces w.cycle = true) :
    (weldFaceGraph w).HasDyadicCycleUpTo 32 := by
  unfold checkWeldDyadicCycle at h
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at h
  rcases h with ⟨⟨⟨hlen, hlt⟩, hnd_b⟩, hwalk⟩
  have hnd : w.cycle.Nodup := nodup_of_nodupNat hnd_b
  let cycF : List (Fin w.numVerts) := toFinList w.numVerts w.cycle hlt
  have hlenF : cycF.length = w.cycle.length := toFinList_length w.numVerts w.cycle hlt
  have hndF : cycF.Nodup := toFinList_nodup w.numVerts w.cycle hlt hnd
  have hge3 : cycF.length ≥ 3 := by
    rw [hlenF]
    rcases hlen with ((h4 | h8) | h16) | h32 <;> omega
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
    have hne_fin : cycF[i]'hi ≠ cycF[j]'hj := nodup_getElem_ne cycF hndF i j hi hj hij_ne
    have hedge : facesHaveEdge w.faces (cycF[i]'hi).val (cycF[j]'hj).val = true := by
      have h1 := toFinList_getElem w.numVerts w.cycle hlt i hi'
      have h2 := toFinList_getElem w.numVerts w.cycle hlt j hj'
      have hadj := isFaceGraphClosedWalk_adj w.faces w.cycle hwalk i hi'
      have hj_eq : j = (i + 1) % w.cycle.length := by show (i + 1) % cycF.length = _; rw [hlenF]
      rw [h1, h2]
      simpa [hj_eq] using hadj
    simp only [weldFaceGraph, Bool.and_eq_true, bne_iff_ne]
    exact ⟨hne_fin, hedge⟩
  rcases hlen with ((h4 | h8) | h16) | h32
  · exact ⟨2, by omega, by decide, cycF, hsimple, by rw [hlenF, h4]⟩
  · exact ⟨3, by omega, by decide, cycF, hsimple, by rw [hlenF, h8]⟩
  · exact ⟨4, by omega, by decide, cycF, hsimple, by rw [hlenF, h16]⟩
  · exact ⟨5, by omega, by decide, cycF, hsimple, by rw [hlenF, h32]⟩

/-- **ALL `114` Boundary Welds Across ALL `12` Symmetry Orbits of `d = 17` Are Killed:**
Every single boundary weld across all 12 orbits (`XLLT`..`XTRR`) satisfies strict face-schema
validity (`WeldSchemaValid w`) and contains a kernel-verified simple dyadic cycle
(`C_8, C_16,` or `C_32`, hence `HasDyadicCycleUpTo 32`). -/
theorem cubic_d17_all_114_welds_killed :
    (all12Orbits.map List.length).foldl (· + ·) 0 = 114 ∧
    ∀ orb ∈ all12Orbits, ∀ w ∈ orb,
      WeldSchemaValid w ∧ (weldFaceGraph w).HasDyadicCycleUpTo 32 := by
  refine ⟨all12Orbits_weld_count, ?_⟩
  intro orb horb w hw
  have horb_ok : checkWeldList orb = true := List.all_eq_true.mp all12Orbits_ok orb horb
  have ⟨hsch, hcyc⟩ := checkWeldList_eq_true horb_ok w hw
  exact ⟨weldSchema_valid_of_bool w hsch, weldFaceGraph_hasDyadicCycle w hcyc⟩

/-- **ALL `R10` Seal Welds Are Killed:**
Every single weld of the `R10` seal (`da ∈ {5, 6, 7, 9, 10}`) satisfies strict face-schema
validity (`WeldSchemaValid w`) and contains a kernel-verified simple dyadic cycle
(`HasDyadicCycleUpTo 32`). -/
theorem cubic_d17_r10_seal_killed :
    ∀ w ∈ r10SealWelds, WeldSchemaValid w ∧ (weldFaceGraph w).HasDyadicCycleUpTo 32 := by
  intro w hw
  have ⟨hsch, hcyc⟩ := checkWeldList_eq_true r10SealWelds_ok w hw
  exact ⟨weldSchema_valid_of_bool w hsch, weldFaceGraph_hasDyadicCycle w hcyc⟩

/-- **ALL `108` `d = 17` Discharging Residuals Eliminated (`cubic_d17_all_108_residuals_killed`):**
1. Exact count: `60` `R10` residuals + `48` patch-orbit residuals = `108` total (matching the
   replay-verified residual word list from `cert/verify_planar_eg.py`);
2. Every `R10` residual has face length `17`, contains both `R10` and `C_TPsR_H_TPsL`, and is
   paired with the kernel-verified `R10` seal (`r10SealWelds`);
3. Every patch-orbit residual rotates to one of the `12` symmetry orbits `oid < 12`, and EVERY
   one of the `114` boundary welds across all `12` orbits satisfies strict `WeldSchemaValid` and
   has a kernel-verified simple dyadic cycle (`C_4, C_8, C_16,` or `C_32`). -/
theorem cubic_d17_all_108_residuals_killed :
    r10ResidualSeqs.length + orbitResidualSeqs.length = 108 ∧
    (∀ seq ∈ r10ResidualSeqs, isR10Residual seq = true) ∧
    (∀ w ∈ r10SealWelds, WeldSchemaValid w ∧ (weldFaceGraph w).HasDyadicCycleUpTo 32) ∧
    (∀ p ∈ orbitResidualSeqs,
      isOrbitResidual p.1 p.2.1 p.2.2 = true ∧ p.1 < 12 ∧
      ∀ (h : p.1 < all12Orbits.length), ∀ w ∈ all12Orbits[p.1]'h,
        WeldSchemaValid w ∧ (weldFaceGraph w).HasDyadicCycleUpTo 32) := by
  refine ⟨by rw [r10ResidualSeqs_len, orbitResidualSeqs_len], ?_, cubic_d17_r10_seal_killed, ?_⟩
  · intro seq hseq
    exact List.all_eq_true.mp r10ResidualSeqs_ok seq hseq
  · intro p hp
    have hok := List.all_eq_true.mp orbitResidualSeqs_ok p hp
    have hlt : p.1 < 12 := decide_eq_true_eq.mp (List.all_eq_true.mp orbitResidualSeqs_lt12 p hp)
    refine ⟨hok, hlt, ?_⟩
    intro hlen w hw
    have hmem : all12Orbits[p.1]'hlen ∈ all12Orbits := List.getElem_mem hlen
    exact cubic_d17_all_114_welds_killed.2 _ hmem w hw

end PlanarEG
