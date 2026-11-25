import PlanarEG.GraphCore
import PlanarEG.SharpWitnesses
import PlanarEG.CubicDischarging
import PlanarEG.CubicWelds
import PlanarEG.GeneralPlanarC16

/-!
# PlanarEG.MainTheorems

**Certified Component & Finite-Certificate Assembly Theorems** for Flagship Paper 1
(*Every Cubic Planar Graph Contains `C_4, C_8, C_16,` or `C_32`: Arbitrary Connectivity,
Planar Claw-Free `C_64`, and General Planar `C_16` Theorems*).

**Honest Formalization Scope (Audit-Aligned):**
Each `main_theorem_*` declaration below assembles the **kernel-proved algebraic, combinatorial,
discharging-conservation, proof-carrying Bellman-Ford/DP, strict-schema explicit dyadic-cycle
weld/rim-kill, and cellular-rotation sharpness components** for the corresponding theorem of Paper 1.
These Lean declarations do **NOT** internalize topological planar embedding / Jordan curve theory,
block/cut-cap existence, graph-to-token discharging maps, conservative enumeration/shift completeness,
bowtie-forest/planar-skeleton constructions, mixed-bipartite `Q`/transversal constructions, or
cycle-preserving quotient lifts — all of those graph-level reductions are proved in full *JCTB*
rigor in `manuscript/planar_eg.tex`, while the full finite searches and automaton simulations are
independently replayed in `cert/verify_planar_eg.py`.

1. **`main_theorem_1_cubic_planar_c32`** — Certified Component & Certificate Assembly for Main Theorem 1
   (cap degree/lift lemmas, relaxed cubic Euler discharging contradiction `≤ 32/3 < 12`, `667`e/`1,588`e/
   relaxed `1,351`e BF & selected `d ≤ 31` DP/BWD/`noN` bounds, replay-matched boundary/chain specs,
   strict-schema + explicit `C_4..C_32` clauses for all `114` `d = 17` orbit welds, `5` `R10` seals,
   `85` len-6 chain welds, and the `R21`/`R22` seal groups plus the `520` seal count, and `G168`
   3-connected cellular-rotation sharpness; full-family schema/cycle proofs for all `1,327` pruned chain
   welds and all `6` seal groups live in `CubicWelds.lean`, and the remaining clean `d ≤ 31` bounds live
   in `CubicDischarging.lean`).
2. **`main_theorem_2_planar_clawfree_c64`** — Certified Component Assembly for Main Theorem 2
   (Bowtie-Forest exclusion arithmetic, inductive `ForestBuild` bound, Universal Dyadic Lift Window
   `C_4..C_32 ↦ C_8..C_64`, coupled to the Main Theorem 1 `d ≥ 33` BF core).
3. **`main_theorem_3_general_planar_c16_trilogy`** — Certified Component & Certificate Assembly for
   Main Theorem 3 (universal cap degree monotonicity, general vertex-face Euler contradiction,
   universal `C_3`/`C_6` absorption, packed BF bounds, exact `1,260` (`C_3`) and `3,501` (`C_5`)
   rim-kill counts, strict-schema + explicit `C_4/C_8/C_16` clauses on all `45` (`C_6`) rim kills, and
   `C60`/`TD60` cellular-rotation sharpness; full-family schema/cycle proofs for all `1,260` and `3,501`
   rim kills, `c5free_f10_5tri_bound`, and small-degree DP bounds are separate audited declarations in
   `GeneralPlanarC16.lean`).
4. **`main_theorem_4_alternating_c6_density`** — Certified Component Assembly for Main Theorem 4
   (`PlaneMap` girth-`≥ 10` Euler edge bound, exact Alternating-`C_6` density algebra, `C_4`-free
   minimum order `n ≥ 7`, and `C_6`-free `|V_3| ≥ ⌈(11n + 10)/16⌉ > 2n/3` with `+1/48` gain).

Pure Lean 4 (`import Std`, ZERO Mathlib, ZERO `sorry`, ZERO `axiom`, ZERO `native_decide`).
-/

namespace PlanarEG

open CertTree
open SharpData
open CubicBFCoreData
open CubicSmallBF1Data
open CubicSmallBF2Data
open CubicDP1Data
open CubicDP11Data
open CubicD17Data
open CubicChainWelds1Data
open CubicChainWelds2Data
open CubicChainWelds3Data
open CubicSealWeldsData
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

/-! ## Main Theorem 1 — ALL Cubic Planar Graphs (Arbitrary Connectivity, Sharp `C_32`) -/

/-- **Main Theorem 1 Certified Component & Certificate Assembly (`main_theorem_1_cubic_planar_c32`):**
Kernel-verified components & finite certificates for Main Theorem 1 (*Every Cubic Planar Graph
Contains `C_4, C_8, C_16,` or `C_32`*, arbitrary connectivity, sharp on `G168`):
- **Kernel-proved in Lean 4:**
  1. Local cap degree increment (`minimal_two_edge_bond_cap_deg`) & cap-avoiding cycle lift;
  2. Cubic `PlaneMap` Euler face-discharging contradiction (relaxed `≤ 32/3 < 12`, paired with strict
     `≤ 10 < 12` in `cubic_discharging_contradiction`);
  3. Packed state-graph BF bounds: clean `d ≥ 33` (`667`e, `scale = 1320`, `b = 9/11`) & frozen
     `CAP` (`1,588`e strict `≤ 10`, `1,351`e reachable relaxed `≤ 32/3 < 12`);
  4. Packed state-graph clean bounds exported here (`d ∈ {7, 9..13}`, `d = 19` BWD DP, unified `noN`
     for `d ≥ 19`; remaining `d ∈ {15, 19..31}` bounds are separate audited theorems in `CubicDischarging.lean`)
     plus replay-matched boundary/chain table specs (`{14: 357→0, 17: 302652→108, 18: 5232→0}`, `51` chains,
     `hhpPhhCommonShifts`, `bfsLen6Survivors = 0`);
  5. Strict face-schema (`WeldSchemaValid`) + explicit simple `C_4..C_32` clauses exported here for all
     `114` `d = 17` orbit welds, all `5` `R10` seal welds, all `85` len-6 chain welds, and the `R21`/`R22`
     seal groups (with exact total `520` seal count & `5/4 + 9/8 = 19/8 < 5/2`; full-family schema/cycle
     proofs across all `1,327` pruned length-`2..6` chain welds and all `6` seal groups are separate audited
     theorems `cubic_51_chains_len6_killed` and `cubic_seal_welds_all_killed` in `CubicWelds.lean`);
  6. Sharpness witness `G168`: nonempty cubic `PlaneMap 168`, 3-connected, exact dart bijection,
     single cyclic rotation per vertex (`HasSingleVertexRotation`), zero `C_4/C_8/C_16`, explicit `C_32`.
- **Proved in `manuscript/planar_eg.tex` / replayed in `cert/verify_planar_eg.py`:**
  Planar embedding/rotation Euler bridge, minimal 2-edge-bond cap existence & cap-cycle exclusion,
  graph-to-token discharging map, conservative enumeration/shift/weld completeness, and cycle-preserving
  lifting of killed patches into the parent cubic planar graph. -/
theorem main_theorem_1_cubic_planar_c32 :
    -- (1) Local cap degree increment & cap-avoiding cycle lift
    (∀ {n : Nat} (H : FinGraph n) (a b : Fin n) (hab : a ≠ b),
      H.adj a b = false → (H.addEdge a b hab).deg a = H.deg a + 1) ∧
    (∀ {n : Nat} (H : FinGraph n) (a b : Fin n) (hab : a ≠ b) (cyc : List (Fin n)),
      (H.addEdge a b hab).IsSimpleCycle cyc →
      (∀ (i : Nat) (hi : i < cyc.length),
        let u := cyc[i]'hi
        let v := cyc[(i + 1) % cyc.length]'(Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le i) hi))
        ¬((u = a ∧ v = b) ∨ (u = b ∧ v = a))) →
      H.IsSimpleCycle cyc) ∧
    -- (2) Cubic PlaneMap face-discharging contradiction (relaxed ≤ 32/3 < 12)
    (∀ {n : Nat} (M : PlaneMap n), M.graph.IsCubic →
      ∀ (isFrozen : List (Fin n) → Bool) (S : Int), S > 0 →
      ∀ (inCh outCh cFin : List (Fin n) → Int),
        (∀ f ∈ M.faces, cFin f = S * ((6 : Int) - (f.length : Int)) + inCh f - outCh f) →
        sumInt (M.faces.map inCh) = sumInt (M.faces.map outCh) →
        (∀ f ∈ M.faces, isFrozen f = false → cFin f ≤ 0) →
        3 * sumInt ((M.faces.filter isFrozen).map cFin) ≤ 32 * S → False) ∧
    -- (3) Packed state-graph clean d ≥ 33 BF (667e) & frozen CAP BF (1,588e strict + relaxed)
    (∀ d : Nat, d ≥ 33 → ∀ {u k : Nat} {recvScaled : Int},
      DirWalk (PackedEdge d33Edges) u u k (recvScaled - 1080 * (d : Int)) →
      recvScaled ≤ 1320 * ((d : Int) - 6)) ∧
    (∀ d : Nat, ∀ {k : Nat} {recvScaled : Int},
      DirWalk (PackedEdge frzEdges) frzCapIdx frzCapIdx k (recvScaled - 120 * ((d : Int) - 1)) →
      120 * ((6 : Int) - (d : Int)) + recvScaled ≤ 5 * 120 ∧
      2 * (120 * ((6 : Int) - (d : Int)) + recvScaled) < 12 * 120) ∧
    (∀ d : Nat, ∀ {p0 uEnd k : Nat} {coreW recvScaled : Int},
      p0 ∈ frzRelInitPairs → uEnd ∈ frzRelEndNodes →
      DirWalk (PackedEdge frzRelCoreEdges) (p0 / WT_RADIX) uEnd k coreW →
      recvScaled - 120 * ((d : Int) - 1) = (((p0 % WT_RADIX : Nat) : Int) - (PI_BIAS : Int)) + coreW →
      3 * (2 * (120 * ((6 : Int) - (d : Int)) + recvScaled)) ≤ 32 * 120) ∧
    -- (4) Packed clean d ≤ 31 bounds & replay-matched conservative-enum table spec
    ((∀ {u k : Nat} {r : Int}, DirWalk (PackedEdge d7Edges) u u k (r - 4 * 7) → r ≤ 28 * (7 - 6)) ∧
     (∀ {k : Nat} {t : Int}, DirWalk (PackedEdge d9Edges) 0 1 k t → t ≤ 120 * (9 - 6)) ∧
     (∀ {k : Nat} {t : Int}, DirWalk (PackedEdge d10Edges) 0 1 k t → t ≤ 120 * (10 - 6)) ∧
     (∀ {k : Nat} {t : Int}, DirWalk (PackedEdge d11Edges) 0 1 k t → t ≤ 120 * (11 - 6)) ∧
     (∀ {k : Nat} {t : Int}, DirWalk (PackedEdge d12Edges) 0 1 k t → t ≤ 120 * (12 - 6)) ∧
     (∀ {k : Nat} {t : Int}, DirWalk (PackedEdge d13Edges) 0 1 k t → t ≤ 120 * (13 - 6)) ∧
     (∀ {z : Nat} {t : Int}, z ∈ d19ClosingQs →
       LenWalk (PackedBwdEdge d19BwdEdges) d19StartQ z 18 t → t ≤ 120 * (19 - 6)) ∧
     (∀ d : Nat, d ≥ 19 → ∀ {u k : Nat} {r : Int},
       DirWalk (PackedEdge noN19to27Edges) u u k (r - 1560 * (d : Int)) → r ≤ 2280 * ((d : Int) - 6)) ∧
     (enumD14Overweight = 357 ∧ enumD14Survivors = 0 ∧
      enumD17Overweight = 302652 ∧ enumD17Survivors = 108 ∧
      enumD18Overweight = 5232 ∧ enumD18Survivors = 0)) ∧
    -- (5) ALL 108 d = 17 residuals: strict face-schema + explicit C_4..C_32 on all 114 orbit & R10 welds
    (r10ResidualSeqs.length + orbitResidualSeqs.length = 108 ∧
     (all12Orbits.map List.length).foldl (· + ·) 0 = 114 ∧
     (∀ orb ∈ all12Orbits, ∀ w ∈ orb, WeldSchemaValid w ∧ (weldFaceGraph w).HasDyadicCycleUpTo 32) ∧
     (∀ w ∈ r10SealWelds, WeldSchemaValid w ∧ (weldFaceGraph w).HasDyadicCycleUpTo 32)) ∧
    -- (6) Replay-matched 51 chains spec + strict face-schema & explicit C_4..C_32 on len-6 (85) welds
    (chains56Table.length = 51 ∧ bfsLen6Survivors = 0 ∧
     hhpPhhCommonShifts = [0, 3, 4, 5, 6, 7, 8] ∧
     (len6WeldsChunks.map List.length).foldl (· + ·) 0 = 85 ∧
     (∀ c ∈ len6WeldsChunks, ∀ w ∈ c, WeldSchemaValid w ∧ (weldFaceGraph w).HasDyadicCycleUpTo 32)) ∧
    -- (7) 520 seal-weld total count, strict face-schema + explicit C_4..C_32 on R21/R22 seal groups, & 19/8 < 5/2
    --     (all 6 seal groups proved in `CubicWelds.cubic_seal_welds_all_killed`)
    ((sealS29Welds.length + sealTpB54HexWelds.length +
      (sealR21TpWeldsChunks.map List.length).foldl (· + ·) 0 + sealR21R10Welds.length +
      (sealR22WeldsChunks.map List.length).foldl (· + ·) 0 + sealExtraWelds.length = 520) ∧
     (∀ c ∈ sealR21TpWeldsChunks, ∀ w ∈ c, WeldSchemaValid w ∧ (weldFaceGraph w).HasDyadicCycleUpTo 32) ∧
     (∀ c ∈ sealR22WeldsChunks, ∀ w ∈ c, WeldSchemaValid w ∧ (weldFaceGraph w).HasDyadicCycleUpTo 32) ∧
     5 * 2 + 9 = 19 ∧ 19 * 2 < 5 * 8) ∧
    -- (8) Sharpness witness G168 (168v cubic PlaneMap, 3-conn, dart bijection + single rotation, no C4/C8/C16, C32)
    (g168Map.graph.IsCubic ∧ g168Map.graph.Is3Connected ∧
     CubicSpec.HasExactDartBijection g168Spec g168Faces g168DartLoc ∧
     CubicSpec.HasSingleVertexRotation g168Spec g168Faces g168DartLoc ∧
     ¬ g168Map.graph.HasSimpleCycleOfLen 4 ∧
     ¬ g168Map.graph.HasSimpleCycleOfLen 8 ∧
     ¬ g168Map.graph.HasSimpleCycleOfLen 16 ∧
     g168Map.graph.HasSimpleCycleOfLen 32) := by
  have h108 := cubic_d17_all_108_residuals_killed
  have h114 := cubic_d17_all_114_welds_killed
  have h51 := cubic_51_chains_len6_killed
  have hseal := cubic_seal_welds_all_killed
  have hhhp := cubic_hhp_phh_shift_spectrum
  have hwt := cubic_tp_b54_weight_bound
  exact ⟨
    fun H a b hab hnot => minimal_two_edge_bond_cap_deg H a b hab hnot,
    fun H a b hab cyc hcyc havoid => cap_cycle_avoiding_edge_lifts H a b hab cyc hcyc havoid,
    fun M hc isF S hS iC oC cF hd hb hcl hfr =>
      cubic_relaxed_discharging_contradiction M hc isF S hS iC oC cF hd hb hcl hfr,
    cubic_clean_d_ge_33_charge_le,
    cubic_frozen_cap_bound,
    fun d {_ _ _ _ _} hp0 hend hw htot => (cubic_frozen_cap_relaxed_bound d hp0 hend hw htot).2.1,
    ⟨fun {_ _ _} hc => cubic_clean_d7_bound hc,
     fun {_ _} hp => cubic_clean_d9_bound hp,
     fun {_ _} hp => cubic_clean_d10_bound hp,
     fun {_ _} hp => cubic_clean_d11_bound hp,
     fun {_ _} hp => cubic_clean_d12_bound hp,
     fun {_ _} hp => cubic_clean_d13_bound hp,
     fun {_ _} hz hp => cubic_clean_d19_noSYZ_noSX_bound hz hp,
     cubic_clean_noN_d_ge_19_bound,
     cubic_conservative_enum_boundary_spec⟩,
    ⟨h108.1, h114.1, h114.2, h108.2.2.1⟩,
    ⟨h51.1, h51.2.2.2.1, hhhp.2.2, h51.2.2.2.2.2.1, h51.2.2.2.2.2.2.2.2.2.2⟩,
    ⟨hseal.2.2.2.2.2.1, hseal.2.2.2.2.2.2.2.2.1, hseal.2.2.2.2.2.2.2.2.2.2.1, hwt.1, hwt.2⟩,
    ⟨g168_isCubic, g168_is3Connected, g168_dartBijection, g168_singleVertexRotation,
     g168_no_C4_C8_C16.1, g168_no_C4_C8_C16.2.1, g168_no_C4_C8_C16.2.2, g168_has_C32⟩⟩

/-! ## Main Theorem 2 — ALL Planar Claw-Free Graphs (`δ ≥ 3`, Explicit `C_64` Cutoff) -/

/-- **Main Theorem 2 Certified Component Assembly (`main_theorem_2_planar_clawfree_c64`):**
Kernel-verified arithmetic & inductive forest components supporting Main Theorem 2
(*Every Planar Claw-Free Graph with `δ ≥ 3` Contains `C_4, C_8, C_16, C_32,` or `C_64`*):
- **Kernel-proved in Lean 4:**
  1. Bowtie-Forest exclusion window (`bowtie_forest_exclusion`: `[L + r, 2L + r]` always contains `2^a ≥ 4` for `r ≤ 2`);
  2. Inductive acyclic forest edge bound (`forest_edge_bound_on_cycle`: `ForestBuild L (k + m) c → k + m ≤ L - 1`);
  3. Universal dyadic lift window (`dyadic_cycle_lift_window`: `2^(a+1) ∈ [2·2^a - k, 3·2^a - k - m]`);
  4. Explicit `C_4, C_8, C_16, C_32 ↦ C_8, C_16, C_32, C_64` lift-window endpoints, paired with the
     Main Theorem 1 `d ≥ 33` BF core.
- **Proved in `manuscript/planar_eg.tex`:**
  Planar claw-free reduction to `G = T(H)/B`, induced acyclicity of `H_B`, simplicity of `H/H_B`,
  planar cubic skeleton construction, and realization of every integer in `[2L - k, 3L - k - m]`
  by a simple cycle in `G`. -/
theorem main_theorem_2_planar_clawfree_c64 :
    -- (1) Bowtie-Forest Exclusion (r ∈ {0, 1, 2} impossible)
    (∀ L r : Nat, L ≥ 3 → r ≤ 2 → ∃ a : Nat, a ≥ 2 ∧ L + r ≤ 2 ^ a ∧ 2 ^ a ≤ 2 * L + r) ∧
    -- (2) Acyclic forest edge-count bound
    (∀ {L k m c : Nat}, ForestBuild L (k + m) c → k + m ≤ L - 1) ∧
    -- (3) Universal dyadic lift window for all a ≥ 2
    (∀ a k m : Nat, a ≥ 2 → k + m ≤ 2 ^ a - 1 →
      2 * 2 ^ a - k ≤ 2 ^ (a + 1) ∧ 2 ^ (a + 1) ≤ 3 * 2 ^ a - k - m) ∧
    -- (4) Explicit C_4, C_8, C_16, C_32 ↦ C_8, C_16, C_32, C_64 lift windows
    (∀ L k m : Nat, (L = 4 ∨ L = 8 ∨ L = 16 ∨ L = 32) → k + m ≤ L - 1 →
      (2 * L = 8 ∨ 2 * L = 16 ∨ 2 * L = 32 ∨ 2 * L = 64) ∧
      2 * L - k ≤ 2 * L ∧ 2 * L ≤ 3 * L - k - m) ∧
    -- (5) Coupled with Main Theorem 1 cubic planar C_32 BF core
    (∀ d : Nat, d ≥ 33 → ∀ {u k : Nat} {recvScaled : Int},
      DirWalk (PackedEdge d33Edges) u u k (recvScaled - 1080 * (d : Int)) →
      recvScaled ≤ 1320 * ((d : Int) - 6)) := by
  refine ⟨bowtie_forest_exclusion, forest_edge_bound_on_cycle, dyadic_cycle_lift_window, ?_,
    cubic_clean_d_ge_33_charge_le⟩
  intro L k m hL hforest
  rcases hL with rfl | rfl | rfl | rfl <;> exact ⟨by omega, by omega, by omega⟩

/-! ## Main Theorem 3 — General Planar (`δ ≥ 3`, ALL Connectivities & `Δ`) `C_16` Trilogy -/

/-- **Main Theorem 3 Certified Component & Certificate Assembly (`main_theorem_3_general_planar_c16_trilogy`):**
Kernel-verified components & finite certificates supporting all three parts of Main Theorem 3
(*General Planar `δ ≥ 3` `C_16` Trilogy: `C_3`-free, `C_5`-free [ZERO `R10`], & `C_6`-free*):
- **Kernel-proved in Lean 4:**
  1. Cap degree monotonicity (`universal_two_vertex_cut_cap_min_deg`) & general vertex-face
     `PlaneMap` Euler discharging contradiction (`general_planar_discharging_contradiction`);
  2. **3(a) `C_3`-free:** universal vertex absorption (`k ≥ 4`), packed BF `d ≥ 14` (`11d ≤ 20(d-6)`),
     exact `1,260` outer-rim kill count (full strict-schema + explicit `C_8/C_16` family proof in
     `GeneralPlanarC16.c3free_outer_rim_all_killed`, paired with `c3free_clean_small_bounds` and
     `c3free_frozen_cap_bound`), and sharpness witness `C60` (nonempty cubic `PlaneMap 60`, exact dart
     bijection + single vertex rotation, zero `C_3/C_4/C_8`, explicit `C_16`);
  3. **3(b) `C_5`-free (ZERO `R10`):** packed BF `d ≥ 18` (`452`e) & frozen `CAP` (`1,029`e, `≤ 10 < 12`),
     exact `3,501` rim/patch kill count (full strict-schema + explicit `C_4/C_8/C_16` family proof in
     `GeneralPlanarC16.c5free_outer_rim_all_killed`, paired with `c5free_f10_5tri_bound` and
     `c5free_clean_small_bounds`), and sharpness witness `TD60` (nonempty cubic `PlaneMap 60`, exact dart
     bijection + single vertex rotation, zero `C_4..C_9`, explicit `C_16`);
  4. **3(c) `C_6`-free:** universal vertex absorption (`t + p ≤ k / 2`), packed BF `d ≥ 15` (`20`e) &
     frozen `CAP` (`54`e, `≤ 10 < 12`), and strict-schema + explicit `C_8/C_16` clauses exported directly
     for all `45` rim kills (paired with `c6free_clean_small_bounds` in `GeneralPlanarC16`).
- **Proved in `manuscript/planar_eg.tex` / replayed in `cert/verify_planar_eg.py`:**
  Universal 2-vertex-cut cap planarity & cycle lifting, non-adjacent `V_{≥ 4}` / rim-geometry
  reductions, actual vertex/face charge maps & absence of `R10`, DP automaton simulations,
  cycle-preserving quotient lifts, and the 119-vertex `Δ = 6` 1-sum sharpness constructions. -/
theorem main_theorem_3_general_planar_c16_trilogy :
    -- (1) Universal 2-vertex-cut cap degree monotonicity & general Euler vertex-face contradiction
    (∀ {n : Nat} (G : FinGraph n) (a b : Fin n) (hab : a ≠ b) (u : Fin n),
      G.deg u ≤ (G.addEdge a b hab).deg u) ∧
    (∀ {n : Nat} (M : PlaneMap n) (isFrozen : VFElem n → Bool) (S : Int), S > 0 →
      ∀ (inCh outCh cFin : VFElem n → Int),
        (∀ v : Fin n, cFin (.vert v) = S * ((6 : Int) - 2 * (M.graph.deg v : Int)) + inCh (.vert v) - outCh (.vert v)) →
        (∀ f ∈ M.faces, cFin (.face f) = S * ((6 : Int) - (f.length : Int)) + inCh (.face f) - outCh (.face f)) →
        sumInt (((List.finRange n).map VFElem.vert ++ M.faces.map VFElem.face).map inCh) =
        sumInt (((List.finRange n).map VFElem.vert ++ M.faces.map VFElem.face).map outCh) →
        (∀ v : Fin n, isFrozen (.vert v) = false → cFin (.vert v) ≤ 0) →
        (∀ f ∈ M.faces, isFrozen (.face f) = false → cFin (.face f) ≤ 0) →
        sumInt ((((List.finRange n).map VFElem.vert ++ M.faces.map VFElem.face).filter isFrozen).map cFin) < 12 * S →
        False) ∧
    -- (2) Main Theorem 3(a): C_3-free components (absorption, BF d>=14, 1,260 rim kills, C60 sharp)
    ((∀ k c : Nat, k ≥ 4 → 2 * c ≤ k →
       (6 : Int) - 2 * (k : Int) + (((k - 2 * c + 1) / 2 : Nat) : Int) + (c : Int) ≤ 0) ∧
     (∀ d : Nat, d ≥ 14 → ∀ {u k : Nat} {r : Int},
       DirWalk (PackedEdge c3D14Edges) u u k (r - 11 * (d : Int)) → r ≤ 20 * ((d : Int) - 6)) ∧
     ((c3P67WeldsChunks.map List.length).foldl (· + ·) 0 +
      (c3P69WeldsChunks.map List.length).foldl (· + ·) 0 +
      (c3CorPWeldsChunks.map List.length).foldl (· + ·) 0 +
      (c3CorVal1WeldsChunks.map List.length).foldl (· + ·) 0 +
      (c3CorVal2WeldsChunks.map List.length).foldl (· + ·) 0 = 1260) ∧
     (c60Map.graph.IsCubic ∧ CubicSpec.HasExactDartBijection c60Spec c60Faces c60DartLoc ∧
      CubicSpec.HasSingleVertexRotation c60Spec c60Faces c60DartLoc ∧
      ¬ c60Map.graph.HasSimpleCycleOfLen 3 ∧ ¬ c60Map.graph.HasSimpleCycleOfLen 4 ∧
      ¬ c60Map.graph.HasSimpleCycleOfLen 8 ∧ c60Map.graph.HasSimpleCycleOfLen 16)) ∧
    -- (3) Main Theorem 3(b): C_5-free ZERO R10 components (BF d>=18 & frozen <= 10, 3,501 rim kills, TD60 sharp)
    ((∀ d : Nat, d ≥ 18 → ∀ {u k : Nat} {r : Int},
       DirWalk (PackedEdge c5D18Edges) u u k (r - 8 * (d : Int)) → r ≤ 12 * ((d : Int) - 6)) ∧
     (∀ d : Nat, ∀ {k : Nat} {r : Int},
       DirWalk (PackedEdge c5FrzEdges) c5FrzCapIdx c5FrzCapIdx k (r - 12 * ((d : Int) - 1)) →
       12 * ((6 : Int) - (d : Int)) + r ≤ 5 * 12 ∧ 2 * (12 * ((6 : Int) - (d : Int)) + r) < 12 * 12) ∧
     ((c5Aux10WeldsChunks.map List.length).foldl (· + ·) 0 +
      (c5H6WeldsChunks.map List.length).foldl (· + ·) 0 + c5VAbsWelds.length +
      (c5F7WeldsChunks.map List.length).foldl (· + ·) 0 + c5TFrzWelds.length +
      (c5V9AWeldsChunks.map List.length).foldl (· + ·) 0 +
      (c5V9BWeldsChunks.map List.length).foldl (· + ·) 0 +
      (c5V9CWeldsChunks.map List.length).foldl (· + ·) 0 +
      (c5V9DWeldsChunks.map List.length).foldl (· + ·) 0 = 3501) ∧
     (td60Map.graph.IsCubic ∧ CubicSpec.HasExactDartBijection td60Spec td60Faces td60DartLoc ∧
      CubicSpec.HasSingleVertexRotation td60Spec td60Faces td60DartLoc ∧
      (∀ L : Nat, 4 ≤ L → L ≤ 9 → ¬ td60Map.graph.HasSimpleCycleOfLen L) ∧
      td60Map.graph.HasSimpleCycleOfLen 16)) ∧
    -- (4) Main Theorem 3(c): C_6-free components (absorption, BF d>=15 & frozen <= 10, 45 strict-schema rim kills)
    ((∀ k t p : Nat, t + p ≤ k / 2 →
       (k = 4 → (6 : Int) - 2 * (k : Int) + ((t + p : Nat) : Int) ≤ 0) ∧
       (k ≥ 5 → (6 : Int) - 2 * (k : Int) + ((2 * t + p : Nat) : Int) ≤ 0)) ∧
     (∀ d : Nat, d ≥ 15 → ∀ {u k : Nat} {r : Int},
       DirWalk (PackedEdge c6D15Edges) u u k (r - 12 * (d : Int)) → r ≤ 20 * ((d : Int) - 6)) ∧
     (∀ d : Nat, ∀ {k : Nat} {r : Int},
       DirWalk (PackedEdge c6FrzEdges) c6FrzCapIdx c6FrzCapIdx k (r - 20 * ((d : Int) - 1)) →
       20 * ((6 : Int) - (d : Int)) + r ≤ 5 * 20 ∧ 2 * (20 * ((6 : Int) - (d : Int)) + r) < 12 * 20) ∧
     (c6RimWelds.length = 45 ∧ ∀ w ∈ c6RimWelds, WeldSchemaValid w ∧ (weldFaceGraph w).HasDyadicCycleUpTo 16)) := by
  have hc3 := c3free_outer_rim_all_killed
  have hc5 := c5free_outer_rim_all_killed
  have hc6 := c6free_outer_rim_all_killed
  refine ⟨universal_two_vertex_cut_cap_min_deg,
    fun M isF S hS iC oC cF hdV hdF hb hcV hcF hfr =>
      general_planar_discharging_contradiction M isF S hS iC oC cF hdV hdF hb hcV hcF hfr,
    ⟨fun k c hk hc => (c3free_vertex_absorption k c hk hc).2.1,
     c3free_clean_d_ge_14_bound,
     by rw [hc3.1, hc3.2.1, hc3.2.2.1]; have := hc3.2.2.2.1; omega,
     ⟨c60_isCubic, c60_dartBijection, c60_singleVertexRotation, c60_no_C3_C4_C8.1, c60_no_C3_C4_C8.2.1,
      c60_no_C3_C4_C8.2.2, c60_has_C16⟩⟩,
    ⟨c5free_clean_d_ge_18_bound,
     c5free_frozen_cap_bound,
     by rw [hc5.1, hc5.2.1, hc5.2.2.1, hc5.2.2.2.1, hc5.2.2.2.2.1]; have := hc5.2.2.2.2.2.1; omega,
     ⟨td60_isCubic, td60_dartBijection, td60_singleVertexRotation, td60_no_C4_to_C9, td60_has_C16⟩⟩,
    ⟨c6free_vertex_absorption,
     c6free_clean_d_ge_15_bound,
     c6free_frozen_cap_bound,
     hc6⟩⟩

/-! ## Main Theorem 4 — Alternating-`C_6` Planar Degree-Density Bound -/

/-- **Main Theorem 4 Certified Component Assembly (`main_theorem_4_alternating_c6_density`):**
Kernel-verified Euler & arithmetic components supporting Main Theorem 4:
- **Kernel-proved in Lean 4:**
  1. `PlaneMap` girth-`≥ 10` Euler edge bound `4 * E ≤ 5 * (n - 2)`;
  2. Exact Alternating-`C_6` degree-density algebra `16 * h + 4 * eps ≤ 5 * (n - 2) + 4 * tau6`;
  3. `C_4`-free minimum-order inequality `n ≥ 7`;
  4. `C_6`-free cubic-vertex density `16 * |V_3| ≥ 11 * n + 10` and `3 * |V_3| > 2 * n` for ALL `n ≥ 7`,
     strictly beating `2/3` by `11/16 - 2/3 = 1/48` (`11 * 3 - 2 * 16 = 1`).
- **Proved in `manuscript/planar_eg.tex`:**
  Construction of the mixed bipartite subgraph `Q`, 6-cycle transversal deletion `Q → Q'`,
  planar girth-`≥ 10` edge bound for possibly disconnected / forest `Q'`, and the `C_4`-free
  neighbor-pair counting inequality `3n ≤ n(n-1)/2` with vertex degree partition `|V_3| + h = n`. -/
theorem main_theorem_4_alternating_c6_density :
    (∀ {n : Nat} (M : PlaneMap n), (∀ f ∈ M.faces, 10 ≤ f.length) →
      4 * (M.numEdges : Int) ≤ 5 * ((n : Int) - 2)) ∧
    (∀ n h eps eQ ePrime tau6 : Nat,
      eQ = 4 * h + eps → eQ ≤ ePrime + tau6 → 4 * ePrime ≤ 5 * (n - 2) →
      16 * h + 4 * eps ≤ 5 * (n - 2) + 4 * tau6) ∧
    (∀ n : Nat, n ≥ 1 → 3 * n ≤ n * (n - 1) / 2 → n ≥ 7) ∧
    (∀ n v3 h eps : Nat, n ≥ 7 → v3 + h = n → 16 * h + 4 * eps ≤ 5 * (n - 2) →
      16 * v3 ≥ 11 * n + 10 ∧ 3 * v3 > 2 * n) ∧
    (11 * 3 - 2 * 16 = 1) :=
  ⟨fun M hf => planar_girth10_edge_bound M hf,
   alternating_c6_density,
   c4_free_min_order,
   c6_free_v3_density,
   by omega⟩

end PlanarEG
