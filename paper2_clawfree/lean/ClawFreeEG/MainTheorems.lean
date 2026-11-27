import ClawFreeEG.LiftWindows
import ClawFreeEG.DyadicPackingData
import ClawFreeEG.DyadicCaseBData
import ClawFreeEG.DyadicPacking2D
import ClawFreeEG.TwoCycleData
import ClawFreeEG.TwoCycleClosure
import ClawFreeEG.PolyKData
import ClawFreeEG.PolyKAndSublinear
import ClawFreeEG.Treewidth3Data
import ClawFreeEG.Treewidth3Q3DataA
import ClawFreeEG.Treewidth3Q3DataB
import ClawFreeEG.Treewidth3AndBowties

/-!
# ClawFreeEG.MainTheorems

Master honest re-export of the kernel-verified (Layers 1–2) components of all four Main Theorems
of Flagship Paper 2 (`paper2_clawfree`):
*Erdős–Gyárfás for 2-Cycle, Sublinear-Circumference, and Bowtie Claw-Free Graphs via
Sub-Unit 2D Dyadic `L_∞`-Packing*.

## Four-Layer Formalization Honesty Contract
- **Layer 1 (Kernel Theorems on `FinGraph`/`Nat`/`Int`):** Pure Lean 4 (`v4.36.0`, ZERO Mathlib,
  ZERO `Std`, ZERO `sorry`, ZERO custom `axiom`, ZERO `native_decide`, ZERO `unsafe`/`partial`).
- **Layer 2 (Kernel-Checked Finite Certificates):** Exact finite tables, box trees, quad-trees,
  expanded-port cycle witnesses, and `F_11`/`H_14`/`G_39` graph witnesses verified by Lean's kernel.
- **Layer 3 (Standalone Zero-Float Python Replay):** Exact integer/rational finite sweeps in
  `cert/verify_clawfree_eg.py` (cross-audited by `cert/verify_clawfree_parity.py`).
- **Layer 4 (LaTeX Manuscript):** Full graph-to-certificate reductions, packing recurrences,
  and structural case analyses turning Layers 1–3 into arbitrary-graph theorems.

Every umbrella theorem docstring below matches its exact Lean 4 type 1-to-1 and lists any
additional standalone kernel declarations explicitly under **Companion Standalone Declarations**.
-/

namespace ClawFreeEG

open ClawFreeEG.DyadicPackingData
open ClawFreeEG.DyadicCaseBData
open ClawFreeEG.TwoCycleData
open ClawFreeEG.PolyKData
open ClawFreeEG.Treewidth3Data

/-- **Main Theorem 1 Umbrella (Kernel-Verified Packing, Case A/B, & Threshold Components):**
Exact conjuncts exported in this Lean type:
1. Numeric `F19` base-table bound on all `210` lower-triangular stored entries `0 ≤ w2 ≤ w1 ≤ 19`
   (symmetric `20 × 20` extension for the exact same-parity, no-diagonal `|u1 - u2| ≠ |v1 - v2|`
   2D `L_∞`-packing domain `IsValid2DPacking`),
2. Key `F19` table entries (`F19[19,19] = 8`, `F19[3,1] = 2`, `F19[2,1] = 1`),
3. Universal infinite-tail Case A (`m ≥ 4096`, `3*s < m`, certified ratio `≤ 96558/100000 < 1`),
4. Exact 2D dyadic quad-tree triangle coverage and strictly-guarded Boolean leaf acceptance
   on all `813` leaves (`0000:78, 1000:78, 1100:132, 1010:126, 1110:249, 1111:150`) of the `6`
   simple Case B orbits, paired with the `14` standalone kernel-proved local semantic soundness
   lemmas (`pupGrid_sound`, `pupEGrid_sound`, `holderPairEGrid_sound`, `factored_amgm_1110_sound`,
   `aMax256_sound`, `weighted_tangent_379_133_sound`, etc., listed below), while full
   leaf-to-analytic objective composition and the geometric orbit/merge reductions are proved in
   `manuscript/clawfree_eg.tex`,
5. Universal threshold collapse `M ≥ 2^57` and sharpness at `M = 2^56`.

*Companion Standalone Declarations (in `DyadicPacking2D` / `DyadicCaseBData`):*
`isqrt_spec`, `isqrt256_spec`, `powBounds_123_256_spec`, `powBounds_123_256_tight`,
`prodLo_sound`, `prodUp_sound`, `amgm_256`, `pupFast_sound`, `ploFast_sound`, `pupE_sound`,
`f19_monotone_x`, `f19_monotone_y`, `dyadic_subinterval_algebra_pow2`, `gap_outside_feg`,
`square_gap_collapse`, `dp_block_soundness_invariant`, `corner_orbit_partition_16`,
`r15_ratio_check`, `gridUp2048_mono`, `pupGrid_sound`, `pupEGrid_sound`,
`pupEGrid_shift2_sound`, `pow123_tangent_linear`, `pow123_concave_sum`,
`holderPairEGrid_sound`, `factored_amgm_1110_sound`, `maxFactoredAMGM_sound`, `aMax256_sound`,
`weighted_tangent_379_133_sound`, `maxTangentForSum_sound`, `checkLeaf1110_rejects_zero`,
`checkLeaf1111_rejects_zero`, `checkLeaf_rejects_invalid_geom`.

*Layers 3–4 boundary:* `F19` clique computation on the no-diagonal same-parity domain,
intermediate DP `m = 32..2048` (`U(2728,2728) = 1076`), unfactored Case B checks on the `813`
leaves, and Orbit `1001` (`55,531` leaves / `114,643` boxes, worst `99920/100000`) are verified
zero-float in `cert/verify_clawfree_eg.py`; the geometric packing recurrence and regime assembly
are proved in the manuscript. -/
theorem main_theorem_1_dyadic_packing_2d :
    (∀ w1 w2 : Nat, w1 ≤ 19 → w2 ≤ w1 →
      (f19Val w1 w2) ^ 256 * 5 ^ 256 ≤ 3 ^ 256 * ((w1 + 2) * (w2 + 2)) ^ 123) ∧
    (f19Val 19 19 = 8 ∧ f19Val 3 1 = 2 ∧ f19Val 2 1 = 1) ∧
    (∀ m s : Nat, m ≥ 4096 → 3 * s < m →
      ∃ p1 p2 den : Nat,
        (s + 4) ^ 123 * SCALE ^ 256 ≤ p1 ^ 256 * (2 * m) ^ 123 ∧
        (m - 3 * s) ^ 123 * SCALE ^ 256 ≤ p2 ^ 256 * (3 * m) ^ 123 ∧
        den ^ 256 * m ^ 123 ≤ (m + s) ^ 123 * SCALE ^ 256 ∧
        (2 * p1 + p2) * SCALE ≤ 96558 * den ∧
        96558 < SCALE) ∧
    (∀ s1 s2 D : Nat, 0 < D → s2 ≤ s1 → 3 * s1 < D →
      (∃ a b c d e k1 k2, forest0000.HasLeaf a b c d e k1 k2 ∧ checkLeaf0000 a b c d e k1 k2 = true ∧
        0 < e ∧ a * D ≤ s1 * e ∧ s1 * e ≤ b * D ∧ c * D ≤ s2 * e ∧ s2 * e ≤ d * D) ∧
      (∃ a b c d e k1 k2, forest1000.HasLeaf a b c d e k1 k2 ∧ checkLeaf1000 a b c d e k1 k2 = true ∧
        0 < e ∧ a * D ≤ s1 * e ∧ s1 * e ≤ b * D ∧ c * D ≤ s2 * e ∧ s2 * e ≤ d * D) ∧
      (∃ a b c d e k1 k2, forest1100.HasLeaf a b c d e k1 k2 ∧ checkLeaf1100 a b c d e k1 k2 = true ∧
        0 < e ∧ a * D ≤ s1 * e ∧ s1 * e ≤ b * D ∧ c * D ≤ s2 * e ∧ s2 * e ≤ d * D) ∧
      (∃ a b c d e k1 k2, forest1010.HasLeaf a b c d e k1 k2 ∧ checkLeaf1010 a b c d e k1 k2 = true ∧
        0 < e ∧ a * D ≤ s1 * e ∧ s1 * e ≤ b * D ∧ c * D ≤ s2 * e ∧ s2 * e ≤ d * D) ∧
      (∃ a b c d e k1 k2, forest1110.HasLeaf a b c d e k1 k2 ∧ checkLeaf1110 a b c d e k1 k2 = true ∧
        0 < e ∧ a * D ≤ s1 * e ∧ s1 * e ≤ b * D ∧ c * D ≤ s2 * e ∧ s2 * e ≤ d * D) ∧
      (∃ a b c d e k1 k2, forest1111.HasLeaf a b c d e k1 k2 ∧ checkLeaf1111 a b c d e k1 k2 = true ∧
        0 < e ∧ a * D ≤ s1 * e ∧ s1 * e ≤ b * D ∧ c * D ≤ s2 * e ∧ s2 * e ≤ d * D)) ∧
    (∀ M : Nat, M ≥ 2 ^ 57 → (34 * 3) ^ 128 * (2 * M + 3) ^ 123 < (3 * 5) ^ 128 * 3 ^ 123 * M ^ 128) ∧
    ((34 * 3) ^ 128 * (2 * 2 ^ 56 + 3) ^ 123 > (3 * 5) ^ 128 * 3 ^ 123 * (2 ^ 56) ^ 128) :=
  ⟨f19_packing_bound, f19_key_values, caseA_universal_m_ge_4096,
   caseB_simple_orbits_cover_triangle, threshold_collapse_all_ge_2pow57,
   threshold_collapse_sharp_2pow56⟩

/-- **Main Theorem 2 Umbrella (All-`M = 2^m ≥ 4` 2-Cycle Arithmetic & Certificate Closure):**
Exact conjuncts exported in this Lean type:
1. Unequal `M2 ≥ 8*M1` (universal, `M1 ≥ 4`),
2. Unequal Fourfold `M2 = 4*M1` symbolic closure (`M1 ≥ 512`),
3. Unequal Fourfold `M2 = 4*M1` medium finite closure (`M1 ∈ {32, 64, 128, 256}` via `46`
   `IBoxTree` leaves distributed `19 + 11 + 9 + 7`),
4. Unequal Twofold `M2 = 2*M1` symbolic closure (`M1 ≥ 128`),
5. Equal-Block `M2 = M1` small semantic reflection (`M ∈ {4, 8, 16, 32, 64, 128}`, ALL `625`
   same-parity pairs via `SmallEqualPairClosed`),
6. Equal-Block `M2 = M1` closure for ALL `M = 2^m ≥ 256` (`EqualPairClosed`: `76,492` medium
   pairs via `61` `IBoxTree` leaves distributed `22 + 23 + 16` + `16` rational tail boxes for
   ALL `M ≥ 2048`).

*Companion Standalone Declarations (in `TwoCycleData` / `TwoCycleClosure`):*
`fourfoldTrees_leaf_count` (`46`), `equalMedTrees_leaf_count` (`61`),
`fourfold_symbolic_constants`, `fourfold_separation_lb`, `fourfold_small_delta2_gt_x`,
`fourfold_small_16_y77_gaps`, `fourfold_finite_small_4_8_16`, `twofold_symbolic_constants`,
`twofold_finite_le64`, `equal_block_geom_identities`, `equal_block_antipodal_width_sum`,
`equal_block_small_625_certified`, `equal_block_med_256_512_1024`, `equalTailBoxes16_count`,
`equalTailBoxes16_all_pass`, `equalTailBoxes16_domain_coverage`,
`equal_block_tail_closure_all_M_ge_2048`.

*Layers 3–4 boundary:* `cert/verify_clawfree_eg.py` independently enumerates all individual finite
pairs (`19,174` twofold, `38,460` fourfold, `625` small equal, `76,492` medium equal) and
regenerates the `16` rational tail boxes; the triangle-quotient, bridge-encoding, attachment, and
cycle-lift reductions for arbitrary 2-cycle cubic claw-free graphs are proved in the manuscript. -/
theorem main_theorem_2_all_two_cycle_cubic_clawfree :
    (∀ M1 M2 : Nat, M1 ≥ 4 → M2 ≥ 8 * M1 →
      ∀ x y : Nat, x ≤ (4 * M1) / 3 → M2 < y → 3 * y ≤ 4 * M2 →
        x < r5AttachLower M2 (y - M2)) ∧
    (∀ M1 x y : Nat, M1 ≥ 512 → M1 < x → x ≤ (4 * M1) / 3 → 4 * M1 < y → y ≤ (16 * M1) / 3 →
      x < r5AttachLower (4 * M1) (y - 4 * M1) ∨
      ((16 * M1) / 3 < x + y + 2 ∧
        diamondBound x y (x + y + 2 - (16 * M1) / 3) < r5AttachLower (4 * M1) (y - 4 * M1))) ∧
    (∀ M1 x y : Nat, (M1 = 32 ∨ M1 = 64 ∨ M1 = 128 ∨ M1 = 256) →
      M1 < x → x ≤ (4 * M1) / 3 → 4 * M1 < y → y ≤ (16 * M1) / 3 →
      x < r5AttachLower (4 * M1) (y - 4 * M1) ∨
      ((16 * M1) / 3 < x + y + 2 ∧
        diamondBound x y (x + y + 2 - (16 * M1) / 3) < r5AttachLower (4 * M1) (y - 4 * M1))) ∧
    (∀ M1 x y : Nat, M1 ≥ 128 → M1 < x → x ≤ (4 * M1) / 3 → 2 * M1 < y → y ≤ (8 * M1) / 3 →
      (8 * M1) / 3 < x + y + 2 ∧ x + y + 2 - (8 * M1) / 3 < y ∧
      diamondBound x y (x + y + 2 - (8 * M1) / 3) < r5AttachLower (2 * M1) (y - 2 * M1)) ∧
    (∀ M ∈ ([4, 8, 16, 32, 64, 128] : List Nat),
      ∀ x y : Nat, M < x → x ≤ y → y ≤ (4 * M) / 3 → (y - x) % 2 = 0 →
        SmallEqualPairClosed M x y) ∧
    (∀ m x y : Nat, m ≥ 8 → 2 ^ m < x → x ≤ y → y ≤ (4 * 2 ^ m) / 3 →
      EqualPairClosed (2 ^ m) x y) :=
  ⟨fun M1 M2 h1 h8 => (unequal_ge_8x_closure M1 M2 h1 h8).2.2,
   fourfold_symbolic_closure_ge512,
   fourfold_finite_32_to_256,
   twofold_symbolic_closure_ge128,
   equal_block_small_625_sound,
   equal_block_closure_all_pow2_ge_256⟩

/-- **Main Theorem 3 Umbrella (Poly-`k`-Cycle, Sublinear `o(n)` Circumference, Equal-`k`, & R5 Sturmian Arithmetic):**
Exact conjuncts exported in this Lean type:
1. Universal Poly-`k`-Cycle arithmetic contradiction (`k ≥ 2`, `(2^97)^5 * k^133 ≤ n^5`),
2. Sublinear `m`-path complement-cover arithmetic contradiction with R19 `+2m` pruning
   (`(2^97)^5 * m^128 ≤ y^5`, `25^133 * n^128 ≤ y^133`; `o(n)` for fixed `m` or `m = o(n^(5/128))`,
   where `n = |V(H)|`, `y = |V(C)|`, `m` = path-cover size),
3. Equal-block `k = 3, 4, 5` rational box closures (`17, 17, 16` boxes at `M ≥ 2^36, 2^51, 2^62`),
4. R5 circumference arithmetic upper bound `18 * L < 17 * N` (contrapositive: `c(G) ≥ (17/18)|V(G)|`
   forces a dyadic cycle via the circumference transfer `2*c(H) ≤ c(G) ≤ 3*c(H)`) and R11
   bipartite-quotient arithmetic upper bound `16 * L < 15 * N` (contrapositive: when the triangle
   quotient `H` is bipartite, `c(G) ≥ (15/16)|V(G)|` forces a dyadic cycle),
5. Matching-complement `ℓ`-cancellation (`M ≥ 16` even, `3 ∤ M`, `ℓ ∈ {1, 2, 3, 4}`).

*Companion Standalone Declarations (in `PolyKAndSublinear` / `LiftWindows`):*
`two_arc_partition_zero_wraparound`, `packing_bound_half_exponent`, `arc_decomp_1x2_bridge_bound`,
`arc_decomp_2x2_bridge_bound`, `path_split_subpath_count`, `path_cover_total_subpaths`,
`universal_y0_97_sharp`, `fixed_k_thresholds_sharp`, `universal_poly_k_threshold`,
`pruning_2m_constants`, `equalK_boxes_counts`, `equalK3Boxes17_domain_coverage`,
`r5_sturmian_steps_in_dual_forb_ge64`, `r5_sturmian_and_bipartite_assembly`,
`indep_circulant_7_1`, `indep_circulant_3_1`, `indep_circulant_11_24`, `indep_circulant_23_3to8`.

*Layers 3–4 boundary:* Graph-level bridge encodings, R5 attachment counts, original-path endpoint
pruning, and both directions of circumference transfer between simple `H` and `G = T(H)`
(`2*c(H) ≤ c(G) ≤ 3*c(H)`, where every cycle of `G` meeting external edges uses an even number—
hence `2`—of external edges per visited triangle and projects to a simple cycle of `H`) are
proved in `manuscript/clawfree_eg.tex`. -/
theorem main_theorem_3_polyk_sublinear_sturmian :
    (∀ n k y r vatt : Nat, k ≥ 2 → (2 ^ 97) ^ 5 * k ^ 133 ≤ n ^ 5 → n ≤ k * y →
      5 ^ 128 * r ^ 128 ≤ 12 ^ 128 * (y + 2) ^ 123 → vatt ≤ (k - 1) * r →
      17 * vatt > 3 * y → False) ∧
    (∀ n m y t r_sub vatt : Nat, m ≥ 1 → y ≥ 3 →
      (2 ^ 97) ^ 5 * m ^ 128 ≤ y ^ 5 → 25 ^ 133 * n ^ 128 ≤ y ^ 133 →
      y * t ≤ m * y + 2 * n → 5 ^ 128 * r_sub ^ 128 ≤ 6 ^ 128 * (y + 2) ^ 123 →
      vatt ≤ 2 * m + t * r_sub → 17 * vatt > 3 * y → False) ∧
    (∀ M x y : Nat, M ≥ 2 ^ 36 → M < x → x ≤ y → y ≤ (4 * M) / 3 → EqualKPairClosed 2 M x y) ∧
    (∀ M x y : Nat, M ≥ 2 ^ 51 → M < x → x ≤ y → y ≤ (4 * M) / 3 → EqualKPairClosed 3 M x y) ∧
    (∀ M x y : Nat, M ≥ 2 ^ 62 → M < x → x ≤ y → y ≤ (4 * M) / 3 → EqualKPairClosed 4 M x y) ∧
    (∀ N L vatt : Nat, L ≤ N → 17 * vatt > 3 * L → vatt ≤ 3 * (N - L) →
      18 * L < 17 * N ∧ 18 * (3 * L) < 17 * (3 * N)) ∧
    (∀ N L vatt : Nat, L ≤ N → 5 * vatt > L → vatt ≤ 3 * (N - L) →
      16 * L < 15 * N ∧ 16 * (3 * L) < 15 * (3 * N)) ∧
    (∀ M delta ell : Nat, M ≥ 16 → M % 2 = 0 → M % 3 ≠ 0 → 1 ≤ delta → 3 * delta ≤ M →
      (ell = 1 ∨ ell = 2 ∨ ell = 3 ∨ ell = 4) →
      let L := M + delta
      let h := (2 * M) / 3
      let smin := max (M / 2 + 1 - ell) (L - h + ell)
      let smax := min (h - ell) (M / 2 + delta - 1 + ell)
      smin ≤ smax →
        12 * smin ≥ 5 * M + 6 * delta + 8 ∧
        12 * (L - smax) ≥ 5 * M + 6 * delta + 8 ∧
        6 * (smax - smin) ≤ M - 8) :=
  ⟨universal_poly_k_cycle_closure,
   sublinear_circumference_m_path_closure,
   equal_k3_closure_all_M_ge_2pow36,
   equal_k4_closure_all_M_ge_2pow51,
   equal_k5_closure_all_M_ge_2pow62,
   r5_circumference_17_18,
   r11_bipartite_circumference_15_16,
   matching_complement_ell_cancellation⟩

/-- **Main Theorem 4 Umbrella (General `Δ ≤ 4, δ ≥ 3` Bowtie Claw-Free Reductions, `d_avg ≥ 7/2`,
`tw(H/B) ≤ 3 → C_8` or `C_16`, Dyadic-Cycle-Free Independent-Bowtie Order `≥ 120`, & Tier-1
Hamiltonian All-Chord-`B`):**
Exact conjuncts exported in this Lean type:
1. Bowtie-forest lift-window exclusion (`r ∈ {0, 1, 2}`), dyadic-cycle universal transfer
   (`2^a → 2^{a+1}`), and `d_avg(G) ≥ 7/2` forest exclusion arithmetic,
2. **15-Line Universal 3-Tree Lemma** directly on `FinGraph`,
3. **ALL `4 + 128 + 2,048 = 2,180` Expanded-Port Kills** (`deg3_tri → C_8`, `K_{2,3} → C_8` or `C_16`,
   `Q_3 - v^* → C_8` or `C_16`) directly on `FinGraph`, plus well-formedness (`SplitConfigWellFormed`)
   on every checked split configuration,
4. `F_11` spanning 3-tree embedding (`F11.IsSubgraphOf T11 ∧ IsSpanning3Tree T11`),
5. Core `G_39 = T(H_14)/B` witness properties (`G39.MinDegreeAtLeast 3`, `G39.IsClawFree`,
   `¬C_4`, `¬C_8`, explicit `C_16` — sharp for `C_16` vs. `C_8` — and `H14.HasK5Minor ∧ G39.HasK5Minor`
   with pairwise disjoint connected branch sets within each minor model, ZERO topological axioms),
6. Dyadic-cycle-free independent-bowtie 4-regular quotient order bridge `nG = 5*c ∧ (c ≥ 24 → nG ≥ 120)`,
7. Tier-1 Hamiltonian All-Chord-`B` Rim-`C_256` closure for ALL even `104 ≤ N ≤ 128`.

*Companion Standalone Declarations (in `LiftWindows` / `Treewidth3AndBowties` / `Treewidth3Data`):*
`bowtie_lift_window_realizable`, `simple_quotient_order_bound`, `universal_bowtie_transfer`,
`single_bowtie_preserves_feg`, `four_regular_preserves_feg`, `four_regular_satisfies_davg_ge_seven_halves`,
`parallel_edge_hits_c8`, `f11_tw3_certified` (incl. 8-bag width-3 tree decomposition),
`g39_sharp_nonplanar_witness` (incl. port-expansion equality, exact degree profile, independent `V_4`,
and `H14.IsCubic`), `indep_bowtie_120_arithmetic_bundle`, `ham_all_chord_b_L2_ge_10`,
`ham_all_chord_b_4tier_octave_universal`, `ham_all_chord_b_tier1_periods_39`.

*Layers 3–4 boundary (Tier-1 ONLY):* The `360,612` lifted-`H` + `166` overlap enumerations
(for dyadic-cycle-free independent-bowtie graphs with `δ ≥ 3`), `K_{3,3}`/`Q_3` `4,608` bowtie
subsets, and Tier-1 Hamiltonian backtracking sweeps (`W ≤ 31` `L_win = 17` [`29,357`], `k = 8`,
`23` odd [`93,902`], arbitrary matchings even `N ≤ 136` [`641` leaves `≤ 102`,
`{130:73, 132:236, 134:242, 136:723}`]) are independently verified zero-float in
`cert/verify_clawfree_eg.py`; global graph-to-port embeddings, quotient completions, distance-3
case analysis, and periodic/finite-search reductions are proved in the manuscript. -/
theorem main_theorem_4_bowties_tw3_and_hamiltonian :
    (∀ L r : Nat, L ≥ 3 → r ≤ 2 → ∃ a : Nat, a ≥ 2 ∧ L + r ≤ 2 ^ a ∧ 2 ^ a ≤ 2 * L + r) ∧
    (∀ a k m : Nat, a ≥ 2 → k + m ≤ 2 ^ a - 1 →
      2 * 2 ^ a - k ≤ 2 ^ (a + 1) ∧ 2 ^ (a + 1) ≤ 3 * 2 ^ a - k - m) ∧
    (∀ N b : Nat, N ≥ 2 → 2 * b ≤ 3 * N → 2 * (9 * N - 2 * b) ≥ 7 * (3 * N - b) →
      b ≥ N ∧ ∀ c : Nat, ¬ForestBuild N b c) ∧
    (∀ {n : Nat} (F T : FinGraph n), F.IsSubgraphOf T → F.MinDegreeAtLeast 3 → IsSpanning3Tree T →
      F.HasDeg3Triangle ∨ F.HasK23 ∨ F.HasQ3MinusV) ∧
    (deg3TriConfigs.length = 4 ∧ ∀ cfg ∈ deg3TriConfigs, (expandedPortGraph cfg).HasSimpleCycleOfLen 8) ∧
    (k23Configs.length = 128 ∧ ∀ cfg ∈ k23Configs,
      (expandedPortGraph cfg).HasSimpleCycleOfLen 8 ∨ (expandedPortGraph cfg).HasSimpleCycleOfLen 16) ∧
    (q3MinusVConfigs.length = 2048 ∧ ∀ cfg ∈ q3MinusVConfigs,
      (expandedPortGraph cfg).HasSimpleCycleOfLen 8 ∨ (expandedPortGraph cfg).HasSimpleCycleOfLen 16) ∧
    ((∀ cfg ∈ deg3TriConfigs, SplitConfigWellFormed cfg) ∧
      (∀ cfg ∈ k23Configs, SplitConfigWellFormed cfg) ∧
      (∀ cfg ∈ q3MinusVConfigs, SplitConfigWellFormed cfg) ∧
      SplitConfigWellFormed f11G39SplitConfig) ∧
    (F11.IsSubgraphOf T11 ∧ IsSpanning3Tree T11) ∧
    (G39.MinDegreeAtLeast 3 ∧ G39.IsClawFree ∧ ¬G39.HasSimpleCycleOfLen 4 ∧
      ¬G39.HasSimpleCycleOfLen 8 ∧ G39.HasSimpleCycleOfLen 16 ∧ H14.HasK5Minor ∧ G39.HasK5Minor) ∧
    (∀ c nH b nG : Nat, nH = 2 * c → b = c → nG = 3 * nH - b → nG = 5 * c ∧ (c ≥ 24 → nG ≥ 120)) ∧
    (∀ k : Nat, 52 ≤ k → k ≤ 64 → ¬AvoidsPow2 (2 * (2 * k)) (3 * (2 * k) - k)) :=
  ⟨bowtie_forest_exclusion,
   dyadic_cycle_lift_window,
   davg_ge_seven_halves_no_forest,
   fun F T hsub hmin htree => universal_3tree_lemma F T hsub hmin htree,
   port_kill_deg3_tri_all_4,
   port_kill_k23_all_128,
   port_kill_q3_minus_v_all_2048,
   port_configs_wellFormed,
   ⟨f11_tw3_certified.1, f11_tw3_certified.2.1⟩,
   ⟨g39_sharp_nonplanar_witness.2.1,
    g39_sharp_nonplanar_witness.2.2.2.2.1,
    g39_sharp_nonplanar_witness.2.2.2.2.2.1,
    g39_sharp_nonplanar_witness.2.2.2.2.2.2.1,
    g39_sharp_nonplanar_witness.2.2.2.2.2.2.2.1,
    g39_sharp_nonplanar_witness.2.2.2.2.2.2.2.2.2.1,
    g39_sharp_nonplanar_witness.2.2.2.2.2.2.2.2.2.2⟩,
   indep_bowtie_4reg_order_5c,
   ham_all_chord_b_rim_c256_104_to_128⟩

end ClawFreeEG
