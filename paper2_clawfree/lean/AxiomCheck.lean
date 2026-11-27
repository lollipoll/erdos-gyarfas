import ClawFreeEG

/-!
# Paper 2 (`paper2_clawfree`) Complete Axiom Audit (Stage 4)

Prints the exact axiom dependencies of EVERY public theorem across ALL 13 modules:
- `ClawFreeEG.LiftWindows` (69 core & graph/counting theorems)
- `ClawFreeEG.DyadicPackingData` (4 certified table theorems)
- `ClawFreeEG.DyadicCaseBData` (34 Case B table, quad-tree, & regression theorems)
- `ClawFreeEG.DyadicPacking2D` (44 Main Theorem 1 packing/AM-GM/Case B soundness/tail theorems)
- `ClawFreeEG.TwoCycleData` (10 certified box-tree, leaf-count, & 16-tail-box theorems)
- `ClawFreeEG.TwoCycleClosure` (23 Main Theorem 2 2-cycle closure & reflection theorems)
- `ClawFreeEG.PolyKData` (3 certified equal-block k=3,4,5 box theorems)
- `ClawFreeEG.PolyKAndSublinear` (19 Main Theorem 3 Poly-k / Sublinear o(n) / Sturmian theorems)
- `ClawFreeEG.Treewidth3Data` (18 certified expanded-port, well-formedness, & G_39/H_14/F_11 data theorems)
- `ClawFreeEG.Treewidth3Q3DataA` (8 Q_3-v* expanded-port shards, 1,024 configs)
- `ClawFreeEG.Treewidth3Q3DataB` (8 Q_3-v* expanded-port shards, 1,024 configs)
- `ClawFreeEG.Treewidth3AndBowties` (21 Main Theorem 4 tw<=3 / G_39 / Bowties / Hamiltonian theorems)
- `ClawFreeEG.MainTheorems` (4 master umbrella theorems)

Host Verification Gate enforces ONLY `{propext, Classical.choice, Quot.sound}`.
-/

-- Stage 1: ClawFreeEG.LiftWindows (69 — ALL public theorems incl. counting/graph helpers)
#print axioms ClawFreeEG.filter_length_le_of_imp
#print axioms ClawFreeEG.countPred_le_of_imp
#print axioms ClawFreeEG.filter_congr_eq
#print axioms ClawFreeEG.countPred_congr
#print axioms ClawFreeEG.filter_length_add_not
#print axioms ClawFreeEG.countPred_add_not
#print axioms ClawFreeEG.filter_length_le_length
#print axioms ClawFreeEG.countPred_le_n
#print axioms ClawFreeEG.countPred_true
#print axioms ClawFreeEG.countPred_insert
#print axioms ClawFreeEG.countPred_erase
#print axioms ClawFreeEG.mem_filter_finRange_iff
#print axioms ClawFreeEG.nodup_filter_finRange
#print axioms ClawFreeEG.subset_length_le_of_nodup
#print axioms ClawFreeEG.eq_of_imp_and_countPred_eq
#print axioms ClawFreeEG.countPred_of_list_eq
#print axioms ClawFreeEG.countPred_le_of_subset_list
#print axioms ClawFreeEG.countPred_ge_of_nodup_subset
#print axioms ClawFreeEG.FinGraph.nodup_of_nodupBool
#print axioms ClawFreeEG.FinGraph.isSimpleCycle_of_bool
#print axioms ClawFreeEG.FinGraph.deg_eq_countPred
#print axioms ClawFreeEG.FinGraph.degIn_eq_countPred
#print axioms ClawFreeEG.FinGraph.degIn_all
#print axioms ClawFreeEG.FinGraph.deg_le_of_subgraph
#print axioms ClawFreeEG.FinGraph.adj_ne
#print axioms ClawFreeEG.list_any_congr
#print axioms ClawFreeEG.foldl_add_init
#print axioms ClawFreeEG.sumFin_add
#print axioms ClawFreeEG.sumFin_le_const
#print axioms ClawFreeEG.sumFin_bool_eq_countPred
#print axioms ClawFreeEG.finRange_map_shift1
#print axioms ClawFreeEG.sumFin_shift1
#print axioms ClawFreeEG.sumFin_shift
#print axioms ClawFreeEG.sumFin_ind01_eq_countPred
#print axioms ClawFreeEG.Is3TreeOn.congr
#print axioms ClawFreeEG.degIn_of_K4
#print axioms ClawFreeEG.degIn_insert_eq
#print axioms ClawFreeEG.pow2_mod_three_ne_zero
#print axioms ClawFreeEG.exists_dyadic_bracket
#print axioms ClawFreeEG.avoidsPow2_2L_3L_iff_inFEG
#print axioms ClawFreeEG.bowtie_lift_window_realizable
#print axioms ClawFreeEG.exists_pow2_in_double_window
#print axioms ClawFreeEG.bowtie_forest_exclusion
#print axioms ClawFreeEG.forest_edge_bound
#print axioms ClawFreeEG.forest_edge_bound_on_cycle
#print axioms ClawFreeEG.universal_bowtie_transfer
#print axioms ClawFreeEG.dyadic_cycle_lift_window
#print axioms ClawFreeEG.single_bowtie_preserves_feg
#print axioms ClawFreeEG.four_regular_preserves_feg
#print axioms ClawFreeEG.davg_lt_seven_halves_of_forest
#print axioms ClawFreeEG.davg_ge_seven_halves_no_forest
#print axioms ClawFreeEG.four_regular_satisfies_davg_ge_seven_halves
#print axioms ClawFreeEG.simple_quotient_order_bound
#print axioms ClawFreeEG.indep_circulant_7_1
#print axioms ClawFreeEG.indep_circulant_3_1
#print axioms ClawFreeEG.indep_circulant_11_24
#print axioms ClawFreeEG.indep_circulant_23_3to8
#print axioms ClawFreeEG.r5_attachment_lower_gt_3_17
#print axioms ClawFreeEG.r5_circumference_17_18
#print axioms ClawFreeEG.r11_bipartite_attachment_lower_gt_1_5
#print axioms ClawFreeEG.r11_bipartite_circumference_15_16
#print axioms ClawFreeEG.r5_sturmian_steps_in_dual_forb_ge64
#print axioms ClawFreeEG.Is3TreeOn.card_ge_4
#print axioms ClawFreeEG.Is3TreeOn.min_deg_ge_3
#print axioms ClawFreeEG.Is3TreeOn.deg3_props
#print axioms ClawFreeEG.Is3TreeOn.peel_any_deg3
#print axioms ClawFreeEG.Is3TreeOn.exists_simplicial
#print axioms ClawFreeEG.peel_simplicial_set
#print axioms ClawFreeEG.universal_3tree_lemma

-- Stage 2: ClawFreeEG.DyadicPackingData (4)
#print axioms ClawFreeEG.DyadicPackingData.anc_table_certified_bool
#print axioms ClawFreeEG.DyadicPackingData.oct_table_certified_bool
#print axioms ClawFreeEG.DyadicPackingData.f19_all_certified_bool
#print axioms ClawFreeEG.DyadicPackingData.peff23_certified

-- Stage 2+4: ClawFreeEG.DyadicCaseBData (34)
#print axioms ClawFreeEG.DyadicCaseBData.tables_144_certified
#print axioms ClawFreeEG.DyadicCaseBData.gridUp2048_c0_ok
#print axioms ClawFreeEG.DyadicCaseBData.gridUp2048_c1_ok
#print axioms ClawFreeEG.DyadicCaseBData.gridUp2048_c2_ok
#print axioms ClawFreeEG.DyadicCaseBData.gridUp2048_all_ok
#print axioms ClawFreeEG.DyadicCaseBData.gridUp2048_mono_ok
#print axioms ClawFreeEG.DyadicCaseBData.aMax256_certified
#print axioms ClawFreeEG.DyadicCaseBData.checkLeaf1110_rejects_zero
#print axioms ClawFreeEG.DyadicCaseBData.checkLeaf1111_rejects_zero
#print axioms ClawFreeEG.DyadicCaseBData.checkLeaf_rejects_invalid_geom
#print axioms ClawFreeEG.DyadicCaseBData.forest0000_covers_bool
#print axioms ClawFreeEG.DyadicCaseBData.forest0000_bounds_bool
#print axioms ClawFreeEG.DyadicCaseBData.forest1000_covers_bool
#print axioms ClawFreeEG.DyadicCaseBData.forest1000_bounds_bool
#print axioms ClawFreeEG.DyadicCaseBData.forest1100_covers_bool
#print axioms ClawFreeEG.DyadicCaseBData.forest1100_bounds_bool
#print axioms ClawFreeEG.DyadicCaseBData.forest1010_covers_bool
#print axioms ClawFreeEG.DyadicCaseBData.forest1010_bounds_bool
#print axioms ClawFreeEG.DyadicCaseBData.forest1110_c0_ok
#print axioms ClawFreeEG.DyadicCaseBData.forest1110_c1_ok
#print axioms ClawFreeEG.DyadicCaseBData.forest1110_c2_ok
#print axioms ClawFreeEG.DyadicCaseBData.forest1110_c3_ok
#print axioms ClawFreeEG.DyadicCaseBData.forest1110_c4_ok
#print axioms ClawFreeEG.DyadicCaseBData.forest1110_c5_ok
#print axioms ClawFreeEG.DyadicCaseBData.forest1110_c6_ok
#print axioms ClawFreeEG.DyadicCaseBData.forest1110_c7_ok
#print axioms ClawFreeEG.DyadicCaseBData.forest1110_covers_bool
#print axioms ClawFreeEG.DyadicCaseBData.forest1110_bounds_bool
#print axioms ClawFreeEG.DyadicCaseBData.forest1111_c0_ok
#print axioms ClawFreeEG.DyadicCaseBData.forest1111_c1_ok
#print axioms ClawFreeEG.DyadicCaseBData.forest1111_c2_ok
#print axioms ClawFreeEG.DyadicCaseBData.forest1111_c3_ok
#print axioms ClawFreeEG.DyadicCaseBData.forest1111_covers_bool
#print axioms ClawFreeEG.DyadicCaseBData.forest1111_bounds_bool

-- Stage 2+4: ClawFreeEG.DyadicPacking2D (44)
#print axioms ClawFreeEG.isqrt_spec
#print axioms ClawFreeEG.isqrt256_spec
#print axioms ClawFreeEG.powBounds_123_256_spec
#print axioms ClawFreeEG.powBounds_123_256_tight
#print axioms ClawFreeEG.prodLo_sound
#print axioms ClawFreeEG.prodUp_sound
#print axioms ClawFreeEG.prodUp_mono
#print axioms ClawFreeEG.prodLo_mono
#print axioms ClawFreeEG.amgm_256
#print axioms ClawFreeEG.anc_certified
#print axioms ClawFreeEG.oct_certified
#print axioms ClawFreeEG.pupFast_sound
#print axioms ClawFreeEG.ploFast_sound
#print axioms ClawFreeEG.f19_key_values
#print axioms ClawFreeEG.f19_packing_bound
#print axioms ClawFreeEG.f19_monotone_x
#print axioms ClawFreeEG.f19_monotone_y
#print axioms ClawFreeEG.dyadic_subinterval_algebra
#print axioms ClawFreeEG.dyadic_subinterval_algebra_pow2
#print axioms ClawFreeEG.gap_outside_feg
#print axioms ClawFreeEG.square_gap_collapse
#print axioms ClawFreeEG.dp_block_soundness_invariant
#print axioms ClawFreeEG.pupE_sound
#print axioms ClawFreeEG.caseA_all_64_le_96558
#print axioms ClawFreeEG.caseA_universal_m_ge_4096
#print axioms ClawFreeEG.corner_orbit_partition_16
#print axioms ClawFreeEG.caseB_simple_orbits_cover_triangle
#print axioms ClawFreeEG.gridUp2048_eq_pupFast
#print axioms ClawFreeEG.gridUp2048_mono
#print axioms ClawFreeEG.pupGrid_sound
#print axioms ClawFreeEG.pupGrid_mono_on_grid
#print axioms ClawFreeEG.pupEGrid_sound
#print axioms ClawFreeEG.pupEGrid_shift2_sound
#print axioms ClawFreeEG.pow123_tangent_linear
#print axioms ClawFreeEG.pow123_concave_sum
#print axioms ClawFreeEG.holderPairEGrid_sound
#print axioms ClawFreeEG.factored_amgm_1110_sound
#print axioms ClawFreeEG.maxFactoredAMGM_sound
#print axioms ClawFreeEG.aMax256_sound
#print axioms ClawFreeEG.weighted_tangent_379_133_sound
#print axioms ClawFreeEG.maxTangentForSum_sound
#print axioms ClawFreeEG.threshold_collapse_all_ge_2pow57
#print axioms ClawFreeEG.threshold_collapse_sharp_2pow56
#print axioms ClawFreeEG.r15_ratio_check

-- Stage 2+4: ClawFreeEG.TwoCycleData (10)
#print axioms ClawFreeEG.TwoCycleData.fourfold_trees_32_ok
#print axioms ClawFreeEG.TwoCycleData.fourfold_trees_64_ok
#print axioms ClawFreeEG.TwoCycleData.fourfold_trees_128_ok
#print axioms ClawFreeEG.TwoCycleData.fourfold_trees_256_ok
#print axioms ClawFreeEG.TwoCycleData.equalMed_trees_256_ok
#print axioms ClawFreeEG.TwoCycleData.equalMed_trees_512_ok
#print axioms ClawFreeEG.TwoCycleData.equalMed_trees_1024_ok
#print axioms ClawFreeEG.TwoCycleData.fourfoldTrees_leaf_count
#print axioms ClawFreeEG.TwoCycleData.equalMedTrees_leaf_count
#print axioms ClawFreeEG.TwoCycleData.equalTailBoxes16_certified_bool

-- Stage 2+4: ClawFreeEG.TwoCycleClosure (23)
#print axioms ClawFreeEG.unequal_ge_8x_closure
#print axioms ClawFreeEG.fourfold_symbolic_constants
#print axioms ClawFreeEG.fourfold_separation_lb
#print axioms ClawFreeEG.fourfold_small_delta2_gt_x
#print axioms ClawFreeEG.fourfold_symbolic_closure_ge512
#print axioms ClawFreeEG.fourfold_small_16_y77_gaps
#print axioms ClawFreeEG.fourfold_finite_small_4_8_16
#print axioms ClawFreeEG.algLower_le_r5AttachLower
#print axioms ClawFreeEG.fourfold_finite_32_to_256
#print axioms ClawFreeEG.twofold_symbolic_constants
#print axioms ClawFreeEG.twofold_symbolic_closure_ge128
#print axioms ClawFreeEG.twofold_finite_le64
#print axioms ClawFreeEG.equal_block_geom_identities
#print axioms ClawFreeEG.equal_block_antipodal_width_sum
#print axioms ClawFreeEG.equal_block_small_625_certified
#print axioms ClawFreeEG.checkEqualSmallPair_sound
#print axioms ClawFreeEG.equal_block_small_625_sound
#print axioms ClawFreeEG.equal_block_med_256_512_1024
#print axioms ClawFreeEG.equalTailBoxes16_count
#print axioms ClawFreeEG.equalTailBoxes16_all_pass
#print axioms ClawFreeEG.equalTailBoxes16_domain_coverage
#print axioms ClawFreeEG.equal_block_tail_closure_all_M_ge_2048
#print axioms ClawFreeEG.equal_block_closure_all_pow2_ge_256

-- Stage 3: ClawFreeEG.PolyKData (3)
#print axioms ClawFreeEG.PolyKData.equalK3Boxes17_certified_bool
#print axioms ClawFreeEG.PolyKData.equalK4Boxes17_certified_bool
#print axioms ClawFreeEG.PolyKData.equalK5Boxes16_certified_bool

-- Stage 3: ClawFreeEG.PolyKAndSublinear (19)
#print axioms ClawFreeEG.two_arc_partition_zero_wraparound
#print axioms ClawFreeEG.packing_bound_half_exponent
#print axioms ClawFreeEG.arc_decomp_1x2_bridge_bound
#print axioms ClawFreeEG.arc_decomp_2x2_bridge_bound
#print axioms ClawFreeEG.path_split_subpath_count
#print axioms ClawFreeEG.path_cover_total_subpaths
#print axioms ClawFreeEG.universal_y0_97_sharp
#print axioms ClawFreeEG.fixed_k_thresholds_sharp
#print axioms ClawFreeEG.universal_poly_k_threshold
#print axioms ClawFreeEG.universal_poly_k_cycle_closure
#print axioms ClawFreeEG.pruning_2m_constants
#print axioms ClawFreeEG.sublinear_circumference_m_path_closure
#print axioms ClawFreeEG.equalK_boxes_counts
#print axioms ClawFreeEG.equalK3Boxes17_domain_coverage
#print axioms ClawFreeEG.equal_k3_closure_all_M_ge_2pow36
#print axioms ClawFreeEG.equal_k4_closure_all_M_ge_2pow51
#print axioms ClawFreeEG.equal_k5_closure_all_M_ge_2pow62
#print axioms ClawFreeEG.matching_complement_ell_cancellation
#print axioms ClawFreeEG.r5_sturmian_and_bipartite_assembly

-- Stage 3+4: ClawFreeEG.Treewidth3Data (14)
#print axioms ClawFreeEG.Treewidth3Data.port_config_counts
#print axioms ClawFreeEG.Treewidth3Data.deg3Tri_all_4_ok
#print axioms ClawFreeEG.Treewidth3Data.k23_c0_ok
#print axioms ClawFreeEG.Treewidth3Data.k23_c1_ok
#print axioms ClawFreeEG.Treewidth3Data.g39_eq_f11_split_expanded
#print axioms ClawFreeEG.Treewidth3Data.g39_no_c4_bool
#print axioms ClawFreeEG.Treewidth3Data.g39_no_c8_bool
#print axioms ClawFreeEG.Treewidth3Data.g39_c16_ok
#print axioms ClawFreeEG.Treewidth3Data.g39_deg_and_clawfree_ok
#print axioms ClawFreeEG.Treewidth3Data.h14_cubic_ok
#print axioms ClawFreeEG.Treewidth3Data.h14_k5_minor_bool
#print axioms ClawFreeEG.Treewidth3Data.g39_k5_minor_bool
#print axioms ClawFreeEG.Treewidth3Data.f11_tw3_decomp_bool
#print axioms ClawFreeEG.Treewidth3Data.f11G39_wellFormed_bool

-- Stage 3: ClawFreeEG.Treewidth3Q3DataA (8)
#print axioms ClawFreeEG.Treewidth3Q3DataA.q3MinusV_c0_ok
#print axioms ClawFreeEG.Treewidth3Q3DataA.q3MinusV_c1_ok
#print axioms ClawFreeEG.Treewidth3Q3DataA.q3MinusV_c2_ok
#print axioms ClawFreeEG.Treewidth3Q3DataA.q3MinusV_c3_ok
#print axioms ClawFreeEG.Treewidth3Q3DataA.q3MinusV_c4_ok
#print axioms ClawFreeEG.Treewidth3Q3DataA.q3MinusV_c5_ok
#print axioms ClawFreeEG.Treewidth3Q3DataA.q3MinusV_c6_ok
#print axioms ClawFreeEG.Treewidth3Q3DataA.q3MinusV_c7_ok

-- Stage 3: ClawFreeEG.Treewidth3Q3DataB (8)
#print axioms ClawFreeEG.Treewidth3Q3DataB.q3MinusV_c8_ok
#print axioms ClawFreeEG.Treewidth3Q3DataB.q3MinusV_c9_ok
#print axioms ClawFreeEG.Treewidth3Q3DataB.q3MinusV_c10_ok
#print axioms ClawFreeEG.Treewidth3Q3DataB.q3MinusV_c11_ok
#print axioms ClawFreeEG.Treewidth3Q3DataB.q3MinusV_c12_ok
#print axioms ClawFreeEG.Treewidth3Q3DataB.q3MinusV_c13_ok
#print axioms ClawFreeEG.Treewidth3Q3DataB.q3MinusV_c14_ok
#print axioms ClawFreeEG.Treewidth3Q3DataB.q3MinusV_c15_ok

-- Stage 3+4: ClawFreeEG.Treewidth3AndBowties (21)
#print axioms ClawFreeEG.checkCycleMasks_sound
#print axioms ClawFreeEG.checkCycleDirect_sound
#print axioms ClawFreeEG.hasSimpleCycleLenBool_false_sound
#print axioms ClawFreeEG.maskDeg_eq_deg
#print axioms ClawFreeEG.isClawFreeMasks_sound
#print axioms ClawFreeEG.FinGraph.ReachableIn.symm
#print axioms ClawFreeEG.FinGraph.ReachableIn.trans
#print axioms ClawFreeEG.checkK5MinorBool_sound
#print axioms ClawFreeEG.port_kill_deg3_tri_all_4
#print axioms ClawFreeEG.port_kill_k23_all_128
#print axioms ClawFreeEG.port_kill_q3_minus_v_all_2048
#print axioms ClawFreeEG.port_configs_wellFormed
#print axioms ClawFreeEG.parallel_edge_hits_c8
#print axioms ClawFreeEG.f11_tw3_certified
#print axioms ClawFreeEG.g39_sharp_nonplanar_witness
#print axioms ClawFreeEG.indep_bowtie_4reg_order_5c
#print axioms ClawFreeEG.indep_bowtie_120_arithmetic_bundle
#print axioms ClawFreeEG.ham_all_chord_b_L2_ge_10
#print axioms ClawFreeEG.ham_all_chord_b_4tier_octave_universal
#print axioms ClawFreeEG.ham_all_chord_b_rim_c256_104_to_128
#print axioms ClawFreeEG.ham_all_chord_b_tier1_periods_39

-- Stage 3: ClawFreeEG.MainTheorems (4)
#print axioms ClawFreeEG.main_theorem_1_dyadic_packing_2d
#print axioms ClawFreeEG.main_theorem_2_all_two_cycle_cubic_clawfree
#print axioms ClawFreeEG.main_theorem_3_polyk_sublinear_sturmian
#print axioms ClawFreeEG.main_theorem_4_bowties_tw3_and_hamiltonian
