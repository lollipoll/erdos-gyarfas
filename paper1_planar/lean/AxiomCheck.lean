import PlanarEG

/-!
# AxiomCheck — Complete Stages 1–3 Trust Audit

Prints axioms for EVERY Stage 1, Stage 2, Stage 3, and Master Main Theorem.
MUST report ONLY standard Lean 4 axioms `{propext, Classical.choice, Quot.sound}`
(ZERO `sorryAx`, ZERO `Lean.ofReduceBool`, ZERO custom axioms!).
-/

-- Stage 1: GraphCore
#print axioms PlanarEG.euler_face_discharging_sum
#print axioms PlanarEG.euler_vertex_face_sum
#print axioms PlanarEG.charge_conservation_contradiction
#print axioms PlanarEG.planar_girth_edge_bound
#print axioms PlanarEG.planar_girth10_edge_bound
#print axioms PlanarEG.universal_two_vertex_cut_cap_min_deg
#print axioms PlanarEG.cap_cycle_avoiding_edge_lifts
#print axioms PlanarEG.minimal_two_edge_bond_cap_deg
#print axioms PlanarEG.c4_free_min_order
#print axioms PlanarEG.alternating_c6_density
#print axioms PlanarEG.c6_free_v3_density
#print axioms PlanarEG.universal_bowtie_transfer
#print axioms PlanarEG.dyadic_cycle_lift_window
#print axioms PlanarEG.forest_edge_bound_on_cycle
#print axioms PlanarEG.bowtie_forest_exclusion

-- Stage 1: SharpWitnesses (incl. Stage 4 Single-Vertex-Rotation Certificates)
#print axioms PlanarEG.g168_isCubic
#print axioms PlanarEG.g168_dartBijection
#print axioms PlanarEG.g168_singleVertexRotation
#print axioms PlanarEG.g168_face_counts
#print axioms PlanarEG.g168_has_C32
#print axioms PlanarEG.g168_no_C4_C8_C16
#print axioms PlanarEG.g168_is3Connected
#print axioms PlanarEG.c60_isCubic
#print axioms PlanarEG.c60_dartBijection
#print axioms PlanarEG.c60_singleVertexRotation
#print axioms PlanarEG.c60_face_counts
#print axioms PlanarEG.c60_has_C16
#print axioms PlanarEG.c60_no_C3_C4_C8
#print axioms PlanarEG.td60_isCubic
#print axioms PlanarEG.td60_dartBijection
#print axioms PlanarEG.td60_singleVertexRotation
#print axioms PlanarEG.td60_face_counts
#print axioms PlanarEG.td60_has_C16
#print axioms PlanarEG.td60_no_C4_to_C9

-- Stage 4: Strict Weld Face-Schema Bridge
#print axioms PlanarEG.CertTree.weldSchema_valid_of_bool

-- Stage 2: General Discharging, Bellman-Ford, & DP Soundness
#print axioms PlanarEG.bf_walk_bound
#print axioms PlanarEG.bf_cycle_bound
#print axioms PlanarEG.bf_potential_walk_bound
#print axioms PlanarEG.bf_potential_cycle_bound
#print axioms PlanarEG.bf_shifted_walk_bound
#print axioms PlanarEG.bf_shifted_cycle_bound
#print axioms PlanarEG.dp_upper_bound_sound
#print axioms PlanarEG.dag_potential_path_bound
#print axioms PlanarEG.bwd_dp_upper_bound_sound
#print axioms PlanarEG.cubic_discharging_contradiction
#print axioms PlanarEG.cubic_relaxed_discharging_contradiction

-- Stage 2: Core Bellman-Ford Dual Potentials (d >= 33 & Frozen CAP)
#print axioms PlanarEG.cubic_d33_bf_valid
#print axioms PlanarEG.cubic_clean_d_ge_33_charge_le
#print axioms PlanarEG.cubic_frozen_cap_bf_valid
#print axioms PlanarEG.cubic_frozen_cap_bound
#print axioms PlanarEG.cubic_frozen_cap_relaxed_bound

-- Stage 2: Clean d <= 31 (Plain BF, Shifted-Slope BF, Cyclic DP DAGs, & d=19 BWD DP)
#print axioms PlanarEG.cubic_clean_d7_bound
#print axioms PlanarEG.cubic_clean_d9_bound
#print axioms PlanarEG.cubic_clean_d10_bound
#print axioms PlanarEG.cubic_clean_d11_bound
#print axioms PlanarEG.cubic_clean_d12_bound
#print axioms PlanarEG.cubic_clean_d13_bound
#print axioms PlanarEG.cubic_clean_d15_bound
#print axioms PlanarEG.cubic_clean_noN_d_ge_19_bound
#print axioms PlanarEG.cubic_clean_d19_hasSYZ_bound
#print axioms PlanarEG.cubic_clean_d19_hasSX_bound
#print axioms PlanarEG.cubic_clean_d19_noSYZ_noSX_bound
#print axioms PlanarEG.cubic_clean_d20_bound
#print axioms PlanarEG.cubic_clean_d21_bound
#print axioms PlanarEG.cubic_clean_d22_bound
#print axioms PlanarEG.cubic_clean_d23_bound
#print axioms PlanarEG.cubic_clean_d24_bound
#print axioms PlanarEG.cubic_clean_d25_bound
#print axioms PlanarEG.cubic_clean_d26_bound
#print axioms PlanarEG.cubic_clean_d27_bound
#print axioms PlanarEG.cubic_clean_d28_bound
#print axioms PlanarEG.cubic_clean_d29_bound
#print axioms PlanarEG.cubic_clean_d30_bound
#print axioms PlanarEG.cubic_clean_d31_bound
#print axioms PlanarEG.cubic_conservative_enum_boundary_spec

-- Stage 2: d = 17 Explicit Dyadic Cycle Witnesses (114 Welds + R10 Seal + 108 Residuals)
#print axioms PlanarEG.weldFaceGraph_hasDyadicCycle
#print axioms PlanarEG.cubic_d17_all_114_welds_killed
#print axioms PlanarEG.cubic_d17_r10_seal_killed
#print axioms PlanarEG.cubic_d17_all_108_residuals_killed

-- Stage 3: CubicWelds (51 Chains + Len-6 Impossibility + 520 Seal Welds)
#print axioms PlanarEG.cubic_hhp_phh_shift_spectrum
#print axioms PlanarEG.cubic_51_chains_len6_killed
#print axioms PlanarEG.cubic_seal_welds_all_killed
#print axioms PlanarEG.cubic_tp_b54_weight_bound

-- Stage 3: GeneralPlanarC16 (C3-Free, C5-Free ZERO R10, & C6-Free C16 Trilogy)
#print axioms PlanarEG.general_planar_discharging_contradiction
#print axioms PlanarEG.weldFaceGraph_hasDyadicCycle16
#print axioms PlanarEG.c3free_vertex_absorption
#print axioms PlanarEG.c3free_outer_rim_all_killed
#print axioms PlanarEG.c3free_clean_d_ge_14_bound
#print axioms PlanarEG.c3free_clean_small_bounds
#print axioms PlanarEG.c3free_frozen_cap_bound
#print axioms PlanarEG.c5free_budget_identities
#print axioms PlanarEG.c5free_f10_5tri_bound
#print axioms PlanarEG.c5free_clean_d_ge_18_bound
#print axioms PlanarEG.c5free_frozen_cap_bound
#print axioms PlanarEG.c5free_clean_small_bounds
#print axioms PlanarEG.c5free_outer_rim_all_killed
#print axioms PlanarEG.c6free_vertex_absorption
#print axioms PlanarEG.c6free_f10_and_budget_identities
#print axioms PlanarEG.c6free_clean_d_ge_15_bound
#print axioms PlanarEG.c6free_frozen_cap_bound
#print axioms PlanarEG.c6free_clean_small_bounds
#print axioms PlanarEG.c6free_outer_rim_all_killed

-- Stage 3: Master Main Theorems (ALL FOUR Tier-1 Theorems)
#print axioms PlanarEG.main_theorem_1_cubic_planar_c32
#print axioms PlanarEG.main_theorem_2_planar_clawfree_c64
#print axioms PlanarEG.main_theorem_3_general_planar_c16_trilogy
#print axioms PlanarEG.main_theorem_4_alternating_c6_density
