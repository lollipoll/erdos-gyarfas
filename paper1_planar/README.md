# Paper 1 (`paper1_planar`) — Reproducibility & Formal Verification Artifact

**Title:** *Every Cubic Planar Graph Contains $C_4, C_8, C_{16},$ or $C_{32}$: Arbitrary Connectivity, Planar Claw-Free $C_{64}$, and General Planar $C_{16}$ Theorems*
**Author:** Seth Rehwaldt *(with AI-assisted exploration, Lean 4 formalization, and AI-assisted adversarial auditing of the artifact using Gemini 4 Neon and GPT 6.2 Astra; see the Declaration of Generative AI and AI-Assisted Technologies in the Manuscript Preparation Process in `manuscript/planar_eg.tex`)*
**Repository:** <https://github.com/lollipoll/erdos-gyarfas> (`paper1_planar/`)
**License:** Dual-licensed — **MIT** for code, Lean 4 formalization, and Python verifiers; **CC-BY-4.0** for the manuscript and figures.

This directory is a self-contained publication, Lean 4 formalization, and standalone zero-float verification bundle for Flagship Paper 1.

---

## 1. Directory Layout

```text
paper1_planar/
├── README.md                  # This guide & Honest Lean-to-Theorem Traceability Table
├── SHA256SUMS                 # Cryptographic manifest over all 41 source, cert, and manuscript files
├── manuscript/
│   ├── planar_eg.tex          # Self-contained AMS/arXiv LaTeX manuscript (with 3 TikZ figures)
│   └── planar_eg.pdf          # Pre-compiled 40-page PDF
├── cert/
│   ├── verify_planar_eg.py      # Pure Python 3 stdlib zero-float verifier (AST-guarded)
│   ├── verify_parity_and_dp.py  # Zero-float Lean/Python/JSON parity, 12 DP sims, & 844 weld invariant
│   └── witnesses/               # 4 deterministic JSON witness tables (byte-identical on re-export)
│       ├── bf_potentials.json
│       ├── cyclic_dp_bounds.json
│       ├── killed_witnesses.json
│       └── sharp_witnesses.json
└── lean/                      # Pure Lean 4 v4.36.0 library (import Std, ZERO Mathlib)
    ├── lakefile.toml
    ├── lean-toolchain
    ├── PlanarEG.lean
    ├── AxiomCheck.lean        # Audits #print axioms on all 106 public declarations
    └── PlanarEG/              # 30 core & certificate data modules
```

---

## 2. Quick Reviewer Reproduction Guide

### 2.1 Standalone Zero-Float Python Verifiers (`cert/verify_planar_eg.py` & `cert/verify_parity_and_dp.py`)

Both scripts require only **Python 3.10+ standard library** (zero third-party packages; both AST-guarded against floating-point literals and true division `/`). Run from the repository root:

```bash
python3 -B paper1_planar/cert/verify_planar_eg.py
python3 -B paper1_planar/cert/verify_parity_and_dp.py
```

To regenerate all four deterministic JSON witness tables and confirm byte-for-byte identity against `cert/witnesses/`:

```bash
python3 -B paper1_planar/cert/verify_planar_eg.py --export-witnesses /tmp/paper1_reexport
diff -ru paper1_planar/cert/witnesses /tmp/paper1_reexport
```

**Verified baselines:**
- **`cert/verify_planar_eg.py`:** `exit 0` in **`~21s`**, peak RSS **`43 MiB`**, `0` diffs across all `4` witness JSON files.
- **`cert/verify_parity_and_dp.py`:** `exit 0` in **`~43s`**, peak RSS **`70 MiB`**, verifying: (i) zero forbidden Lean trust tokens, (ii) exact `F_10` 5-triangle combinatorics (`30,996` pairs, `2,136` admissible, `max = 47/12 < 4`), (iii) literal parity across all `6` packed BF models + relaxed core (`1,351` reachable arcs), all `3` sharpness witnesses + `119`-v `1`-sums, all `51` chain shift spectra, all `108` `d=17` residuals, and all **`6,772`** strict-schema explicit simple dyadic-cycle Lean/Python weld entries, (iv) all **`12/12`** weighted DP-collapse forward simulations (`7` $C_5$-free + `5` $C_6$-free), (v) the exact Lemma 3.1 boundary-regularity invariant across all **`844/844`** production `enum_planar_welds` calls (`722/844` also satisfy the stronger biconditional), and (vi) all supplemental cubic & $C_5$-free subaudits (cubic `Triad-D1` 4-edge seals [`461` welds $\to 0$], cubic $d = 9$ flag welds [`9 + 78` welds $\to 0$], cubic $d = 17$ `6o` rim-triangle coverage [`113,601/113,601`] + `112`-case contact test [`110` killed $+ 2$ antipodal $\to 0$ cubic triangles], $d \in \{14, 18\}$ `6o` all-3-sites 1-drop [`357`/`5,232` $\to 0$], $d = 17$ `TP_s3` `(0..3)` post-sieve [`7,924` overweight $\to$ `496` residuals, `496/496` with isolated triangle], and all **`14,962`** $C_5$-free Stage-3 outer-rim capacity kills $\to 0$ survivors).

### 2.2 Pure Lean 4 Build & Axiom Audit (`v4.36.0`, ZERO Mathlib)

- **Exact Toolchain:** `leanprover/lean4:v4.36.0` (`Lean version 4.36.0, commit 611c117bfaf7b7ae1cfcf246ce6fba31e8f509e9, Release`, pinned in `lean/lean-toolchain`)
- **Trust Standard:** **ZERO `sorry`**, **ZERO `admit`**, **ZERO custom `axiom`**, **ZERO `native_decide`**, **ZERO `unsafe`/`implemented_by`/`extern`/`partial`**.

Run serialized (`LEAN_NUM_THREADS=1`, safe on `< 8 GiB` RAM hosts) inside `paper1_planar/lean/`:

```bash
cd paper1_planar/lean
LEAN_NUM_THREADS=1 lake build
LEAN_NUM_THREADS=1 lake env lean AxiomCheck.lean
```

**Verified baselines:**
- **Full cold build (`64/64` jobs from empty `.lake` cache):** `exit 0`, `0` warnings, wall-clock **`1035.34s`**, peak RSS **`1,437,640 KiB` (`1.37 GiB`)**.
- **Axiom audit (`AxiomCheck.lean`):** `exit 0`, **`106/106`** distinct declarations strictly within `{propext, Classical.choice, Quot.sound}`.

### 2.3 Manuscript Compilation (LaTeX / TikZ)

`paper1_planar/manuscript/planar_eg.tex` is completely self-contained (standard `amsart` + `tikz` packages, no external image files or `.bib` files). On any TeX Live / MiKTeX / arXiv environment with `pdflatex`:

```bash
cd paper1_planar/manuscript
pdflatex -interaction=nonstopmode planar_eg.tex
pdflatex -interaction=nonstopmode planar_eg.tex
```

*(Verified with TeX Live `pdfTeX 3.141592653-2.6-1.40.25`: compiles cleanly in two passes to 40 pages with zero errors, zero undefined references/citations, and zero bookmark warnings.)*

### 2.4 Cryptographic Integrity Verification

From `paper1_planar/`:

```bash
sha256sum -c SHA256SUMS
```

---

## 3. Honest Lean-to-Theorem Traceability Table

Our Lean 4 formalization adopts a **strictly honest proof-carrying architecture**: Lean 4 kernel-verifies every core discrete algebraic/discharging identity, Bellman--Ford/DP/BWD soundness lemma, exact `F_10` exhaustive check, strict face-schema (`WeldSchemaValid`) + explicit simple dyadic cycle on all **6,772** eliminated weld/rim entries (counted with multiplicity across certificate groups), and exact dart-bijection / single-vertex-rotation / cycle sharpness certificates for `G168`, `C60`, and `TD60`. Lean 4 does **NOT** internalize topological Jordan-curve/Kuratowski planarity or end-to-end graph-level reductions from arbitrary planar graphs — all such graph-level proofs are presented in full rigor in `manuscript/planar_eg.tex`, all underlying finite searches and uncollapsed DPs are replayed in `cert/verify_planar_eg.py`, and literal Lean--Python--JSON parity plus all `12/12` weighted DP-collapse simulations and `844/844` weld invariants are verified by `cert/verify_parity_and_dp.py`. Within the Lean column below, we explicitly distinguish **conditional graph-of-states bounds** from **replay-matched literal table specifications**.

| Paper Claim / Section | Proved in Lean 4 Kernel (Exact Module & Declarations) | Finite Proof-Carrying / Python Replay Evidence | Proved in Manuscript (`manuscript/planar_eg.tex`) |
|---|---|---|---|
| **Preliminaries, Euler Identities, & Cap Reductions** (Sec. 2) | `GraphCore`: `FinGraph`, nonempty `IsCubic`/`MinDegreeAtLeast`, `PlaneMap` (combinatorial facial-Euler structure), `euler_face_discharging_sum`, `euler_vertex_face_sum`, `charge_conservation_contradiction`, `minimal_two_edge_bond_cap_deg`, `universal_two_vertex_cut_cap_min_deg`, `cap_cycle_avoiding_edge_lifts` | `cert/verify_planar_eg.py` (`verify_engine_self_tests`): adversarial self-tests on hereditary vs emit-only boundary welding (`((0,1,2),(0,3,4))` and disconnected seeds) and disconnected subcubic cycle search + precondition assertions | Sec. 2.1: Spherical rotation systems, Euler $V-E+F=1+c$ via $c-1$ bridges, simple facial walks & Whitney face-intersection properties (**Lemma 2.1**). Sec. 2.2: **Minimal 2-Edge-Bond Cap Lemma (Lemma 2.2)** (with exact $(2,1)/(1,2)$ $3$-edge-to-$3$-vertex-connectivity proof) and **Edge-Minimality $V_{\ge 4}$-Independence & Universal 2-Vertex-Cut Cap Lemma (Lemma 2.3)**. |
| **Main Theorem 1 (Theorem 1.1) — ALL Cubic Planar Graphs $\implies C_4, C_8, C_{16},$ or $C_{32}$** (Sec. 3, sharp `G168`) | `MainTheorems`: `main_theorem_1_cubic_planar_c32` (component/certificate assembly); `CubicDischarging`: generic walk/cycle bounds `bf_walk_bound`, `bf_cycle_bound`, `bf_potential_walk_bound`, `bf_potential_cycle_bound`, `bf_shifted_walk_bound`, `bf_shifted_cycle_bound`, `dp_upper_bound_sound`, `dag_potential_path_bound`, `bwd_dp_upper_bound_sound`; conditional discharging contradictions `cubic_discharging_contradiction`, `cubic_relaxed_discharging_contradiction`; conditional graph-of-states bounds `cubic_d33_bf_valid`, `cubic_clean_d_ge_33_charge_le`, `cubic_frozen_cap_bf_valid`, `cubic_frozen_cap_bound`, `cubic_frozen_cap_relaxed_bound`, `cubic_clean_noN_d_ge_19_bound`, `cubic_clean_d7_bound`, `cubic_clean_d9_bound`, `cubic_clean_d10_bound`, `cubic_clean_d11_bound`, `cubic_clean_d12_bound`, `cubic_clean_d13_bound`, `cubic_clean_d15_bound`, `cubic_clean_d19_hasSYZ_bound`, `cubic_clean_d19_hasSX_bound`, `cubic_clean_d19_noSYZ_noSX_bound`, `cubic_clean_d20_bound`, `cubic_clean_d21_bound`, `cubic_clean_d22_bound`, `cubic_clean_d23_bound`, `cubic_clean_d24_bound`, `cubic_clean_d25_bound`, `cubic_clean_d26_bound`, `cubic_clean_d27_bound`, `cubic_clean_d28_bound`, `cubic_clean_d29_bound`, `cubic_clean_d30_bound`, `cubic_clean_d31_bound`; replay-matched literal table specs `cubic_conservative_enum_boundary_spec`; weld schema/cycle proofs `CertTree.weldSchema_valid_of_bool`, `weldFaceGraph_hasDyadicCycle`, `cubic_d17_all_114_welds_killed`, `cubic_d17_r10_seal_killed`, `cubic_d17_all_108_residuals_killed`; `CubicWelds`: replay-matched specs `cubic_hhp_phh_shift_spectrum`, `cubic_tp_b54_weight_bound`, and strict-schema cycle proofs `cubic_51_chains_len6_killed`, `cubic_seal_welds_all_killed`; `SharpWitnesses`: `g168_isCubic`, `g168_is3Connected`, `g168_dartBijection`, `g168_singleVertexRotation`, `g168_face_counts`, `g168_no_C4_C8_C16`, `g168_has_C32` | Packed BF (`667`e clean $d\ge 33$, `1,588`e frozen CAP, `1,351`e reachable relaxed core); uncollapsed searches independently replayed in `cert/verify_planar_eg.py` (`1,581` tested / `1,327` pruned len-`2..6` BFS welds across `51` chains; `520 = 16+3+216+5+258+22` seal welds, headline `221+258`; `{14: 357→0, 17: 302652→108, 18: 5232→0}` with `48` words mapped to `114` total welds + `60` `R10` kills reusing the `5` `R10` seals); all **`1,966`** (`114+5+1,327+520`, with multiplicity) Lean weld entries kernel-verified for `WeldSchemaValid` + simple $C_4..C_{32}$; `sharp_witnesses.json`, `bf_potentials.json`, `cyclic_dp_bounds.json`, `killed_witnesses.json` | Sec. 3.1: Boundary-regular dart-parity, spherical Euler $V-E+F=2-h$, & edge-union cycle lifting (**Lemma 3.1**). Sec. 3.2: Complete deterministic charge-conserving cubic discharging rules across all 3 stages (incl. frozen neighborhoods & $R_{10}$ Stage-2 relay), exact Table 1 weights, $51$-chain alphabet/wraparound & $520$-seal completeness (**Prop. 3.2**). Sec. 3.3: Complete `pair_ok`, small-$d$ flags, frozen `CAP` state machine, exact `starts_N` SCC proof, $(TP_{b54,R})^7$ & shift-mask disjointness, $60$ `R10` splice & $48 \to 12$ orbit mapping (**Lemma 3.3**), $G_{168}$ inflation (**Fig. 2**). |
| **Main Theorem 2 (Theorem 1.2) — ALL Planar Induced Claw-Free Graphs ($\delta \ge 3$) $\implies C_4..C_{64}$** (Sec. 4) | `MainTheorems`: `main_theorem_2_planar_clawfree_c64` (component/certificate assembly: arithmetic/forest assembly coupled to `cubic_clean_d_ge_33_charge_le`); `GraphCore`: `bowtie_forest_exclusion`, `forest_edge_bound_on_cycle`, `universal_bowtie_transfer`, `dyadic_cycle_lift_window` | `cert/verify_planar_eg.py` (`verify_theorems_2_and_4`): independent arithmetic sanity checks over $L \le 500$, $r \in \{0,1,2\}$, and lift endpoints | Sec. 4: Induced claw-free $C_4$-free bowtie decomposition $G \cong T(H)/B$ (unique up to marked-skeleton isomorphism) & **Planar Bowtie-Splitting (Lemma 4.1)**; explicit simple cycle realization across $[2L-k, 3L-k-m]$, global induced forest $H_B$ & simple $H/H_B$, and local cycle-forest lift (**Lemma 4.2**), conditional on Theorem 1.1. |
| **Main Theorem 3(a) (Theorem 1.3(a)) — ALL $C_3$-Free General Planar ($\delta \ge 3$) $\implies C_4, C_8, C_{16}$** (Sec. 5.1, sharp `C60` & `C60·C60`) | `MainTheorems`: `main_theorem_3_general_planar_c16_trilogy`; `GeneralPlanarC16`: `general_planar_discharging_contradiction`, `weldFaceGraph_hasDyadicCycle16`, `c3free_vertex_absorption`, `c3free_outer_rim_all_killed`, `c3free_clean_d_ge_14_bound`, `c3free_clean_small_bounds`, `c3free_frozen_cap_bound`; `SharpWitnesses`: `c60_isCubic`, `c60_dartBijection`, `c60_singleVertexRotation`, `c60_face_counts`, `c60_no_C3_C4_C8`, `c60_has_C16` | Packed BF (`d ≥ 14`, `11/20`) & DP (`d = 6,7,9..13`, frozen `≤ 8 < 12`); all **`1,260`** (`59+105+106+990`) outer-rim quotients kernel-verified for `WeldSchemaValid` + simple $C_8/C_{16}$; `cert/verify_planar_eg.py` replays `Corannulene` uniqueness (`46 → 1`, i.e., `45` killed + `1` survivor) and `119`-v `C60·C60` | Sec. 5: Non-circular exterior-disk noncrossing outer-rim partition soundness & seed completeness (**Lemma 5.1**). Sec. 5.1: Complete pure-$P$ ring classification, disjoint Corannulene wedge pairs, clean & frozen graph-to-token maps. Sec. 5.4: **$119$-vertex $\Delta=6$ planar $1$-sum gluing proof (Prop. 5.2)**. |
| **Main Theorem 3(b) (Theorem 1.3(b)) — ALL $C_5$-Free General Planar ($\delta \ge 3$, ZERO `R10`) $\implies C_4, C_8, C_{16}$** (Sec. 5.2, sharp `TD60` & `TD60·TD60`) | `GeneralPlanarC16`: `c5free_budget_identities`, `c5free_f10_5tri_bound` ($252\times 123$, $\max = 47/12 < 4$), `c5free_clean_d_ge_18_bound`, `c5free_frozen_cap_bound`, `c5free_clean_small_bounds`, `c5free_outer_rim_all_killed`; `SharpWitnesses`: `td60_isCubic`, `td60_dartBijection`, `td60_singleVertexRotation`, `td60_face_counts`, `td60_no_C4_to_C9`, `td60_has_C16` | Packed BF (`452`e $d \ge 18$, `1,029`e frozen `≤ 10 < 12`), cyclic DP ($d = 9..14$), BF ($d = 15$), $17$-row BWD DP ($d = 17$); all **7** weighted DP-collapse simulations verified in `cert/verify_parity_and_dp.py`; all **`3,501`** (`2,887 + 4 + 47 + 71 + 71 + 385 + 31 + 5`) outer-rim/patch quotients kernel-verified for `WeldSchemaValid` + simple $C_4/C_8/C_{16}$; `119`-v `TD60·TD60` replayed in Python | Sec. 5.2: Rules V3/V6 & vertex wedge-bound deductions ($k = 4, 5, \ge 6$, sealed by `3-hex+2T` `47` kills), complete mutually exclusive Stage-1/Stage-3 routing, exact 25-seed valley-9 correspondence (covering all 27 ordered pairs + $d_{A,B} \in \{11,12\}$), $F_{10}$ zero-$H_6$ & safe-gap proof eliminating `R10`, clean & frozen graph-to-token maps. Sec. 5.4: **$119$-vertex $\Delta=6$ planar $1$-sum proof (Prop. 5.2)**. |
| **Main Theorem 3(c) (Theorem 1.3(c)) — ALL $C_6$-Free General Planar ($\delta \ge 3$) $\implies C_4, C_8, C_{16}$** (Sec. 5.3, sharp `TD60` & `TD60·TD60`) | `GeneralPlanarC16`: `c6free_vertex_absorption`, `c6free_f10_and_budget_identities`, `c6free_clean_d_ge_15_bound`, `c6free_frozen_cap_bound`, `c6free_clean_small_bounds`, `c6free_outer_rim_all_killed` | Packed BF (`20`e $d \ge 15$, `54`e frozen `≤ 10 < 12`), cyclic DP ($d = 9, 11..14$); all **5** weighted DP-collapse simulations verified in `cert/verify_parity_and_dp.py`; all **`45`** full-rim quotients kernel-verified for `WeldSchemaValid` + simple $C_8/C_{16}$ | Sec. 5.3: Zero $6$-faces, deterministic vertex absorption ($t+p \le \lfloor k/2 \rfloor$), complete Stage-1 $k=4$ & $k\ge 5$ ($(1/2, 1/4, 1/4)$) triangle rules & $2/3$ $F_{10}$ ceiling, $d=7$ bound, complete reduction of every $t=4$ and $t=5$ clean $F_{10}$ to the $9$ checked seeds, `(0,1)` apex-disjointness proof, clean & frozen state-graph mappings. |
| **Main Theorem 4 (Theorem 1.4) — Alternating-$C_6$ Planar Degree-Density Bound** (Sec. 6) | `MainTheorems`: `main_theorem_4_alternating_c6_density` (component/certificate assembly: girth-$10$/order/density algebra); `GraphCore`: `planar_girth10_edge_bound`, `alternating_c6_density`, `c4_free_min_order`, `c6_free_v3_density` ($+1/48$ identity) | `cert/verify_planar_eg.py` (`verify_theorems_2_and_4`): arithmetic checks across $n < 500$ and $\tau_6$ lower bounds | Sec. 6: Mixed bipartite $Q = G[V_{\ge 4}, V_3]$, minimum $6$-cycle edge transversal $T$ ($Q' = Q - T$), **Planar Girth-$\ge 10$ Edge Bound allowing bridges, components, and forests (Lemma 6.1)**, and $C_4$-free neighbor-pair bound $3n \le \binom{n}{2} \implies n \ge 7$. |

---

## 4. Count Reconciliation Reference

To avoid ambiguity across summary tables and verifier logs:
- **Cubic mixed-chain BFS welds:** `1,581` total tested welds across all BFS visits; **`1,327`** (`37 + 406 + 535 + 264 + 85`) pruned length-`2..6` welds carried in Lean (`CubicChainWelds1..3Data.lean`).
- **Cubic seal welds:** **`520`** total (`16` `s2_9` + `3` `TP_b54+hex` + `216` `R21 TP_b54` + `5` `R10` + `258` `R22 after_A9 & TP_b54+t89` + `22` `a9_tpsr/THT/TT2`), where the headline R21+R22 pair is `221 + 258`.
- **Cubic $d = 17$ residuals:** `108` total (`60` `R10` kills reusing the `5` `R10` seals + `48` words across `12` symmetry orbits mapped to **`114`** total full $17$-face boundary welds — the verifier log's `48x114 welds` shorthand means `48` words mapped to `114` total welds).
- **$C_5$-free general planar kills:** **`3,501`** total:
  - Verifier grouping: `2,962` (`= 2,887` valley-9 + `4` core vertex-absorption + `71` cubic $F_7$) `+ 47` (`3-hex+2T` vertex-absorption) `+ 71` (`F_10 aux10`) `+ 385` (`F_10 H6`) `+ 31` (high-vertex $F_7$-pair) `+ 5` (`T_frz`) `= 3,501`;
  - Lean grouping: `71` (`aux10`) `+ 385` (`H6`) `+ 51` (`= 4` core + `47` `3-hex+2T` vertex-absorption) `+ 102` (`= 71` cubic $F_7$ + `31` high-vertex $F_7$-pair) `+ 5` (`T_frz`) `+ 2,887` (valley-9) `= 3,501`.
- **Total Lean-verified strict-schema explicit dyadic-cycle weld/rim entries (with multiplicity across certificate groups):** `114 + 5 + 1,327 + 520 + 1,260 + 3,501 + 45 =` **`6,772`** (noting that the `5` cubic `R10` seals appear both inside the `520` seal group and inside the `d = 17` residual group).
