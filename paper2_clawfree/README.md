# Paper 2 (`paper2_clawfree`) — Reproducibility & Formal Verification Artifact

**Title:** *Erdős–Gyárfás for 2-Cycle, Sublinear-Circumference, and Bowtie Claw-Free Graphs via Sub-Unit 2D Dyadic $L_\infty$-Packing*
**Author:** Seth Rehwaldt *(with AI-assisted exploration, Lean 4 formalization, and AI-assisted adversarial auditing of the artifact using Gemini 4 Neon and GPT 6.2 Astra; see the Declaration of Generative AI and AI-Assisted Technologies in the Manuscript Preparation Process in `manuscript/clawfree_eg.tex`)*
**Repository:** <https://github.com/lollipoll/erdos-gyarfas> *(bundled under `paper2_clawfree/` and archived alongside Paper 1 upon publication release)*
**License:** Dual-licensed — **MIT** for code, Lean 4 formalization, and Python verifiers; **CC-BY-4.0** for the manuscript and figures.

This directory is a self-contained publication, pure Lean 4 formalization (100% discrete combinatorics, ZERO topological axioms), and standalone zero-float verification bundle for Flagship Paper 2.

---

## 1. Directory Layout

```text
paper2_clawfree/
├── README.md                  # This guide, 4-Layer Honest Traceability Table, & Count Reconciliation
├── SHA256SUMS                 # Cryptographic manifest over all 26 tracked source, cert, and manuscript files
├── manuscript/
│   ├── clawfree_eg.tex        # Self-contained AMS/arXiv LaTeX manuscript (with 4 TikZ figures)
│   └── clawfree_eg.pdf        # Pre-compiled 41-page PDF
├── cert/
│   ├── verify_clawfree_eg.py      # Pure Python 3 stdlib zero-float verifier (AST-guarded)
│   ├── verify_clawfree_parity.py  # AST audit, 15-file trust scan, live AxiomCheck, & 1-to-1 literal parity
│   └── witnesses/                 # 4 deterministic JSON witness tables (byte-identical on re-export)
│       ├── dyadic_packing_2d.json
│       ├── hamiltonian_all_chord_b.json
│       ├── tw3_and_g39.json
│       └── two_cycle_closure.json
└── lean/                      # Pure Lean 4 v4.36.0 library (ZERO Mathlib, ZERO Std)
    ├── lakefile.toml
    ├── lean-toolchain
    ├── ClawFreeEG.lean
    ├── AxiomCheck.lean        # Audits #print axioms on all 261 public declarations
    └── ClawFreeEG/            # 13 core & proof-carrying certificate modules
```

---

## 2. Quick Reviewer Reproduction Guide

### 2.1 Standalone Zero-Float Python Verifiers (`cert/verify_clawfree_eg.py` & `cert/verify_clawfree_parity.py`)

Both scripts require only **Python 3.10+ standard library** (zero third-party packages; both AST-guarded against floating-point/complex literals, true division `/`, and `research/` imports, and both refuse `python3 -O` optimization bypass). Run from `paper2_clawfree/`:

```bash
python3 -B cert/verify_clawfree_eg.py
python3 -B cert/verify_clawfree_parity.py --check-axioms <path-to-lean-4.36.0-sysroot>
```

To regenerate all four deterministic JSON witness tables and confirm byte-for-byte identity against `cert/witnesses/`:

```bash
python3 -B cert/verify_clawfree_eg.py --export-witnesses /tmp/paper2_reexport
diff -ru cert/witnesses /tmp/paper2_reexport
```

**Verified baselines:**
- **`cert/verify_clawfree_eg.py`:** `exit 0` in **`~31–34 s`**, peak RSS **`~111–133 MiB`**, `0` diffs across all `4` witness JSON files.
- **`cert/verify_clawfree_parity.py --check-axioms <sysroot>`:** `exit 0` in **`< 1 s`** (after `lake build`), verifying: (i) AST zero-float / zero-`/` / zero-`research` audit on both scripts, (ii) `15`-file Lean trust-token scan (including `AxiomCheck.lean`) and live `261/261` axiom compliance strictly in `{propext, Classical.choice, Quot.sound}`, and (iii) literal data parity across Lean, Python, and JSON (exact comparison units detailed in Section 4: `F19 = 210` lower-tri entries, Case B `= 813` leaf geometries + positive packed params, Lean `IBoxTree = 46 + 61` leaves vs. Python exhaustive pair enumerations, `16` rational tail boxes, `50` equal-`k` rational boxes, `2,180` expanded-port witnesses, `F_11`/`H_14`/`G_39` graphs/minors, `360,612` + `166` indep-bowtie counts, `39` Tier-1 periods, `23` odd open cases).

### 2.2 Pure Lean 4 Build & Axiom Audit (`v4.36.0`, ZERO Mathlib, ZERO `Std`)

- **Exact Toolchain:** `leanprover/lean4:v4.36.0` (pinned in `lean/lean-toolchain`)
- **Trust Standard:** **ZERO `sorry`**, **ZERO `admit`**, **ZERO custom `axiom`**, **ZERO `native_decide`**, **ZERO `unsafe`/`implemented_by`/`extern`/`partial`**, **ZERO `set_option`**.

Run serialized (`LEAN_NUM_THREADS=1`, safe on `< 8 GiB` RAM hosts) inside `paper2_clawfree/lean/`:

```bash
cd lean
LEAN_NUM_THREADS=1 lake build
LEAN_NUM_THREADS=1 lake env lean AxiomCheck.lean
```

**Verified baselines:**
- **Full cold build (`30/30` jobs from empty `.lake` cache):** `exit 0`, `0` warnings, wall-clock **`6:30.17`**, peak RSS **`1,393,452 KiB` (`1.33 GiB < 1.50 GiB`)**.
- **Axiom audit (`AxiomCheck.lean`):** `exit 0`, **`261/261`** distinct public theorems across `13` modules strictly within `{propext, Classical.choice, Quot.sound}`.

### 2.3 Manuscript Compilation (LaTeX / TikZ)

`manuscript/clawfree_eg.tex` is completely self-contained (standard `amsart` + `tikz` packages, no external image files or `.bib` files). On any TeX Live / MiKTeX / arXiv environment with `pdflatex`:

```bash
cd manuscript
pdflatex -interaction=nonstopmode clawfree_eg.tex
pdflatex -interaction=nonstopmode clawfree_eg.tex
pdflatex -interaction=nonstopmode clawfree_eg.tex
```

*(Verified with TeX Live `pdfTeX 3.141592653-2.6-1.40.25`: compiles cleanly in three passes to 41 pages with 0 errors, 0 undefined references/citations, 0 bookmark warnings, 0 `Float too large` warnings, 0 `Rerun` warnings, and 0 overfull hboxes.)*

### 2.4 Cryptographic Integrity Verification

From `paper2_clawfree/`:

```bash
sha256sum -c SHA256SUMS
```

---

## 3. Four-Layer Honest Lean-to-Theorem Traceability Table

Our verification architecture explicitly separates four transparent layers, matching Table 1 of `manuscript/clawfree_eg.tex` (listing principal declarations; the complete `261`-theorem index is audited in `lean/AxiomCheck.lean`). Structure/inductive types (`ClawFreeEG.FinGraph`, `ClawFreeEG.TwoCycleData.IBoxTree`) and stored data (`ClawFreeEG.DyadicPackingData.f19Val`) are explicitly distinguished from kernel-audited theorems. Each Lean umbrella certifies the discrete arithmetic and finite-certificate core of its corresponding theorem rather than quantifying over arbitrary graphs end-to-end:
- **Layer 1:** Pure Lean 4 kernel theorems on `FinGraph`, `Nat`, and `Int`.
- **Layer 2:** Lean 4 kernel-checked finite tables, box trees, quad-trees, expanded-port cycle witnesses, and `F_11`/`H_14`/`G_39` graph witnesses.
- **Layer 3:** Standalone zero-float Python 3 replay (`cert/verify_clawfree_eg.py`) and literal parity/axiom auditing (`cert/verify_clawfree_parity.py`).
- **Layer 4:** Full discrete graph-to-certificate reductions, geometric packing recurrences, effective-width and real-to-integer bridge lemmas, and structural case analyses proved in `manuscript/clawfree_eg.tex`.

| Paper Claim / Section | Layer 1: Principal Lean 4 Kernel Theorems (Exact Fully Qualified Names) | Layers 2–3: Finite Certificates & Python Replay | Layer 4: Proved in Manuscript (`manuscript/clawfree_eg.tex`) |
|---|---|---|---|
| **Foundations, Lift Windows, & R5 Sturmian** (Sec. 2) | *Type:* `ClawFreeEG.FinGraph`. *Theorems (`LiftWindows`):* `avoidsPow2_2L_3L_iff_inFEG`, `bowtie_lift_window_realizable`, `indep_circulant_7_1`, `indep_circulant_3_1`, `indep_circulant_11_24`, `indep_circulant_23_3to8`, `r5_attachment_lower_gt_3_17`, `r5_circumference_17_18`, `r11_bipartite_attachment_lower_gt_1_5`, `r11_bipartite_circumference_15_16`, `r5_sturmian_steps_in_dual_forb_ge64` | `cert/verify_clawfree_eg.py`: exhaustive Sturmian template check ($M \le 2^{18}$, `174,750` pairs), `26` minimal short-chord chains ($e_I \le 15$), $M = 16$ zero-$K_2$ & Regime 1/2 crossing (`174,750` pairs), small-$M$ chordlessness ($M \in \{4, 8\}$), bipartite $y \le 42$ | Claw-free $C_4$-free representation $G \cong T(H)/B$ & simplicity of $H$ (**Lemma 2.1**), exact lift window $[2L-k, 3L-k-m]$ & two-sided circumference transfer $2c(H) \le c(G) = 3c(H)$ (**Lemma 2.2**), short-chord packing & Sturmian crossing (**Lemma 2.3**), Matching-Complement two-regime closure (Sec. 2.3) |
| **Main Theorem 1 (Theorem 1.1) — Sub-Unit 2D Dyadic $L_\infty$-Packing** (Sec. 3) | *Umbrella:* `ClawFreeEG.main_theorem_1_dyadic_packing_2d`. *Core (`DyadicPacking2D`):* `isqrt256_spec`, `powBounds_123_256_tight`, `amgm_256`, `dyadic_subinterval_algebra_pow2`, `square_gap_collapse`, `dp_block_soundness_invariant`, `caseA_universal_m_ge_4096`, `corner_orbit_partition_16`, all 14 Case B local soundness lemmas (`gridUp2048_eq_pupFast`, `gridUp2048_mono`, `pupGrid_sound`, `pupGrid_mono_on_grid`, `pupEGrid_sound`, `pupEGrid_shift2_sound`, `pow123_tangent_linear`, `pow123_concave_sum`, `holderPairEGrid_sound`, `factored_amgm_1110_sound`, `maxFactoredAMGM_sound`, `aMax256_sound`, `weighted_tangent_379_133_sound`, `maxTangentForSum_sound`), `threshold_collapse_all_ge_2pow57`, `threshold_collapse_sharp_2pow56` | Lean Layer 2 (`DyadicPackingData.f19Val` data; `DyadicCaseBData`): `F19` (`210` lower-tri numeric entries, `f19_packing_bound`, `f19_key_values`), `65+32` anchor/octave tables, `813` guarded Case B simple leaves + regression checks (`checkLeaf1110_rejects_zero`, `checkLeaf1111_rejects_zero`, `checkLeaf_rejects_invalid_geom`). Python Layer 3: `F19` exact clique search, coordinatewise nondecreasing DP $m = 32..2048$ (`U(2728,2728) = 1076`), unfactored `813` leaves, Orbit `1001` (`55,531` leaves / `114,643` boxes, worst `99920/100000`) | $45^\circ$-rotated bridge encoding & no-diagonal necessity (**Lemma 3.1**, **Remark 1.1**), dyadic block decomposition & child-first Case A collapse (**Lemma 3.2**), all 7 corner orbits & Orbit `1001` H/V-merge geometry (Sec. 3.2), `effAE` semantic soundness (**Lemma 3.3**), real concavity/envelope/supporting-line bridge (**Lemma 3.4**), unrounded `1110` decoupling & strong induction (Sec. 3.3) |
| **Main Theorem 2 (Theorem 1.2) — ALL 2-Cycle Cubic Claw-Free Graphs** (Sec. 4) | *Umbrella:* `ClawFreeEG.main_theorem_2_all_two_cycle_cubic_clawfree`. *Core (`TwoCycleClosure`):* `unequal_ge_8x_closure`, `fourfold_symbolic_closure_ge512`, `twofold_symbolic_closure_ge128`, `equal_block_geom_identities`, `equal_block_antipodal_width_sum`, `checkEqualSmallPair_sound`, `equal_block_small_625_sound`, `equal_block_closure_all_pow2_ge_256` | Lean Layer 2 (`TwoCycleData.IBoxTree` type; `TwoCycleClosure`): `46` fourfold (`19+11+9+7`) & `61` equal-med (`22+23+16`) `IBoxTree` leaves (`fourfoldTrees_leaf_count`, `equalMedTrees_leaf_count`), `625` small equal pairs, `16` rational tail boxes ($M \ge 2048$). Python Layer 3: `19,174` twofold, `38,460` fourfold, `625` small equal, `76,492` med equal individual pairs + `16` tail boxes | Four cycles from a bridge pair, diamond packing on torus $\mathbb{Z}_x \times \mathbb{Z}_y$, unequal block separation (Sec. 4.1), equal-block near/far 2-class cover, `3e/2e` imbalance collapse, antipodal zero-wraparound lift, parity rule (**Lemma 4.1**) |
| **Main Theorem 3 (Theorem 1.3) — Poly-$k$-Cycle, Sublinear Circumference, Sturmian, & Matching-Complement** (Sec. 5) | *Umbrella:* `ClawFreeEG.main_theorem_3_polyk_sublinear_sturmian`. *Core (`PolyKAndSublinear`):* `two_arc_partition_zero_wraparound`, `arc_decomp_1x2_bridge_bound`, `arc_decomp_2x2_bridge_bound`, `path_cover_total_subpaths`, `universal_poly_k_cycle_closure`, `sublinear_circumference_m_path_closure`, `equal_k3_closure_all_M_ge_2pow36`, `equal_k4_closure_all_M_ge_2pow51`, `equal_k5_closure_all_M_ge_2pow62`, `matching_complement_ell_cancellation`, `r5_sturmian_and_bipartite_assembly` | Lean Layer 2 (`PolyKData`): `50 = 17 + 17 + 16` equal-block $k = 3, 4, 5$ rational boxes ($M \ge 2^{36}, 2^{51}, 2^{62}$). Python Layer 3: sharp thresholds $y_0 = 2^{97}$, fixed-$k$ exponents (`97, 122, 137, 148, 178`), `+2m` constants, equal-$k$ box regeneration, Matching-Complement finite checks | $2 \times 2$ & $1 \times 2$ arc decomposition (**Lemma 5.1**), R19 `+2m` original-path endpoint pruning on surviving bridge matching, asymptotic quantifier ($m = o(n^{5/128})$) & same-cycle transfer $H \to G$, matching-complement $K_1/K_2$ dichotomy & two-regime crossing (Sec. 2.3, Sec. 5) |
| **Main Theorem 4 (Theorem 1.4) — General $\Delta \le 4, \delta \ge 3$ Bowties, $\tw(H/B) \le 3$, Order $\ge 120$, & Tier-1 Hamiltonian** (Sec. 6) | *Umbrella:* `ClawFreeEG.main_theorem_4_bowties_tw3_and_hamiltonian`. *Core (`LiftWindows`, `Treewidth3AndBowties`):* `bowtie_forest_exclusion`, `davg_ge_seven_halves_no_forest`, `universal_bowtie_transfer`, `universal_3tree_lemma`, `parallel_edge_hits_c8`, `port_kill_deg3_tri_all_4`, `port_kill_k23_all_128`, `port_kill_q3_minus_v_all_2048`, `port_configs_wellFormed`, `f11_tw3_certified`, `g39_sharp_nonplanar_witness`, `indep_bowtie_4reg_order_5c`, `indep_bowtie_120_arithmetic_bundle`, `ham_all_chord_b_L2_ge_10`, `ham_all_chord_b_4tier_octave_universal`, `ham_all_chord_b_rim_c256_104_to_128`, `ham_all_chord_b_tier1_periods_39` | Lean Layer 2 (`Treewidth3Data`, `Treewidth3Q3DataA/B`): `2,180 = 4 + 128 + 2,048` well-formed port witnesses, `F_11` 8-bag `tw <= 3` & `T_11`, `H_14`/`G_39` cubic/claw-free/DFS/$K_5$-minor checks. Python Layer 3: `4,608` (`512 + 4,096`) $K_{3,3}/Q_3$ subsets, `360,612` lifted-$H$ + `166` overlap configs, strip $W \le 31$ (`29,357`), $k = 8$ (`1,781` + `104..160`), `23` odd (`93,902`), arbitrary matchings even $N \le 136$ (`641` leaves $\le 102$, `{130:73, 132:236, 134:242, 136:723}`) | Bowtie spanning forest (induced tree components), simple $F = H/H_B$, universal transfer (Sec. 6.1), nearest-bag smooth width-3 to spanning 3-tree completion (**Lemma 6.1**), injective local port-witness embedding (Sec. 6.2), distance-3 order-120 local exclusions (**Remark 1.2**, Sec. 6.3), sliding-window $\lceil N/34 \rceil$, seventh-translate, odd-period involution, 4-Tier Octave ($g \mid N$), and finite-order Hamiltonian reductions (Sec. 6.4) |

---

## 4. Count Reconciliation & Parity Comparison Units

To ensure complete transparency across Lean modules, Python verifier logs, JSON witnesses, and the manuscript (explicitly noting the unit of comparison for each parity check in `cert/verify_clawfree_parity.py`):
- **Base packing table `F19` (literal 1-to-1 entry equality):** **`210`** lower-triangular stored entries ($0 \le W_2 \le W_1 \le 19$, with symmetric $20 \times 20$ extension; `F19[19, 19] = 8`), matched identically between `DyadicPackingData.lean` and `dyadic_packing_2d.json`.
- **Case B infinite-tail (`m >= 4096`) leaves (literal leaf-geometry equality + positive packed params):** **`813`** leaves across the `6` simple orbits (`0000: 78`, `1000: 78`, `1100: 132`, `1010: 126`, `1110: 249`, `1111: 150`; exact leaf coordinates `(s1l, s1h, s2l, s2h, curD)` matched 1-to-1 between `DyadicCaseBData.lean` and `dyadic_packing_2d.json`, while Lean stores packed positive subdivision parameters and Python records unfactored scores), plus **`55,531`** terminal leaves out of **`114,643`** visited boxes in Orbit `1001` (Python zero-float B&B, worst `99920/100000`).
- **Two-cycle finite certificates (two independent numerical closure proofs + literal tail-box equality):**
  - Lean `IBoxTree` leaf counts (verified in `TwoCycleData.lean`): **`46`** fourfold leaves (`19 + 11 + 9 + 7` for $M_1 \in \{32, 64, 128, 256\}$, `fourfoldTrees_leaf_count`) and **`61`** equal-medium leaves (`22 + 23 + 16` for $M \in \{256, 512, 1024\}$, `equalMedTrees_leaf_count`), plus `625` small equal-block pairs and **`16`** equal-tail rational boxes ($M \ge 2048$, matched literally to `two_cycle_closure.json`).
  - Python exhaustive point-pair counts (independent enumerations in `verify_clawfree_eg.py`): **`19,174`** twofold ($M_1 \le 256$), **`38,460`** fourfold ($M_1 \le 256$), **`625`** small equal ($M \le 128$, via `exact_attachment_lower(y)`, the conservative R5 Sturmian bound with empty short/long band checks, distinct from `exact_attachment_r11`), and **`76,492`** medium equal ($M \in \{256, 512, 1024\}$) arithmetic comparisons (out of $3{,}655 + 14{,}535 + 58{,}311 = 76{,}501$ triangular integer pairs, with $9$ pairs---$3$ per block---having $e = K - x - 2 < 0$, excluded immediately by Lemma 4.1(ii) and $r \ge 2$), plus the exact same **`16`** tail boxes.
- **Equal-block $k = 3, 4, 5$ rational boxes (literal 1-to-1 box equality):** **`50`** total (`17` at $M \ge 2^{36}$ + `17` at $M \ge 2^{51}$ + `16` at $M \ge 2^{62}$), matched literally between `PolyKData.lean` and `two_cycle_closure.json`.
- **Expanded-port `tw(H/B) <= 3` witnesses (literal 1-to-1 cycle/graph equality):** **`2,180`** total (`4` deg-3 triangle + `128` $K_{2,3}$ + `2,048` $Q_3 - v^*$), plus `F_11`, `H_14`, `G_39` graphs and $K_5$-minor branch sets, all kernel-verified in Lean and matched literally to `tw3_and_g39.json`.
- **Exhaustive $K_{3,3}$/$Q_3$ bowtie subsets (Python replay):** **`4,608`** total (`512` on $K_{3,3}$ + `4,096` on $Q_3$), each cycle validated by `verify_cycle_witness`.
- **Dyadic-cycle-free independent-bowtie order-120 sweep (Python replay):** **`360,612`** lifted-$H$ configurations across `12` pattern families (`243 + 729 + 2,187 + 6,561 + 19,683 + 59,049 + 11,664 + 34,992 + 104,976 + 104,976 + 3,888 + 11,664`) plus **`166`** extra-vertex single-edge-overlap graphs (`9 + 27 + 75 + 55`).
- **Tier-1 Hamiltonian All-Chord-$B$ counts (literal 1-to-1 period/open-case equality + Python replay):** **`39`** all-order periods (`7` even `{2, 4, 6, 8, 10, 12, 14}` + `32` odd `{1, 3, ..., 63}`) and **`23`** odd open $(g, m)$ cases (`93,902` nodes) matched literally between `Treewidth3AndBowties.lean` and `hamiltonian_all_chord_b.json`; **`29,357`** strip visits (`W <= 31, L_win = 17`), and arbitrary matchings for ALL even $N \le 136$ (**`641`** leaves for $N \le 102$, universal rim-$C_{256}$ on $104..128$, and `{130: 73, 132: 236, 134: 242, 136: 723}` frontier visits).
