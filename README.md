# Erdős–Gyárfás Conjecture: Manuscripts, Pure Lean 4 Formalizations, and Zero-Float Verification Artifacts

**Author:** Seth Rehwaldt  
**Repository:** <https://github.com/lollipoll/erdos-gyarfas>  
**License:** Dual-licensed — **MIT** for code, Lean 4 formalizations, Python verifiers, and JSON witness tables ([`LICENSE-MIT`](LICENSE-MIT)); **CC-BY-4.0** for manuscripts and figures ([`LICENSE-CC-BY-4.0`](LICENSE-CC-BY-4.0)).

This umbrella repository archives manuscripts, pure Lean 4 proof-carrying formalizations (zero Mathlib, zero `sorry`, zero custom axioms, zero `native_decide`), and standalone pure-stdlib zero-float Python verification suites for results on the **Erdős–Gyárfás conjecture** (1995): every finite simple graph with minimum degree $\delta(G) \ge 3$ contains a simple cycle whose length is a power of two ($2^k$, $k \ge 2$).

---

## Papers in This Repository

### 1. [`paper1_planar/`](paper1_planar/) — *Every Cubic Planar Graph Contains $C_4, C_8, C_{16},$ or $C_{32}$: Arbitrary Connectivity, Planar Claw-Free $C_{64}$, and General Planar $C_{16}$ Theorems* (Released: `paper1-v1.0`)

- **Manuscript:** [`paper1_planar/manuscript/planar_eg.pdf`](paper1_planar/manuscript/planar_eg.pdf) (40 pages, 3 figures, 2 tables) · LaTeX source: [`paper1_planar/manuscript/planar_eg.tex`](paper1_planar/manuscript/planar_eg.tex)
- **Detailed Guide & Honest Traceability Matrix:** [`paper1_planar/README.md`](paper1_planar/README.md)
- **Main Results** (for all finite nonempty simple planar graphs of *arbitrary connectivity*, permitting disconnected graphs, bridges, cut-vertices, and 2-cuts):
  1. **All Cubic Planar Graphs (Sharp $C_{32}$):** Every finite nonempty simple cubic planar graph contains a simple cycle in $\{C_4, C_8, C_{16}, C_{32}\}$, dropping 3-connectivity from Heckman–Krakovski (2013) and improving the cutoff fourfold from $128$ to the exact optimum $32$. Sharpness is witnessed by an elementary 168-vertex 6-face-free 3-connected cubic planar graph $G_{168} = C_{24} * [T_1 + P + T_2]$ with no $C_4, C_8, C_{16}$ and an explicit $C_{32}$, fully kernel-verified in Lean 4.
  2. **All Planar Induced Claw-Free Graphs (Explicit $C_{64}$):** Every finite nonempty simple planar induced claw-free (induced $K_{1,3}$-free) graph with $\delta(G) \ge 3$ contains a simple cycle in $\{C_4, C_8, C_{16}, C_{32}, C_{64}\}$, via planar bowtie-splitting and a universal cubic-to-claw-free transfer theorem.
  3. **General Planar $\delta \ge 3$ $C_{16}$ Trilogy (Arbitrary $\Delta$):** Every finite nonempty simple planar graph with $\delta(G) \ge 3$ that is $C_3$-free, $C_5$-free, or $C_6$-free contains a simple cycle in $\{C_4, C_8, C_{16}\}$. Each part is sharp, witnessed by $C_{60}$, $TD_{60}$, and their 119-vertex $\Delta = 6$ planar 1-sums.
  4. **Alternating-$C_6$ Planar Degree-Density Bound:** Every finite nonempty simple planar graph with $\delta(G) \ge 3$, independent $V_{\ge 4}$, and no $C_4, C_8$ satisfies $16h + 4\varepsilon \le 5(n - 2) + 4\tau_6$; in particular, when $C_6$-free, $|V_3| \ge \lceil(11n + 10)/16\rceil > 2n/3$ for all $n \ge 7$ (improving the $2/3$ density coefficient by $+1/48$).

#### Four-Layer Honest Verification Architecture (`paper1_planar/`)

1. **Pure Lean 4 Kernel (`paper1_planar/lean/`, Lean `v4.36.0`, `import Std`, zero Mathlib):** Core algebraic, discharging, Bellman–Ford/DP/BWD soundness, exhaustive $F_{10}$ 5-triangle bound (`47/12 < 4`), bowtie-forest arithmetic, and density lemmas. All `106/106` audited declarations in `AxiomCheck.lean` depend strictly on `{propext, Classical.choice, Quot.sound}` (zero `sorry`, zero custom axioms, zero `native_decide`).
2. **Proof-Carrying Lean 4 Certificates:** Kernel-checked dual potentials, DP/BWD bounds, strict face-schema (`WeldSchemaValid`) + explicit simple dyadic-cycle proofs across all **6,772** eliminated weld/outer-rim entries (counted with multiplicity across certificate groups), and cellular-rotation / 3-connectivity / cycle-exclusion certificates for $G_{168}$, $C_{60}$, and $TD_{60}$.
3. **Standalone Zero-Float Python Verifiers (`paper1_planar/cert/`):** Pure Python 3 standard library, AST-guarded against floats and `/` true division:
   - `cert/verify_planar_eg.py` (`~21s`, `43 MiB` RSS) replays all finite searches, boundary-weld and outer-rim enumerations, 51-chain BFS, conservative $d \in \{14, 17, 18\}$ enumerations, uncollapsed DPs, Bellman–Ford potentials, and 119-vertex 1-sum witnesses, reproducing all 4 JSON tables in `cert/witnesses/` byte for byte.
   - `cert/verify_parity_and_dp.py` (`~43s`, `70 MiB` RSS) checks literal Lean–Python–JSON parity across all 6,772 entries, verifies the Lemma 3.1 boundary-regularity invariant across all `844/844` production calls, verifies all `12/12` weighted forward-simulation proofs linking the uncollapsed DPs to the packed Lean automata, and replays all supplemental manuscript subaudits (including all `14,962` $C_5$-free Stage-3 outer-rim capacity kills).
4. **Full Manuscript Proofs (`paper1_planar/manuscript/planar_eg.tex`):** Complete topological spherical embeddings, Jordan curve arguments, connectivity-cap reductions, discharging rules, graph-to-token maps, and 1-sum gluing proofs.

---

### 2. `paper2_clawfree/` — *(Upcoming)*

A second paper extending the structural and computational methods to broader claw-free and related sparse regimes will be added under `paper2_clawfree/` in a future release.

---

## Quick Verification (`paper1_planar/`)

```bash
# 1. Verify SHA-256 manifest (41 tracked files)
(cd paper1_planar && sha256sum -c SHA256SUMS)

# 2. Run both standalone zero-float Python verifiers (~1 min total)
python3 -B paper1_planar/cert/verify_planar_eg.py
python3 -B paper1_planar/cert/verify_parity_and_dp.py

# 3. Build pure Lean 4 library (v4.36.0, zero Mathlib) and audit all 106 declarations
(cd paper1_planar/lean && LEAN_NUM_THREADS=1 lake build && LEAN_NUM_THREADS=1 lake env lean AxiomCheck.lean)

# 4. Recompile the self-contained 40-page LaTeX manuscript
(cd paper1_planar/manuscript && pdflatex -interaction=nonstopmode planar_eg.tex && pdflatex -interaction=nonstopmode planar_eg.tex)
```

---

## AI-Assistance Disclosure

During the preparation of this work, the author used *Gemini 4 Neon* to assist with interactive proof exploration, discharging-rule and certificate design, Lean 4 formalization, and manuscript drafting, and used *GPT 6.2 Astra* to perform an AI-assisted adversarial audit of the Lean 4 declarations, Python verification scripts, certificate parity, and manuscript proofs. Every machine-checkable claim is independently verified by the pure Lean 4 kernel and standalone zero-float Python scripts, and the author takes full responsibility for all mathematical claims, proofs, code, and references.
