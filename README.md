# Erdős–Gyárfás Conjecture: Manuscripts, Pure Lean 4 Formalizations, and Zero-Float Verification Artifacts

**Author:** Seth Rehwaldt  
**Repository:** <https://github.com/lollipoll/erdos-gyarfas>  
**License:** Dual-licensed — **MIT** for code, Lean 4 formalizations, Python verifiers, and JSON witness tables ([`LICENSE-MIT`](LICENSE-MIT)); **CC-BY-4.0** for manuscripts and figures ([`LICENSE-CC-BY-4.0`](LICENSE-CC-BY-4.0)).

This umbrella repository archives manuscripts, pure Lean 4 proof-carrying formalizations (zero Mathlib, zero `sorry`, zero custom axioms, zero `native_decide`), and standalone pure-stdlib zero-float Python verification suites for results on the **Erdős–Gyárfás conjecture** (1995): every finite simple graph with minimum degree $\delta(G) \ge 3$ contains a simple cycle whose length is a power of two ($2^k$, $k \ge 2$).

---

## Papers in This Repository

### 1. [`paper1_planar/`](paper1_planar/) — *Every Cubic Planar Graph Contains $C_4, C_8, C_{16},$ or $C_{32}$: Arbitrary Connectivity, Planar Claw-Free $C_{64}$, and General Planar $C_{16}$ Theorems* (Released: `paper1-v1.0`)

- **Preprint (aiXiv):** <https://aixiv.science/abs/aixiv.261126.000002>
- **Manuscript:** [`paper1_planar/manuscript/planar_eg.pdf`](paper1_planar/manuscript/planar_eg.pdf) (40 pages, 3 figures, 2 tables) · LaTeX source: [`paper1_planar/manuscript/planar_eg.tex`](paper1_planar/manuscript/planar_eg.tex)
- **Detailed Guide & Honest Traceability Matrix:** [`paper1_planar/README.md`](paper1_planar/README.md)
- **Main Results** (for all finite nonempty simple planar graphs of *arbitrary connectivity*, permitting disconnected graphs, bridges, cut-vertices, and 2-cuts):
  1. **All Cubic Planar Graphs (Sharp $C_{32}$):** Every finite nonempty simple cubic planar graph contains a simple cycle in $\{C_4, C_8, C_{16}, C_{32}\}$, dropping 3-connectivity from Heckman–Krakovski (2013) and improving the cutoff fourfold from $128$ to the exact optimum $32$. Sharpness is witnessed by an elementary 168-vertex 6-face-free 3-connected cubic planar graph $G_{168} = C_{24} * [T_1 + P + T_2]$ with no $C_4, C_8, C_{16}$ and an explicit $C_{32}$, fully kernel-verified in Lean 4.
  2. **All Planar Induced Claw-Free Graphs (Explicit $C_{64}$):** Every finite nonempty simple planar induced claw-free (induced $K_{1,3}$-free) graph with $\delta(G) \ge 3$ contains a simple cycle in $\{C_4, C_8, C_{16}, C_{32}, C_{64}\}$, via planar bowtie-splitting and a universal cubic-to-claw-free transfer theorem.
  3. **General Planar $\delta \ge 3$ $C_{16}$ Trilogy (Arbitrary $\Delta$):** Every finite nonempty simple planar graph with $\delta(G) \ge 3$ that is $C_3$-free, $C_5$-free, or $C_6$-free contains a simple cycle in $\{C_4, C_8, C_{16}\}$. Each part is sharp, witnessed by $C_{60}$, $TD_{60}$, and their 119-vertex $\Delta = 6$ planar 1-sums.
  4. **Alternating-$C_6$ Planar Degree-Density Bound:** Every finite nonempty simple planar graph with $\delta(G) \ge 3$, independent $V_{\ge 4}$, and no $C_4, C_8$ satisfies $16h + 4\varepsilon \le 5(n - 2) + 4\tau_6$; in particular, when $C_6$-free, $|V_3| \ge \lceil(11n + 10)/16\rceil > 2n/3$ for all $n \ge 7$ (improving the $2/3$ density coefficient by $+1/48$).
- **Verification Summary (`paper1_planar/`):** Pure Lean 4 `v4.36.0` (zero Mathlib, `106/106` audited declarations strictly in `{propext, Classical.choice, Quot.sound}`, `6,772` strict-schema explicit simple dyadic-cycle weld/rim entries, cellular-rotation certificates for $G_{168}, C_{60}, TD_{60}$) + standalone zero-float Python verifiers (`verify_planar_eg.py`, `verify_parity_and_dp.py`, `41/41` SHA-256 manifest).

---

### 2. [`paper2_clawfree/`](paper2_clawfree/) — *Erdős–Gyárfás for 2-Cycle, Sublinear-Circumference, and Bowtie Claw-Free Graphs via Sub-Unit 2D Dyadic $L_\infty$-Packing* (Released: `paper2-v1.0`)

- **Manuscript:** [`paper2_clawfree/manuscript/clawfree_eg.pdf`](paper2_clawfree/manuscript/clawfree_eg.pdf) (41 pages, 4 figures, 1 traceability table) · LaTeX source: [`paper2_clawfree/manuscript/clawfree_eg.tex`](paper2_clawfree/manuscript/clawfree_eg.tex)
- **Detailed Guide & Honest Traceability Matrix:** [`paper2_clawfree/README.md`](paper2_clawfree/README.md)
- **Main Results** (100% pure discrete combinatorics, zero topological axioms):
  1. **Sub-Unit-Constant 2D Dyadic $L_\infty$-Packing (Theorem 1.1):** For every $W_1, W_2 \ge 0$ and every same-parity subset $S \subset [0, W_1] \times [0, W_2]$ with no diagonal collisions ($|u_1 - u_2| \neq |v_1 - v_2|$) and $\|p - q\|_\infty + 2 \in \mathcal{F}_{\mathrm{EG}}$, $|S| \le \frac{3}{5}((W_1 + 2)(W_2 + 2))^{123/256}$, collapsing the equal-block coarse crossover to $M_0 = 2^{57}$.
  2. **All 2-Cycle Cubic Claw-Free Graphs (Theorem 1.2):** Every finite nonempty simple cubic claw-free graph whose triangle quotient $H$ admits a 2-cycle spanning 2-factor (arbitrary block ratios, chords, parity, or non-Hamiltonicity) contains a power-of-two cycle.
  3. **Poly-$k$-Cycle, Sublinear Circumference, Sturmian, and Matching-Complement Theorems (Theorem 1.3):** Pairwise bridge cap $r(C_1, C_2) \le \frac{12}{5}(y + 2)^{123/128}$, closing all $k$-cycle spanning 2-factors with $k \le (n/2^{97})^{5/133}$ (and equal-block $k \in \{3, 4, 5\}$ at $M \ge 2^{36}, 2^{51}, 2^{62}$); sublinear $o(n)$ circumference threshold $y \ge \max(2^{97} m^{128/5}, 25 n^{128/133})$ for $m$-path complement covers ($m = o(n^{5/128})$); unconditional Sturmian bounds $c(G) \ge \frac{17}{18}|V(G)|$ (bipartite quotient $H$: $\frac{15}{16}|V(G)|$); and matching-complement closure ($\Delta(H - V(C)) \le 1$).
  4. **General $\Delta \le 4, \delta \ge 3$ Bowtie Claw-Free Reductions, $\bar{d} \ge \frac{7}{2}$, $\operatorname{tw}(H/B) \le 3$, Order $\ge 120$, and Tier-1 Hamiltonian All-Chord-$B$ (Theorem 1.4):** Exact lift window $[2L - k, 3L - k - m]$, spanning induced bowtie forest $H_B$, simple quotient $F = H/H_B$, universal transfer ($2^K \to 2^{K+1}$), $\bar{d}(G) \ge \frac{7}{2}$ (all 4-regular claw-free graphs); 15-line Universal 3-Tree Lemma forcing $C_8$ or $C_{16}$ for all $C_4$-free independent-bowtie graphs with $\operatorname{tw}(H/B) \le 3$ (sharp via explicit 39-vertex non-planar $K_5$-minor witness $G_{39} = T(H_{14})/B$); $|V(G)| \ge 120$ for dyadic-cycle-free independent-bowtie graphs with 4-regular quotient $F$; and Tier-1 Hamiltonian all-chord-$B$ closures ($L_2 \ge 10$, $W \le 31$ forcing $\ge \lceil N/34 \rceil$ long chords, 39 all-order periods, 4-Tier Dyadic-Octave regimes, and arbitrary matchings of even order $4 \le N \le 136$).
- **Verification Summary (`paper2_clawfree/`):** Pure Lean 4 `v4.36.0` (zero Mathlib, **zero `Std`**, `261/261` audited public theorems strictly in `{propext, Classical.choice, Quot.sound}`, `2,180` expanded-port `FinGraph` cycle witnesses, full `FinGraph` verification of $F_{11}, H_{14}, G_{39}$ + $K_5$-minors) + standalone zero-float Python verifiers (`verify_clawfree_eg.py`, `verify_clawfree_parity.py`, `26/26` SHA-256 manifest).

---

## Quick Verification

### Paper 1 (`paper1_planar/`)

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

### Paper 2 (`paper2_clawfree/`)

```bash
# 1. Verify SHA-256 manifest (26 tracked files)
(cd paper2_clawfree && sha256sum -c SHA256SUMS)

# 2. Build pure Lean 4 library (v4.36.0, zero Mathlib, zero Std) and audit all 261 declarations
(cd paper2_clawfree/lean && LEAN_NUM_THREADS=1 lake build && LEAN_NUM_THREADS=1 lake env lean AxiomCheck.lean)

# 3. Run both standalone zero-float Python verifiers (~30 s total)
(cd paper2_clawfree && python3 -B cert/verify_clawfree_eg.py && python3 -B cert/verify_clawfree_parity.py)

# 4. Recompile the self-contained 41-page LaTeX manuscript
(cd paper2_clawfree/manuscript && pdflatex -interaction=nonstopmode clawfree_eg.tex && pdflatex -interaction=nonstopmode clawfree_eg.tex)
```

---

## AI-Assistance Disclosure

During the preparation of these works, the author used *Gemini 4 Neon* to assist with interactive proof exploration, certificate design, Lean 4 formalization, and manuscript drafting, and used *GPT 6.2 Astra* to perform independent AI-assisted adversarial audits of the Lean 4 declarations, Python verification scripts, certificate parity, and manuscript proofs. Every machine-checkable claim is independently verified by the pure Lean 4 kernel and standalone zero-float Python scripts, and the author takes full responsibility for all mathematical claims, proofs, code, and references.
