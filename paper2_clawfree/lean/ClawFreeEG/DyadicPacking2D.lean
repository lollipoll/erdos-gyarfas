import ClawFreeEG.LiftWindows
import ClawFreeEG.DyadicPackingData
import ClawFreeEG.DyadicCaseBData

/-!
# ClawFreeEG.DyadicPacking2D

Pure Lean 4 (`v4.36.0`, ZERO Mathlib, ZERO `Std`, ZERO `sorry`, ZERO `axiom`,
ZERO `native_decide`, ZERO `unsafe`/`implemented_by`/`extern`/`partial`) formalization &
kernel verification for the arithmetic, power-enclosure, and finite-certificate components
of Main Theorem 1 (Sub-Unit-Constant 2D Dyadic `L_∞`-Packing, `C = 3/5`, `α = 123/256`, `c_0 = 2`):

  `|S| ≤ (3/5) * ((W1 + 2) * (W2 + 2))^(123/256)` for all `W1, W2 ≥ 0`

over the **exact packing domain** (`IsValid2DPacking`): same-parity subsets
`S ⊂ [0, W1] × [0, W2]` (`(u + v) mod 2` constant) with **distinct absolute differences
`|u1 - u2| ≠ |v1 - v2|`** (equivalently, pairwise distinct `u + v` and pairwise distinct
`u - v`, i.e., no diagonal collisions — corresponding to pairwise distinct arc endpoints
`(i, j)` under the 45°-rotated bridge encoding `(u, v) = (i + j, i - j)`), and
`max(|u1 - u2|, |v1 - v2|) + 2 ∈ F_EG`.

## Kernel-Verified Components in This Module (Layers 1–2)
1. **Exact `isqrt` & 8-fold `isqrt256`** (`isqrt_spec`, `isqrt256_spec`), exact
   `powBounds_123_256` with tight bracket proof (`powBounds_123_256_spec`,
   `powBounds_123_256_tight`), and exact `prodUp`/`prodLo` rounding soundness.
2. **Pure-Algebraic 8-Fold AM-GM Power Enclosure Engine** (`amgm_256`, `pupFast_sound`,
   `ploFast_sound`) proving unconditional soundness of `123/256`-power bounds from the
   `97` kernel-certified table entries (`65` anchors + `32` octaves) in `DyadicPackingData`.
3. **Exact Base `F19` Table Certificate (`210` Lower-Triangular Entries `0 ≤ w2 ≤ w1 ≤ 19`):**
   monotonicity, key values (`F19[19, 19] = 8`, `F19[3, 1] = 2`, `F19[2, 1] = 1`), and all
   `210` packing-table bounds `(F19[w1][w2])^256 * 5^256 ≤ 3^256 * ((w1 + 2)*(w2 + 2))^123`,
   plus all `7` dyadic sub-interval algebraic identities for every dyadic block `m = 2^k ≥ 32`.
4. **2D Packing Predicate & Monotone DP Invariants:** `IsValid2DPacking` (explicitly enforcing
   same parity, no diagonal collisions `|u1 - u2| ≠ |v1 - v2|`, and `L_∞`-band `F_EG`),
   exact forbidden gap theorem `gap_outside_feg`, square gap collapse `square_gap_collapse`,
   and block monotonicity soundness `dp_block_soundness_invariant`.
5. **Universal Infinite-Tail Case A (`m ≥ 4096`):** all `64` intervals kernel-verified
   (`max ≤ 96558 ≤ 99920 < 100000`) and bridged to a universal inequality for ALL `m ≥ 4096`
   and ALL `0 ≤ s` with `3 * s < m`.
6. **Exact `Z_2 × Z_2` Symmetry-Orbit Partition (`16 = 1 + 4 + 2 + 2 + 4 + 1 + 2`) & Case B
   Optimized Evaluator Semantic Soundness:**
   - Kernel-proved semantic soundness of `pupGrid` (`pupGrid_sound`, `gridUp2048_mono`),
     `pupEGrid` (`pupEGrid_sound`, `pupEGrid_shift2_sound`), `holderPairEGrid`
     (`holderPairEGrid_sound`, including exact concavity midpoint and 8-subinterval envelope),
     `aMax256Tree` & `maxFactoredAMGM` (`factored_amgm_1110_sound`, `maxFactoredAMGM_sound`,
     `aMax256_sound`), and the `379,133`-weighted tangent majorant for `1111`
     (`pow123_tangent_linear`, `weighted_tangent_379_133_sound`, `maxTangentForSum_sound`).
   - Exact 2D dyadic quad-tree triangle coverage AND strictly-guarded leaf checks (`≤ 99920/100000`)
     for ALL `6` simple Case B orbits (`0000:78, 1000:78, 1100:132, 1010:126, 1110:249, 1111:150`;
     total `813` leaves).
7. **Universal Threshold Collapse (`M ≥ 2^57`, sharp at `2^56`)** and R15 ratio bound.

## Transparent Scope Boundary (Layers 3–4)
- **Layer 3 (`cert/verify_clawfree_eg.py`):** independently verifies the exact `F19` clique
  search on the no-diagonal same-parity domain, the intermediate finite DP sweep `m = 32..2048`
  (`U(2728, 2728) = 1076`), the unfactored subdivisions on all `813` simple-orbit Case B leaves,
  and the `55,531`-leaf diagonal-orbit `1001` B&B certificate (`114,643` visited boxes, worst
  `99920 / 100000`).
- **Layer 4 (LaTeX Manuscript):** proves the geometric packing-to-DP recurrence, Case A/B
  rectangle decompositions (including ties, empty widths, clipped gaps, and `1001` H/V-merges),
  and the induction joining `F19`, `m = 32..2048`, and `m ≥ 4096` into the full packing theorem.
-/

namespace ClawFreeEG

open ClawFreeEG.DyadicPackingData
open ClawFreeEG.DyadicCaseBData

/-! ## 1. Exact `isqrt`, `isqrt256`, `powBounds_123_256`, & `prodUp` / `prodLo` -/

/-- Exact fixed-point scale `SCALE = 100000` for rational interval bounds. -/
abbrev SCALE : Nat := 100000

/-- Exact integer square root `⌊√n⌋` (total, zero `partial`). -/
def isqrt (n : Nat) : Nat := Nat.sqrt n

/-- Exact 256th integer root `⌊n^(1/256)⌋` via 8-fold `isqrt`. -/
def isqrt256 (n : Nat) : Nat :=
  isqrt (isqrt (isqrt (isqrt (isqrt (isqrt (isqrt (isqrt n)))))))

/-- Exact specification of `isqrt`: `(isqrt n)^2 ≤ n < (isqrt n + 1)^2`. -/
theorem isqrt_spec (n : Nat) : (isqrt n) ^ 2 ≤ n ∧ n < (isqrt n + 1) ^ 2 := by
  unfold isqrt
  rw [Nat.pow_two, Nat.pow_two]
  exact ⟨Nat.sqrt_le n, Nat.lt_succ_sqrt n⟩

/-- Helper: doubling the exponent via one `isqrt` composition preserves exact floor brackets. -/
private theorem isqrt_double_spec {a r n k : Nat}
    (hr : a ^ k ≤ r ∧ r < (a + 1) ^ k)
    (hn : r ^ 2 ≤ n ∧ n < (r + 1) ^ 2) :
    a ^ (2 * k) ≤ n ∧ n < (a + 1) ^ (2 * k) := by
  have hpow1 : a ^ (2 * k) = (a ^ k) ^ 2 := by
    rw [Nat.mul_comm, Nat.pow_mul]
  have hpow2 : (a + 1) ^ (2 * k) = ((a + 1) ^ k) ^ 2 := by
    rw [Nat.mul_comm, Nat.pow_mul]
  constructor
  · rw [hpow1]
    exact Nat.le_trans (Nat.pow_le_pow_left hr.1 2) hn.1
  · rw [hpow2]
    have hle : r + 1 ≤ (a + 1) ^ k := hr.2
    exact Nat.lt_of_lt_of_le hn.2 (Nat.pow_le_pow_left hle 2)

/-- Exact specification of 8-fold `isqrt256`: `(isqrt256 n)^256 ≤ n < (isqrt256 n + 1)^256`. -/
theorem isqrt256_spec (n : Nat) : (isqrt256 n) ^ 256 ≤ n ∧ n < (isqrt256 n + 1) ^ 256 := by
  unfold isqrt256
  let r1 := isqrt n
  let r2 := isqrt r1
  let r3 := isqrt r2
  let r4 := isqrt r3
  let r5 := isqrt r4
  let r6 := isqrt r5
  let r7 := isqrt r6
  have h7 : (isqrt r7) ^ 2 ≤ r7 ∧ r7 < (isqrt r7 + 1) ^ 2 := isqrt_spec r7
  have h6 : (isqrt r7) ^ 4 ≤ r6 ∧ r6 < (isqrt r7 + 1) ^ 4 := isqrt_double_spec h7 (isqrt_spec r6)
  have h5 : (isqrt r7) ^ 8 ≤ r5 ∧ r5 < (isqrt r7 + 1) ^ 8 := isqrt_double_spec h6 (isqrt_spec r5)
  have h4 : (isqrt r7) ^ 16 ≤ r4 ∧ r4 < (isqrt r7 + 1) ^ 16 := isqrt_double_spec h5 (isqrt_spec r4)
  have h3 : (isqrt r7) ^ 32 ≤ r3 ∧ r3 < (isqrt r7 + 1) ^ 32 := isqrt_double_spec h4 (isqrt_spec r3)
  have h2 : (isqrt r7) ^ 64 ≤ r2 ∧ r2 < (isqrt r7 + 1) ^ 64 := isqrt_double_spec h3 (isqrt_spec r2)
  have h1 : (isqrt r7) ^ 128 ≤ r1 ∧ r1 < (isqrt r7 + 1) ^ 128 := isqrt_double_spec h2 (isqrt_spec r1)
  exact isqrt_double_spec h1 (isqrt_spec n)

/-- Helper computing `(lo, hi)` for `p * S256 / q` without exposing `SCALE ^ 256` to `isDefEq`. -/
def powBounds_aux_pair (p q S256 : Nat) : Nat × Nat :=
  let lo := isqrt256 ((p * S256) / q)
  let hi := if lo ^ 256 * q == p * S256 then lo else lo + 1
  (lo, hi)

/-- Exact integer pair `(lo, hi)` bracketing `(num / den)^(123/256) * SCALE`. -/
def powBounds_123_256 (num den : Nat) : Nat × Nat :=
  if num == 0 then (0, 0)
  else powBounds_aux_pair (num ^ 123) (den ^ 123) (SCALE ^ 256)

private theorem powBounds_aux (p q S256 : Nat) (hq_pos : 0 < q) :
    let (lo, hi) := powBounds_aux_pair p q S256
    lo ^ 256 * q ≤ p * S256 ∧ p * S256 ≤ hi ^ 256 * q := by
  unfold powBounds_aux_pair
  dsimp only
  generalize ht : p * S256 = target
  generalize hl : isqrt256 (target / q) = lo
  have hspec : lo ^ 256 ≤ target / q ∧ target / q < (lo + 1) ^ 256 := by
    rw [← hl]; exact isqrt256_spec (target / q)
  have hlo_mul : lo ^ 256 * q ≤ target := by
    have h1 : lo ^ 256 * q ≤ (target / q) * q := Nat.mul_le_mul_right q hspec.1
    have h2 : (target / q) * q ≤ target := by
      rw [Nat.mul_comm]; exact Nat.mul_div_le target q
    exact Nat.le_trans h1 h2
  have hhi_strict : target < (lo + 1) ^ 256 * q := by
    have h1 : target / q + 1 ≤ (lo + 1) ^ 256 := hspec.2
    have h2 : (target / q + 1) * q ≤ (lo + 1) ^ 256 * q := Nat.mul_le_mul_right q h1
    have h3 : target < (target / q + 1) * q := by
      have hdm := Nat.div_add_mod target q
      have hmod : target % q < q := Nat.mod_lt target hq_pos
      rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm (target / q) q]
      omega
    exact Nat.lt_of_lt_of_le h3 h2
  by_cases heq : lo ^ 256 * q = target
  · simp only [heq, beq_self_eq_true, ↓reduceIte]
    exact ⟨Nat.le_refl _, Nat.le_refl _⟩
  · have hne : (lo ^ 256 * q == target) = false := beq_false_of_ne heq
    simp only [hne, Bool.false_eq_true, ↓reduceIte]
    exact ⟨hlo_mul, Nat.le_of_lt hhi_strict⟩

private theorem powBounds_tight_aux (p q S256 : Nat) (hp_pos : 0 < p) (hq_pos : 0 < q) (hS_pos : 0 < S256) :
    let (lo, hi) := powBounds_aux_pair p q S256
    p * S256 < (lo + 1) ^ 256 * q ∧ (hi - 1) ^ 256 * q < p * S256 := by
  unfold powBounds_aux_pair
  dsimp only
  have htarget_pos : 0 < p * S256 := Nat.mul_pos hp_pos hS_pos
  generalize ht : p * S256 = target at htarget_pos ⊢
  generalize hl : isqrt256 (target / q) = lo
  have hspec : lo ^ 256 ≤ target / q ∧ target / q < (lo + 1) ^ 256 := by
    rw [← hl]; exact isqrt256_spec (target / q)
  have hlo_mul : lo ^ 256 * q ≤ target := by
    have h1 : lo ^ 256 * q ≤ (target / q) * q := Nat.mul_le_mul_right q hspec.1
    have h2 : (target / q) * q ≤ target := by
      rw [Nat.mul_comm]; exact Nat.mul_div_le target q
    exact Nat.le_trans h1 h2
  have hhi_strict : target < (lo + 1) ^ 256 * q := by
    have h1 : target / q + 1 ≤ (lo + 1) ^ 256 := hspec.2
    have h2 : (target / q + 1) * q ≤ (lo + 1) ^ 256 * q := Nat.mul_le_mul_right q h1
    have h3 : target < (target / q + 1) * q := by
      have hdm := Nat.div_add_mod target q
      have hmod : target % q < q := Nat.mod_lt target hq_pos
      rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm (target / q) q]
      omega
    exact Nat.lt_of_lt_of_le h3 h2
  by_cases heq : lo ^ 256 * q = target
  · simp only [heq, beq_self_eq_true, ↓reduceIte]
    refine ⟨hhi_strict, ?_⟩
    have hlo_pos : 0 < lo := by
      cases hlo : lo with
      | zero => rw [hlo] at heq; simp at heq; omega
      | succ k => exact Nat.zero_lt_succ k
    have hpow_lt : (lo - 1) ^ 256 < lo ^ 256 := by
      have step : ∀ e : Nat, e ≥ 1 → (lo - 1) ^ e < lo ^ e := by
        intro e he
        induction e with
        | zero => omega
        | succ e' ih =>
          by_cases he0 : e' = 0
          · subst he0; simp; omega
          · have ih' := ih (by omega)
            rw [Nat.pow_succ, Nat.pow_succ]
            calc (lo - 1) ^ e' * (lo - 1)
                ≤ (lo - 1) ^ e' * lo := Nat.mul_le_mul_left _ (by omega)
              _ < lo ^ e' * lo := Nat.mul_lt_mul_of_pos_right ih' hlo_pos
      exact step 256 (by omega)
    rw [← heq]
    exact Nat.mul_lt_mul_of_pos_right hpow_lt hq_pos
  · have hne : (lo ^ 256 * q == target) = false := beq_false_of_ne heq
    simp only [hne, Bool.false_eq_true, ↓reduceIte, Nat.add_sub_cancel]
    exact ⟨hhi_strict, Nat.lt_of_le_of_ne hlo_mul heq⟩

/-- Exact bracket theorem for `powBounds_123_256`:
`lo^256 * den^123 ≤ num^123 * SCALE^256 ≤ hi^256 * den^123` for every `den > 0`. -/
theorem powBounds_123_256_spec (num den : Nat) (hden : 0 < den) :
    let (lo, hi) := powBounds_123_256 num den
    lo ^ 256 * den ^ 123 ≤ num ^ 123 * SCALE ^ 256 ∧
    num ^ 123 * SCALE ^ 256 ≤ hi ^ 256 * den ^ 123 := by
  unfold powBounds_123_256
  cases num with
  | zero => simp
  | succ m =>
    simp only [Nat.succ_ne_zero, beq_iff_eq, ↓reduceIte]
    exact powBounds_aux ((m + 1) ^ 123) (den ^ 123) (SCALE ^ 256) (Nat.pow_pos hden)

/-- Tightness of `powBounds_123_256`: `lo` is the exact floor and `hi` is the exact ceiling. -/
theorem powBounds_123_256_tight (num den : Nat) (hden : 0 < den) :
    let (lo, hi) := powBounds_123_256 num den
    num ^ 123 * SCALE ^ 256 < (lo + 1) ^ 256 * den ^ 123 ∧
    (0 < num → (hi - 1) ^ 256 * den ^ 123 < num ^ 123 * SCALE ^ 256) := by
  unfold powBounds_123_256
  cases num with
  | zero =>
    simp only [beq_self_eq_true, ↓reduceIte, Nat.zero_add, Nat.one_pow, Nat.one_mul]
    exact ⟨by
      have hq : 0 < den ^ 123 := Nat.pow_pos hden
      simp [hq], fun h => by omega⟩
  | succ m =>
    simp only [Nat.succ_ne_zero, beq_iff_eq, ↓reduceIte]
    have h := powBounds_tight_aux ((m + 1) ^ 123) (den ^ 123) (SCALE ^ 256)
      (Nat.pow_pos (Nat.zero_lt_succ m)) (Nat.pow_pos hden) (Nat.pow_pos (by decide : 0 < SCALE))
    exact ⟨h.1, fun _ => h.2⟩

/-- Sound outward-rounded product `⌈(a * b) / SCALE⌉`. -/
@[inline] def prodUp (a b : Nat) : Nat := prodUpD a b

/-- Sound inward-rounded product `⌊(a * b) / SCALE⌋`. -/
@[inline] def prodLo (a b : Nat) : Nat := prodLoD a b

/-- Soundness of `prodLo`: `prodLo a b * SCALE ≤ a * b < (prodLo a b + 1) * SCALE`. -/
theorem prodLo_sound (a b : Nat) :
    prodLo a b * SCALE ≤ a * b ∧ a * b < (prodLo a b + 1) * SCALE := by
  unfold prodLo prodLoD
  have hS : 0 < SCALE := by decide
  have hdm := Nat.div_add_mod (a * b) SCALE
  have hmod := Nat.mod_lt (a * b) hS
  have hcomm : SCALE * (a * b / SCALE) = (a * b / SCALE) * SCALE := Nat.mul_comm _ _
  rw [Nat.add_mul, Nat.one_mul]
  change (a * b / SCALE) * SCALE ≤ a * b ∧ a * b < (a * b / SCALE) * SCALE + SCALE
  omega

/-- Soundness of `prodUp`: `a * b ≤ prodUp a b * SCALE` and tightness when `a * b > 0`. -/
theorem prodUp_sound (a b : Nat) :
    a * b ≤ prodUp a b * SCALE ∧ (0 < a * b → (prodUp a b - 1) * SCALE < a * b) := by
  unfold prodUp prodUpD
  have hS : 0 < SCALE := by decide
  have hdm := Nat.div_add_mod (a * b + SCALE - 1) SCALE
  have hmod := Nat.mod_lt (a * b + SCALE - 1) hS
  have hcomm : SCALE * ((a * b + SCALE - 1) / SCALE) = ((a * b + SCALE - 1) / SCALE) * SCALE :=
    Nat.mul_comm _ _
  change a * b ≤ ((a * b + SCALE - 1) / SCALE) * SCALE ∧
         (0 < a * b → ((a * b + SCALE - 1) / SCALE - 1) * SCALE < a * b)
  constructor
  · omega
  · intro hpos
    have hge1 : 1 ≤ (a * b + SCALE - 1) / SCALE := Nat.div_pos (by omega) hS
    have hsub : ((a * b + SCALE - 1) / SCALE - 1) * SCALE + SCALE =
                ((a * b + SCALE - 1) / SCALE) * SCALE := by
      have hadd := Nat.sub_add_cancel hge1
      have hmul : ((a * b + SCALE - 1) / SCALE - 1 + 1) * SCALE =
                  ((a * b + SCALE - 1) / SCALE) * SCALE := congrArg (· * SCALE) hadd
      rw [Nat.add_mul, Nat.one_mul] at hmul
      exact hmul
    omega

theorem prodUp_mono {a1 a2 b1 b2 : Nat} (ha : a1 ≤ a2) (hb : b1 ≤ b2) :
    prodUp a1 b1 ≤ prodUp a2 b2 := by
  unfold prodUp prodUpD
  have hmul : a1 * b1 ≤ a2 * b2 := Nat.mul_le_mul ha hb
  exact Nat.div_le_div_right (by omega)

theorem prodLo_mono {a1 a2 b1 b2 : Nat} (ha : a1 ≤ a2) (hb : b1 ≤ b2) :
    prodLo a1 b1 ≤ prodLo a2 b2 := by
  unfold prodLo prodLoD
  exact Nat.div_le_div_right (Nat.mul_le_mul ha hb)

/-! ## 2. Pure-Algebraic 8-Fold AM-GM Power Enclosure Engine (`amgm_256`, `pupFast`, `ploFast`) -/

/-- Elementary 2-variable AM-GM: `4 * u * v ≤ (u + v)^2`. -/
private theorem amgm_2 (u v : Nat) : 4 * u * v ≤ (u + v) ^ 2 := by
  have hexp : (u + v) ^ 2 = u * u + 2 * (u * v) + v * v := by
    rw [Nat.pow_two, Nat.mul_add, Nat.add_mul, Nat.add_mul]
    have hc : v * u = u * v := Nat.mul_comm v u
    omega
  rw [hexp]
  have h4 : 4 * u * v = 4 * (u * v) := Nat.mul_assoc 4 u v
  rw [h4]
  by_cases huv : u ≤ v
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le huv
    have h1 : (u + d) * (u + d) = u * u + 2 * (u * d) + d * d := by
      rw [Nat.mul_add, Nat.add_mul, Nat.add_mul]
      have hc : d * u = u * d := Nat.mul_comm d u
      omega
    have h2 : u * (u + d) = u * u + u * d := Nat.mul_add u u d
    omega
  · have hvu : v ≤ u := by omega
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hvu
    have h1 : (v + d) * (v + d) = v * v + 2 * (v * d) + d * d := by
      rw [Nat.mul_add, Nat.add_mul, Nat.add_mul]
      have hc : d * v = v * d := Nat.mul_comm d v
      omega
    have h2 : (v + d) * v = v * v + v * d := by
      rw [Nat.add_mul, Nat.mul_comm d v]
    omega

/-- One normalized doubling step of binary-tree AM-GM: combines `a^p1 * b^q1` and `a^p2 * b^q2`
on `n` terms into `a^(p1+p2) * b^(q1+q2)` on `2*n` terms with ZERO AST blowup. -/
private theorem amgm_step {n a b p1 q1 p2 q2 : Nat}
    (h1 : a ^ p1 * b ^ q1 * n ^ n ≤ (p1 * a + q1 * b) ^ n)
    (h2 : a ^ p2 * b ^ q2 * n ^ n ≤ (p2 * a + q2 * b) ^ n) :
    a ^ (p1 + p2) * b ^ (q1 + q2) * (2 * n) ^ (2 * n) ≤ ((p1 + p2) * a + (q1 + q2) * b) ^ (2 * n) := by
  have hmul := Nat.mul_le_mul_right (4 ^ n) (Nat.mul_le_mul h1 h2)
  have hlhs :
      (a ^ p1 * b ^ q1 * n ^ n) * (a ^ p2 * b ^ q2 * n ^ n) * 4 ^ n =
      a ^ (p1 + p2) * b ^ (q1 + q2) * (2 * n) ^ (2 * n) := by
    have h2n : (2 * n) ^ (2 * n) = 4 ^ n * (n ^ n * n ^ n) := by
      calc (2 * n) ^ (2 * n)
          = 2 ^ (2 * n) * n ^ (2 * n) := Nat.mul_pow 2 n (2 * n)
        _ = (2 ^ 2) ^ n * (n ^ n * n ^ n) := by
              rw [Nat.pow_mul, show 2 * n = n + n by omega, Nat.pow_add]
        _ = 4 ^ n * (n ^ n * n ^ n) := rfl
    rw [h2n, Nat.pow_add, Nat.pow_add]
    ac_rfl
  have hrhs :
      ((p1 * a + q1 * b) ^ n * (p2 * a + q2 * b) ^ n) * 4 ^ n ≤
      ((p1 + p2) * a + (q1 + q2) * b) ^ (2 * n) := by
    have hsum : (p1 * a + q1 * b) + (p2 * a + q2 * b) = (p1 + p2) * a + (q1 + q2) * b := by
      rw [Nat.add_mul, Nat.add_mul]; omega
    have hbase : 4 * (p1 * a + q1 * b) * (p2 * a + q2 * b) ≤ ((p1 + p2) * a + (q1 + q2) * b) ^ 2 := by
      rw [← hsum]; exact amgm_2 _ _
    have hpow := Nat.pow_le_pow_left hbase n
    have hrew1 : (4 * (p1 * a + q1 * b) * (p2 * a + q2 * b)) ^ n =
                 ((p1 * a + q1 * b) ^ n * (p2 * a + q2 * b) ^ n) * 4 ^ n := by
      rw [Nat.mul_pow, Nat.mul_pow]; ac_rfl
    have hrew2 : (((p1 + p2) * a + (q1 + q2) * b) ^ 2) ^ n =
                 ((p1 + p2) * a + (q1 + q2) * b) ^ (2 * n) := by
      rw [← Nat.pow_mul]
    rw [← hrew1, ← hrew2]
    exact hpow
  rw [← hlhs]
  exact Nat.le_trans hmul hrhs

private theorem amgm_step_eq {n a b p1 q1 p2 q2 p q m : Nat}
    (hp : p1 + p2 = p) (hq : q1 + q2 = q) (hm : 2 * n = m)
    (h1 : a ^ p1 * b ^ q1 * n ^ n ≤ (p1 * a + q1 * b) ^ n)
    (h2 : a ^ p2 * b ^ q2 * n ^ n ≤ (p2 * a + q2 * b) ^ n) :
    a ^ p * b ^ q * m ^ m ≤ (p * a + q * b) ^ m := by
  subst hp; subst hq; subst hm
  exact amgm_step h1 h2

/-- **Weighted 256-Term AM-GM Inequality (`123` copies of `a`, `133` copies of `b`):**
`a^123 * b^133 * 256^256 ≤ (123 * a + 133 * b)^256` for ALL `a, b : Nat`. -/
theorem amgm_256 (a b : Nat) :
    a ^ 123 * b ^ 133 * 256 ^ 256 ≤ (123 * a + 133 * b) ^ 256 := by
  have h10 : a ^ 1 * b ^ 0 * 1 ^ 1 ≤ (1 * a + 0 * b) ^ 1 := by simp
  have h01 : a ^ 0 * b ^ 1 * 1 ^ 1 ≤ (0 * a + 1 * b) ^ 1 := by simp
  have h20 := amgm_step_eq (p := 2) (q := 0) (m := 2) rfl rfl rfl h10 h10
  have h11 := amgm_step_eq (p := 1) (q := 1) (m := 2) rfl rfl rfl h10 h01
  have h02 := amgm_step_eq (p := 0) (q := 2) (m := 2) rfl rfl rfl h01 h01
  have h40 := amgm_step_eq (p := 4) (q := 0) (m := 4) rfl rfl rfl h20 h20
  have h31 := amgm_step_eq (p := 3) (q := 1) (m := 4) rfl rfl rfl h20 h11
  have h04 := amgm_step_eq (p := 0) (q := 4) (m := 4) rfl rfl rfl h02 h02
  have h80 := amgm_step_eq (p := 8) (q := 0) (m := 8) rfl rfl rfl h40 h40
  have h35 := amgm_step_eq (p := 3) (q := 5) (m := 8) rfl rfl rfl h31 h04
  have h08 := amgm_step_eq (p := 0) (q := 8) (m := 8) rfl rfl rfl h04 h04
  have h16_0 := amgm_step_eq (p := 16) (q := 0) (m := 16) rfl rfl rfl h80 h80
  have h11_5 := amgm_step_eq (p := 11) (q := 5) (m := 16) rfl rfl rfl h80 h35
  have h0_16 := amgm_step_eq (p := 0) (q := 16) (m := 16) rfl rfl rfl h08 h08
  have h32_0 := amgm_step_eq (p := 32) (q := 0) (m := 32) rfl rfl rfl h16_0 h16_0
  have h27_5 := amgm_step_eq (p := 27) (q := 5) (m := 32) rfl rfl rfl h16_0 h11_5
  have h0_32 := amgm_step_eq (p := 0) (q := 32) (m := 32) rfl rfl rfl h0_16 h0_16
  have h64_0 := amgm_step_eq (p := 64) (q := 0) (m := 64) rfl rfl rfl h32_0 h32_0
  have h59_5 := amgm_step_eq (p := 59) (q := 5) (m := 64) rfl rfl rfl h32_0 h27_5
  have h0_64 := amgm_step_eq (p := 0) (q := 64) (m := 64) rfl rfl rfl h0_32 h0_32
  have h123_5 := amgm_step_eq (p := 123) (q := 5) (m := 128) rfl rfl rfl h64_0 h59_5
  have h0_128 := amgm_step_eq (p := 0) (q := 128) (m := 128) rfl rfl rfl h0_64 h0_64
  exact amgm_step_eq (p := 123) (q := 133) (m := 256) rfl rfl rfl h123_5 h0_128

private theorem natMin_le_left (a b : Nat) : natMin a b ≤ a := by
  unfold natMin
  by_cases h : a ≤ b
  · simp only [Nat.ble_eq.mpr h, ↓reduceIte]
    exact Nat.le_refl a
  · have hbf : Nat.ble a b = false := Bool.eq_false_iff.mpr (fun ht => h (Nat.ble_eq.mp ht))
    simp only [hbf, Bool.false_eq_true, ↓reduceIte]
    omega

private theorem natMin_eq_min (a b : Nat) : natMin a b = min a b := by
  unfold natMin
  by_cases h : a ≤ b
  · simp only [Nat.ble_eq.mpr h, ↓reduceIte, Nat.min_eq_left h]
  · have hbf : Nat.ble a b = false := Bool.eq_false_iff.mpr (fun ht => h (Nat.ble_eq.mp ht))
    simp only [hbf, Bool.false_eq_true, ↓reduceIte, Nat.min_eq_right (Nat.le_of_not_le h)]

/-- Propositional bridge for the `65` certified anchor bounds (`j ≤ 64`). -/
theorem anc_certified (j : Nat) (hj : j ≤ 64) :
    (ancLo j) ^ 256 * ANCHOR_N ^ 123 ≤ (ANCHOR_N + j) ^ 123 * S2 ^ 256 ∧
    (ANCHOR_N + j) ^ 123 * S2 ^ 256 ≤ (ancHi j) ^ 256 * ANCHOR_N ^ 123 := by
  have haux : ∀ m, checkAnchorsAux m = true → ∀ k, k ≤ m → checkAnchorEntry k = true := by
    intro m
    induction m with
    | zero =>
      intro hm k hk
      have hk0 : k = 0 := by omega
      subst hk0; exact hm
    | succ m' ih =>
      intro hm k hk
      unfold checkAnchorsAux at hm
      cases hc : checkAnchorEntry (m' + 1)
      · rw [hc] at hm; cases hm
      · rw [hc] at hm
        by_cases hkm : k = m' + 1
        · subst hkm; exact hc
        · exact ih hm k (by omega)
  have hent := haux 64 anc_table_certified_bool j hj
  unfold checkAnchorEntry at hent
  simp only [Bool.and_eq_true] at hent
  exact ⟨Nat.le_of_ble_eq_true hent.1, Nat.le_of_ble_eq_true hent.2⟩

/-- Propositional bridge for the `32` certified octave upper bounds (`k ≤ 31`). -/
theorem oct_certified (k : Nat) (hk : k ≤ 31) :
    S2 ^ 256 ≤ (octHi k) ^ 256 * (2 ^ k) ^ 123 := by
  have haux : ∀ m, checkOctavesAux m = true → ∀ i, i ≤ m → checkOctaveEntry i = true := by
    intro m
    induction m with
    | zero =>
      intro hm i hi
      have hi0 : i = 0 := by omega
      subst hi0; exact hm
    | succ m' ih =>
      intro hm i hi
      unfold checkOctavesAux at hm
      cases hc : checkOctaveEntry (m' + 1)
      · rw [hc] at hm; cases hm
      · rw [hc] at hm
        by_cases him : i = m' + 1
        · subst him; exact hc
        · exact ih hm i (by omega)
  have hent := haux 31 oct_table_certified_bool k hk
  unfold checkOctaveEntry at hent
  exact Nat.le_of_ble_eq_true hent

private theorem pupFast_alg {n den cNum pow2k AN s2 sc c256 ah oh lin : Nat}
    (hAN : 0 < AN) (hp2 : 0 < pow2k) (hs2 : 0 < s2) (hc256 : 0 < c256) (hden : 0 < den) (hc : 0 < cNum)
    (ham : (n * pow2k * AN) ^ 123 * (den * cNum) ^ 133 * c256 ^ 256 ≤ lin ^ 256)
    (hanc : cNum ^ 123 * s2 ^ 256 ≤ ah ^ 256 * AN ^ 123)
    (hoct : s2 ^ 256 ≤ oh ^ 256 * pow2k ^ 123) :
    n ^ 123 * sc ^ 256 ≤
      ((ah * oh * lin * sc + s2 * s2 * c256 * den * cNum - 1) / (s2 * s2 * c256 * den * cNum)) ^ 256 * den ^ 123 := by
  let top := ah * oh * lin * sc
  let bot := s2 * s2 * c256 * den * cNum
  have hbot_pos : 0 < bot :=
    Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (Nat.mul_pos hs2 hs2) hc256) hden) hc
  have h1 :
      ((n * pow2k * AN) ^ 123 * (den * cNum) ^ 133 * c256 ^ 256) *
      (cNum ^ 123 * s2 ^ 256) * s2 ^ 256 ≤
      (lin ^ 256) * (ah ^ 256 * AN ^ 123) * (oh ^ 256 * pow2k ^ 123) :=
    Nat.mul_le_mul (Nat.mul_le_mul ham hanc) hoct
  let fac := AN ^ 123 * pow2k ^ 123
  have hfac_pos : 0 < fac := Nat.mul_pos (Nat.pow_pos hAN) (Nat.pow_pos hp2)
  have hlhs_eq :
      ((n * pow2k * AN) ^ 123 * (den * cNum) ^ 133 * c256 ^ 256) *
      (cNum ^ 123 * s2 ^ 256) * s2 ^ 256 * den ^ 123 =
      n ^ 123 * bot ^ 256 * fac := by
    have hbot_pow : bot ^ 256 = s2 ^ 256 * s2 ^ 256 * c256 ^ 256 * den ^ 256 * cNum ^ 256 := by
      simp only [bot, Nat.mul_pow]
    have hr_pow : (n * pow2k * AN) ^ 123 = n ^ 123 * pow2k ^ 123 * AN ^ 123 := by
      simp only [Nat.mul_pow]
    have hdc_pow : (den * cNum) ^ 133 = den ^ 133 * cNum ^ 133 := Nat.mul_pow den cNum 133
    have hd256 : den ^ 133 * den ^ 123 = den ^ 256 := by rw [← Nat.pow_add]
    have hc256e : cNum ^ 133 * cNum ^ 123 = cNum ^ 256 := by rw [← Nat.pow_add]
    rw [hbot_pow, hr_pow, hdc_pow, ← hd256, ← hc256e]
    simp only [fac]
    ac_rfl
  have hrhs_eq :
      (lin ^ 256) * (ah ^ 256 * AN ^ 123) * (oh ^ 256 * pow2k ^ 123) * den ^ 123 =
      (ah * oh * lin) ^ 256 * den ^ 123 * fac := by
    have hp : (ah * oh * lin) ^ 256 = ah ^ 256 * oh ^ 256 * lin ^ 256 := by
      simp only [Nat.mul_pow]
    rw [hp]
    simp only [fac]
    ac_rfl
  have h2 : n ^ 123 * bot ^ 256 * fac ≤ (ah * oh * lin) ^ 256 * den ^ 123 * fac := by
    rw [← hlhs_eq, ← hrhs_eq]
    exact Nat.mul_le_mul_right (den ^ 123) h1
  have h3 : n ^ 123 * bot ^ 256 ≤ (ah * oh * lin) ^ 256 * den ^ 123 :=
    Nat.le_of_mul_le_mul_right h2 hfac_pos
  have h4 : n ^ 123 * sc ^ 256 * bot ^ 256 ≤ top ^ 256 * den ^ 123 := by
    have htop_pow : top ^ 256 = (ah * oh * lin) ^ 256 * sc ^ 256 := by
      simp only [top, Nat.mul_pow]
    rw [htop_pow]
    calc n ^ 123 * sc ^ 256 * bot ^ 256
        = (n ^ 123 * bot ^ 256) * sc ^ 256 := by ac_rfl
      _ ≤ ((ah * oh * lin) ^ 256 * den ^ 123) * sc ^ 256 :=
          Nat.mul_le_mul_right (sc ^ 256) h3
      _ = (ah * oh * lin) ^ 256 * sc ^ 256 * den ^ 123 := by ac_rfl
  have hceil : top ≤ ((top + bot - 1) / bot) * bot := by
    have hdm := Nat.div_add_mod (top + bot - 1) bot
    have hmod := Nat.mod_lt (top + bot - 1) hbot_pos
    have hcomm : bot * ((top + bot - 1) / bot) = ((top + bot - 1) / bot) * bot := Nat.mul_comm _ _
    omega
  have h5 : top ^ 256 * den ^ 123 ≤ ((top + bot - 1) / bot) ^ 256 * den ^ 123 * bot ^ 256 := by
    have hp : top ^ 256 ≤ ((top + bot - 1) / bot) ^ 256 * bot ^ 256 := by
      rw [← Nat.mul_pow]
      exact Nat.pow_le_pow_left hceil 256
    have hmul := Nat.mul_le_mul_right (den ^ 123) hp
    rw [Nat.mul_assoc, Nat.mul_comm (bot ^ 256) (den ^ 123), ← Nat.mul_assoc] at hmul
    exact hmul
  exact Nat.le_of_mul_le_mul_right (Nat.le_trans h4 h5) (Nat.pow_pos hbot_pos)

/-- **Unconditional Soundness of `pupFast`:**
For EVERY `num, den : Nat` with `0 < den`,
`num^123 * SCALE^256 ≤ (pupFast num den)^256 * den^123`. -/
theorem pupFast_sound (num den : Nat) (hden : 0 < den) :
    num ^ 123 * SCALE ^ 256 ≤ (pupFast num den) ^ 256 * den ^ 123 := by
  unfold pupFast
  cases num with
  | zero => simp
  | succ m =>
    simp only [Nat.succ_ne_zero, beq_iff_eq, ↓reduceIte]
    let n := m + 1
    let k := findShift31 n den
    let j := if Nat.ble (n * 2 ^ k) den then 0
             else natMin ANCHOR_N (((n * 2 ^ k - den) * ANCHOR_N * 2 + den) / (2 * den))
    let cNum := ANCHOR_N + j
    have hk : k ≤ 31 := natMin_le_left 31 _
    have hj : j ≤ 64 := by
      dsimp only [j]
      cases Nat.ble (n * 2 ^ k) den
      · exact natMin_le_left 64 _
      · exact Nat.zero_le 64
    have hc_pos : 0 < cNum := by dsimp only [cNum, ANCHOR_N]; omega
    have hanc := (anc_certified j hj).2
    have hoct := oct_certified k hk
    have ham := amgm_256 (n * 2 ^ k * ANCHOR_N) (den * cNum)
    have hlin_eq : 123 * (n * 2 ^ k * ANCHOR_N) + 133 * (den * cNum) =
                   123 * (n * 2 ^ k) * ANCHOR_N + 133 * den * cNum := by
      simp only [Nat.mul_assoc]
    rw [hlin_eq] at ham
    exact pupFast_alg (by decide : 0 < ANCHOR_N) (Nat.pow_pos (by decide : 0 < 2))
      (by decide : 0 < S2) (by decide : 0 < 256) hden hc_pos ham hanc hoct

private theorem ploFast_alg {n den cNum AN s2 sc c256 al lin : Nat}
    (hAN : 0 < AN) (hs2 : 0 < s2) (hc : 0 < cNum) (hlin : 0 < lin)
    (hanc : al ^ 256 * AN ^ 123 ≤ cNum ^ 123 * s2 ^ 256)
    (ham : (den * cNum) ^ 123 * (n * AN) ^ 133 * c256 ^ 256 ≤ lin ^ 256) :
    ((al * c256 * n * AN * sc) / (s2 * lin)) ^ 256 * den ^ 123 ≤ n ^ 123 * sc ^ 256 := by
  let top := al * c256 * n * AN * sc
  let bot := s2 * lin
  have hbot_pos : 0 < bot := Nat.mul_pos hs2 hlin
  have h1 :
      (al ^ 256 * AN ^ 123) *
      ((den * cNum) ^ 123 * (n * AN) ^ 133 * c256 ^ 256) ≤
      (cNum ^ 123 * s2 ^ 256) * lin ^ 256 :=
    Nat.mul_le_mul hanc ham
  let fac := AN ^ 123 * cNum ^ 123
  have hfac_pos : 0 < fac := Nat.mul_pos (Nat.pow_pos hAN) (Nat.pow_pos hc)
  have hlhs_eq :
      (al ^ 256 * AN ^ 123) *
      ((den * cNum) ^ 123 * (n * AN) ^ 133 * c256 ^ 256) * (n ^ 123 * AN ^ 123 * sc ^ 256) =
      top ^ 256 * den ^ 123 * fac := by
    have htop_pow : top ^ 256 = al ^ 256 * c256 ^ 256 * n ^ 256 * AN ^ 256 * sc ^ 256 := by
      simp only [top, Nat.mul_pow]
    have hdc : (den * cNum) ^ 123 = den ^ 123 * cNum ^ 123 := Nat.mul_pow den cNum 123
    have hna : (n * AN) ^ 133 = n ^ 133 * AN ^ 133 := Nat.mul_pow n AN 133
    have hn256 : n ^ 133 * n ^ 123 = n ^ 256 := by rw [← Nat.pow_add]
    have ha256 : AN ^ 133 * AN ^ 123 = AN ^ 256 := by rw [← Nat.pow_add]
    rw [htop_pow, hdc, hna, ← hn256, ← ha256]
    simp only [fac]
    ac_rfl
  have hrhs_eq :
      (cNum ^ 123 * s2 ^ 256) * lin ^ 256 * (n ^ 123 * AN ^ 123 * sc ^ 256) =
      n ^ 123 * sc ^ 256 * bot ^ 256 * fac := by
    have hbot_pow : bot ^ 256 = s2 ^ 256 * lin ^ 256 := Nat.mul_pow s2 lin 256
    rw [hbot_pow]
    simp only [fac]
    ac_rfl
  have h2 : top ^ 256 * den ^ 123 * fac ≤ n ^ 123 * sc ^ 256 * bot ^ 256 * fac := by
    rw [← hlhs_eq, ← hrhs_eq]
    exact Nat.mul_le_mul_right _ h1
  have h3 : top ^ 256 * den ^ 123 ≤ n ^ 123 * sc ^ 256 * bot ^ 256 :=
    Nat.le_of_mul_le_mul_right h2 hfac_pos
  have hfl : (top / bot) * bot ≤ top := by
    rw [Nat.mul_comm]
    exact Nat.mul_div_le top bot
  have h4 : (top / bot) ^ 256 * den ^ 123 * bot ^ 256 ≤ top ^ 256 * den ^ 123 := by
    have hp := Nat.pow_le_pow_left hfl 256
    rw [Nat.mul_pow] at hp
    calc (top / bot) ^ 256 * den ^ 123 * bot ^ 256
        = ((top / bot) ^ 256 * bot ^ 256) * den ^ 123 := by ac_rfl
      _ ≤ top ^ 256 * den ^ 123 := Nat.mul_le_mul_right _ hp
  exact Nat.le_of_mul_le_mul_right (Nat.le_trans h4 h3) (Nat.pow_pos hbot_pos)

/-- **Unconditional Soundness of `ploFast`:**
For EVERY `num, den : Nat` with `0 < den`,
`(ploFast num den)^256 * den^123 ≤ num^123 * SCALE^256`. -/
theorem ploFast_sound (num den : Nat) (_hden : 0 < den) :
    (ploFast num den) ^ 256 * den ^ 123 ≤ num ^ 123 * SCALE ^ 256 := by
  unfold ploFast
  cases num with
  | zero => simp
  | succ m =>
    simp only [Nat.succ_ne_zero, beq_iff_eq, ↓reduceIte]
    let n := m + 1
    let j := if Nat.ble n den then 0
             else natMin ANCHOR_N (((n - den) * ANCHOR_N * 2 + den) / (2 * den))
    let cNum := ANCHOR_N + j
    have hj : j ≤ 64 := by
      dsimp only [j]
      cases Nat.ble n den
      · exact natMin_le_left 64 _
      · exact Nat.zero_le 64
    have hc_pos : 0 < cNum := by dsimp only [cNum, ANCHOR_N]; omega
    have hanc := (anc_certified j hj).1
    have ham := amgm_256 (den * cNum) (n * ANCHOR_N)
    have hlin_eq : 123 * (den * cNum) + 133 * (n * ANCHOR_N) =
                   123 * den * cNum + 133 * n * ANCHOR_N := by
      simp only [Nat.mul_assoc]
    rw [hlin_eq] at ham
    have hlin_pos : 0 < 123 * den * cNum + 133 * n * ANCHOR_N := by
      have h1 : 0 < 133 * n := Nat.mul_pos (by decide) (Nat.zero_lt_succ m)
      have h2 : 0 < 133 * n * ANCHOR_N := Nat.mul_pos h1 (by decide)
      omega
    exact ploFast_alg (by decide : 0 < ANCHOR_N) (by decide : 0 < S2) hc_pos hlin_pos hanc ham

/-! ## 3. Exact Base `F19` Certificate (`0 ≤ W2 ≤ W1 ≤ 19`) & Dyadic Sub-Interval Algebra -/

/-- Key exact values of the base `F19` packing table. -/
theorem f19_key_values :
    f19Val 19 19 = 8 ∧ f19Val 3 1 = 2 ∧ f19Val 2 1 = 1 := by
  decide

private theorem checkF19Row_sound (w1 : Nat) :
    ∀ k, checkF19Row w1 k = true → ∀ w2, w2 ≤ k →
      (f19Val w1 w2) ^ 256 * 5 ^ 256 ≤ 3 ^ 256 * ((w1 + 2) * (w2 + 2)) ^ 123 ∧
      (1 ≤ w2 → f19Val w1 (w2 - 1) ≤ f19Val w1 w2) ∧
      (1 ≤ w1 → f19Val (w1 - 1) (min w2 (w1 - 1)) ≤ f19Val w1 w2)
  | 0, h, w2, hw2 => by
    have hw20 : w2 = 0 := by omega
    subst hw20
    unfold checkF19Row at h
    simp only [Bool.and_eq_true] at h
    refine ⟨Nat.le_of_ble_eq_true h.1, fun h1 => by omega, fun hw1 => ?_⟩
    have hne : (w1 == 0) = false := beq_false_of_ne (by omega)
    have h2 := h.2
    simp only [hne, Bool.false_eq_true, ↓reduceIte] at h2
    have hm0 : min 0 (w1 - 1) = 0 := Nat.zero_min (w1 - 1)
    rw [hm0]
    exact Nat.le_of_ble_eq_true h2
  | k + 1, h, w2, hw2 => by
    unfold checkF19Row at h
    dsimp only at h
    cases hok : (Nat.ble (f19Val w1 (k + 1) ^ 256 * 5 ^ 256) (3 ^ 256 * ((w1 + 2) * (k + 3)) ^ 123) &&
                 Nat.ble (f19Val w1 k) (f19Val w1 (k + 1)) &&
                 if (w1 == 0) = true then true
                 else Nat.ble (f19Val (w1 - 1) (natMin (k + 1) (w1 - 1))) (f19Val w1 (k + 1)))
    · rw [hok] at h; cases h
    · rw [hok] at h
      simp only [Bool.and_eq_true] at hok
      by_cases heq : w2 = k + 1
      · subst heq
        refine ⟨Nat.le_of_ble_eq_true hok.1.1, fun _ => ?_, fun hw1 => ?_⟩
        · simpa using Nat.le_of_ble_eq_true hok.1.2
        · have hne : (w1 == 0) = false := beq_false_of_ne (by omega)
          have h3 := hok.2
          simp only [hne, Bool.false_eq_true, ↓reduceIte] at h3
          rw [← natMin_eq_min]
          exact Nat.le_of_ble_eq_true h3
      · exact checkF19Row_sound w1 k h w2 (by omega)

private theorem checkF19All_sound :
    ∀ m, checkF19All m = true → ∀ w1 w2, w1 ≤ m → w2 ≤ w1 →
      (f19Val w1 w2) ^ 256 * 5 ^ 256 ≤ 3 ^ 256 * ((w1 + 2) * (w2 + 2)) ^ 123 ∧
      (1 ≤ w2 → f19Val w1 (w2 - 1) ≤ f19Val w1 w2) ∧
      (1 ≤ w1 → f19Val (w1 - 1) (min w2 (w1 - 1)) ≤ f19Val w1 w2)
  | 0, h, w1, w2, h1, h2 => by
    have hw1 : w1 = 0 := by omega
    subst hw1
    exact checkF19Row_sound 0 0 h w2 h2
  | m + 1, h, w1, w2, h1, h2 => by
    unfold checkF19All at h
    cases hrow : checkF19Row (m + 1) (m + 1)
    · rw [hrow] at h; cases h
    · rw [hrow] at h
      by_cases heq : w1 = m + 1
      · subst heq
        exact checkF19Row_sound (m + 1) (m + 1) hrow w2 h2
      · exact checkF19All_sound m h w1 w2 (by omega) h2

/-- **Base `F19` Table Numeric Bound (ALL `210` Lower-Triangular Stored Entries `0 ≤ w2 ≤ w1 ≤ 19`):**
`(F19[w1][w2])^256 * 5^256 ≤ 3^256 * ((w1 + 2) * (w2 + 2))^123` for the symmetric `20 × 20`
extension of the `210` stored entries (whose exact maximum-clique values on the same-parity,
no-diagonal `|u1 - u2| ≠ |v1 - v2|` domain are independently verified in `cert/verify_clawfree_eg.py`). -/
theorem f19_packing_bound (w1 w2 : Nat) (h1 : w1 ≤ 19) (h2 : w2 ≤ w1) :
    (f19Val w1 w2) ^ 256 * 5 ^ 256 ≤ 3 ^ 256 * ((w1 + 2) * (w2 + 2)) ^ 123 :=
  (checkF19All_sound 19 f19_all_certified_bool w1 w2 h1 h2).1

/-- Monotonicity of `F19` in the `x`-coordinate (`1 ≤ w1 ≤ 19`, `w2 ≤ w1`). -/
theorem f19_monotone_x (w1 w2 : Nat) (hlo : 1 ≤ w1) (hhi : w1 ≤ 19) (h2 : w2 ≤ w1) :
    f19Val (w1 - 1) (min w2 (w1 - 1)) ≤ f19Val w1 w2 :=
  (checkF19All_sound 19 f19_all_certified_bool w1 w2 hhi h2).2.2 hlo

/-- Monotonicity of `F19` in the `y`-coordinate (`1 ≤ w2 ≤ w1 ≤ 19`). -/
theorem f19_monotone_y (w1 w2 : Nat) (h1 : w1 ≤ 19) (hlo : 1 ≤ w2) (h2 : w2 ≤ w1) :
    f19Val w1 (w2 - 1) ≤ f19Val w1 w2 :=
  (checkF19All_sound 19 f19_all_certified_bool w1 w2 h1 h2).2.1 hlo

/-- **Dyadic Sub-Interval Algebraic Lemmas (ALL even `m ≥ 32` with `3 ∤ m`):**
Every sub-interval inequality used in the Case A / Case B decomposition for dyadic blocks
`m = 2^k ≥ 32` holds universally! -/
theorem dyadic_subinterval_algebra (m : Nat) (_hm : m ≥ 32) (heven : m % 2 = 0) (_hm3 : m % 3 ≠ 0) :
    let low : Int := (m : Int) - 1
    let upper : Int := (((2 * m) / 3 : Nat) : Int) - 2
    let halfLow : Int := ((m / 2 : Nat) : Int) - 1
    let halfUpper : Int := ((m / 3 : Nat) : Int) - 2
    (∀ span : Nat, span < m / 3 → 3 * (2 * upper - low - (span : Int) + 2) ≤ (m : Int) - 3 * (span : Int)) ∧
    (∀ span : Nat, span < m / 3 → 3 * (upper - (span : Int) - 1 + 2) ≤ 2 * (m : Int) - 3 * (span : Int)) ∧
    6 * (upper - halfLow + 2) ≤ (m : Int) + 6 ∧
    6 * (halfUpper - halfLow + 2) ≤ -(m : Int) + 6 ∧
    upper - halfLow < halfLow - halfUpper ∧
    3 * (max (((m / 3 : Nat) : Int) - 1) halfUpper + 2) ≤ (m : Int) + 3 ∧
    6 * (2 * halfUpper - halfLow + 2) ≤ (m : Int) - 6 := by
  dsimp only
  refine ⟨fun span hspan => by omega, fun span hspan => by omega,
          by omega, by omega, by omega, by omega, by omega⟩

/-- Corollary: `dyadic_subinterval_algebra` applies to EVERY dyadic block `m = 2^k` (`k ≥ 5`). -/
theorem dyadic_subinterval_algebra_pow2 (k : Nat) (hk : k ≥ 5) :
    let m : Nat := 2 ^ k
    let low : Int := (m : Int) - 1
    let upper : Int := (((2 * m) / 3 : Nat) : Int) - 2
    let halfLow : Int := ((m / 2 : Nat) : Int) - 1
    let halfUpper : Int := ((m / 3 : Nat) : Int) - 2
    (∀ span : Nat, span < m / 3 → 3 * (2 * upper - low - (span : Int) + 2) ≤ (m : Int) - 3 * (span : Int)) ∧
    (∀ span : Nat, span < m / 3 → 3 * (upper - (span : Int) - 1 + 2) ≤ 2 * (m : Int) - 3 * (span : Int)) ∧
    6 * (upper - halfLow + 2) ≤ (m : Int) + 6 ∧
    6 * (halfUpper - halfLow + 2) ≤ -(m : Int) + 6 ∧
    upper - halfLow < halfLow - halfUpper ∧
    3 * (max (((m / 3 : Nat) : Int) - 1) halfUpper + 2) ≤ (m : Int) + 3 ∧
    6 * (2 * halfUpper - halfLow + 2) ≤ (m : Int) - 6 := by
  have hm32 : 2 ^ k ≥ 32 :=
    Nat.le_trans (by decide : 32 ≤ 2 ^ 5) (Nat.pow_le_pow_right (by omega : 0 < 2) hk)
  have heven : 2 ^ k % 2 = 0 := by
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    rw [Nat.pow_succ]; omega
  exact dyadic_subinterval_algebra (2 ^ k) hm32 heven (pow2_mod_three_ne_zero k)

/-! ## 4. Exact 2D Packing Predicate, Forbidden Gap Collapse, & DP Monotone Invariant -/

/-- Absolute difference `|a - b|` on `Nat`. -/
@[inline] def absDiff (a b : Nat) : Nat := if a ≤ b then b - a else a - b

/-- Exact 2D dyadic `L_∞`-packing domain in `[0, W1] × [0, W2]`:
same parity (`(u + v) % 2` constant), distinct absolute differences `|u1 - u2| ≠ |v1 - v2|`
(no diagonal collisions, i.e., pairwise distinct `u + v` and `u - v`), and
`2 + max(|u1 - u2|, |v1 - v2|) ∈ F_EG`. -/
def IsValid2DPacking (W1 W2 : Nat) (S : List (Nat × Nat)) : Prop :=
  S.Nodup ∧
  (∃ p : Nat, ∀ pt ∈ S, pt.1 ≤ W1 ∧ pt.2 ≤ W2 ∧ (pt.1 + pt.2) % 2 = p) ∧
  (∀ p ∈ S, ∀ q ∈ S, p ≠ q →
    absDiff p.1 q.1 ≠ absDiff p.2 q.2 ∧
    InFEG (2 + max (absDiff p.1 q.1) (absDiff p.2 q.2)))

/-- **Exact Forbidden Gap Theorem (`(U_m, L_m) ∩ (F_EG - 2) = ∅`):**
For every dyadic block `m = 2^k` (`k ≥ 5`), no integer `d` strictly between
`U_m = (2*m)/3 - 2` and `L_m = m - 1` satisfies `2 + d ∈ F_EG`. -/
theorem gap_outside_feg (k d : Nat) (hk : k ≥ 5)
    (hlo : (2 * 2 ^ k) / 3 - 2 < d) (hhi : d < 2 ^ k - 1) :
    ¬InFEG (2 + d) := by
  rintro ⟨a, ha, hlt, hle⟩
  have hpow5 : 2 ^ k ≥ 32 := Nat.le_trans (by decide : 32 ≤ 2 ^ 5) (Nat.pow_le_pow_right (by omega) hk)
  have hm3 := pow2_mod_three_ne_zero k
  by_cases hak : a ≥ k
  · have hge : 2 ^ k ≤ 2 ^ a := Nat.pow_le_pow_right (by omega) hak
    omega
  · have ha_le : a ≤ k - 1 := by omega
    have hpow_a : 2 ^ a ≤ 2 ^ (k - 1) := Nat.pow_le_pow_right (by omega) ha_le
    have hhalf : 2 * 2 ^ (k - 1) = 2 ^ k := by
      have hk_eq : 2 ^ k = 2 ^ ((k - 1) + 1) := congrArg (2 ^ ·) (by omega)
      rw [hk_eq, Nat.pow_succ]
      omega
    omega

/-- **Square Gap Collapse (`(U_m, L_m)^2 → [0, U_m]^2`):**
Any valid 2D packing `S` inside `[0, W1] × [0, W2]` with `W1 < L_m` and `W2 < L_m` has
both `x`-diameter and `y`-diameter at most `U_m = (2*m)/3 - 2`. -/
theorem square_gap_collapse (k W1 W2 : Nat) (hk : k ≥ 5)
    (h1 : W1 < 2 ^ k - 1) (h2 : W2 < 2 ^ k - 1)
    (S : List (Nat × Nat)) (hS : IsValid2DPacking W1 W2 S) :
    ∀ p ∈ S, ∀ q ∈ S,
      absDiff p.1 q.1 ≤ (2 * 2 ^ k) / 3 - 2 ∧
      absDiff p.2 q.2 ≤ (2 * 2 ^ k) / 3 - 2 := by
  rcases hS with ⟨_, ⟨par, hbox⟩, hpair⟩
  intro p hp q hq
  by_cases hpq : p = q
  · subst hpq; simp [absDiff]
  · have hp_b := hbox p hp
    have hq_b := hbox q hq
    have hdx : absDiff p.1 q.1 < 2 ^ k - 1 := by unfold absDiff; split <;> omega
    have hdy : absDiff p.2 q.2 < 2 ^ k - 1 := by unfold absDiff; split <;> omega
    have hmax_lt : max (absDiff p.1 q.1) (absDiff p.2 q.2) < 2 ^ k - 1 := by omega
    have hfeg := (hpair p hp q hq hpq).2
    have hnot_gt : ¬((2 * 2 ^ k) / 3 - 2 < max (absDiff p.1 q.1) (absDiff p.2 q.2)) :=
      fun hgt => gap_outside_feg k _ hk hgt hmax_lt hfeg
    omega

/-- **DP Block Monotonicity Soundness Invariant:**
If a monotone DP upper bound `U w1 w2 ≤ U_hi` on `[W1_lo, W1_hi] × [W2_lo, W2_hi]` satisfies
the packing bound at the lower-left corner `(W1_lo, W2_lo)`, then it satisfies the packing
bound at EVERY `(w1, w2)` in that block! -/
theorem dp_block_soundness_invariant (U : Nat → Nat → Nat)
    (W1_lo W1_hi W2_lo W2_hi U_hi : Nat)
    (hmono : ∀ w1 w2, W1_lo ≤ w1 → w1 ≤ W1_hi → W2_lo ≤ w2 → w2 ≤ W2_hi → U w1 w2 ≤ U_hi)
    (hcorner : U_hi ^ 256 * 5 ^ 256 ≤ 3 ^ 256 * ((W1_lo + 2) * (W2_lo + 2)) ^ 123) :
    ∀ w1 w2, W1_lo ≤ w1 → w1 ≤ W1_hi → W2_lo ≤ w2 → w2 ≤ W2_hi →
      (U w1 w2) ^ 256 * 5 ^ 256 ≤ 3 ^ 256 * ((w1 + 2) * (w2 + 2)) ^ 123 := by
  intro w1 w2 h1l h1h h2l h2h
  have hu : (U w1 w2) ^ 256 * 5 ^ 256 ≤ U_hi ^ 256 * 5 ^ 256 :=
    Nat.mul_le_mul_right (5 ^ 256) (Nat.pow_le_pow_left (hmono w1 w2 h1l h1h h2l h2h) 256)
  have hr : 3 ^ 256 * ((W1_lo + 2) * (W2_lo + 2)) ^ 123 ≤ 3 ^ 256 * ((w1 + 2) * (w2 + 2)) ^ 123 :=
    Nat.mul_le_mul_left (3 ^ 256)
      (Nat.pow_le_pow_left (Nat.mul_le_mul (by omega) (by omega)) 123)
  exact Nat.le_trans hu (Nat.le_trans hcorner hr)

/-! ## 5. Universal Infinite-Tail Case A (`m ≥ 4096`, ALL `64` Intervals) -/

/-- Soundness of `pupE` for shifted rational upper bounds. -/
theorem pupE_sound (n d kEps : Nat) (hd : 0 < d) :
    (n * 4096 + kEps * d) ^ 123 * SCALE ^ 256 ≤ (pupE n d kEps) ^ 256 * (d * 4096) ^ 123 := by
  unfold pupE
  cases kEps with
  | zero =>
    simp only [beq_self_eq_true, ↓reduceIte, Nat.zero_mul, Nat.add_zero]
    have h := pupFast_sound n d hd
    have h4096 : (n * 4096) ^ 123 = n ^ 123 * 4096 ^ 123 := Nat.mul_pow n 4096 123
    have hd4096 : (d * 4096) ^ 123 = d ^ 123 * 4096 ^ 123 := Nat.mul_pow d 4096 123
    rw [h4096, hd4096]
    calc n ^ 123 * 4096 ^ 123 * SCALE ^ 256
        = (n ^ 123 * SCALE ^ 256) * 4096 ^ 123 := by ac_rfl
      _ ≤ ((pupFast n d) ^ 256 * d ^ 123) * 4096 ^ 123 := Nat.mul_le_mul_right _ h
      _ = (pupFast n d) ^ 256 * (d ^ 123 * 4096 ^ 123) := by ac_rfl
  | succ k =>
    simp only [Nat.succ_ne_zero, beq_iff_eq, ↓reduceIte]
    exact pupFast_sound (n * 4096 + (k + 1) * d) (d * 4096) (Nat.mul_pos hd (by decide))

/-- Case A certified ratio on interval `i ∈ 0..63` (`G = 64, D = 192, c0 = 2, m0 = 4096`). -/
@[inline] def caseARatioFast (i : Nat) : Nat :=
  let num := 2 * pupE (i + 1) 384 2 + pupE (64 - i) 192 0
  let den := ploFast (192 + i) 192
  (num * SCALE + den - 1) / den

private def checkCaseAAux : Nat → Bool
  | 0 => Nat.ble (caseARatioFast 0) 96558 && Nat.ble 1 (ploFast 192 192)
  | i + 1 =>
    if Nat.ble (caseARatioFast (i + 1)) 96558 && Nat.ble 1 (ploFast (192 + i + 1) 192) then
      checkCaseAAux i
    else false

private theorem caseA_check_bool : checkCaseAAux 63 = true := by decide

/-- **Kernel-Verified Case A `64`-Interval Bound (`max ≤ 96558 ≤ 99920 < 100000`):** -/
theorem caseA_all_64_le_96558 (i : Nat) (hi : i < 64) :
    caseARatioFast i ≤ 96558 ∧ 1 ≤ ploFast (192 + i) 192 := by
  have haux : ∀ m, checkCaseAAux m = true → ∀ j, j ≤ m →
      caseARatioFast j ≤ 96558 ∧ 1 ≤ ploFast (192 + j) 192 := by
    intro m
    induction m with
    | zero =>
      intro hm j hj
      have hj0 : j = 0 := by omega
      subst hj0
      unfold checkCaseAAux at hm
      simp only [Bool.and_eq_true] at hm
      exact ⟨Nat.le_of_ble_eq_true hm.1, Nat.le_of_ble_eq_true hm.2⟩
    | succ m' ih =>
      intro hm j hj
      unfold checkCaseAAux at hm
      cases hok : (Nat.ble (caseARatioFast (m' + 1)) 96558 && Nat.ble 1 (ploFast (192 + m' + 1) 192))
      · rw [hok] at hm; cases hm
      · rw [hok] at hm
        simp only [Bool.and_eq_true] at hok
        by_cases heq : j = m' + 1
        · subst heq
          exact ⟨Nat.le_of_ble_eq_true hok.1, Nat.le_of_ble_eq_true hok.2⟩
        · exact ih hm j (by omega)
  exact haux 63 caseA_check_bool i (by omega)

/-- Rational monotonicity helper for `123/256`-power upper bounds. -/
private theorem pow123_ub_mono {n1 d1 n2 d2 u : Nat}
    (hd2 : 0 < d2)
    (hle : n1 * d2 ≤ n2 * d1)
    (hub : n2 ^ 123 * SCALE ^ 256 ≤ u ^ 256 * d2 ^ 123) :
    n1 ^ 123 * SCALE ^ 256 ≤ u ^ 256 * d1 ^ 123 := by
  have h1 : (n1 * d2) ^ 123 ≤ (n2 * d1) ^ 123 := Nat.pow_le_pow_left hle 123
  rw [Nat.mul_pow, Nat.mul_pow] at h1
  have h2 : n1 ^ 123 * SCALE ^ 256 * d2 ^ 123 ≤ u ^ 256 * d1 ^ 123 * d2 ^ 123 := by
    calc n1 ^ 123 * SCALE ^ 256 * d2 ^ 123
        = (n1 ^ 123 * d2 ^ 123) * SCALE ^ 256 := by ac_rfl
      _ ≤ (n2 ^ 123 * d1 ^ 123) * SCALE ^ 256 := Nat.mul_le_mul_right _ h1
      _ = (n2 ^ 123 * SCALE ^ 256) * d1 ^ 123 := by ac_rfl
      _ ≤ (u ^ 256 * d2 ^ 123) * d1 ^ 123 := Nat.mul_le_mul_right _ hub
      _ = u ^ 256 * d1 ^ 123 * d2 ^ 123 := by ac_rfl
  exact Nat.le_of_mul_le_mul_right h2 (Nat.pow_pos hd2)

/-- Rational monotonicity helper for `123/256`-power lower bounds. -/
private theorem pow123_lb_mono {n1 d1 n2 d2 lo : Nat}
    (hd1 : 0 < d1)
    (hle : n1 * d2 ≤ n2 * d1)
    (hlb : lo ^ 256 * d1 ^ 123 ≤ n1 ^ 123 * SCALE ^ 256) :
    lo ^ 256 * d2 ^ 123 ≤ n2 ^ 123 * SCALE ^ 256 := by
  have h1 : (n1 * d2) ^ 123 ≤ (n2 * d1) ^ 123 := Nat.pow_le_pow_left hle 123
  rw [Nat.mul_pow, Nat.mul_pow] at h1
  have h2 : lo ^ 256 * d2 ^ 123 * d1 ^ 123 ≤ n2 ^ 123 * SCALE ^ 256 * d1 ^ 123 := by
    calc lo ^ 256 * d2 ^ 123 * d1 ^ 123
        = (lo ^ 256 * d1 ^ 123) * d2 ^ 123 := by ac_rfl
      _ ≤ (n1 ^ 123 * SCALE ^ 256) * d2 ^ 123 := Nat.mul_le_mul_right _ hlb
      _ = (n1 ^ 123 * d2 ^ 123) * SCALE ^ 256 := by ac_rfl
      _ ≤ (n2 ^ 123 * d1 ^ 123) * SCALE ^ 256 := Nat.mul_le_mul_right _ h1
      _ = n2 ^ 123 * SCALE ^ 256 * d1 ^ 123 := by ac_rfl
  exact Nat.le_of_mul_le_mul_right h2 (Nat.pow_pos hd1)

/-- **Universal Infinite-Tail Case A Theorem (ALL `m ≥ 4096`, ALL `0 ≤ s` with `3 * s < m`):**
For every `m ≥ 4096` and every `s` with `3 * s < m`, there exist exact rational-scale
bounds `p1, p2, den` certifying:
- `((s + 4) / (2*m))^(123/256) ≤ p1 / SCALE` (i.e. `(s/2 + 2) / m`),
- `((m - 3*s) / (3*m))^(123/256) ≤ p2 / SCALE` (i.e. `1/3 - s/m`),
- `den / SCALE ≤ ((m + s) / m)^(123/256)`,
- `(2 * p1 + p2) / den ≤ 96558 / 100000 < 1`! -/
theorem caseA_universal_m_ge_4096 (m s : Nat) (hm : m ≥ 4096) (hs : 3 * s < m) :
    ∃ p1 p2 den : Nat,
      (s + 4) ^ 123 * SCALE ^ 256 ≤ p1 ^ 256 * (2 * m) ^ 123 ∧
      (m - 3 * s) ^ 123 * SCALE ^ 256 ≤ p2 ^ 256 * (3 * m) ^ 123 ∧
      den ^ 256 * m ^ 123 ≤ (m + s) ^ 123 * SCALE ^ 256 ∧
      (2 * p1 + p2) * SCALE ≤ 96558 * den ∧
      96558 < SCALE := by
  let i := (192 * s) / m
  have hi_lt : i < 64 := Nat.div_lt_of_lt_mul (by omega : 192 * s < m * 64)
  have hi_lo : i * m ≤ 192 * s := by
    rw [Nat.mul_comm]; exact Nat.mul_div_le (192 * s) m
  have hi_hi : 192 * s < (i + 1) * m := by
    have hdm : m * i + (192 * s) % m = 192 * s := Nat.div_add_mod (192 * s) m
    have hmod : (192 * s) % m < m := Nat.mod_lt (192 * s) (by omega : 0 < m)
    rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm i m]
    omega
  let p1 := pupE (i + 1) 384 2
  let p2 := pupE (64 - i) 192 0
  let den := ploFast (192 + i) 192
  have hca := caseA_all_64_le_96558 i hi_lt
  refine ⟨p1, p2, den, ?_, ?_, ?_, ?_, by decide⟩
  · have hrat : (s + 4) * (384 * 4096) ≤ ((i + 1) * 4096 + 2 * 384) * (2 * m) := by
      have h1 : s * (384 * 4096) ≤ (i + 1) * 4096 * (2 * m) := by
        have hstep : 192 * s ≤ (i + 1) * m := Nat.le_of_lt hi_hi
        have hmul := Nat.mul_le_mul_right (2 * 4096) hstep
        calc s * (384 * 4096) = (192 * s) * (2 * 4096) := by omega
          _ ≤ ((i + 1) * m) * (2 * 4096) := hmul
          _ = (i + 1) * 4096 * (2 * m) := by ac_rfl
      have h2 : 4 * (384 * 4096) ≤ 2 * 384 * (2 * m) := by
        have hmul := Nat.mul_le_mul_left (4 * 384) hm
        calc 4 * (384 * 4096) = (4 * 384) * 4096 := rfl
          _ ≤ (4 * 384) * m := hmul
          _ = 2 * 384 * (2 * m) := by omega
      rw [Nat.add_mul, Nat.add_mul]
      exact Nat.add_le_add h1 h2
    exact pow123_ub_mono (by decide) hrat (pupE_sound (i + 1) 384 2 (by decide))
  · have hrat : (m - 3 * s) * (192 * 4096) ≤ ((64 - i) * 4096 + 0 * 192) * (3 * m) := by
      have h1 : (m - 3 * s) * 192 ≤ (64 - i) * (3 * m) := by
        have hsub : (m - 3 * s) * 192 = 192 * m - 3 * (192 * s) := by
          rw [Nat.sub_mul]; omega
        have hrhs : (64 - i) * (3 * m) = 192 * m - 3 * (i * m) := by
          rw [Nat.sub_mul]
          have ha : 64 * (3 * m) = 192 * m := by omega
          have hb : i * (3 * m) = 3 * (i * m) := by ac_rfl
          rw [ha, hb]
        rw [hsub, hrhs]
        omega
      have hmul := Nat.mul_le_mul_right 4096 h1
      calc (m - 3 * s) * (192 * 4096)
          = (m - 3 * s) * 192 * 4096 := by ac_rfl
        _ ≤ (64 - i) * (3 * m) * 4096 := hmul
        _ = ((64 - i) * 4096 + 0 * 192) * (3 * m) := by simp; ac_rfl
    exact pow123_ub_mono (by decide) hrat (pupE_sound (64 - i) 192 0 (by decide))
  · have hrat : (192 + i) * m ≤ (m + s) * 192 := by
      rw [Nat.add_mul, Nat.add_mul]
      omega
    exact pow123_lb_mono (by decide) hrat (ploFast_sound (192 + i) 192 (by decide))
  · have hratio : ((2 * p1 + p2) * SCALE + den - 1) / den ≤ 96558 := hca.1
    have hden_pos : 0 < den := hca.2
    have hceil : (2 * p1 + p2) * SCALE ≤ (((2 * p1 + p2) * SCALE + den - 1) / den) * den := by
      have hdm := Nat.div_add_mod ((2 * p1 + p2) * SCALE + den - 1) den
      have hmod := Nat.mod_lt ((2 * p1 + p2) * SCALE + den - 1) hden_pos
      have hcomm : den * (((2 * p1 + p2) * SCALE + den - 1) / den) =
                   (((2 * p1 + p2) * SCALE + den - 1) / den) * den := Nat.mul_comm _ _
      omega
    exact Nat.le_trans hceil (Nat.mul_le_mul_right den hratio)

/-! ## 6. Exact `Z_2 × Z_2` Symmetry-Orbit Partition (`16 = 1 + 4 + 2 + 2 + 4 + 1 + 2`) & Case B Simple Orbits -/

/-- The `7` symmetry orbits of the `16` corner-occupancy patterns under `Z_2 × Z_2`
(horizontal & vertical reflections preserving `W2 ≤ W1`). -/
inductive CornerOrbit where
  | o0000 | o1000 | o1100 | o1010 | o1110 | o1111 | o1001
  deriving DecidableEq, Repr

/-- Corner occupancy mask `(c00, c20, c02, c22)` for the 4 outer corners of the 3×3 grid. -/
abbrev CornerMask := Bool × Bool × Bool × Bool

/-- Horizontal reflection `(c00, c20, c02, c22) ↦ (c20, c00, c22, c02)`. -/
def flipH (c : CornerMask) : CornerMask := (c.2.1, c.1, c.2.2.2, c.2.2.1)

/-- Vertical reflection `(c00, c20, c02, c22) ↦ (c02, c22, c00, c20)`. -/
def flipV (c : CornerMask) : CornerMask := (c.2.2.1, c.2.2.2, c.1, c.2.1)

/-- Canonical `Z_2 × Z_2` orbit representative of a 4-corner occupancy pattern. -/
def orbitOf : CornerMask → CornerOrbit
  | (false, false, false, false) => .o0000
  | (true, false, false, false) | (false, true, false, false)
  | (false, false, true, false) | (false, false, false, true) => .o1000
  | (true, true, false, false) | (false, false, true, true) => .o1100
  | (true, false, true, false) | (false, true, false, true) => .o1010
  | (true, true, true, false) | (true, true, false, true)
  | (true, false, true, true) | (false, true, true, true) => .o1110
  | (true, true, true, true) => .o1111
  | (true, false, false, true) | (false, true, true, false) => .o1001

/-- All `16` corner-occupancy masks. -/
def allCornerMasks : List CornerMask :=
  let bs := [false, true]
  bs.flatMap fun a => bs.flatMap fun b => bs.flatMap fun c => bs.map fun d => (a, b, c, d)

/-- **Exact `16 = 1 + 4 + 2 + 2 + 4 + 1 + 2` `Z_2 × Z_2` Symmetry-Orbit Partition:**
`orbitOf` is invariant under `flipH` and `flipV`, and partitions the `16` patterns into
exact orbit sizes `1, 4, 2, 2, 4, 1, 2`. -/
theorem corner_orbit_partition_16 :
    (∀ c : CornerMask, orbitOf (flipH c) = orbitOf c ∧ orbitOf (flipV c) = orbitOf c) ∧
    allCornerMasks.length = 16 ∧
    (allCornerMasks.filter (fun c => orbitOf c == .o0000)).length = 1 ∧
    (allCornerMasks.filter (fun c => orbitOf c == .o1000)).length = 4 ∧
    (allCornerMasks.filter (fun c => orbitOf c == .o1100)).length = 2 ∧
    (allCornerMasks.filter (fun c => orbitOf c == .o1010)).length = 2 ∧
    (allCornerMasks.filter (fun c => orbitOf c == .o1110)).length = 4 ∧
    (allCornerMasks.filter (fun c => orbitOf c == .o1111)).length = 1 ∧
    (allCornerMasks.filter (fun c => orbitOf c == .o1001)).length = 2 := by
  refine ⟨?_, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩
  rintro ⟨a, b, c, d⟩
  cases a <;> cases b <;> cases c <;> cases d <;> decide

/-! ### Exact 2D Dyadic Quad-Tree Coverage & Bound Soundness for All 6 Simple Orbits -/

/-- A leaf `(s1l, s1h, s2l, s2h, curD, k1, k2)` occurs in a `QuadTree`. -/
def DyadicCaseBData.QuadTree.HasLeaf (a b c d e k1 k2 : Nat) : QuadTree → Prop
  | .empty => False
  | .leaf a' b' c' d' e' k1' k2' =>
      a = a' ∧ b = b' ∧ c = c' ∧ d = d' ∧ e = e' ∧ k1 = k1' ∧ k2 = k2'
  | .split c00 c01 c10 c11 =>
      c00.HasLeaf a b c d e k1 k2 ∨ c01.HasLeaf a b c d e k1 k2 ∨
      c10.HasLeaf a b c d e k1 k2 ∨ c11.HasLeaf a b c d e k1 k2

/-- A leaf occurs in some cell of a `CellForest`. -/
def DyadicCaseBData.CellForest.HasLeaf (a b c d e k1 k2 : Nat) : CellForest → Prop
  | .cell _ _ t => t.HasLeaf a b c d e k1 k2
  | .node l r => l.HasLeaf a b c d e k1 k2 ∨ r.HasLeaf a b c d e k1 k2

private theorem checkQuadTree_covers
    (chk : Nat → Nat → Nat → Nat → Nat → Nat → Nat → Bool) :
    ∀ (t : QuadTree) (s1l s1h s2l s2h curD s1 s2 D : Nat),
      checkQuadTree chk s1l s1h s2l s2h curD t = true →
      0 < curD → 0 < D → s2 ≤ s1 →
      s1l * D ≤ s1 * curD → s1 * curD ≤ s1h * D →
      s2l * D ≤ s2 * curD → s2 * curD ≤ s2h * D →
      ∃ a b c d e k1 k2,
        t.HasLeaf a b c d e k1 k2 ∧
        chk a b c d e k1 k2 = true ∧
        0 < e ∧
        a * D ≤ s1 * e ∧ s1 * e ≤ b * D ∧
        c * D ≤ s2 * e ∧ s2 * e ≤ d * D
  | .empty, s1l, s1h, s2l, s2h, curD, s1, s2, D, h, hcur, hD, hord, _, h1h, h2l, _ => by
    unfold checkQuadTree at h
    have hlt : s1h < s2l := by
      unfold Nat.blt at h
      have hle := Nat.le_of_ble_eq_true h
      omega
    have h1 : s2l * D ≤ s1h * D := by
      have hle : s2 * curD ≤ s1 * curD := Nat.mul_le_mul_right curD hord
      omega
    have h2 : s1h * D < s2l * D := Nat.mul_lt_mul_of_pos_right hlt hD
    omega
  | .leaf a b c d e k1 k2, s1l, s1h, s2l, s2h, curD, s1, s2, D, h, hcur, _, _, h1l, h1h, h2l, h2h => by
    unfold checkQuadTree at h
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    rcases h with ⟨⟨⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩, rfl⟩, hchk⟩
    exact ⟨a, b, c, d, e, k1, k2, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
           hchk, hcur, h1l, h1h, h2l, h2h⟩
  | .split c00 c01 c10 c11, s1l, s1h, s2l, s2h, curD, s1, s2, D, h, hcur, hD, hord, h1l, h1h, h2l, h2h => by
    unfold checkQuadTree at h
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    rcases h with ⟨⟨⟨⟨⟨hs1, hs2⟩, h00⟩, h01⟩, h10⟩, h11⟩
    have h2D : 0 < 2 * curD := by omega
    have hmin_bound : ∀ u v : Nat, s2 * (2 * curD) ≤ u * D → s2 * (2 * curD) ≤ v * D →
        s2 * (2 * curD) ≤ natMin u v * D := by
      intro u v hu hv
      unfold natMin
      cases Nat.ble u v <;> assumption
    have h21 : s2 * (2 * curD) ≤ s1 * (2 * curD) := Nat.mul_le_mul_right (2 * curD) hord
    by_cases hmid1 : s1 * (2 * curD) ≤ (2 * s1l + 1) * D
    · by_cases hmid2 : s2 * (2 * curD) ≤ (2 * s2l + 1) * D
      · rcases checkQuadTree_covers chk c00 (2 * s1l) (2 * s1l + 1) (2 * s2l)
            (natMin (2 * s2l + 1) (2 * s1l + 1)) (2 * curD) s1 s2 D h00 h2D hD hord
            (by rw [← Nat.mul_assoc]; calc 2 * s1l * D = 2 * (s1l * D) := by ac_rfl
              _ ≤ 2 * (s1 * curD) := Nat.mul_le_mul_left 2 h1l
              _ = s1 * 2 * curD := by ac_rfl)
            hmid1
            (by rw [← Nat.mul_assoc]; calc 2 * s2l * D = 2 * (s2l * D) := by ac_rfl
              _ ≤ 2 * (s2 * curD) := Nat.mul_le_mul_left 2 h2l
              _ = s2 * 2 * curD := by ac_rfl)
            (hmin_bound _ _ hmid2 (Nat.le_trans h21 hmid1))
          with ⟨a, b, c, d, e, k1, k2, hl, rest⟩
        exact ⟨a, b, c, d, e, k1, k2, Or.inl hl, rest⟩
      · rcases checkQuadTree_covers chk c01 (2 * s1l) (2 * s1l + 1) (2 * s2l + 1)
            (natMin (2 * s2l + 2) (2 * s1l + 1)) (2 * curD) s1 s2 D h01 h2D hD hord
            (by rw [← Nat.mul_assoc]; calc 2 * s1l * D = 2 * (s1l * D) := by ac_rfl
              _ ≤ 2 * (s1 * curD) := Nat.mul_le_mul_left 2 h1l
              _ = s1 * 2 * curD := by ac_rfl)
            hmid1
            (by omega)
            (hmin_bound _ _
              (by have : 2 * s2l + 2 = 2 * s2h := by omega
                  rw [this]
                  calc s2 * (2 * curD) = 2 * (s2 * curD) := by ac_rfl
                    _ ≤ 2 * (s2h * D) := Nat.mul_le_mul_left 2 h2h
                    _ = 2 * s2h * D := by ac_rfl)
              (Nat.le_trans h21 hmid1))
          with ⟨a, b, c, d, e, k1, k2, hl, rest⟩
        exact ⟨a, b, c, d, e, k1, k2, Or.inr (Or.inl hl), rest⟩
    · have h1hi2 : s1 * (2 * curD) ≤ (2 * s1l + 2) * D := by
        have : 2 * s1l + 2 = 2 * s1h := by omega
        rw [this]
        calc s1 * (2 * curD) = 2 * (s1 * curD) := by ac_rfl
          _ ≤ 2 * (s1h * D) := Nat.mul_le_mul_left 2 h1h
          _ = 2 * s1h * D := by ac_rfl
      by_cases hmid2 : s2 * (2 * curD) ≤ (2 * s2l + 1) * D
      · rcases checkQuadTree_covers chk c10 (2 * s1l + 1) (2 * s1l + 2) (2 * s2l)
            (natMin (2 * s2l + 1) (2 * s1l + 2)) (2 * curD) s1 s2 D h10 h2D hD hord
            (by omega) h1hi2
            (by rw [← Nat.mul_assoc]; calc 2 * s2l * D = 2 * (s2l * D) := by ac_rfl
              _ ≤ 2 * (s2 * curD) := Nat.mul_le_mul_left 2 h2l
              _ = s2 * 2 * curD := by ac_rfl)
            (hmin_bound _ _ hmid2 (Nat.le_trans h21 h1hi2))
          with ⟨a, b, c, d, e, k1, k2, hl, rest⟩
        exact ⟨a, b, c, d, e, k1, k2, Or.inr (Or.inr (Or.inl hl)), rest⟩
      · rcases checkQuadTree_covers chk c11 (2 * s1l + 1) (2 * s1l + 2) (2 * s2l + 1)
            (natMin (2 * s2l + 2) (2 * s1l + 2)) (2 * curD) s1 s2 D h11 h2D hD hord
            (by omega) h1hi2 (by omega)
            (hmin_bound _ _
              (by have : 2 * s2l + 2 = 2 * s2h := by omega
                  rw [this]
                  calc s2 * (2 * curD) = 2 * (s2 * curD) := by ac_rfl
                    _ ≤ 2 * (s2h * D) := Nat.mul_le_mul_left 2 h2h
                    _ = 2 * s2h * D := by ac_rfl)
              (Nat.le_trans h21 h1hi2))
          with ⟨a, b, c, d, e, k1, k2, hl, rest⟩
        exact ⟨a, b, c, d, e, k1, k2, Or.inr (Or.inr (Or.inr hl)), rest⟩

private theorem forestHasCell_extract
    (chk : Nat → Nat → Nat → Nat → Nat → Nat → Nat → Bool) (i j : Nat) :
    ∀ f : CellForest,
      forestHasCell i j f = true →
      checkForestBounds chk f = true →
      ∃ t : QuadTree,
        (∀ a b c d e k1 k2, t.HasLeaf a b c d e k1 k2 → f.HasLeaf a b c d e k1 k2) ∧
        checkQuadTree chk i (i + 1) j (j + 1) 36 t = true
  | .cell ci cj t, hhas, hbnd => by
    unfold forestHasCell at hhas
    simp only [Bool.and_eq_true, beq_iff_eq] at hhas
    rcases hhas with ⟨rfl, rfl⟩
    exact ⟨t, fun _ _ _ _ _ _ _ hl => hl, hbnd⟩
  | .node l r, hhas, hbnd => by
    unfold checkForestBounds at hbnd
    cases hl : checkForestBounds chk l
    · rw [hl] at hbnd; cases hbnd
    · rw [hl] at hbnd
      unfold forestHasCell at hhas
      simp only [Bool.or_eq_true] at hhas
      rcases hhas with h1 | h2
      · rcases forestHasCell_extract chk i j l h1 hl with ⟨t, hsub, ht⟩
        exact ⟨t, fun _ _ _ _ _ _ _ h => Or.inl (hsub _ _ _ _ _ _ _ h), ht⟩
      · rcases forestHasCell_extract chk i j r h2 hbnd with ⟨t, hsub, ht⟩
        exact ⟨t, fun _ _ _ _ _ _ _ h => Or.inr (hsub _ _ _ _ _ _ _ h), ht⟩

private theorem checkForestCoversRow_sound (f : CellForest) (i : Nat) :
    ∀ m, checkForestCoversRow f i m = true → ∀ j, j ≤ m → forestHasCell i j f = true
  | 0, h, j, hj => by
    have hj0 : j = 0 := by omega
    subst hj0; exact h
  | m + 1, h, j, hj => by
    unfold checkForestCoversRow at h
    cases hc : forestHasCell i (m + 1) f
    · rw [hc] at h; cases h
    · rw [hc] at h
      by_cases heq : j = m + 1
      · subst heq; exact hc
      · exact checkForestCoversRow_sound f i m h j (by omega)

private theorem checkForestCoversAll_sound (f : CellForest) :
    ∀ m, checkForestCoversAll f m = true → ∀ i j, i ≤ m → j ≤ i → forestHasCell i j f = true
  | 0, h, i, j, hi, hj => by
    have hi0 : i = 0 := by omega
    subst hi0
    exact checkForestCoversRow_sound f 0 0 h j hj
  | m + 1, h, i, j, hi, hj => by
    unfold checkForestCoversAll at h
    cases hc : checkForestCoversRow f (m + 1) (m + 1)
    · rw [hc] at h; cases h
    · rw [hc] at h
      by_cases heq : i = m + 1
      · subst heq; exact checkForestCoversRow_sound f (m + 1) (m + 1) hc j hj
      · exact checkForestCoversAll_sound f m h i j (by omega) hj

private theorem forest_covers_triangle
    (chk : Nat → Nat → Nat → Nat → Nat → Nat → Nat → Bool) (f : CellForest)
    (hcov : checkForestCoversAll f 11 = true)
    (hbnd : checkForestBounds chk f = true)
    (s1 s2 D : Nat) (hD : 0 < D) (hord : s2 ≤ s1) (h3 : 3 * s1 < D) :
    ∃ a b c d e k1 k2,
      f.HasLeaf a b c d e k1 k2 ∧
      chk a b c d e k1 k2 = true ∧
      0 < e ∧
      a * D ≤ s1 * e ∧ s1 * e ≤ b * D ∧
      c * D ≤ s2 * e ∧ s2 * e ≤ d * D := by
  let i := (36 * s1) / D
  let j := (36 * s2) / D
  have hi_lt : i < 12 := Nat.div_lt_of_lt_mul (by omega : 36 * s1 < D * 12)
  have hji : j ≤ i := Nat.div_le_div_right (Nat.mul_le_mul_left 36 hord)
  have hhas := checkForestCoversAll_sound f 11 hcov i j (by omega) hji
  rcases forestHasCell_extract chk i j f hhas hbnd with ⟨t, hsub, ht⟩
  have hi_lo : i * D ≤ s1 * 36 := by
    have h1 := Nat.mul_div_le (36 * s1) D
    rw [Nat.mul_comm D i] at h1
    omega
  have hi_hi : s1 * 36 ≤ (i + 1) * D := by
    have hdm : D * i + (36 * s1) % D = 36 * s1 := Nat.div_add_mod (36 * s1) D
    have hmod : (36 * s1) % D < D := Nat.mod_lt (36 * s1) hD
    rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm i D]
    omega
  have hj_lo : j * D ≤ s2 * 36 := by
    have h1 := Nat.mul_div_le (36 * s2) D
    rw [Nat.mul_comm D j] at h1
    omega
  have hj_hi : s2 * 36 ≤ (j + 1) * D := by
    have hdm : D * j + (36 * s2) % D = 36 * s2 := Nat.div_add_mod (36 * s2) D
    have hmod : (36 * s2) % D < D := Nat.mod_lt (36 * s2) hD
    rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm j D]
    omega
  rcases checkQuadTree_covers chk t i (i + 1) j (j + 1) 36 s1 s2 D ht
      (by decide) hD hord hi_lo hi_hi hj_lo hj_hi with ⟨a, b, c, d, e, k1, k2, hl, rest⟩
  exact ⟨a, b, c, d, e, k1, k2, hsub a b c d e k1 k2 hl, rest⟩

/-- **Exact Kernel-Certified Triangle Coverage & Strictly-Guarded Leaf Acceptance for ALL `6` Simple Case B Orbits:**
For EVERY rational point `(s1/D, s2/D)` with `0 ≤ s2 ≤ s1 < D/3`, EACH of the 6 simple orbits
(`0000:78, 1000:78, 1100:132, 1010:126, 1110:249, 1111:150`; total `813` leaves) contains a
dyadic quad-tree leaf covering `(s1/D, s2/D)` accepted by its strictly-guarded optimized evaluator
(`≤ 99920/100000`). The semantic analytic inequalities for every primitive of the optimized
evaluator (`pupGrid`, `pupEGrid`, `holderPairEGrid`, `aMax256Tree`, factored AM-GM for `1110`,
and the `379,133`-weighted tangent majorant for `1111`) are kernel-proved immediately below;
`cert/verify_clawfree_eg.py` independently certifies unfactored subdivisions on the exact same
`813` geometric leaves plus all `55,531` leaves of Orbit `1001`. -/
theorem caseB_simple_orbits_cover_triangle (s1 s2 D : Nat) (hD : 0 < D) (hord : s2 ≤ s1) (h3 : 3 * s1 < D) :
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
      0 < e ∧ a * D ≤ s1 * e ∧ s1 * e ≤ b * D ∧ c * D ≤ s2 * e ∧ s2 * e ≤ d * D) :=
  ⟨forest_covers_triangle checkLeaf0000 forest0000 forest0000_covers_bool forest0000_bounds_bool s1 s2 D hD hord h3,
   forest_covers_triangle checkLeaf1000 forest1000 forest1000_covers_bool forest1000_bounds_bool s1 s2 D hD hord h3,
   forest_covers_triangle checkLeaf1100 forest1100 forest1100_covers_bool forest1100_bounds_bool s1 s2 D hD hord h3,
   forest_covers_triangle checkLeaf1010 forest1010 forest1010_covers_bool forest1010_bounds_bool s1 s2 D hD hord h3,
   forest_covers_triangle checkLeaf1110 forest1110 forest1110_covers_bool forest1110_bounds_bool s1 s2 D hD hord h3,
   forest_covers_triangle checkLeaf1111 forest1111 forest1111_covers_bool forest1111_bounds_bool s1 s2 D hD hord h3⟩

/-! ### Semantic Soundness of the Case B Optimized Evaluator (`pupGrid`, `pupEGrid`, `holderPairEGrid`, `1110` Factored AM-GM, `1111` `379,133`-Tangent) -/

private theorem le_of_pow256_le {a b : Nat} (h : a ^ 256 ≤ b ^ 256) : a ≤ b := by
  by_cases hab : a ≤ b
  · exact hab
  · exfalso
    have hlt : b < a := by omega
    have hstep : ∀ e : Nat, 1 ≤ e → b ^ e < a ^ e := by
      intro e he
      induction e with
      | zero => omega
      | succ e' ih =>
        by_cases h0 : e' = 0
        · subst h0; simpa using hlt
        · rw [Nat.pow_succ, Nat.pow_succ]
          exact Nat.lt_of_le_of_lt (Nat.mul_le_mul_left (b ^ e') (Nat.le_of_lt hlt))
            (Nat.mul_lt_mul_of_pos_right (ih (by omega)) (by omega))
    have h256 := hstep 256 (by decide)
    omega

private theorem ceil_div_mul_ge (a b : Nat) (hb : 0 < b) : a ≤ ((a + b - 1) / b) * b := by
  have hdm := Nat.div_add_mod (a + b - 1) b
  have hmod := Nat.mod_lt (a + b - 1) hb
  have hcomm : b * ((a + b - 1) / b) = ((a + b - 1) / b) * b := Nat.mul_comm _ _
  omega

private theorem checkGridTree_sound :
    ∀ (d start : Nat), checkGridTree start d = true →
      ∀ i, start ≤ i → i < start + 2 ^ d → i ≤ 692 →
        gridUp2048Tree.get i = pupFast i 2048
  | 0, start, h, i, hlo, hhi, h692 => by
    have hi : i = start := by omega
    subst hi
    unfold checkGridTree at h
    have hble : Nat.ble i 692 = true := Nat.ble_eq_true_of_le h692
    simp only [hble, ↓reduceIte, beq_iff_eq] at h
    exact h
  | d + 1, start, h, i, hlo, hhi, h692 => by
    unfold checkGridTree at h
    dsimp only at h
    cases hl : checkGridTree start d
    · rw [hl] at h; cases h
    · rw [hl] at h
      simp only [↓reduceIte] at h
      have hpow : 2 ^ (d + 1) = 2 ^ d + 2 ^ d := by rw [Nat.pow_succ]; omega
      by_cases hmid : i < start + 2 ^ d
      · exact checkGridTree_sound d start hl i hlo hmid h692
      · exact checkGridTree_sound d (start + 2 ^ d) h i (by omega) (by omega) h692

/-- Exact equality of the precomputed `1/2048` table against `pupFast i 2048` for all `i ≤ 692`. -/
theorem gridUp2048_eq_pupFast (i : Nat) (hi : i ≤ 692) :
    gridUp2048Tree.get i = pupFast i 2048 :=
  checkGridTree_sound 10 0 gridUp2048_all_ok i (Nat.zero_le i) (by omega) hi

private theorem checkGridMonoTree_sound :
    ∀ (d start : Nat), checkGridMonoTree start d = true →
      ∀ a, start ≤ a → a < start + 2 ^ d → a < 692 →
        gridUp2048Tree.get a ≤ gridUp2048Tree.get (a + 1)
  | 0, start, h, a, hlo, hhi, h692 => by
    have heq : a = start := by omega
    subst heq
    unfold checkGridMonoTree at h
    have hlt : Nat.blt a 692 = true := Nat.ble_eq_true_of_le (by omega)
    rw [hlt] at h
    simp only [↓reduceIte] at h
    exact Nat.le_of_ble_eq_true h
  | d + 1, start, h, a, hlo, hhi, h692 => by
    unfold checkGridMonoTree at h
    dsimp only at h
    cases hl : checkGridMonoTree start d
    · rw [hl] at h; cases h
    · rw [hl] at h; simp only [↓reduceIte] at h
      have hpow : 2 ^ (d + 1) = 2 ^ d + 2 ^ d := by rw [Nat.pow_succ]; omega
      by_cases hmid : a < start + 2 ^ d
      · exact checkGridMonoTree_sound d start hl a hlo hmid h692
      · exact checkGridMonoTree_sound d (start + 2 ^ d) h a (by omega) (by omega) h692

/-- **Monotonicity of `gridUp2048Tree` on `0..692`:** `i ≤ j ≤ 692 → gridUp2048Tree.get i ≤ gridUp2048Tree.get j`. -/
theorem gridUp2048_mono {i j : Nat} (hij : i ≤ j) (hj : j ≤ 692) :
    gridUp2048Tree.get i ≤ gridUp2048Tree.get j := by
  induction j with
  | zero =>
    have hi0 : i = 0 := by omega
    subst hi0; exact Nat.le_refl _
  | succ j' ih =>
    by_cases hEq : i = j' + 1
    · subst hEq; exact Nat.le_refl _
    · exact Nat.le_trans (ih (by omega) (by omega))
        (checkGridMonoTree_sound 10 0 gridUp2048_mono_ok j' (Nat.zero_le j') (by omega) (by omega))

/-- **Unconditional Semantic Soundness of `pupGrid`:**
For EVERY `num, den : Nat` with `0 < den`,
`num^123 * SCALE^256 ≤ (pupGrid num den)^256 * den^123`. -/
theorem pupGrid_sound (num den : Nat) (hden : 0 < den) :
    num ^ 123 * SCALE ^ 256 ≤ (pupGrid num den) ^ 256 * den ^ 123 := by
  unfold pupGrid
  cases num with
  | zero => simp
  | succ m =>
    simp only [Nat.succ_ne_zero, beq_iff_eq, ↓reduceIte]
    let n := m + 1
    let idx := (n * 2048 + den - 1) / den
    cases hble : Nat.ble idx 692
    · simp only [Bool.false_eq_true, ↓reduceIte]
      exact pupFast_sound n den hden
    · simp only [↓reduceIte]
      have hidx692 : idx ≤ 692 := Nat.le_of_ble_eq_true hble
      rw [gridUp2048_eq_pupFast idx hidx692]
      have hrat : n * 2048 ≤ idx * den := ceil_div_mul_ge (n * 2048) den hden
      exact pow123_ub_mono (by decide) hrat (pupFast_sound idx 2048 (by decide))

/-- Monotonicity of `pupGrid` whenever the upper argument lands inside the `1/2048` table (`≤ 692`). -/
theorem pupGrid_mono_on_grid {n1 n2 den : Nat} (hden : 0 < den) (hle : n1 ≤ n2)
    (hgrid : (n2 * 2048 + den - 1) / den ≤ 692) :
    pupGrid n1 den ≤ pupGrid n2 den := by
  unfold pupGrid
  cases n1 with
  | zero => simp
  | succ m1 =>
    cases n2 with
    | zero => omega
    | succ m2 =>
      simp only [Nat.succ_ne_zero, beq_iff_eq, ↓reduceIte]
      have hidx_le : ((m1 + 1) * 2048 + den - 1) / den ≤ ((m2 + 1) * 2048 + den - 1) / den :=
        Nat.div_le_div_right (by omega)
      have hb1 : Nat.ble (((m1 + 1) * 2048 + den - 1) / den) 692 = true :=
        Nat.ble_eq_true_of_le (Nat.le_trans hidx_le hgrid)
      have hb2 : Nat.ble (((m2 + 1) * 2048 + den - 1) / den) 692 = true :=
        Nat.ble_eq_true_of_le hgrid
      simp only [hb1, hb2, ↓reduceIte]
      exact gridUp2048_mono hidx_le hgrid

/-- **Unconditional Semantic Soundness of `pupEGrid` (including `+kEps/4096` shift):**
For EVERY `n, d, kEps : Nat` with `0 < d`,
`(n * 4096 + kEps * d)^123 * SCALE^256 ≤ (pupEGrid n d kEps)^256 * (d * 4096)^123`. -/
theorem pupEGrid_sound (n d kEps : Nat) (hd : 0 < d) :
    (n * 4096 + kEps * d) ^ 123 * SCALE ^ 256 ≤ (pupEGrid n d kEps) ^ 256 * (d * 4096) ^ 123 := by
  unfold pupEGrid
  cases kEps with
  | zero =>
    simp only [beq_self_eq_true, ↓reduceIte, Nat.zero_mul, Nat.add_zero]
    have h := pupGrid_sound n d hd
    have h4096 : (n * 4096) ^ 123 = n ^ 123 * 4096 ^ 123 := Nat.mul_pow n 4096 123
    have hd4096 : (d * 4096) ^ 123 = d ^ 123 * 4096 ^ 123 := Nat.mul_pow d 4096 123
    rw [h4096, hd4096]
    calc n ^ 123 * 4096 ^ 123 * SCALE ^ 256
        = (n ^ 123 * SCALE ^ 256) * 4096 ^ 123 := by ac_rfl
      _ ≤ ((pupGrid n d) ^ 256 * d ^ 123) * 4096 ^ 123 := Nat.mul_le_mul_right _ h
      _ = (pupGrid n d) ^ 256 * (d ^ 123 * 4096 ^ 123) := by ac_rfl
  | succ k =>
    simp only [Nat.succ_ne_zero, beq_iff_eq, ↓reduceIte]
    exact pupGrid_sound (n * 4096 + (k + 1) * d) (d * 4096) (Nat.mul_pos hd (by decide))

/-- **Shift-2 Semantic Corollary (`c_0 = 2`, `m ≥ 4096`):**
If `m ≥ 4096`, `0 < d`, and `h / m ≤ n / d`, then
`((h + 2) / m)^(123/256) * SCALE ≤ pupEGrid n d 2` in exact powered-integer form. -/
theorem pupEGrid_shift2_sound (h m n d : Nat) (hm : m ≥ 4096) (hd : 0 < d) (hrat : h * d ≤ n * m) :
    (h + 2) ^ 123 * SCALE ^ 256 ≤ (pupEGrid n d 2) ^ 256 * m ^ 123 := by
  have hle : (h + 2) * (d * 4096) ≤ (n * 4096 + 2 * d) * m := by
    rw [Nat.add_mul, Nat.add_mul]
    have h1 : h * (d * 4096) ≤ n * 4096 * m := by
      calc h * (d * 4096) = (h * d) * 4096 := by ac_rfl
        _ ≤ (n * m) * 4096 := Nat.mul_le_mul_right 4096 hrat
        _ = n * 4096 * m := by ac_rfl
    have h2 : 2 * (d * 4096) ≤ 2 * d * m := by
      calc 2 * (d * 4096) = (2 * d) * 4096 := by ac_rfl
        _ ≤ (2 * d) * m := Nat.mul_le_mul_left (2 * d) hm
    exact Nat.add_le_add h1 h2
  exact pow123_ub_mono (Nat.mul_pos hd (by decide)) hle (pupEGrid_sound n d 2 hd)

/-- **Pure-`Nat` Tangent Linearization of `x ↦ x^(123/256)` via `amgm_256`:**
For any `u` with `u/SCALE ≤ (A/den)^(123/256)` and any `pM` with `(M/den)^(123/256) ≤ pM/SCALE`,
the exact tangent line at `M` gives `u * 256 * M ≤ (123 * A + 133 * M) * pM`! -/
theorem pow123_tangent_linear {u A M pM den : Nat}
    (hden : 0 < den)
    (hu : u ^ 256 * den ^ 123 ≤ A ^ 123 * SCALE ^ 256)
    (hM : M ^ 123 * SCALE ^ 256 ≤ pM ^ 256 * den ^ 123) :
    u * 256 * M ≤ (123 * A + 133 * M) * pM := by
  apply le_of_pow256_le
  have ham := amgm_256 A M
  have hM256 : M ^ 256 = M ^ 133 * M ^ 123 := by rw [← Nat.pow_add]
  have hmul : (u * 256 * M) ^ 256 * den ^ 123 ≤ ((123 * A + 133 * M) * pM) ^ 256 * den ^ 123 := by
    rw [Nat.mul_pow, Nat.mul_pow, Nat.mul_pow, hM256]
    calc u ^ 256 * 256 ^ 256 * (M ^ 133 * M ^ 123) * den ^ 123
        = (u ^ 256 * den ^ 123) * (256 ^ 256 * M ^ 133 * M ^ 123) := by ac_rfl
      _ ≤ (A ^ 123 * SCALE ^ 256) * (256 ^ 256 * M ^ 133 * M ^ 123) := Nat.mul_le_mul_right _ hu
      _ = (A ^ 123 * M ^ 133 * 256 ^ 256) * (M ^ 123 * SCALE ^ 256) := by ac_rfl
      _ ≤ (123 * A + 133 * M) ^ 256 * (pM ^ 256 * den ^ 123) := Nat.mul_le_mul ham hM
      _ = (123 * A + 133 * M) ^ 256 * pM ^ 256 * den ^ 123 := by ac_rfl
  exact Nat.le_of_mul_le_mul_right hmul (Nat.pow_pos hden)

/-- **Pure-`Nat` Concavity Midpoint Inequality for `x ↦ x^(123/256)`:**
If `u1/SCALE ≤ (A/den)^(123/256)`, `u2/SCALE ≤ (B/den)^(123/256)`, `A + B ≤ 2 * M` (`0 < M`),
and `(M/den)^(123/256) ≤ pM/SCALE`, then `u1 + u2 ≤ 2 * pM`. -/
theorem pow123_concave_sum {u1 u2 A B M pM den : Nat}
    (hden : 0 < den) (hMpos : 0 < M) (hsum : A + B ≤ 2 * M)
    (hu1 : u1 ^ 256 * den ^ 123 ≤ A ^ 123 * SCALE ^ 256)
    (hu2 : u2 ^ 256 * den ^ 123 ≤ B ^ 123 * SCALE ^ 256)
    (hM : M ^ 123 * SCALE ^ 256 ≤ pM ^ 256 * den ^ 123) :
    u1 + u2 ≤ 2 * pM := by
  have ht1 := pow123_tangent_linear hden hu1 hM
  have ht2 := pow123_tangent_linear hden hu2 hM
  have hadd : (u1 + u2) * (256 * M) ≤ (2 * pM) * (256 * M) := by
    have hL : (u1 + u2) * (256 * M) = u1 * 256 * M + u2 * 256 * M := by
      rw [Nat.add_mul, Nat.mul_assoc, Nat.mul_assoc]
    have hlin : (123 * A + 133 * M) + (123 * B + 133 * M) ≤ 2 * 256 * M := by omega
    rw [hL]
    calc u1 * 256 * M + u2 * 256 * M
        ≤ (123 * A + 133 * M) * pM + (123 * B + 133 * M) * pM := Nat.add_le_add ht1 ht2
      _ = ((123 * A + 133 * M) + (123 * B + 133 * M)) * pM := (Nat.add_mul _ _ _).symm
      _ ≤ (2 * 256 * M) * pM := Nat.mul_le_mul_right pM hlin
      _ = (2 * pM) * (256 * M) := by ac_rfl
  exact Nat.le_of_mul_le_mul_right hadd (Nat.mul_pos (by decide) hMpos)

private theorem natMax_le_left_le {a b c : Nat} (h : a ≤ b) : a ≤ natMax b c := by
  unfold natMax
  cases hb : Nat.ble b c
  · simp only [Bool.false_eq_true, ↓reduceIte]; exact h
  · simp only [↓reduceIte]; exact Nat.le_trans h (Nat.le_of_ble_eq_true hb)

private theorem natMax_le_right_le {a b c : Nat} (h : a ≤ c) : a ≤ natMax b c := by
  unfold natMax
  cases hb : Nat.ble b c
  · simp only [Bool.false_eq_true, ↓reduceIte]
    have hnot : ¬(b ≤ c) := fun hle => by rw [Nat.ble_eq_true_of_le hle] at hb; cases hb
    omega
  · simp only [↓reduceIte]; exact h

private theorem holderPairEGrid_go_ge (pw1 pw2 sHi sDen lo hi : Nat) :
    ∀ (k best : Nat),
      best ≤ holderPairEGrid.go pw1 pw2 sHi sDen lo hi k best ∧
      ∀ idx, idx < k →
        let an := lo * 8 + (hi - lo) * idx
        let bn := lo * 8 + (hi - lo) * (idx + 1)
        prodUpD pw1 (pupEGrid bn (sDen * 8) 2) +
          prodUpD pw2 (pupEGrid (sHi * 8 - an) (sDen * 8) 2) ≤
          holderPairEGrid.go pw1 pw2 sHi sDen lo hi k best
  | 0, best => ⟨Nat.le_refl _, fun _ h => by omega⟩
  | k' + 1, best => by
    unfold holderPairEGrid.go
    dsimp only
    let v := prodUpD pw1 (pupEGrid (lo * 8 + (hi - lo) * (k' + 1)) (sDen * 8) 2) +
             prodUpD pw2 (pupEGrid (sHi * 8 - (lo * 8 + (hi - lo) * k')) (sDen * 8) 2)
    have ih := holderPairEGrid_go_ge pw1 pw2 sHi sDen lo hi k' (natMax best v)
    refine ⟨Nat.le_trans (natMax_le_left_le (Nat.le_refl best)) ih.1, ?_⟩
    intro idx hidx
    by_cases heq : idx = k'
    · subst heq
      exact Nat.le_trans (natMax_le_right_le (Nat.le_refl v)) ih.1
    · exact ih.2 idx (by omega)

/-- **Semantic Soundness of `holderPairEGrid` (All Branches: Direct, Symmetric Midpoint Concavity, & 8-Subinterval Envelope):**
For EVERY `pw1, pw2, sHi, sDen, h1mRaw, h2mRaw : Nat` with `0 < sDen`, and EVERY feasible
rational pair `(t1/q, t2/q)` (`0 < q`) with `t1 ≤ h1mRaw * q`, `t2 ≤ h2mRaw * q`, `t1 + t2 ≤ sHi * q`,
if `u1, u2` satisfy the exact `123/256`-power bounds
`u_i^256 * (sDen * q * 4096)^123 ≤ (t_i * 4096 + 2 * sDen * q)^123 * SCALE^256`,
then `pw1 * u1 + pw2 * u2 ≤ holderPairEGrid pw1 pw2 sHi sDen h1mRaw h2mRaw * SCALE`. -/
theorem holderPairEGrid_sound (pw1 pw2 sHi sDen h1mRaw h2mRaw t1 t2 q u1 u2 : Nat)
    (hsDen : 0 < sDen) (hq : 0 < q)
    (ht1 : t1 ≤ h1mRaw * q) (ht2 : t2 ≤ h2mRaw * q) (hsum : t1 + t2 ≤ sHi * q)
    (hu1 : u1 ^ 256 * (sDen * q * 4096) ^ 123 ≤ (t1 * 4096 + 2 * sDen * q) ^ 123 * SCALE ^ 256)
    (hu2 : u2 ^ 256 * (sDen * q * 4096) ^ 123 ≤ (t2 * 4096 + 2 * sDen * q) ^ 123 * SCALE ^ 256) :
    pw1 * u1 + pw2 * u2 ≤ holderPairEGrid pw1 pw2 sHi sDen h1mRaw h2mRaw * SCALE := by
  have u_le_pupEGrid : ∀ (u t n d : Nat), 0 < d →
      u ^ 256 * (sDen * q * 4096) ^ 123 ≤ (t * 4096 + 2 * sDen * q) ^ 123 * SCALE ^ 256 →
      t * d ≤ n * (sDen * q) → u ≤ pupEGrid n d 2 := by
    intro u t n d hd hu hrat
    have hle : (t * 4096 + 2 * sDen * q) * (d * 4096) ≤ (n * 4096 + 2 * d) * (sDen * q * 4096) := by
      rw [Nat.add_mul, Nat.add_mul]
      have h1 : t * 4096 * (d * 4096) ≤ n * 4096 * (sDen * q * 4096) := by
        calc t * 4096 * (d * 4096) = (t * d) * (4096 * 4096) := by ac_rfl
          _ ≤ (n * (sDen * q)) * (4096 * 4096) := Nat.mul_le_mul_right _ hrat
          _ = n * 4096 * (sDen * q * 4096) := by ac_rfl
      have h2 : 2 * sDen * q * (d * 4096) = 2 * d * (sDen * q * 4096) := by ac_rfl
      exact Nat.add_le_add h1 (Nat.le_of_eq h2)
    have hpow := pow123_ub_mono (Nat.mul_pos hd (by decide)) hle (pupEGrid_sound n d 2 hd)
    have hcomb := Nat.le_trans hu hpow
    exact le_of_pow256_le (Nat.le_of_mul_le_mul_right hcomb
      (Nat.pow_pos (Nat.mul_pos (Nat.mul_pos hsDen hq) (by decide))))
  have prod_add_le : ∀ (a1 a2 : Nat), u1 ≤ a1 → u2 ≤ a2 →
      pw1 * u1 + pw2 * u2 ≤ (prodUpD pw1 a1 + prodUpD pw2 a2) * SCALE := by
    intro a1 a2 ha1 ha2
    rw [Nat.add_mul]
    exact Nat.add_le_add
      (Nat.le_trans (Nat.mul_le_mul_left pw1 ha1) (prodUp_sound pw1 a1).1)
      (Nat.le_trans (Nat.mul_le_mul_left pw2 ha2) (prodUp_sound pw2 a2).1)
  unfold holderPairEGrid
  by_cases h0 : pw1 = 0 ∧ pw2 = 0
  · rcases h0 with ⟨rfl, rfl⟩; simp
  · have h0f : ((pw1 == 0) && (pw2 == 0)) = false := by
      cases hb : ((pw1 == 0) && (pw2 == 0))
      · rfl
      · simp only [Bool.and_eq_true, beq_iff_eq] at hb; exact absurd hb h0
    simp only [h0f, Bool.false_eq_true, ↓reduceIte]
    let h1m := natMin h1mRaw sHi
    let h2m := natMin h2mRaw sHi
    have ht1_m : t1 ≤ h1m * q := by
      dsimp only [h1m]; rw [natMin_eq_min]
      by_cases h : h1mRaw ≤ sHi
      · rw [Nat.min_eq_left h]; exact ht1
      · rw [Nat.min_eq_right (by omega)]; omega
    have ht2_m : t2 ≤ h2m * q := by
      dsimp only [h2m]; rw [natMin_eq_min]
      by_cases h : h2mRaw ≤ sHi
      · rw [Nat.min_eq_left h]; exact ht2
      · rw [Nat.min_eq_right (by omega)]; omega
    cases hle : Nat.ble (h1m + h2m) sHi
    · simp only [Bool.false_eq_true, ↓reduceIte]
      have hgt : sHi < h1m + h2m := by
        have hnot : ¬(h1m + h2m ≤ sHi) := fun h => by rw [Nat.ble_eq_true_of_le h] at hle; cases hle
        omega
      let lo := sHi - h2m
      let hi := h1m
      have h2le : h2m ≤ sHi := by dsimp only [h2m]; rw [natMin_eq_min]; exact Nat.min_le_right _ _
      have hlo_lt_hi : lo < hi := by dsimp only [lo, hi]; omega
      have hnot_hilo : Nat.ble hi lo = false := by
        cases hb : Nat.ble hi lo
        · rfl
        · have := Nat.le_of_ble_eq_true hb; omega
      dsimp only [lo, hi, h1m, h2m] at hnot_hilo
      rw [hnot_hilo]
      simp only [Bool.false_eq_true, ↓reduceIte]
      cases hsym : ((pw1 == pw2) && Nat.ble (2 * lo) sHi && Nat.ble sHi (2 * hi))
      · simp only [Bool.false_eq_true, ↓reduceIte]
        -- 8-subinterval upper envelope:
        let t1' := max t1 (lo * q)
        have ht1_le' : t1 ≤ t1' := Nat.le_max_left _ _
        have ht1'_lo : lo * q ≤ t1' := Nat.le_max_right _ _
        have ht1'_hi : t1' ≤ hi * q := Nat.max_le.mpr ⟨ht1_m, Nat.mul_le_mul_right q (by omega)⟩
        have ht2_rem : t2 ≤ sHi * q - t1' := by
          dsimp only [t1']
          by_cases hc : t1 ≤ lo * q
          · rw [Nat.max_eq_right hc]
            have hsub : sHi * q - lo * q = h2m * q := by
              rw [← Nat.sub_mul]
              have h2le : h2m ≤ sHi := by dsimp only [h2m]; rw [natMin_eq_min]; exact Nat.min_le_right _ _
              congr 1; dsimp only [lo]; omega
            rw [hsub]; exact ht2_m
          · rw [Nat.max_eq_left (by omega)]; omega
        let span := (hi - lo) * q
        have hspan_pos : 0 < span := Nat.mul_pos (by omega) hq
        let idx := min 7 ((8 * (t1' - lo * q)) / span)
        have hidx_lt : idx < 8 := by dsimp only [idx]; omega
        have hidx_lo : idx * span ≤ 8 * (t1' - lo * q) := by
          have hle1 : idx ≤ (8 * (t1' - lo * q)) / span := Nat.min_le_right _ _
          have h1 := Nat.mul_le_mul_right span hle1
          have h2 : ((8 * (t1' - lo * q)) / span) * span ≤ 8 * (t1' - lo * q) := by
            rw [Nat.mul_comm]; exact Nat.mul_div_le _ _
          exact Nat.le_trans h1 h2
        have hidx_hi : 8 * (t1' - lo * q) ≤ (idx + 1) * span := by
          dsimp only [idx]
          by_cases h7 : (8 * (t1' - lo * q)) / span ≤ 7
          · rw [Nat.min_eq_right h7]
            have hdm := Nat.div_add_mod (8 * (t1' - lo * q)) span
            have hmod := Nat.mod_lt (8 * (t1' - lo * q)) hspan_pos
            rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm _ span]
            omega
          · rw [Nat.min_eq_left (by omega)]
            have hspan_eq : span = hi * q - lo * q := Nat.sub_mul hi lo q
            have hx_le : t1' - lo * q ≤ span := by rw [hspan_eq]; omega
            omega
        let an := lo * 8 + (hi - lo) * idx
        let bn := lo * 8 + (hi - lo) * (idx + 1)
        have han_le : an * q ≤ 8 * t1' := by
          dsimp only [an]
          rw [Nat.add_mul]
          have h1 : lo * 8 * q = 8 * (lo * q) := by ac_rfl
          have h2 : (hi - lo) * idx * q = idx * span := by dsimp only [span]; ac_rfl
          rw [h1, h2]
          omega
        have hbn_ge : 8 * t1' ≤ bn * q := by
          dsimp only [bn]
          rw [Nat.add_mul]
          have h1 : lo * 8 * q = 8 * (lo * q) := by ac_rfl
          have h2 : (hi - lo) * (idx + 1) * q = (idx + 1) * span := by dsimp only [span]; ac_rfl
          rw [h1, h2]
          omega
        have hu1_le : u1 ≤ pupEGrid bn (sDen * 8) 2 := by
          apply u_le_pupEGrid u1 t1 bn (sDen * 8) (Nat.mul_pos hsDen (by decide)) hu1
          calc t1 * (sDen * 8) = sDen * (8 * t1) := by ac_rfl
            _ ≤ sDen * (8 * t1') := Nat.mul_le_mul_left sDen (Nat.mul_le_mul_left 8 ht1_le')
            _ ≤ sDen * (bn * q) := Nat.mul_le_mul_left sDen hbn_ge
            _ = bn * (sDen * q) := by ac_rfl
        have hu2_le : u2 ≤ pupEGrid (sHi * 8 - an) (sDen * 8) 2 := by
          apply u_le_pupEGrid u2 t2 (sHi * 8 - an) (sDen * 8) (Nat.mul_pos hsDen (by decide)) hu2
          have h8t2 : 8 * t2 ≤ (sHi * 8 - an) * q := by
            rw [Nat.sub_mul]
            have hs8 : sHi * 8 * q = 8 * (sHi * q) := by ac_rfl
            rw [hs8]
            have h1 : 8 * t2 ≤ 8 * (sHi * q - t1') := Nat.mul_le_mul_left 8 ht2_rem
            rw [Nat.mul_sub] at h1
            omega
          calc t2 * (sDen * 8) = sDen * (8 * t2) := by ac_rfl
            _ ≤ sDen * ((sHi * 8 - an) * q) := Nat.mul_le_mul_left sDen h8t2
            _ = (sHi * 8 - an) * (sDen * q) := by ac_rfl
        have hstep := (holderPairEGrid_go_ge pw1 pw2 sHi sDen lo hi 8 0).2 idx hidx_lt
        exact Nat.le_trans (prod_add_le _ _ hu1_le hu2_le) (Nat.mul_le_mul_right SCALE hstep)
      · simp only [↓reduceIte]
        -- Symmetric midpoint concavity case (`pw1 = pw2`):
        simp only [Bool.and_eq_true, beq_iff_eq] at hsym
        rcases hsym with ⟨⟨hpw_eq, _⟩, _⟩
        subst hpw_eq
        let A := 2 * (t1 * 4096 + 2 * sDen * q)
        let B := 2 * (t2 * 4096 + 2 * sDen * q)
        let M := sHi * q * 4096 + 4 * sDen * q
        let den2 := 2 * (sDen * q * 4096)
        have hM_pos : 0 < M := by
          have : 0 < 4 * sDen * q := Nat.mul_pos (Nat.mul_pos (by decide) hsDen) hq
          dsimp only [M]; omega
        have hden2_pos : 0 < den2 := Nat.mul_pos (by decide) (Nat.mul_pos (Nat.mul_pos hsDen hq) (by decide))
        have hAB_le : A + B ≤ 2 * M := by
          dsimp only [A, B, M]
          have h1 : (t1 + t2) * 4096 ≤ sHi * q * 4096 := Nat.mul_le_mul_right 4096 hsum
          have h4 : 4 * sDen * q = 2 * (2 * sDen * q) := by
            rw [← Nat.mul_assoc 2 (2 * sDen) q, ← Nat.mul_assoc 2 2 sDen]
          omega
        have hu1' : u1 ^ 256 * den2 ^ 123 ≤ A ^ 123 * SCALE ^ 256 := by
          dsimp only [A, den2]
          rw [Nat.mul_pow 2 (sDen * q * 4096) 123, Nat.mul_pow 2 (t1 * 4096 + 2 * sDen * q) 123]
          calc u1 ^ 256 * (2 ^ 123 * (sDen * q * 4096) ^ 123)
              = 2 ^ 123 * (u1 ^ 256 * (sDen * q * 4096) ^ 123) := by ac_rfl
            _ ≤ 2 ^ 123 * ((t1 * 4096 + 2 * sDen * q) ^ 123 * SCALE ^ 256) := Nat.mul_le_mul_left _ hu1
            _ = 2 ^ 123 * (t1 * 4096 + 2 * sDen * q) ^ 123 * SCALE ^ 256 := by ac_rfl
        have hu2' : u2 ^ 256 * den2 ^ 123 ≤ B ^ 123 * SCALE ^ 256 := by
          dsimp only [B, den2]
          rw [Nat.mul_pow 2 (sDen * q * 4096) 123, Nat.mul_pow 2 (t2 * 4096 + 2 * sDen * q) 123]
          calc u2 ^ 256 * (2 ^ 123 * (sDen * q * 4096) ^ 123)
              = 2 ^ 123 * (u2 ^ 256 * (sDen * q * 4096) ^ 123) := by ac_rfl
            _ ≤ 2 ^ 123 * ((t2 * 4096 + 2 * sDen * q) ^ 123 * SCALE ^ 256) := Nat.mul_le_mul_left _ hu2
            _ = 2 ^ 123 * (t2 * 4096 + 2 * sDen * q) ^ 123 * SCALE ^ 256 := by ac_rfl
        have hM_ub : M ^ 123 * SCALE ^ 256 ≤ (pupEGrid sHi (2 * sDen) 2) ^ 256 * den2 ^ 123 := by
          have hp := pupEGrid_sound sHi (2 * sDen) 2 (Nat.mul_pos (by decide) hsDen)
          have hM_eq : M = (sHi * 4096 + 2 * (2 * sDen)) * q := by
            dsimp only [M]
            rw [Nat.add_mul, Nat.mul_right_comm sHi 4096 q, ← Nat.mul_assoc 2 2 sDen]
          have hden_eq : den2 = (2 * sDen * 4096) * q := by
            dsimp only [den2]
            rw [Nat.mul_right_comm (2 * sDen) 4096 q, ← Nat.mul_assoc 2 (sDen * q) 4096, ← Nat.mul_assoc 2 sDen q]
          rw [hM_eq, hden_eq, Nat.mul_pow (sHi * 4096 + 2 * (2 * sDen)) q 123, Nat.mul_pow (2 * sDen * 4096) q 123]
          calc (sHi * 4096 + 2 * (2 * sDen)) ^ 123 * q ^ 123 * SCALE ^ 256
              = ((sHi * 4096 + 2 * (2 * sDen)) ^ 123 * SCALE ^ 256) * q ^ 123 := by ac_rfl
            _ ≤ ((pupEGrid sHi (2 * sDen) 2) ^ 256 * (2 * sDen * 4096) ^ 123) * q ^ 123 := Nat.mul_le_mul_right _ hp
            _ = (pupEGrid sHi (2 * sDen) 2) ^ 256 * ((2 * sDen * 4096) ^ 123 * q ^ 123) := by ac_rfl
        have hsum_u := pow123_concave_sum hden2_pos hM_pos hAB_le hu1' hu2' hM_ub
        have hprod := (prodUp_sound pw1 (pupEGrid sHi (2 * sDen) 2)).1
        calc pw1 * u1 + pw1 * u2 = pw1 * (u1 + u2) := (Nat.mul_add _ _ _).symm
          _ ≤ pw1 * (2 * pupEGrid sHi (2 * sDen) 2) := Nat.mul_le_mul_left pw1 hsum_u
          _ = 2 * (pw1 * pupEGrid sHi (2 * sDen) 2) := by ac_rfl
          _ ≤ 2 * (prodUpD pw1 (pupEGrid sHi (2 * sDen) 2) * SCALE) := Nat.mul_le_mul_left 2 hprod
          _ = 2 * prodUpD pw1 (pupEGrid sHi (2 * sDen) 2) * SCALE := by ac_rfl
    · simp only [↓reduceIte]
      have hu1_le : u1 ≤ pupEGrid h1m sDen 2 := by
        apply u_le_pupEGrid u1 t1 h1m sDen hsDen hu1
        calc t1 * sDen = sDen * t1 := Nat.mul_comm _ _
          _ ≤ sDen * (h1m * q) := Nat.mul_le_mul_left sDen ht1_m
          _ = h1m * (sDen * q) := by ac_rfl
      have hu2_le : u2 ≤ pupEGrid h2m sDen 2 := by
        apply u_le_pupEGrid u2 t2 h2m sDen hsDen hu2
        calc t2 * sDen = sDen * t2 := Nat.mul_comm _ _
          _ ≤ sDen * (h2m * q) := Nat.mul_le_mul_left sDen ht2_m
          _ = h2m * (sDen * q) := by ac_rfl
      exact prod_add_le _ _ hu1_le hu2_le

/-- **Factored 2-Variable AM-GM Soundness for Orbit `1110`:**
Justifies the `aMax`/`bMax` decoupling `pw0 * ph0 ≤ ((pw0^2)/(2*pu1))*pv1 + pu1*((ph0^2)/(2*pv1))`
in exact integer arithmetic (including ceiling division and the `+1` rounding margin in `checkLeaf1110`). -/
theorem factored_amgm_1110_sound {pw0 ph0 pw10 ph01 pu1 pv1 aMax bMax : Nat}
    (hpu : 0 < pu1) (hpv : 0 < pv1)
    (ha : pw10 + (pw0 * pw0 + 2 * pu1 - 1) / (2 * pu1) ≤ aMax)
    (hb : ph01 + (ph0 * ph0 + 2 * pv1 - 1) / (2 * pv1) ≤ bMax) :
    pw0 * ph0 + pw10 * pv1 + pu1 * ph01 ≤ aMax * pv1 + pu1 * bMax ∧
    pw0 * ph0 + pw10 * pv1 + pu1 * ph01 ≤ (prodUpD aMax pv1 + prodUpD pu1 bMax) * SCALE ∧
    prodUpD pw0 ph0 * SCALE + pw10 * pv1 + pu1 * ph01 ≤ (prodUpD aMax pv1 + prodUpD pu1 bMax + 1) * SCALE := by
  let qA := (pw0 * pw0 + 2 * pu1 - 1) / (2 * pu1)
  let qB := (ph0 * ph0 + 2 * pv1 - 1) / (2 * pv1)
  have hqA : pw0 * pw0 ≤ qA * (2 * pu1) := ceil_div_mul_ge (pw0 * pw0) (2 * pu1) (by omega)
  have hqB : ph0 * ph0 ≤ qB * (2 * pv1) := ceil_div_mul_ge (ph0 * ph0) (2 * pv1) (by omega)
  have h2xy : ∀ x y : Nat, 2 * x * y ≤ x * x + y * y := by
    intro x y
    have h := amgm_2 x y
    have hexp : (x + y) ^ 2 = x * x + 2 * (x * y) + y * y := by
      rw [Nat.pow_two, Nat.mul_add, Nat.add_mul, Nat.add_mul]
      have hc : y * x = x * y := Nat.mul_comm y x
      omega
    have h2 : 2 * x * y = 2 * (x * y) := Nat.mul_assoc 2 x y
    have h4 : 4 * x * y = 4 * (x * y) := Nat.mul_assoc 4 x y
    rw [hexp, h4] at h
    omega
  have hcore : pw0 * ph0 ≤ qA * pv1 + pu1 * qB := by
    have hxy := h2xy (pw0 * pv1) (ph0 * pu1)
    have hL : 2 * (pw0 * pv1) * (ph0 * pu1) = (pw0 * ph0) * (2 * pu1 * pv1) := by ac_rfl
    have hR1 : (pw0 * pv1) * (pw0 * pv1) ≤ (qA * pv1) * (2 * pu1 * pv1) := by
      calc (pw0 * pv1) * (pw0 * pv1) = (pw0 * pw0) * (pv1 * pv1) := by ac_rfl
        _ ≤ (qA * (2 * pu1)) * (pv1 * pv1) := Nat.mul_le_mul_right _ hqA
        _ = (qA * pv1) * (2 * pu1 * pv1) := by ac_rfl
    have hR2 : (ph0 * pu1) * (ph0 * pu1) ≤ (pu1 * qB) * (2 * pu1 * pv1) := by
      calc (ph0 * pu1) * (ph0 * pu1) = (ph0 * ph0) * (pu1 * pu1) := by ac_rfl
        _ ≤ (qB * (2 * pv1)) * (pu1 * pu1) := Nat.mul_le_mul_right _ hqB
        _ = (pu1 * qB) * (2 * pu1 * pv1) := by ac_rfl
    have htot : (pw0 * ph0) * (2 * pu1 * pv1) ≤ (qA * pv1 + pu1 * qB) * (2 * pu1 * pv1) := by
      rw [← hL, Nat.add_mul]
      exact Nat.le_trans hxy (Nat.add_le_add hR1 hR2)
    exact Nat.le_of_mul_le_mul_right htot (Nat.mul_pos (Nat.mul_pos (by decide) hpu) hpv)
  have h1 : pw0 * ph0 + pw10 * pv1 + pu1 * ph01 ≤ aMax * pv1 + pu1 * bMax := by
    have hA : (pw10 + qA) * pv1 ≤ aMax * pv1 := Nat.mul_le_mul_right pv1 ha
    have hB : pu1 * (ph01 + qB) ≤ pu1 * bMax := Nat.mul_le_mul_left pu1 hb
    rw [Nat.add_mul] at hA
    rw [Nat.mul_add] at hB
    omega
  have h2 : pw0 * ph0 + pw10 * pv1 + pu1 * ph01 ≤ (prodUpD aMax pv1 + prodUpD pu1 bMax) * SCALE := by
    rw [Nat.add_mul]
    exact Nat.le_trans h1 (Nat.add_le_add (prodUp_sound aMax pv1).1 (prodUp_sound pu1 bMax).1)
  have h3 : prodUpD pw0 ph0 * SCALE + pw10 * pv1 + pu1 * ph01 ≤ (prodUpD aMax pv1 + prodUpD pu1 bMax + 1) * SCALE := by
    have hup : prodUpD pw0 ph0 * SCALE ≤ pw0 * ph0 + SCALE := by
      unfold prodUpD
      have h1 : ((pw0 * ph0 + SCALE - 1) / SCALE) * SCALE ≤ pw0 * ph0 + SCALE - 1 := by
        rw [Nat.mul_comm]; exact Nat.mul_div_le _ _
      exact Nat.le_trans h1 (Nat.sub_le _ 1)
    rw [Nat.add_mul, Nat.one_mul]
    calc prodUpD pw0 ph0 * SCALE + pw10 * pv1 + pu1 * ph01
        ≤ (pw0 * ph0 + SCALE) + pw10 * pv1 + pu1 * ph01 :=
            Nat.add_le_add_right (Nat.add_le_add_right hup _) _
      _ = (pw0 * ph0 + pw10 * pv1 + pu1 * ph01) + SCALE := by ac_rfl
      _ ≤ (prodUpD aMax pv1 + prodUpD pu1 bMax) * SCALE + SCALE := Nat.add_le_add_right h2 SCALE
  exact ⟨h1, h2, h3⟩

private theorem maxFactoredAMGM_ge (u1h dUw pu1 : Nat) :
    ∀ (k best : Nat),
      best ≤ maxFactoredAMGM u1h dUw pu1 k best ∧
      ∀ kw, kw < k →
        let pw0 := pupEGrid (u1h * (kw + 1)) dUw 2
        let pw10 := pupEGrid (dUw - 3 * u1h * kw) (3 * dUw) 0
        pw10 + (pw0 * pw0 + 2 * pu1 - 1) / (2 * pu1) ≤ maxFactoredAMGM u1h dUw pu1 k best
  | 0, best => ⟨Nat.le_refl _, fun _ h => by omega⟩
  | kw' + 1, best => by
    unfold maxFactoredAMGM
    dsimp only
    let pw0 := pupEGrid (u1h * (kw' + 1)) dUw 2
    let pw10 := pupEGrid (dUw - 3 * u1h * kw') (3 * dUw) 0
    let v := pw10 + (pw0 * pw0 + 2 * pu1 - 1) / (2 * pu1)
    have ih := maxFactoredAMGM_ge u1h dUw pu1 kw' (natMax best v)
    refine ⟨Nat.le_trans (natMax_le_left_le (Nat.le_refl best)) ih.1, ?_⟩
    intro kw hkw
    by_cases heq : kw = kw'
    · subst heq; exact Nat.le_trans (natMax_le_right_le (Nat.le_refl v)) ih.1
    · exact ih.2 kw (by omega)

/-- **Semantic Soundness of `maxFactoredAMGM`:**
For any `0 < dU`, `0 < kwS`, `0 < q`, and `t ≤ u1h * q`, there exists a subinterval `kw < kwS`
whose grid bounds `(pw0, pw10)` soundly upper-bound `(t/(dU*q) + 2/4096)^(123/256)` and
`(1/3 - t/(dU*q))^(123/256)` AND whose factored AM-GM score is `≤ maxFactoredAMGM u1h (dU * kwS) pu1 kwS 0`. -/
theorem maxFactoredAMGM_sound (u1h dU kwS pu1 t q : Nat)
    (hdU : 0 < dU) (hkwS : 0 < kwS) (hq : 0 < q) (ht : t ≤ u1h * q) :
    ∃ kw, kw < kwS ∧
      let dUw := dU * kwS
      let pw0 := pupEGrid (u1h * (kw + 1)) dUw 2
      let pw10 := pupEGrid (dUw - 3 * u1h * kw) (3 * dUw) 0
      (t * 4096 + 2 * dU * q) ^ 123 * SCALE ^ 256 ≤ pw0 ^ 256 * (dU * q * 4096) ^ 123 ∧
      (dU * q - 3 * t) ^ 123 * SCALE ^ 256 ≤ pw10 ^ 256 * (3 * dU * q) ^ 123 ∧
      pw10 + (pw0 * pw0 + 2 * pu1 - 1) / (2 * pu1) ≤ maxFactoredAMGM u1h dUw pu1 kwS 0 := by
  let dUw := dU * kwS
  have hdUw : 0 < dUw := Nat.mul_pos hdU hkwS
  by_cases hu0 : u1h = 0
  · subst hu0
    have ht0 : t = 0 := by omega
    subst ht0
    refine ⟨0, hkwS, ?_, ?_, (maxFactoredAMGM_ge 0 dUw pu1 kwS 0).2 0 hkwS⟩
    · have hp := pupEGrid_sound 0 dUw 2 hdUw
      have hrat : (0 * 4096 + 2 * dU * q) * (dUw * 4096) ≤ (0 * 4096 + 2 * dUw) * (dU * q * 4096) := by
        simp only [Nat.zero_mul, Nat.zero_add]; exact Nat.le_of_eq (by ac_rfl)
      simpa using pow123_ub_mono (Nat.mul_pos hdUw (by decide)) hrat hp
    · have hp := pupEGrid_sound dUw (3 * dUw) 0 (Nat.mul_pos (by decide) hdUw)
      have hrat : (dU * q) * (3 * dUw * 4096) ≤ (dUw * 4096 + 0 * (3 * dUw)) * (3 * dU * q) := by
        simp only [Nat.zero_mul, Nat.add_zero]; exact Nat.le_of_eq (by ac_rfl)
      simpa using pow123_ub_mono (Nat.mul_pos (Nat.mul_pos (by decide) hdUw) (by decide)) hrat hp
  · have hu_pos : 0 < u1h := by omega
    let denK := u1h * q
    have hdenK : 0 < denK := Nat.mul_pos hu_pos hq
    let kw := min (kwS - 1) ((t * kwS) / denK)
    have hkw_lt : kw < kwS := by dsimp only [kw]; omega
    have hkw_lo : kw * denK ≤ t * kwS := by
      have h1 := Nat.mul_le_mul_right denK (Nat.min_le_right (kwS - 1) ((t * kwS) / denK))
      have h2 : ((t * kwS) / denK) * denK ≤ t * kwS := by rw [Nat.mul_comm]; exact Nat.mul_div_le _ _
      exact Nat.le_trans h1 h2
    have hkw_hi : t * kwS ≤ (kw + 1) * denK := by
      dsimp only [kw]
      by_cases hc : (t * kwS) / denK ≤ kwS - 1
      · rw [Nat.min_eq_right hc]
        have hdm := Nat.div_add_mod (t * kwS) denK
        have hmod := Nat.mod_lt (t * kwS) hdenK
        rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm _ denK]
        omega
      · rw [Nat.min_eq_left (by omega)]
        have h1 : kwS - 1 + 1 = kwS := by omega
        rw [h1]
        exact Nat.mul_le_mul_right kwS ht |> fun hm => by
          calc t * kwS ≤ (u1h * q) * kwS := hm
            _ = kwS * denK := by dsimp only [denK]; ac_rfl
    refine ⟨kw, hkw_lt, ?_, ?_, (maxFactoredAMGM_ge u1h dUw pu1 kwS 0).2 kw hkw_lt⟩
    · have hrat : (t * 4096 + 2 * dU * q) * (dUw * 4096) ≤
                  (u1h * (kw + 1) * 4096 + 2 * dUw) * (dU * q * 4096) := by
        rw [Nat.add_mul, Nat.add_mul]
        have h1 : t * 4096 * (dUw * 4096) ≤ u1h * (kw + 1) * 4096 * (dU * q * 4096) := by
          calc t * 4096 * (dUw * 4096) = (t * kwS) * (dU * 4096 * 4096) := by dsimp only [dUw]; ac_rfl
            _ ≤ ((kw + 1) * denK) * (dU * 4096 * 4096) := Nat.mul_le_mul_right _ hkw_hi
            _ = u1h * (kw + 1) * 4096 * (dU * q * 4096) := by dsimp only [denK]; ac_rfl
        have h2 : 2 * dU * q * (dUw * 4096) = 2 * dUw * (dU * q * 4096) := by ac_rfl
        exact Nat.add_le_add h1 (Nat.le_of_eq h2)
      exact pow123_ub_mono (Nat.mul_pos hdUw (by decide)) hrat (pupEGrid_sound (u1h * (kw + 1)) dUw 2 hdUw)
    · by_cases hzero : dU * q ≤ 3 * t
      · have hsub0 : dU * q - 3 * t = 0 := by omega
        rw [hsub0]; simp
      · have hsub_le : (dU * q - 3 * t) * (3 * dUw * 4096) ≤
                       ((dUw - 3 * u1h * kw) * 4096 + 0 * (3 * dUw)) * (3 * dU * q) := by
          simp only [Nat.zero_mul, Nat.add_zero]
          have hcore : (dU * q - 3 * t) * kwS ≤ (dUw - 3 * u1h * kw) * q := by
            have h3 : 3 * u1h * kw * q ≤ 3 * t * kwS := by
              calc 3 * u1h * kw * q = 3 * (kw * denK) := by dsimp only [denK]; ac_rfl
                _ ≤ 3 * (t * kwS) := Nat.mul_le_mul_left 3 hkw_lo
                _ = 3 * t * kwS := by ac_rfl
            rw [Nat.sub_mul, Nat.sub_mul]
            have heq : dU * q * kwS = dUw * q := by dsimp only [dUw]; ac_rfl
            rw [heq]; omega
          calc (dU * q - 3 * t) * (3 * dUw * 4096)
              = ((dU * q - 3 * t) * kwS) * (3 * dU * 4096) := by dsimp only [dUw]; ac_rfl
            _ ≤ ((dUw - 3 * u1h * kw) * q) * (3 * dU * 4096) := Nat.mul_le_mul_right _ hcore
            _ = (dUw - 3 * u1h * kw) * 4096 * (3 * dU * q) := by ac_rfl
        exact pow123_ub_mono (Nat.mul_pos (Nat.mul_pos (by decide) hdUw) (by decide)) hsub_le
          (pupEGrid_sound (dUw - 3 * u1h * kw) (3 * dUw) 0 (Nat.mul_pos (by decide) hdUw))

private theorem checkAMax256Tree_sound :
    ∀ (d start : Nat), checkAMax256Tree start d = true →
      ∀ idx, start ≤ idx → idx < start + 2 ^ d → 1 ≤ idx → idx ≤ 86 →
        let pu1 := gridUp2048Tree.get (8 * idx + 1)
        0 < pu1 ∧ pu1 = pupEGrid idx 256 2 ∧ aMax256Tree.get idx = maxFactoredAMGM idx 2048 pu1 8 0
  | 0, start, h, idx, hlo, hhi, h1, h86 => by
    have heq : idx = start := by omega
    subst heq
    unfold checkAMax256Tree at h
    have hcond : (Nat.ble 1 idx && Nat.ble idx 86) = true := by
      rw [Nat.ble_eq_true_of_le h1, Nat.ble_eq_true_of_le h86]; rfl
    simp only [hcond, ↓reduceIte, Bool.and_eq_true, beq_iff_eq] at h
    have hpos : 0 < gridUp2048Tree.get (8 * idx + 1) := by
      have := Nat.le_of_ble_eq_true h.1.1; omega
    exact ⟨hpos, h.1.2, h.2⟩
  | d + 1, start, h, idx, hlo, hhi, h1, h86 => by
    unfold checkAMax256Tree at h
    dsimp only at h
    cases hl : checkAMax256Tree start d
    · rw [hl] at h; cases h
    · rw [hl] at h; simp only [↓reduceIte] at h
      have hpow : 2 ^ (d + 1) = 2 ^ d + 2 ^ d := by rw [Nat.pow_succ]; omega
      by_cases hmid : idx < start + 2 ^ d
      · exact checkAMax256Tree_sound d start hl idx hlo hmid h1 h86
      · exact checkAMax256Tree_sound d (start + 2 ^ d) h idx (by omega) (by omega) h1 h86

/-- **Semantic Soundness of the Precomputed `aMax256Tree` Table (`idx ∈ 1..86`):**
For EVERY `idx ∈ 1..86` and EVERY `w0 = t / q ≤ idx / 256` (`0 < q`), the cached `pu1` and
`aMax256Tree.get idx` soundly upper-bound `(idx/256 + 2/4096)^(123/256)` and the factored
AM-GM objective over `[0, idx/256]`. -/
theorem aMax256_sound (idx t q : Nat) (h1 : 1 ≤ idx) (h86 : idx ≤ 86) (hq : 0 < q) (ht : t * 256 ≤ idx * q) :
    let pu1 := gridUp2048Tree.get (8 * idx + 1)
    0 < pu1 ∧
    pu1 = pupEGrid idx 256 2 ∧
    ∃ kw, kw < 8 ∧
      let pw0 := pupEGrid (idx * (kw + 1)) 2048 2
      let pw10 := pupEGrid (2048 - 3 * idx * kw) (3 * 2048) 0
      (t * 4096 + 2 * q) ^ 123 * SCALE ^ 256 ≤ pw0 ^ 256 * (q * 4096) ^ 123 ∧
      (q - 3 * t) ^ 123 * SCALE ^ 256 ≤ pw10 ^ 256 * (3 * q) ^ 123 ∧
      pw10 + (pw0 * pw0 + 2 * pu1 - 1) / (2 * pu1) ≤ aMax256Tree.get idx := by
  have hcert := checkAMax256Tree_sound 7 0 aMax256_certified idx (Nat.zero_le idx) (by omega) h1 h86
  rcases hcert with ⟨hpos, hpu_eq, ha_eq⟩
  refine ⟨hpos, hpu_eq, ?_⟩
  rcases maxFactoredAMGM_sound idx 256 8 (gridUp2048Tree.get (8 * idx + 1)) (t * 256) q
      (by decide) (by decide) hq ht with ⟨kw, hkw, hpw0, hpw10, hmax⟩
  refine ⟨kw, hkw, ?_, ?_, ha_eq ▸ hmax⟩
  · have hmul : (t * 4096 + 2 * q) * 256 = t * 256 * 4096 + 2 * 256 * q := by
      rw [Nat.add_mul, Nat.mul_right_comm t 4096 256, Nat.mul_right_comm 2 q 256]
    have hden : (q * 4096) * 256 = 256 * q * 4096 := by
      rw [Nat.mul_right_comm q 4096 256, Nat.mul_comm q 256]
    have hpow := hpw0
    rw [← hmul, ← hden, Nat.mul_pow, Nat.mul_pow] at hpow
    have hc : (t * 4096 + 2 * q) ^ 123 * SCALE ^ 256 * 256 ^ 123 ≤
              (pupEGrid (idx * (kw + 1)) 2048 2) ^ 256 * (q * 4096) ^ 123 * 256 ^ 123 := by
      calc (t * 4096 + 2 * q) ^ 123 * SCALE ^ 256 * 256 ^ 123
          = (t * 4096 + 2 * q) ^ 123 * 256 ^ 123 * SCALE ^ 256 := by ac_rfl
        _ ≤ (pupEGrid (idx * (kw + 1)) 2048 2) ^ 256 * ((q * 4096) ^ 123 * 256 ^ 123) := hpow
        _ = (pupEGrid (idx * (kw + 1)) 2048 2) ^ 256 * (q * 4096) ^ 123 * 256 ^ 123 := by ac_rfl
    exact Nat.le_of_mul_le_mul_right hc (Nat.pow_pos (by decide : 0 < 256))
  · have hmul : (q - 3 * t) * 256 = 256 * q - 3 * (t * 256) := by
      rw [Nat.sub_mul, Nat.mul_comm q 256, Nat.mul_assoc]
    have hden : (3 * q) * 256 = 3 * 256 * q := Nat.mul_right_comm 3 q 256
    have hpow := hpw10
    rw [← hmul, ← hden, Nat.mul_pow, Nat.mul_pow] at hpow
    have hc : (q - 3 * t) ^ 123 * SCALE ^ 256 * 256 ^ 123 ≤
              (pupEGrid (2048 - 3 * idx * kw) (3 * 2048) 0) ^ 256 * (3 * q) ^ 123 * 256 ^ 123 := by
      calc (q - 3 * t) ^ 123 * SCALE ^ 256 * 256 ^ 123
          = (q - 3 * t) ^ 123 * 256 ^ 123 * SCALE ^ 256 := by ac_rfl
        _ ≤ (pupEGrid (2048 - 3 * idx * kw) (3 * 2048) 0) ^ 256 * ((3 * q) ^ 123 * 256 ^ 123) := hpow
        _ = (pupEGrid (2048 - 3 * idx * kw) (3 * 2048) 0) ^ 256 * (3 * q) ^ 123 * 256 ^ 123 := by ac_rfl
    exact Nat.le_of_mul_le_mul_right hc (Nat.pow_pos (by decide : 0 < 256))

/-- **`379,133`-Weighted Tangent Majorant Soundness for Orbit `1111`:**
At the midpoint `M` (`A + B ≤ 2 * M`, `0 < M`), for any weights `wj ≤ wi`, the linear tangent
majorant `u * 256 * M ≤ (123 * X + 133 * M) * pM` (proved from `amgm_256`) implies
`wi * u1 + wj * u2 ≤ ((379 * wi + 133 * wj + 255) / 256) * pM ≤ prodUpD ((379 * wi + 133 * wj + 255) / 256) pM * SCALE`!
Here `379 = 2 * 123 + 133` and `133 = 133` (`379 + 133 = 512 = 2 * 256`). -/
theorem weighted_tangent_379_133_sound {wi wj u1 u2 A B M pM den : Nat}
    (hden : 0 < den) (hMpos : 0 < M) (hw : wj ≤ wi) (hsum : A + B ≤ 2 * M)
    (hu1 : u1 ^ 256 * den ^ 123 ≤ A ^ 123 * SCALE ^ 256)
    (hu2 : u2 ^ 256 * den ^ 123 ≤ B ^ 123 * SCALE ^ 256)
    (hM : M ^ 123 * SCALE ^ 256 ≤ pM ^ 256 * den ^ 123) :
    wi * u1 + wj * u2 ≤ ((379 * wi + 133 * wj + 255) / 256) * pM ∧
    wi * u1 + wj * u2 ≤ prodUpD ((379 * wi + 133 * wj + 255) / 256) pM * SCALE := by
  have ht1 := pow123_tangent_linear hden hu1 hM
  have ht2 := pow123_tangent_linear hden hu2 hM
  have hABw : wi * A + wj * B ≤ 2 * wi * M := by
    have h1 : wj * B ≤ wi * B := Nat.mul_le_mul_right B hw
    have h2 : wi * A + wi * B = wi * (A + B) := (Nat.mul_add wi A B).symm
    have h3 : wi * (A + B) ≤ wi * (2 * M) := Nat.mul_le_mul_left wi hsum
    have h4 : wi * (2 * M) = 2 * wi * M := by ac_rfl
    omega
  have hlin : wi * (123 * A + 133 * M) + wj * (123 * B + 133 * M) ≤ (379 * wi + 133 * wj) * M := by
    rw [Nat.mul_add, Nat.mul_add, Nat.add_mul]
    have h1 : wi * (123 * A) + wj * (123 * B) = 123 * (wi * A + wj * B) := by
      rw [Nat.mul_add]; congr 1 <;> ac_rfl
    have h2 : 123 * (wi * A + wj * B) ≤ 123 * (2 * wi * M) := Nat.mul_le_mul_left 123 hABw
    have h3 : 123 * (2 * wi * M) = 246 * wi * M := by ac_rfl
    have h4 : wi * (133 * M) = 133 * wi * M := by ac_rfl
    have h5 : wj * (133 * M) = 133 * wj * M := by ac_rfl
    have h6 : 246 * wi * M + 133 * wi * M = 379 * wi * M := by
      rw [← Nat.add_mul, ← Nat.add_mul]
    omega
  have h256M : (wi * u1 + wj * u2) * 256 * M ≤ (379 * wi + 133 * wj) * pM * M := by
    calc (wi * u1 + wj * u2) * 256 * M
        = wi * (u1 * 256 * M) + wj * (u2 * 256 * M) := by
            rw [Nat.add_mul, Nat.add_mul]; congr 1 <;> ac_rfl
      _ ≤ wi * ((123 * A + 133 * M) * pM) + wj * ((123 * B + 133 * M) * pM) :=
            Nat.add_le_add (Nat.mul_le_mul_left wi ht1) (Nat.mul_le_mul_left wj ht2)
      _ = (wi * (123 * A + 133 * M) + wj * (123 * B + 133 * M)) * pM := by
            rw [← Nat.mul_assoc, ← Nat.mul_assoc, ← Nat.add_mul]
      _ ≤ ((379 * wi + 133 * wj) * M) * pM := Nat.mul_le_mul_right pM hlin
      _ = (379 * wi + 133 * wj) * pM * M := by ac_rfl
  have h256 := Nat.le_of_mul_le_mul_right h256M hMpos
  have hceil : 379 * wi + 133 * wj ≤ ((379 * wi + 133 * wj + 255) / 256) * 256 :=
    ceil_div_mul_ge (379 * wi + 133 * wj) 256 (by decide)
  have hmain : wi * u1 + wj * u2 ≤ ((379 * wi + 133 * wj + 255) / 256) * pM := by
    have hm : (wi * u1 + wj * u2) * 256 ≤ (((379 * wi + 133 * wj + 255) / 256) * pM) * 256 := by
      calc (wi * u1 + wj * u2) * 256 ≤ (379 * wi + 133 * wj) * pM := h256
        _ ≤ (((379 * wi + 133 * wj + 255) / 256) * 256) * pM := Nat.mul_le_mul_right pM hceil
        _ = (((379 * wi + 133 * wj + 255) / 256) * pM) * 256 := by ac_rfl
    exact Nat.le_of_mul_le_mul_right hm (by decide)
  exact ⟨hmain, Nat.le_trans hmain (prodUp_sound _ pM).1⟩

/-- **Soundness of `maxTangentForSum`:** every evaluated index `i ∈ [i0, i0 + steps)` has its
`379,133`-weighted tangent bound dominated by `maxTangentForSum pws s steps i0 best`. -/
theorem maxTangentForSum_sound (pws : List Nat) (s : Nat) :
    ∀ (steps i0 best : Nat),
      best ≤ maxTangentForSum pws s steps i0 best ∧
      ∀ i, i0 ≤ i → i < i0 + steps →
        (379 * listGetD pws i + 133 * listGetD pws (s - i) + 255) / 256 ≤
          maxTangentForSum pws s steps i0 best
  | 0, _, best => ⟨Nat.le_refl _, fun _ h1 h2 => by omega⟩
  | steps + 1, i0, best => by
    unfold maxTangentForSum
    dsimp only
    let v := (379 * listGetD pws i0 + 133 * listGetD pws (s - i0) + 255) / 256
    have ih := maxTangentForSum_sound pws s steps (i0 + 1) (natMax best v)
    refine ⟨Nat.le_trans (natMax_le_left_le (Nat.le_refl best)) ih.1, ?_⟩
    intro i hlo hhi
    by_cases heq : i = i0
    · subst heq; exact Nat.le_trans (natMax_le_right_le (Nat.le_refl v)) ih.1
    · exact ih.2 i (by omega) (by omega)

/-! ## 7. Exact Threshold Collapse (`M0 = 2^57`, Sharp at `2^56`) & R15 Ratio Check -/

private theorem threshold_collapse_base :
    (34 * 3) ^ 128 * (2 * 2 ^ 57 + 3) ^ 123 < (3 * 5) ^ 128 * 3 ^ 123 * (2 ^ 57) ^ 128 := by
  decide

private theorem threshold_collapse_mono {A B M0 M : Nat} (hM0_pos : 0 < M0) (hM : M0 ≤ M)
    (hbase : A * (2 * M0 + 3) ^ 123 < B * M0 ^ 128) :
    A * (2 * M + 3) ^ 123 < B * M ^ 128 := by
  have hlin : (2 * M + 3) * M0 ≤ (2 * M0 + 3) * M := by
    rw [Nat.add_mul, Nat.add_mul]
    have h2 : 2 * M * M0 = 2 * M0 * M := by ac_rfl
    omega
  have h123 : (2 * M + 3) ^ 123 * M0 ^ 123 ≤ (2 * M0 + 3) ^ 123 * M ^ 123 := by
    rw [← Nat.mul_pow, ← Nat.mul_pow]
    exact Nat.pow_le_pow_left hlin 123
  have h5 : M0 ^ 5 ≤ M ^ 5 := Nat.pow_le_pow_left hM 5
  have h128 : (2 * M + 3) ^ 123 * M0 ^ 128 ≤ (2 * M0 + 3) ^ 123 * M ^ 128 := by
    have hcomb := Nat.mul_le_mul h123 h5
    have hM0 : M0 ^ 123 * M0 ^ 5 = M0 ^ 128 := by rw [← Nat.pow_add]
    have hMM : M ^ 123 * M ^ 5 = M ^ 128 := by rw [← Nat.pow_add]
    calc (2 * M + 3) ^ 123 * M0 ^ 128
        = (2 * M + 3) ^ 123 * M0 ^ 123 * M0 ^ 5 := by rw [← hM0]; ac_rfl
      _ ≤ (2 * M0 + 3) ^ 123 * M ^ 123 * M ^ 5 := hcomb
      _ = (2 * M0 + 3) ^ 123 * M ^ 128 := by rw [← hMM]; ac_rfl
  have hlt : A * (2 * M + 3) ^ 123 * M0 ^ 128 < B * M ^ 128 * M0 ^ 128 := by
    calc A * (2 * M + 3) ^ 123 * M0 ^ 128
        = A * ((2 * M + 3) ^ 123 * M0 ^ 128) := by ac_rfl
      _ ≤ A * ((2 * M0 + 3) ^ 123 * M ^ 128) := Nat.mul_le_mul_left _ h128
      _ = (A * (2 * M0 + 3) ^ 123) * M ^ 128 := by ac_rfl
      _ < (B * M0 ^ 128) * M ^ 128 :=
          Nat.mul_lt_mul_of_pos_right hbase (Nat.pow_pos (Nat.lt_of_lt_of_le hM0_pos hM))
      _ = B * M ^ 128 * M0 ^ 128 := by ac_rfl
  exact Nat.lt_of_mul_lt_mul_right hlt

/-- **Universal Threshold Collapse Theorem (ALL `M ≥ 2^57`):**
For EVERY `M ≥ 2^57`, `(34 * 3)^128 * (2 * M + 3)^123 < (3 * 5)^128 * 3^123 * M^128`. -/
theorem threshold_collapse_all_ge_2pow57 (M : Nat) (hM : M ≥ 2 ^ 57) :
    (34 * 3) ^ 128 * (2 * M + 3) ^ 123 < (3 * 5) ^ 128 * 3 ^ 123 * M ^ 128 :=
  threshold_collapse_mono (A := (34 * 3) ^ 128) (B := (3 * 5) ^ 128 * 3 ^ 123) (M0 := 2 ^ 57)
    (by decide) hM threshold_collapse_base

/-- **Sharpness of Threshold Collapse at `M = 2^56`:** -/
theorem threshold_collapse_sharp_2pow56 :
    (34 * 3) ^ 128 * (2 * 2 ^ 56 + 3) ^ 123 > (3 * 5) ^ 128 * 3 ^ 123 * (2 ^ 56) ^ 128 := by
  decide

/-- **R15 Ratio Check:** `3^256 * 8^123 < 5^256 * 3^124`. -/
theorem r15_ratio_check : 3 ^ 256 * 8 ^ 123 < 5 ^ 256 * 3 ^ 124 := by
  decide

end ClawFreeEG
