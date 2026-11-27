import ClawFreeEG.LiftWindows
import ClawFreeEG.DyadicPackingData
import ClawFreeEG.DyadicPacking2D
import ClawFreeEG.TwoCycleData
import ClawFreeEG.TwoCycleClosure
import ClawFreeEG.PolyKData

/-!
# ClawFreeEG.PolyKAndSublinear

Pure Lean 4 (`v4.36.0`, ZERO Mathlib, ZERO `Std`, ZERO `sorry`, ZERO `axiom`,
ZERO `native_decide`, ZERO `unsafe`/`implemented_by`/`extern`/`partial`) formalization &
kernel verification for the arithmetic & certificate closure components of Main Theorem 3
(Universal Poly-`k`-Cycle, Sublinear `o(n)` Circumference with R19 `+2m` Endpoint Pruning,
Equal-Block `k = 3, 4, 5` Rational Box Certificates, and R5 Sturmian & Matching-Complement
Assembly):

1. **2-Arc Partition & Pairwise Bridge Bounds (`2×2` and `1×2`):**
   - Zero-wraparound 2-arc partition on any cycle of length `x ≥ 3` (`two_arc_partition_zero_wraparound`),
   - Exact `1×2` sub-path-to-cycle bridge bound `5^128 * r^128 ≤ 6^128 * (y + 2)^123`,
   - Exact `2×2` cycle-to-cycle bridge bound `5^128 * r^128 ≤ 12^128 * (y + 2)^123`
     (exact integer form of `r(C_1, C_2) ≤ (12/5) * (y + 2)^(123/128)`),
   - Path-splitting sub-path count bound `y * ∑ ⌈L_j / (⌊y/2⌋ + 1)⌉ ≤ m * y + 2 * ∑ L_j`.
2. **Universal Poly-`k`-Cycle & Sublinear `o(n)` Circumference Arithmetic (with R19 `+2m` Pruning):**
   - Sharp universal threshold `y_0 = 2^97` (sharp at `2^96`) and exact sharp fixed-`k`
     exponents `k ∈ {2, 3, 4, 5, 10}` (`97, 122, 137, 148, 178`),
   - Universal `k`-cycle arithmetic closure for ALL `k ≥ 2` with `k ≤ (n / 2^97)^(5/133)`
     (exact integer form `(2^97)^5 * k^133 ≤ n^5`),
   - Complete `m`-path complement-cover arithmetic closure with R19 `+2m` endpoint pruning for
     ALL `m ≥ 1` with `y ≥ max(2^97 * m^(128/5), 25 * n^(128/133))` (exact integer forms
     `(2^97)^5 * m^128 ≤ y^5` and `25^133 * n^128 ≤ y^133`). Here `n = |V(H)|` is the order
     of the cubic triangle quotient `H`, `y = |V(C)|` is the length of a longest cycle `C` in `H`,
     and `m` is the number of vertex-disjoint paths covering `H - V(C)`. For fixed `m` (or any
     `m = o(n^(5/128))`), the threshold `max(2^97 * m^(128/5), 25 * n^(128/133))` is `o(n)`, and
     transfers between simple `H` and `G = T(H)` via `|V(G)| = 3*n` and `2*c(H) ≤ c(G) ≤ 3*c(H)`
     (every cycle of `G` meeting external edges uses an even number—hence `2`—of external edges
     per visited triangle and projects to a simple cycle of `H`).
3. **Equal-Block `k = 3, 4, 5` Rational Box Certificates (`17 + 17 + 16 = 50` Boxes):**
   - Kernel-verified 4-regime domain coverage AND exact integer-to-rational scaling bridge for
     ALL `M ≥ 2^36` (`k = 3`, `17` boxes), ALL `M ≥ 2^51` (`k = 4`, `17` boxes), and
     ALL `M ≥ 2^62` (`k = 5`, `16` boxes).
4. **R5 Sturmian, Bipartite `15/16`, & Matching-Complement `ℓ`-Cancellation Assembly.**

*Transparent scope boundary (Layer 4):* Graph-level bridge encodings, R5 attachment counts,
path-pruning endpoint accounting on original paths, and cycle lifting from `H` to `G = T(H)`
are proved in full rigor in the LaTeX manuscript.
-/

namespace ClawFreeEG

open ClawFreeEG.TwoCycleData
open ClawFreeEG.PolyKData

/-! ## 1. 2-Arc Partition, Sub-Path Splitting, & Pairwise Bridge Bounds (`1×2`, `2×2`) -/

/-- **2-Arc Partition Zero-Wraparound Lemma:**
Splitting a cycle `Fin x` (`x ≥ 3`) into the two arcs `[0, x/2)` and `[x/2, x)` guarantees that
for any two vertices `u, v` in the same arc, their linear distance `|u - v|` equals their cyclic
distance `min ((u + x - v) % x) ((v + x - u) % x)` and is at most `x / 2`; moreover `2*(x/2 + 1) > x`. -/
theorem two_arc_partition_zero_wraparound (x : Nat) (hx : x ≥ 3) :
    2 * (x / 2 + 1) > x ∧
    ∀ u v : Nat, u < x → v < x →
      ((u < x / 2 ∧ v < x / 2) ∨ (x / 2 ≤ u ∧ x / 2 ≤ v)) →
      absDiff u v ≤ x / 2 ∧
      absDiff u v = min ((u + x - v) % x) ((v + x - u) % x) := by
  refine ⟨by omega, ?_⟩
  intro u v hu hv harc
  unfold absDiff
  by_cases huv : u ≤ v
  · simp only [huv, ↓reduceIte]
    have hd : v - u ≤ x / 2 := by omega
    have h1 : (v + x - u) % x = v - u := by
      have heq : v + x - u = (v - u) + x := by omega
      rw [heq, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    by_cases heq : u = v
    · subst heq
      have h0 : (u + x - u) % x = 0 := by rw [Nat.add_sub_cancel_left, Nat.mod_self]
      rw [Nat.sub_self, h0, Nat.min_self]
      exact ⟨Nat.zero_le _, rfl⟩
    · have h2 : (u + x - v) % x = x - (v - u) := by
        have hlt : u + x - v < x := by omega
        rw [Nat.mod_eq_of_lt hlt]; omega
      rw [h1, h2]
      exact ⟨hd, by omega⟩
  · simp only [huv, ↓reduceIte]
    have hd : u - v ≤ x / 2 := by omega
    have h1 : (u + x - v) % x = u - v := by
      have heq : u + x - v = (u - v) + x := by omega
      rw [heq, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    have h2 : (v + x - u) % x = x - (u - v) := by
      have hlt : v + x - u < x := by omega
      rw [Nat.mod_eq_of_lt hlt]; omega
    rw [h1, h2]
    exact ⟨hd, by omega⟩

/-- Helper: `a^2 ≤ b^2 → a ≤ b` on `Nat`. -/
private theorem le_of_sq_le_sq {a b : Nat} (h : a ^ 2 ≤ b ^ 2) : a ≤ b := by
  by_cases hab : a ≤ b
  · exact hab
  · exfalso
    have hba : b < a := by omega
    have hsq : b ^ 2 < a ^ 2 := by
      rw [Nat.pow_two, Nat.pow_two]
      exact Nat.lt_of_le_of_lt (Nat.mul_le_mul_left b (Nat.le_of_lt hba))
        (Nat.mul_lt_mul_of_pos_right hba (by omega))
    omega

/-- Helper: strict monotonicity of `a ↦ a ^ d` for `d ≥ 1`. -/
private theorem pow_lt_pow_left' {a b d : Nat} (hd : 1 ≤ d) (h : a < b) : a ^ d < b ^ d := by
  induction d with
  | zero => omega
  | succ d' ih =>
    by_cases h0 : d' = 0
    · subst h0; simpa using h
    · rw [Nat.pow_succ, Nat.pow_succ]
      exact Nat.lt_of_le_of_lt (Nat.mul_le_mul_left (a ^ d') (Nat.le_of_lt h))
        (Nat.mul_lt_mul_of_pos_right (ih (by omega)) (by omega))

/-- Helper: `a^d ≤ b^d → a ≤ b` for any `d ≥ 1`. -/
private theorem le_of_pow_le_pow {a b d : Nat} (hd : 1 ≤ d) (h : a ^ d ≤ b ^ d) : a ≤ b := by
  by_cases hab : a ≤ b
  · exact hab
  · exfalso
    have hlt := pow_lt_pow_left' hd (by omega : b < a)
    omega

/-- Helper: `a^d < b^d → a < b` for any `d ≥ 1`. -/
private theorem lt_of_pow_lt_pow {a b d : Nat} (_hd : 1 ≤ d) (h : a ^ d < b ^ d) : a < b := by
  by_cases hab : a < b
  · exact hab
  · exfalso
    have hle : b ^ d ≤ a ^ d := Nat.pow_le_pow_left (by omega : b ≤ a) d
    omega

/-- **Square-Root Collapse of the 2D Packing Bound (`256 → 128`):**
If `s` satisfies the Main Theorem 1 packing bound on `[0, W1] × [0, W2]` with `W1 ≤ y` and `W2 ≤ y`,
then `5^128 * s^128 ≤ 3^128 * (y + 2)^123`. -/
theorem packing_bound_half_exponent {s W1 W2 y : Nat}
    (hpack : s ^ 256 * 5 ^ 256 ≤ 3 ^ 256 * ((W1 + 2) * (W2 + 2)) ^ 123)
    (h1 : W1 ≤ y) (h2 : W2 ≤ y) :
    5 ^ 128 * s ^ 128 ≤ 3 ^ 128 * (y + 2) ^ 123 := by
  apply le_of_sq_le_sq
  have hlhs : (5 ^ 128 * s ^ 128) ^ 2 = s ^ 256 * 5 ^ 256 := by
    rw [Nat.mul_pow, ← Nat.pow_mul, ← Nat.pow_mul]
    ac_rfl
  have hrhs : (3 ^ 128 * (y + 2) ^ 123) ^ 2 = 3 ^ 256 * ((y + 2) * (y + 2)) ^ 123 := by
    rw [Nat.mul_pow, ← Nat.pow_mul, ← Nat.pow_mul, ← Nat.pow_two, ← Nat.pow_mul]
  rw [hlhs, hrhs]
  have hprod : (W1 + 2) * (W2 + 2) ≤ (y + 2) * (y + 2) :=
    Nat.mul_le_mul (by omega) (by omega)
  exact Nat.le_trans hpack (Nat.mul_le_mul_left (3 ^ 256) (Nat.pow_le_pow_left hprod 123))

/-- **`1 × 2` Arc-Decomposition Sub-Path-to-Cycle Bridge Bound (`≤ (6/5) * (y + 2)^(123/128)`):**
If a bridge set of size `r` splits across 2 arcs into pieces `s0, s1` (`r ≤ s0 + s1`), each obeying
Main Theorem 1 on widths `≤ y`, then `5^128 * r^128 ≤ 6^128 * (y + 2)^123`. -/
theorem arc_decomp_1x2_bridge_bound {r s0 s1 W1 W2a W2b y : Nat}
    (hsum : r ≤ s0 + s1)
    (h0 : s0 ^ 256 * 5 ^ 256 ≤ 3 ^ 256 * ((W1 + 2) * (W2a + 2)) ^ 123)
    (h1 : s1 ^ 256 * 5 ^ 256 ≤ 3 ^ 256 * ((W1 + 2) * (W2b + 2)) ^ 123)
    (hw1 : W1 ≤ y) (hwa : W2a ≤ y) (hwb : W2b ≤ y) :
    5 ^ 128 * r ^ 128 ≤ 6 ^ 128 * (y + 2) ^ 123 := by
  have hb0 := packing_bound_half_exponent h0 hw1 hwa
  have hb1 := packing_bound_half_exponent h1 hw1 hwb
  let m := max s0 s1
  have hr : r ≤ 2 * m := by dsimp only [m]; omega
  have hm : 5 ^ 128 * m ^ 128 ≤ 3 ^ 128 * (y + 2) ^ 123 := by
    dsimp only [m]
    by_cases h01 : s0 ≤ s1
    · rw [Nat.max_eq_right h01]; exact hb1
    · rw [Nat.max_eq_left (by omega)]; exact hb0
  have h6 : (6 : Nat) ^ 128 = 2 ^ 128 * 3 ^ 128 := by rw [← Nat.mul_pow]
  calc 5 ^ 128 * r ^ 128
      ≤ 5 ^ 128 * (2 * m) ^ 128 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hr 128)
    _ = 2 ^ 128 * (5 ^ 128 * m ^ 128) := by rw [Nat.mul_pow, Nat.mul_left_comm]
    _ ≤ 2 ^ 128 * (3 ^ 128 * (y + 2) ^ 123) := Nat.mul_le_mul_left _ hm
    _ = (2 ^ 128 * 3 ^ 128) * (y + 2) ^ 123 := (Nat.mul_assoc _ _ _).symm
    _ = 6 ^ 128 * (y + 2) ^ 123 := by rw [h6]

/-- **`2 × 2` Arc-Decomposition Pairwise Bridge Bound (`r(C_1, C_2) ≤ (12/5) * (y + 2)^(123/128)`):**
If a bridge set of size `r` between two cycles splits across `2 × 2` arcs into `s00, s01, s10, s11`
(`r ≤ s00 + s01 + s10 + s11`), each obeying Main Theorem 1 on widths `≤ y`, then
`5^128 * r^128 ≤ 12^128 * (y + 2)^123`. -/
theorem arc_decomp_2x2_bridge_bound {r s00 s01 s10 s11 W1a W1b W2a W2b y : Nat}
    (hsum : r ≤ s00 + s01 + s10 + s11)
    (h00 : s00 ^ 256 * 5 ^ 256 ≤ 3 ^ 256 * ((W1a + 2) * (W2a + 2)) ^ 123)
    (h01 : s01 ^ 256 * 5 ^ 256 ≤ 3 ^ 256 * ((W1a + 2) * (W2b + 2)) ^ 123)
    (h10 : s10 ^ 256 * 5 ^ 256 ≤ 3 ^ 256 * ((W1b + 2) * (W2a + 2)) ^ 123)
    (h11 : s11 ^ 256 * 5 ^ 256 ≤ 3 ^ 256 * ((W1b + 2) * (W2b + 2)) ^ 123)
    (hw1a : W1a ≤ y) (hw1b : W1b ≤ y) (hw2a : W2a ≤ y) (hw2b : W2b ≤ y) :
    5 ^ 128 * r ^ 128 ≤ 12 ^ 128 * (y + 2) ^ 123 := by
  have hb00 := packing_bound_half_exponent h00 hw1a hw2a
  have hb01 := packing_bound_half_exponent h01 hw1a hw2b
  have hb10 := packing_bound_half_exponent h10 hw1b hw2a
  have hb11 := packing_bound_half_exponent h11 hw1b hw2b
  let m := max (max s00 s01) (max s10 s11)
  have hr : r ≤ 4 * m := by dsimp only [m]; omega
  have hm : 5 ^ 128 * m ^ 128 ≤ 3 ^ 128 * (y + 2) ^ 123 := by
    have hle : m = s00 ∨ m = s01 ∨ m = s10 ∨ m = s11 := by dsimp only [m]; omega
    rcases hle with h | h | h | h <;> rw [h] <;> assumption
  have h12 : (12 : Nat) ^ 128 = 4 ^ 128 * 3 ^ 128 := by rw [← Nat.mul_pow]
  calc 5 ^ 128 * r ^ 128
      ≤ 5 ^ 128 * (4 * m) ^ 128 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hr 128)
    _ = 4 ^ 128 * (5 ^ 128 * m ^ 128) := by rw [Nat.mul_pow, Nat.mul_left_comm]
    _ ≤ 4 ^ 128 * (3 ^ 128 * (y + 2) ^ 123) := Nat.mul_le_mul_left _ hm
    _ = (4 ^ 128 * 3 ^ 128) * (y + 2) ^ 123 := (Nat.mul_assoc _ _ _).symm
    _ = 12 ^ 128 * (y + 2) ^ 123 := by rw [h12]

/-- **Path-Splitting Sub-Path Count Bound:**
Splitting a path of `L` vertices into blocks of `B = y/2 + 1` vertices (each having max coordinate
difference `≤ y/2`) produces `⌈L / B⌉` sub-paths satisfying `y * ⌈L / B⌉ ≤ y + 2 * L`. -/
theorem path_split_subpath_count (L y : Nat) (hy : y ≥ 3) :
    let B := y / 2 + 1
    y * ((L + B - 1) / B) ≤ y + 2 * L := by
  dsimp only
  let B := y / 2 + 1
  change y * ((L + B - 1) / B) ≤ y + 2 * L
  have hB_pos : 0 < B := by omega
  have h2B : y < 2 * B := by omega
  by_cases hL0 : L = 0
  · subst hL0
    have hq : (0 + B - 1) / B = 0 := Nat.div_eq_of_lt (by omega)
    rw [hq]; omega
  · have hq_le : (L + B - 1) / B ≤ 1 + L / B := by
      have h1 : L + B - 1 ≤ L + B := by omega
      have h2 := Nat.div_le_div_right (c := B) h1
      rw [Nat.add_div_right L hB_pos] at h2
      omega
    have hmul_div : B * (L / B) ≤ L := Nat.mul_div_le L B
    have hy_div : y * (L / B) ≤ 2 * L := by
      have h1 : y * (L / B) ≤ (2 * B) * (L / B) := Nat.mul_le_mul_right _ (by omega)
      have h2 : (2 * B) * (L / B) = 2 * (B * (L / B)) := Nat.mul_assoc 2 B (L / B)
      omega
    have hstep : y * ((L + B - 1) / B) ≤ y * (1 + L / B) := Nat.mul_le_mul_left y hq_le
    rw [Nat.mul_add, Nat.mul_one] at hstep
    omega

/-- Sum of a list of `Nat`s. -/
def sumList : List Nat → Nat
  | [] => 0
  | x :: xs => x + sumList xs

/-- **Aggregated `m`-Path Splitting Bound:**
Splitting `m = Ls.length` vertex-disjoint paths of lengths `Ls` into blocks of size `B = y/2 + 1`
produces total sub-paths `t` satisfying `y * t ≤ Ls.length * y + 2 * sumList Ls`. -/
theorem path_cover_total_subpaths (Ls : List Nat) (y : Nat) (hy : y ≥ 3) :
    let B := y / 2 + 1
    y * sumList (Ls.map fun L => (L + B - 1) / B) ≤ Ls.length * y + 2 * sumList Ls := by
  induction Ls with
  | nil => simp [sumList]
  | cons L rest ih =>
    simp only [List.map_cons, sumList, List.length_cons]
    have h1 := path_split_subpath_count L y hy
    rw [Nat.mul_add, Nat.add_mul, Nat.one_mul, Nat.mul_add]
    omega

/-! ## 2. Universal Poly-`k`-Cycle & Sublinear `o(n)` Circumference (with R19 `+2m` Pruning) -/

/-- **Sharp Universal Threshold at `y_0 = 2^97` (Sharp at `2^96`):** -/
theorem universal_y0_97_sharp :
    (5 * 2 ^ 97) ^ 128 > 68 ^ 128 * (2 ^ 97 + 2) ^ 123 ∧
    (5 * 2 ^ 96) ^ 128 < 68 ^ 128 * (2 ^ 96 + 2) ^ 123 := by
  decide

/-- **Sharp Fixed-`k` Exponents (`k ∈ {2, 3, 4, 5, 10} ↔ {97, 122, 137, 148, 178}`):**
Matches `cert/witnesses/two_cycle_closure.json["fixed_k_exps"]` 1-to-1. -/
theorem fixed_k_thresholds_sharp :
    ((5 * 2 ^ 97) ^ 128 ≥ (68 * 1) ^ 128 * (2 ^ 97 + 2) ^ 123 ∧
     (5 * 2 ^ 96) ^ 128 < (68 * 1) ^ 128 * (2 ^ 96 + 2) ^ 123) ∧
    ((5 * 2 ^ 122) ^ 128 ≥ (68 * 2) ^ 128 * (2 ^ 122 + 2) ^ 123 ∧
     (5 * 2 ^ 121) ^ 128 < (68 * 2) ^ 128 * (2 ^ 121 + 2) ^ 123) ∧
    ((5 * 2 ^ 137) ^ 128 ≥ (68 * 3) ^ 128 * (2 ^ 137 + 2) ^ 123 ∧
     (5 * 2 ^ 136) ^ 128 < (68 * 3) ^ 128 * (2 ^ 136 + 2) ^ 123) ∧
    ((5 * 2 ^ 148) ^ 128 ≥ (68 * 4) ^ 128 * (2 ^ 148 + 2) ^ 123 ∧
     (5 * 2 ^ 147) ^ 128 < (68 * 4) ^ 128 * (2 ^ 147 + 2) ^ 123) ∧
    ((5 * 2 ^ 178) ^ 128 ≥ (68 * 9) ^ 128 * (2 ^ 178 + 2) ^ 123 ∧
     (5 * 2 ^ 177) ^ 128 < (68 * 9) ^ 128 * (2 ^ 177 + 2) ^ 123) := by
  decide

/-- Parametric monotonicity helper (abstracting big powers away from `ac_rfl`/`omega`):
if `(a * y0)^128 > b^128 * (y0 + 2)^123` and `y0^5 * mult^128 ≤ y^5` (with `y0 > 0, mult ≥ 1`),
then `y0 ≤ y` AND `(a * y)^128 > (b * mult)^128 * (y + 2)^123`. -/
private theorem threshold_scale_param {a b y0 mult y : Nat}
    (hy0 : 0 < y0) (hmult : 1 ≤ mult)
    (hbase : b ^ 128 * (y0 + 2) ^ 123 < (a * y0) ^ 128)
    (hpow : y0 ^ 5 * mult ^ 128 ≤ y ^ 5) :
    y0 ≤ y ∧ (b * mult) ^ 128 * (y + 2) ^ 123 < (a * y) ^ 128 := by
  have hy0_le : y0 ≤ y := by
    apply le_of_pow_le_pow (d := 5) (by omega)
    have hm1 : 1 ≤ mult ^ 128 := Nat.one_le_pow 128 mult (by omega)
    have h1 : y0 ^ 5 * 1 ≤ y0 ^ 5 * mult ^ 128 := Nat.mul_le_mul_left _ hm1
    omega
  have hy_pos : 0 < y := Nat.lt_of_lt_of_le hy0 hy0_le
  refine ⟨hy0_le, ?_⟩
  -- Key monotonicity: `(y + 2) * y0 ≤ (y0 + 2) * y`
  have hlin : (y + 2) * y0 ≤ (y0 + 2) * y := by
    rw [Nat.add_mul, Nat.add_mul]
    have hc : y * y0 = y0 * y := Nat.mul_comm y y0
    omega
  have h123 : (y + 2) ^ 123 * y0 ^ 123 ≤ (y0 + 2) ^ 123 * y ^ 123 := by
    rw [← Nat.mul_pow, ← Nat.mul_pow]
    exact Nat.pow_le_pow_left hlin 123
  -- Combine `h123` with `hpow : y0^5 * mult^128 ≤ y^5`:
  have hcomb : (y + 2) ^ 123 * mult ^ 128 * y0 ^ 128 ≤ (y0 + 2) ^ 123 * y ^ 128 := by
    have h128_y0 : y0 ^ 123 * y0 ^ 5 = y0 ^ 128 := by rw [← Nat.pow_add]
    have h128_y : y ^ 123 * y ^ 5 = y ^ 128 := by rw [← Nat.pow_add]
    have hm := Nat.mul_le_mul h123 hpow
    generalize (y + 2) ^ 123 = A, (y0 + 2) ^ 123 = B, mult ^ 128 = M128,
               y0 ^ 123 = Y0A, y0 ^ 5 = Y0B, y0 ^ 128 = Y0C,
               y ^ 123 = YA, y ^ 5 = YB, y ^ 128 = YC at h128_y0 h128_y hm ⊢
    calc A * M128 * Y0C
        = A * M128 * (Y0A * Y0B) := by rw [← h128_y0]
      _ = (A * Y0A) * (Y0B * M128) := by ac_rfl
      _ ≤ (B * YA) * YB := hm
      _ = B * (YA * YB) := by ac_rfl
      _ = B * YC := by rw [h128_y]
  -- Multiply by `b^128` and apply `hbase`:
  have ha_y0 : (a * y0) ^ 128 = a ^ 128 * y0 ^ 128 := Nat.mul_pow a y0 128
  have ha_y : (a * y) ^ 128 = a ^ 128 * y ^ 128 := Nat.mul_pow a y 128
  have hbm : (b * mult) ^ 128 = b ^ 128 * mult ^ 128 := Nat.mul_pow b mult 128
  have hlt : (b * mult) ^ 128 * (y + 2) ^ 123 * y0 ^ 128 < (a * y) ^ 128 * y0 ^ 128 := by
    rw [hbm, ha_y]
    have hy_pow_pos : 0 < y ^ 128 := Nat.pow_pos hy_pos
    rw [ha_y0] at hbase
    generalize b ^ 128 = B128, mult ^ 128 = M128, (y + 2) ^ 123 = P1, (y0 + 2) ^ 123 = P0,
               a ^ 128 = A128, y0 ^ 128 = Y0C, y ^ 128 = YC at hcomb hbase hy_pow_pos ⊢
    calc B128 * M128 * P1 * Y0C
        = B128 * (P1 * M128 * Y0C) := by ac_rfl
      _ ≤ B128 * (P0 * YC) := Nat.mul_le_mul_left B128 hcomb
      _ = (B128 * P0) * YC := by ac_rfl
      _ < (A128 * Y0C) * YC := Nat.mul_lt_mul_of_pos_right hbase hy_pow_pos
      _ = A128 * YC * Y0C := by ac_rfl
  exact Nat.lt_of_mul_lt_mul_right hlt

/-- **Universal Poly-`k`-Cycle Threshold Inequality (ALL `k ≥ 2`, ALL `y ≥ 2^97 * (k-1)^(128/5)`):**
For every `k ≥ 2` and `y` with `(2^97)^5 * (k - 1)^128 ≤ y^5`, we have `y ≥ 2^97` and strictly
`(68 * (k - 1))^128 * (y + 2)^123 < (5 * y)^128`. -/
theorem universal_poly_k_threshold (k y : Nat) (hk : k ≥ 2)
    (hy_pow : (2 ^ 97) ^ 5 * (k - 1) ^ 128 ≤ y ^ 5) :
    2 ^ 97 ≤ y ∧ (68 * (k - 1)) ^ 128 * (y + 2) ^ 123 < (5 * y) ^ 128 :=
  threshold_scale_param (a := 5) (b := 68) (y0 := 2 ^ 97) (mult := k - 1) (y := y)
    (by decide) (by omega) universal_y0_97_sharp.1 hy_pow

/-- Parametric `k`-cycle closure helper (abstracting `y0 = 2^97` so `omega` never sees big powers). -/
private theorem poly_k_cycle_closure_param (y0 n k y r vatt : Nat)
    (hy0_pos : 0 < y0) (hk : k ≥ 2)
    (hbase : 68 ^ 128 * (y0 + 2) ^ 123 < (5 * y0) ^ 128)
    (hk_bound : y0 ^ 5 * k ^ 133 ≤ n ^ 5)
    (hmax_cyc : n ≤ k * y)
    (hbridge : 5 ^ 128 * r ^ 128 ≤ 12 ^ 128 * (y + 2) ^ 123)
    (hcov : vatt ≤ (k - 1) * r)
    (hvatt : 17 * vatt > 3 * y) : False := by
  have hy_pow : y0 ^ 5 * (k - 1) ^ 128 ≤ y ^ 5 := by
    have hk_pos : 0 < k ^ 5 := Nat.pow_pos (Nat.lt_of_lt_of_le (by decide : 0 < 2) hk)
    have hky : n ^ 5 ≤ k ^ 5 * y ^ 5 := by
      rw [← Nat.mul_pow]; exact Nat.pow_le_pow_left hmax_cyc 5
    have hk133 : k ^ 133 = k ^ 128 * k ^ 5 := by rw [← Nat.pow_add]
    have hmul : y0 ^ 5 * k ^ 128 * k ^ 5 ≤ y ^ 5 * k ^ 5 := by
      calc y0 ^ 5 * k ^ 128 * k ^ 5
          = y0 ^ 5 * (k ^ 128 * k ^ 5) := Nat.mul_assoc _ _ _
        _ = y0 ^ 5 * k ^ 133 := by rw [← hk133]
        _ ≤ n ^ 5 := hk_bound
        _ ≤ k ^ 5 * y ^ 5 := hky
        _ = y ^ 5 * k ^ 5 := Nat.mul_comm _ _
    have hle_k : y0 ^ 5 * k ^ 128 ≤ y ^ 5 := Nat.le_of_mul_le_mul_right hmul hk_pos
    exact Nat.le_trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.sub_le k 1) 128)) hle_k
  have hkm1 : 1 ≤ k - 1 := Nat.le_sub_of_add_le (by exact hk)
  have hth := (threshold_scale_param hy0_pos hkm1 hbase hy_pow).2
  have hv_le : (17 * 5 * vatt) ^ 128 < (3 * 5 * y) ^ 128 := by
    have h1 : 17 * 5 * vatt ≤ 17 * (k - 1) * (5 * r) := by
      calc 17 * 5 * vatt = 17 * (5 * vatt) := Nat.mul_assoc 17 5 vatt
        _ ≤ 17 * (5 * ((k - 1) * r)) := Nat.mul_le_mul_left 17 (Nat.mul_le_mul_left 5 hcov)
        _ = 17 * (k - 1) * (5 * r) := by ac_rfl
    have h17_12 : (17 * (k - 1)) ^ 128 * 12 ^ 128 = 3 ^ 128 * (68 * (k - 1)) ^ 128 := by
      rw [← Nat.mul_pow, ← Nat.mul_pow]
      congr 1
      calc 17 * (k - 1) * 12 = (17 * 12) * (k - 1) := by rw [Nat.mul_right_comm]
        _ = (3 * 68) * (k - 1) := rfl
        _ = 3 * (68 * (k - 1)) := Nat.mul_assoc 3 68 (k - 1)
    have h35 : (3 * 5 * y) ^ 128 = 3 ^ 128 * (5 * y) ^ 128 := by
      rw [Nat.mul_assoc 3 5 y, Nat.mul_pow]
    have h5r : (5 * r) ^ 128 ≤ 12 ^ 128 * (y + 2) ^ 123 := by
      rw [Nat.mul_pow]; exact hbridge
    calc (17 * 5 * vatt) ^ 128
        ≤ (17 * (k - 1) * (5 * r)) ^ 128 := Nat.pow_le_pow_left h1 128
      _ = (17 * (k - 1)) ^ 128 * (5 * r) ^ 128 := Nat.mul_pow _ _ 128
      _ ≤ (17 * (k - 1)) ^ 128 * (12 ^ 128 * (y + 2) ^ 123) := Nat.mul_le_mul_left _ h5r
      _ = ((17 * (k - 1)) ^ 128 * 12 ^ 128) * (y + 2) ^ 123 := (Nat.mul_assoc _ _ _).symm
      _ = 3 ^ 128 * ((68 * (k - 1)) ^ 128 * (y + 2) ^ 123) := by rw [h17_12, Nat.mul_assoc]
      _ < 3 ^ 128 * (5 * y) ^ 128 := Nat.mul_lt_mul_of_pos_left hth (by decide)
      _ = (3 * 5 * y) ^ 128 := h35.symm
  have hlt : 17 * 5 * vatt < 3 * 5 * y := lt_of_pow_lt_pow (d := 128) (by decide) hv_le
  have hlt5 : 5 * (17 * vatt) < 5 * (3 * y) := by
    rw [Nat.mul_left_comm 5 17 vatt, ← Nat.mul_assoc 17 5 vatt,
        Nat.mul_left_comm 5 3 y, ← Nat.mul_assoc 3 5 y]
    exact hlt
  have hcontr : 17 * vatt < 3 * y := Nat.lt_of_mul_lt_mul_left hlt5
  exact Nat.lt_irrefl _ (Nat.lt_trans hcontr hvatt)

/-- **Universal Poly-`k`-Cycle Closure Theorem (`k ≤ (n / 2^97)^(5/133)`):**
For EVERY `k ≥ 2` and `n, y, r, vatt : Nat` satisfying:
- `(2^97)^5 * k^133 ≤ n^5` (i.e. `k ≤ (n / 2^97)^(5/133)`),
- `n ≤ k * y` (largest cycle of the `k`-cycle 2-factor has length `y ≥ n / k`),
- `5^128 * r^128 ≤ 12^128 * (y + 2)^123` (pairwise `2×2` bridge bound `r ≤ (12/5)(y+2)^(123/128)`),
- `vatt ≤ (k - 1) * r` (all attachments on the largest cycle come from the `k - 1` other cycles),
- `17 * vatt > 3 * y` (R5 Sturmian attachment lower bound),
we reach an immediate contradiction (`False`)! -/
theorem universal_poly_k_cycle_closure (n k y r vatt : Nat)
    (hk : k ≥ 2)
    (hk_bound : (2 ^ 97) ^ 5 * k ^ 133 ≤ n ^ 5)
    (hmax_cyc : n ≤ k * y)
    (hbridge : 5 ^ 128 * r ^ 128 ≤ 12 ^ 128 * (y + 2) ^ 123)
    (hcov : vatt ≤ (k - 1) * r)
    (hvatt : 17 * vatt > 3 * y) : False :=
  poly_k_cycle_closure_param (2 ^ 97) n k y r vatt (by decide) hk
    universal_y0_97_sharp.1 hk_bound hmax_cyc hbridge hcov hvatt

/-- **Exact R19 `+2m` Endpoint Pruning & `25 * n^(128/133)` Integer Constants:**
Matches `verify_clawfree_eg.py` lines 1350–1354 bit-for-bit. -/
theorem pruning_2m_constants :
    5000 ^ 128 < 3 ^ 128 * (2 ^ 97 + 2) ^ 123 ∧
    (5000 * 2 ^ 97) ^ 128 > (68 * 1001) ^ 128 * (2 ^ 97 + 2) ^ 123 ∧
    (2 ^ 97 + 2) ^ 123 < 2 * (2 ^ 97) ^ 123 ∧
    5 ^ 128 * 25 ^ 133 ≥ 2 * 136 ^ 128 ∧
    5 ^ 128 * 24 ^ 133 < 2 * 136 ^ 128 := by
  decide

/-- Pure-`Nat` Minkowski-style strict addition lemma for `d`-th powers:
if `A^d < u^d * P` and `B^d ≤ v^d * P` (`u > 0, v > 0, d ≥ 1`), then `(A + B)^d < (u + v)^d * P`! -/
private theorem pow_add_strict_of_bounds {A B u v P d : Nat}
    (hu : 0 < u) (hv : 0 < v) (hd : 1 ≤ d)
    (hA : A ^ d < u ^ d * P) (hB : B ^ d ≤ v ^ d * P) :
    (A + B) ^ d < (u + v) ^ d * P := by
  by_cases hcmp : v * A < u * B
  · have hlin : v * (A + B) < (u + v) * B := by
      rw [Nat.mul_add, Nat.add_mul]
      have hc : v * B = B * v := Nat.mul_comm v B
      have hc2 : u * B = B * u := Nat.mul_comm u B
      omega
    have hpow_lt : v ^ d * (A + B) ^ d < (u + v) ^ d * B ^ d := by
      rw [← Nat.mul_pow, ← Nat.mul_pow]
      exact pow_lt_pow_left' hd hlin
    have hmul : v ^ d * (A + B) ^ d < v ^ d * ((u + v) ^ d * P) := by
      calc v ^ d * (A + B) ^ d
          < (u + v) ^ d * B ^ d := hpow_lt
        _ ≤ (u + v) ^ d * (v ^ d * P) := Nat.mul_le_mul_left _ hB
        _ = v ^ d * ((u + v) ^ d * P) := by ac_rfl
    exact Nat.lt_of_mul_lt_mul_left hmul
  · have hlin : u * (A + B) ≤ (u + v) * A := by
      rw [Nat.mul_add, Nat.add_mul]
      have hc : u * A = A * u := Nat.mul_comm u A
      have hc2 : v * A = A * v := Nat.mul_comm v A
      omega
    have hpow_le : u ^ d * (A + B) ^ d ≤ (u + v) ^ d * A ^ d := by
      rw [← Nat.mul_pow, ← Nat.mul_pow]
      exact Nat.pow_le_pow_left hlin d
    have hmul : u ^ d * (A + B) ^ d < u ^ d * ((u + v) ^ d * P) := by
      calc u ^ d * (A + B) ^ d
          ≤ (u + v) ^ d * A ^ d := hpow_le
        _ < (u + v) ^ d * (u ^ d * P) :=
            Nat.mul_lt_mul_of_pos_left hA (Nat.pow_pos (by omega))
        _ = u ^ d * ((u + v) ^ d * P) := by ac_rfl
    exact Nat.lt_of_mul_lt_mul_left hmul

/-- Parametric sublinear circumference closure (abstracting `y0 = 2^97` away from `omega`). -/
private theorem sublinear_m_path_param (y0 n m y t r_sub vatt : Nat)
    (hy0_pos : 0 < y0) (hm : m ≥ 1)
    (hc1 : 5000 ^ 128 < 3 ^ 128 * (y0 + 2) ^ 123)
    (hc2 : (68 * 1001) ^ 128 * (y0 + 2) ^ 123 < (5000 * y0) ^ 128)
    (hc3 : (y0 + 2) ^ 123 < 2 * y0 ^ 123)
    (hc4 : 2 * 136 ^ 128 ≤ 5 ^ 128 * 25 ^ 133)
    (hy_m : y0 ^ 5 * m ^ 128 ≤ y ^ 5)
    (hy_n : 25 ^ 133 * n ^ 128 ≤ y ^ 133)
    (hsub : y * t ≤ m * y + 2 * n)
    (hbridge : 5 ^ 128 * r_sub ^ 128 ≤ 6 ^ 128 * (y + 2) ^ 123)
    (hcov : vatt ≤ 2 * m + t * r_sub)
    (hvatt : 17 * vatt > 3 * y) : False := by
  -- Step 1: Deduce `y0 ≤ y` and `(68 * 1001 * m)^128 * (y + 2)^123 < (5000 * y)^128`!
  have hterm1_scale := threshold_scale_param (a := 5000) (b := 68 * 1001) (y0 := y0) (mult := m)
    (y := y) hy0_pos hm hc2 hy_m
  have hy_ge : y0 ≤ y := hterm1_scale.1
  have hy_pos : 0 < y := Nat.lt_of_lt_of_le hy0_pos hy_ge
  have hterm1_pow : (68 * 1001 * m) ^ 128 * (y + 2) ^ 123 < (5000 * y) ^ 128 := hterm1_scale.2
  -- Step 2: Show `(5000 * (2 + r_sub))^128 < (6 * 1001)^128 * (y + 2)^123`!
  have h2_bound : (5000 * 2) ^ 128 < 6 ^ 128 * (y + 2) ^ 123 := by
    have hmono : (y0 + 2) ^ 123 ≤ (y + 2) ^ 123 := Nat.pow_le_pow_left (Nat.add_le_add_right hy_ge 2) 123
    have h6 : (6 : Nat) ^ 128 = 2 ^ 128 * 3 ^ 128 := by rw [← Nat.mul_pow]
    calc (5000 * 2) ^ 128
        = 2 ^ 128 * 5000 ^ 128 := by rw [Nat.mul_pow, Nat.mul_comm]
      _ < 2 ^ 128 * (3 ^ 128 * (y0 + 2) ^ 123) := Nat.mul_lt_mul_of_pos_left hc1 (by decide)
      _ ≤ 2 ^ 128 * (3 ^ 128 * (y + 2) ^ 123) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hmono)
      _ = 6 ^ 128 * (y + 2) ^ 123 := by rw [← Nat.mul_assoc, h6]
  have hr_bound : (5000 * r_sub) ^ 128 ≤ (1000 * 6) ^ 128 * (y + 2) ^ 123 := by
    have h5000 : 5000 * r_sub = 1000 * (5 * r_sub) := Nat.mul_assoc 1000 5 r_sub
    rw [h5000, Nat.mul_pow, Nat.mul_pow, Nat.mul_pow]
    calc 1000 ^ 128 * (5 ^ 128 * r_sub ^ 128)
        ≤ 1000 ^ 128 * (6 ^ 128 * (y + 2) ^ 123) := Nat.mul_le_mul_left _ hbridge
      _ = 1000 ^ 128 * 6 ^ 128 * (y + 2) ^ 123 := (Nat.mul_assoc _ _ _).symm
  have hsum_2r : (5000 * (2 + r_sub)) ^ 128 < (6 * 1001) ^ 128 * (y + 2) ^ 123 := by
    have hadd := pow_add_strict_of_bounds (A := 5000 * 2) (B := 5000 * r_sub) (u := 6) (v := 1000 * 6)
      (P := (y + 2) ^ 123) (d := 128) (by decide) (by decide) (by decide) h2_bound hr_bound
    have hL : 5000 * 2 + 5000 * r_sub = 5000 * (2 + r_sub) := (Nat.mul_add 5000 2 r_sub).symm
    have hR : 6 + 1000 * 6 = 6 * 1001 := by decide
    rw [hL, hR] at hadd
    exact hadd
  -- Step 3: Deduce Term 1: `34 * m * (2 + r_sub) < 3 * y`!
  have hterm1 : 34 * m * (2 + r_sub) < 3 * y := by
    apply lt_of_pow_lt_pow (d := 128) (by decide)
    have h3_pos : 0 < 3 ^ 128 := by decide
    have h34_6 : 34 * m * (6 * 1001) = 3 * (68 * 1001 * m) := by
      calc 34 * m * (6 * 1001) = (34 * 6 * 1001) * m := by ac_rfl
        _ = (3 * (68 * 1001)) * m := rfl
        _ = 3 * (68 * 1001 * m) := Nat.mul_assoc 3 (68 * 1001) m
    have h34m_pos : 0 < 34 * m := Nat.mul_pos (by decide) (Nat.lt_of_lt_of_le (by decide : 0 < 1) hm)
    have hpow : 5000 ^ 128 * (34 * m * (2 + r_sub)) ^ 128 < 5000 ^ 128 * (3 * y) ^ 128 := by
      have hL : 5000 ^ 128 * (34 * m * (2 + r_sub)) ^ 128 = (34 * m) ^ 128 * (5000 * (2 + r_sub)) ^ 128 := by
        rw [← Nat.mul_pow, ← Nat.mul_pow]; congr 1; ac_rfl
      have hR : 5000 ^ 128 * (3 * y) ^ 128 = 3 ^ 128 * (5000 * y) ^ 128 := by
        rw [← Nat.mul_pow, ← Nat.mul_pow]; congr 1; ac_rfl
      rw [hL, hR]
      calc (34 * m) ^ 128 * (5000 * (2 + r_sub)) ^ 128
          < (34 * m) ^ 128 * ((6 * 1001) ^ 128 * (y + 2) ^ 123) :=
            Nat.mul_lt_mul_of_pos_left hsum_2r (Nat.pow_pos h34m_pos)
        _ = ((34 * m) * (6 * 1001)) ^ 128 * (y + 2) ^ 123 := by rw [← Nat.mul_assoc, ← Nat.mul_pow]
        _ = (3 * (68 * 1001 * m)) ^ 128 * (y + 2) ^ 123 := by rw [h34_6]
        _ = 3 ^ 128 * ((68 * 1001 * m) ^ 128 * (y + 2) ^ 123) := by rw [Nat.mul_pow, Nat.mul_assoc]
        _ < 3 ^ 128 * (5000 * y) ^ 128 := Nat.mul_lt_mul_of_pos_left hterm1_pow h3_pos
    exact Nat.lt_of_mul_lt_mul_left hpow
  -- Step 4: Deduce Term 2: `68 * n * r_sub ≤ 3 * y * y`!
  have hterm2 : 68 * n * r_sub ≤ 3 * y * y := by
    apply le_of_pow_le_pow (d := 128) (by decide)
    have hy2_lt : (y + 2) ^ 123 < 2 * y ^ 123 := by
      have hlin : (y + 2) * y0 ≤ (y0 + 2) * y := by
        rw [Nat.add_mul, Nat.add_mul, Nat.mul_comm y y0]
        exact Nat.add_le_add_left (Nat.mul_le_mul_left 2 hy_ge) (y0 * y)
      have h123 : (y + 2) ^ 123 * y0 ^ 123 ≤ (y0 + 2) ^ 123 * y ^ 123 := by
        rw [← Nat.mul_pow, ← Nat.mul_pow]
        exact Nat.pow_le_pow_left hlin 123
      have hmul : (y + 2) ^ 123 * y0 ^ 123 < (2 * y ^ 123) * y0 ^ 123 := by
        calc (y + 2) ^ 123 * y0 ^ 123
            ≤ (y0 + 2) ^ 123 * y ^ 123 := h123
          _ < (2 * y0 ^ 123) * y ^ 123 := Nat.mul_lt_mul_of_pos_right hc3 (Nat.pow_pos hy_pos)
          _ = (2 * y ^ 123) * y0 ^ 123 := by rw [Nat.mul_assoc, Nat.mul_comm (y0 ^ 123) (y ^ 123), ← Nat.mul_assoc]
      exact Nat.lt_of_mul_lt_mul_right hmul
    have hpow5 : 5 ^ 128 * (68 * n * r_sub) ^ 128 ≤ 5 ^ 128 * (3 * y * y) ^ 128 := by
      have hL : 5 ^ 128 * (68 * n * r_sub) ^ 128 = (68 * n) ^ 128 * (5 * r_sub) ^ 128 := by
        rw [← Nat.mul_pow, ← Nat.mul_pow]; congr 1; ac_rfl
      have hR : 5 ^ 128 * (3 * y * y) ^ 128 = 3 ^ 128 * (5 ^ 128 * (y ^ 133 * y ^ 123)) := by
        have h256 : y ^ 133 * y ^ 123 = y ^ 256 := by rw [← Nat.pow_add]
        rw [h256, ← Nat.mul_pow, show 5 * (3 * y * y) = 3 * (5 * y ^ 2) by rw [Nat.pow_two]; ac_rfl,
            Nat.mul_pow, Nat.mul_pow, ← Nat.pow_mul]
      have h5r : (5 * r_sub) ^ 128 ≤ 6 ^ 128 * (y + 2) ^ 123 := by
        rw [Nat.mul_pow]; exact hbridge
      have h5_25 : 2 * 136 ^ 128 * n ^ 128 ≤ 5 ^ 128 * y ^ 133 := by
        calc 2 * 136 ^ 128 * n ^ 128
            ≤ (5 ^ 128 * 25 ^ 133) * n ^ 128 := Nat.mul_le_mul_right _ hc4
          _ = 5 ^ 128 * (25 ^ 133 * n ^ 128) := Nat.mul_assoc _ _ _
          _ ≤ 5 ^ 128 * y ^ 133 := Nat.mul_le_mul_left _ hy_n
      have h68n_eq : (68 * n) ^ 128 * 6 ^ 128 = 3 ^ 128 * (136 ^ 128 * n ^ 128) := by
        rw [← Nat.mul_pow, show 68 * n * 6 = 3 * (136 * n) by
          calc 68 * n * 6 = (68 * 6) * n := Nat.mul_right_comm 68 n 6
            _ = (3 * 136) * n := rfl
            _ = 3 * (136 * n) := Nat.mul_assoc 3 136 n, Nat.mul_pow, Nat.mul_pow]
      rw [hL, hR]
      calc (68 * n) ^ 128 * (5 * r_sub) ^ 128
          ≤ (68 * n) ^ 128 * (6 ^ 128 * (y + 2) ^ 123) := Nat.mul_le_mul_left _ h5r
        _ = ((68 * n) ^ 128 * 6 ^ 128) * (y + 2) ^ 123 := (Nat.mul_assoc _ _ _).symm
        _ = 3 ^ 128 * (136 ^ 128 * n ^ 128 * (y + 2) ^ 123) := by rw [h68n_eq, Nat.mul_assoc]
        _ ≤ 3 ^ 128 * (136 ^ 128 * n ^ 128 * (2 * y ^ 123)) :=
            Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.le_of_lt hy2_lt))
        _ = 3 ^ 128 * ((2 * 136 ^ 128 * n ^ 128) * y ^ 123) := by
            congr 1
            rw [Nat.mul_assoc 2, ← Nat.mul_assoc (136 ^ 128 * n ^ 128), Nat.mul_comm (136 ^ 128 * n ^ 128) 2]
        _ ≤ 3 ^ 128 * ((5 ^ 128 * y ^ 133) * y ^ 123) :=
            Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ h5_25)
        _ = 3 ^ 128 * (5 ^ 128 * (y ^ 133 * y ^ 123)) := by rw [Nat.mul_assoc (5 ^ 128)]
    exact Nat.le_of_mul_le_mul_left hpow5 (by decide)
  -- Step 5: Combine Term 1 + Term 2 (pure `Nat` algebra, zero `omega`!):
  have hv_y : y * vatt ≤ m * y * (2 + r_sub) + 2 * n * r_sub := by
    have h1 : y * vatt ≤ y * (2 * m) + y * (t * r_sub) := by
      rw [← Nat.mul_add]; exact Nat.mul_le_mul_left y hcov
    have h2 : y * (t * r_sub) ≤ m * y * r_sub + 2 * n * r_sub := by
      rw [← Nat.add_mul, ← Nat.mul_assoc]; exact Nat.mul_le_mul_right r_sub hsub
    have h3 : y * (2 * m) + m * y * r_sub = m * y * (2 + r_sub) := by
      rw [Nat.mul_add]; ac_rfl
    calc y * vatt
        ≤ y * (2 * m) + y * (t * r_sub) := h1
      _ ≤ y * (2 * m) + (m * y * r_sub + 2 * n * r_sub) := Nat.add_le_add_left h2 _
      _ = (y * (2 * m) + m * y * r_sub) + 2 * n * r_sub := (Nat.add_assoc _ _ _).symm
      _ = m * y * (2 + r_sub) + 2 * n * r_sub := by rw [h3]
  have h1_y : 34 * (m * y * (2 + r_sub)) < 3 * (y * y) := by
    have hmul := Nat.mul_lt_mul_of_pos_right hterm1 hy_pos
    calc 34 * (m * y * (2 + r_sub))
        = (34 * m * (2 + r_sub)) * y := by ac_rfl
      _ < (3 * y) * y := hmul
      _ = 3 * (y * y) := Nat.mul_assoc 3 y y
  have h2_y : 34 * (2 * n * r_sub) ≤ 3 * (y * y) := by
    rw [show 34 * (2 * n * r_sub) = 68 * n * r_sub by ac_rfl, ← Nat.mul_assoc 3 y y]
    exact hterm2
  have htot : 34 * (y * vatt) < 6 * (y * y) := by
    have h34 := Nat.mul_le_mul_left 34 hv_y
    rw [Nat.mul_add] at h34
    exact Nat.lt_of_le_of_lt h34 (by
      have hadd := Nat.add_lt_add_of_lt_of_le h1_y h2_y
      rw [← Nat.add_mul] at hadd
      exact hadd)
  have hcontr : 6 * (y * y) < 34 * (y * vatt) := by
    have h2y_pos : 0 < 2 * y := Nat.mul_pos (by decide) hy_pos
    have hm := Nat.mul_lt_mul_of_pos_left hvatt h2y_pos
    have hL : 2 * y * (17 * vatt) = 34 * (y * vatt) := by ac_rfl
    have hR : 2 * y * (3 * y) = 6 * (y * y) := by ac_rfl
    rw [hL, hR] at hm
    exact hm
  exact Nat.lt_irrefl _ (Nat.lt_trans htot hcontr)

/-- **Sublinear `o(n)` `m`-Path Complement-Cover Arithmetic Closure (with R19 `+2m` Endpoint Pruning):**
Here `n = |V(H)|` is the order of the cubic triangle quotient `H`, `y = |V(C)|` is the length of a
longest cycle `C` in `H`, and `m ≥ 1` is the number of vertex-disjoint paths covering `H - V(C)`
(split into `t` sub-paths of length `≤ y/2 + 1`, so `y * t ≤ m * y + 2 * n`). If:
- `y ≥ 2^97 * m^(128/5)` (exact integer form `(2^97)^5 * m^128 ≤ y^5`),
- `y ≥ 25 * n^(128/133)` (exact integer form `25^133 * n^128 ≤ y^133`),
- `5^128 * r_sub^128 ≤ 6^128 * (y + 2)^123` (exact `1×2` bridge bound per sub-path),
- `vatt ≤ 2 * m + t * r_sub` (including the `+2*m` pruned original-path endpoint bridges),
- `17 * vatt > 3 * y` (R5 Sturmian attachment lower bound),
then `False`! Consequently, for fixed `m` (or any `m = o(n^(5/128))`), a dyadic-cycle-free cubic
claw-free graph `G = T(H)` (`|V(G)| = 3*n`) satisfies the sublinear upper bound
`y < max(2^97 * m^(128/5), 25 * n^(128/133)) = o(n)` on its quotient circumference (and hence
`c(G) = O(y) = o(|V(G)|)` via the `3*y` triangle-lift bound proved in the manuscript). -/
theorem sublinear_circumference_m_path_closure (n m y t r_sub vatt : Nat)
    (hm : m ≥ 1) (_hy3 : y ≥ 3)
    (hy_m : (2 ^ 97) ^ 5 * m ^ 128 ≤ y ^ 5)
    (hy_n : 25 ^ 133 * n ^ 128 ≤ y ^ 133)
    (hsub : y * t ≤ m * y + 2 * n)
    (hbridge : 5 ^ 128 * r_sub ^ 128 ≤ 6 ^ 128 * (y + 2) ^ 123)
    (hcov : vatt ≤ 2 * m + t * r_sub)
    (hvatt : 17 * vatt > 3 * y) : False :=
  sublinear_m_path_param (2 ^ 97) n m y t r_sub vatt (by decide) hm
    pruning_2m_constants.1 pruning_2m_constants.2.1 pruning_2m_constants.2.2.1
    pruning_2m_constants.2.2.2.1 hy_m hy_n hsub hbridge hcov hvatt

/-! ## 3. Equal-Block `k = 3, 4, 5` Rational Box Certificates (`17 + 17 + 16 = 50` Boxes) -/

/-- Exact 1-class and 2-class equal-block closure predicate for `k`-cycle multiplicity `mult = k - 1`. -/
def EqualKPairClosed (mult M x y : Nat) : Prop :=
  let K := (4 * M) / 3
  let lo := r5AttachLower M (y - M)
  let r := lo + (if lo ≥ x then (lo - x) % 2 else (x - lo) % 2)
  let W := x + y + 1 - 2 * M
  x + 2 ≤ K →
    let e := K - x - 2
    let P := max ((min W (3 * e) + 2) * (min W (3 * e) + 2)) ((W + 2) * (min W (2 * e) + 2))
    (3 * mult) ^ 256 * P ^ 123 < (5 * r) ^ 256 ∧
    (x + y + 4 ≤ 2 * K →
      let twoR := min (2 * W) (2 * K - x - y - 4)
      (6 * mult) ^ 256 * (twoR + 4) ^ 246 < (5 * r) ^ 256 * 2 ^ 246)

theorem equalK_boxes_counts :
    equalK3Boxes17.length = 17 ∧
    equalK4Boxes17.length = 17 ∧
    equalK5Boxes16.length = 16 := by
  decide

/-- **Exact 4-Regime Domain Coverage for the `17`-Box Equal-Block Family (`k = 3` & `k = 4`):** -/
theorem equalK3Boxes17_domain_coverage (M dx dy : Nat) (hM : M ≥ 2048)
    (hord : dx ≤ dy) (h3 : 3 * dy ≤ M) :
    ∃ b ∈ equalK3Boxes17,
      (b.n, b.k) = r5Template M dy ∧
      0 < b.xlo.den ∧ 0 < b.xhi.den ∧ 0 < b.ylo.den ∧ 0 < b.yhi.den ∧
      b.xlo.num * M ≤ dx * b.xlo.den ∧ dx * b.xhi.den ≤ b.xhi.num * M ∧
      b.ylo.num * M ≤ dy * b.ylo.den ∧ dy * b.yhi.den ≤ b.yhi.num * M := by
  have hmem : ∀ (i : Nat) (hi : i < equalK3Boxes17.length), equalK3Boxes17[i]'hi ∈ equalK3Boxes17 :=
    fun i hi => List.getElem_mem hi
  unfold r5Template
  by_cases h1 : 5 * dy ≤ M + 4
  · simp only [h1, ↓reduceIte]
    have hdy_hi : 2560 * dy ≤ 513 * M := by omega
    by_cases hy1 : 5120 * dy ≤ 513 * M
    · refine ⟨equalK3Boxes17[7]'(by decide), hmem 7 (by decide), rfl, by decide, by decide, by decide, by decide, ?_, ?_, ?_, ?_⟩ <;>
        (simp only [equalK3Boxes17, List.getElem_cons_zero, List.getElem_cons_succ]; omega)
    · by_cases hx1 : 513 * M ≤ 5120 * dx
      · refine ⟨equalK3Boxes17[0]'(by decide), hmem 0 (by decide), rfl, by decide, by decide, by decide, by decide, ?_, ?_, ?_, ?_⟩ <;>
          (simp only [equalK3Boxes17, List.getElem_cons_zero]; omega)
      · by_cases hy2 : 10240 * dy ≤ 1539 * M
        · by_cases hx2 : 513 * M ≤ 10240 * dx
          · refine ⟨equalK3Boxes17[2]'(by decide), hmem 2 (by decide), rfl, by decide, by decide, by decide, by decide, ?_, ?_, ?_, ?_⟩ <;>
              (simp only [equalK3Boxes17, List.getElem_cons_zero, List.getElem_cons_succ]; omega)
          · refine ⟨equalK3Boxes17[6]'(by decide), hmem 6 (by decide), rfl, by decide, by decide, by decide, by decide, ?_, ?_, ?_, ?_⟩ <;>
              (simp only [equalK3Boxes17, List.getElem_cons_zero, List.getElem_cons_succ]; omega)
        · by_cases hx2 : 513 * M ≤ 10240 * dx
          · refine ⟨equalK3Boxes17[1]'(by decide), hmem 1 (by decide), rfl, by decide, by decide, by decide, by decide, ?_, ?_, ?_, ?_⟩ <;>
              (simp only [equalK3Boxes17, List.getElem_cons_zero, List.getElem_cons_succ]; omega)
          · by_cases hx3 : 513 * M ≤ 20480 * dx
            · by_cases hy3 : 20480 * dy ≤ 3591 * M
              · refine ⟨equalK3Boxes17[4]'(by decide), hmem 4 (by decide), rfl, by decide, by decide, by decide, by decide, ?_, ?_, ?_, ?_⟩ <;>
                  (simp only [equalK3Boxes17, List.getElem_cons_zero, List.getElem_cons_succ]; omega)
              · refine ⟨equalK3Boxes17[3]'(by decide), hmem 3 (by decide), rfl, by decide, by decide, by decide, by decide, ?_, ?_, ?_, ?_⟩ <;>
                  (simp only [equalK3Boxes17, List.getElem_cons_zero, List.getElem_cons_succ]; omega)
            · refine ⟨equalK3Boxes17[5]'(by decide), hmem 5 (by decide), rfl, by decide, by decide, by decide, by decide, ?_, ?_, ?_, ?_⟩ <;>
                (simp only [equalK3Boxes17, List.getElem_cons_zero, List.getElem_cons_succ]; omega)
  · by_cases h2 : 4 * dy ≤ M + 2
    · simp only [h1, h2, ↓reduceIte]
      refine ⟨equalK3Boxes17[8]'(by decide), hmem 8 (by decide), rfl, by decide, by decide, by decide, by decide, ?_, ?_, ?_, ?_⟩ <;>
        (simp only [equalK3Boxes17, List.getElem_cons_zero, List.getElem_cons_succ]; omega)
    · by_cases h3r : 31 * dy ≤ 10 * M
      · simp only [h1, h2, h3r, ↓reduceIte]
        by_cases hx1 : 15 * M ≤ 62 * dx
        · refine ⟨equalK3Boxes17[9]'(by decide), hmem 9 (by decide), rfl, by decide, by decide, by decide, by decide, ?_, ?_, ?_, ?_⟩ <;>
            (simp only [equalK3Boxes17, List.getElem_cons_zero, List.getElem_cons_succ]; omega)
        · by_cases hx2 : 25 * M ≤ 124 * dx
          · refine ⟨equalK3Boxes17[10]'(by decide), hmem 10 (by decide), rfl, by decide, by decide, by decide, by decide, ?_, ?_, ?_, ?_⟩ <;>
              (simp only [equalK3Boxes17, List.getElem_cons_zero, List.getElem_cons_succ]; omega)
          · by_cases hx3 : 31 * dx ≤ 5 * M
            · refine ⟨equalK3Boxes17[14]'(by decide), hmem 14 (by decide), rfl, by decide, by decide, by decide, by decide, ?_, ?_, ?_, ?_⟩ <;>
                (simp only [equalK3Boxes17, List.getElem_cons_zero, List.getElem_cons_succ]; omega)
            · by_cases hy1 : 248 * dy ≤ 71 * M
              · refine ⟨equalK3Boxes17[13]'(by decide), hmem 13 (by decide), rfl, by decide, by decide, by decide, by decide, ?_, ?_, ?_, ?_⟩ <;>
                  (simp only [equalK3Boxes17, List.getElem_cons_zero, List.getElem_cons_succ]; omega)
              · by_cases hx4 : 45 * M ≤ 248 * dx
                · refine ⟨equalK3Boxes17[11]'(by decide), hmem 11 (by decide), rfl, by decide, by decide, by decide, by decide, ?_, ?_, ?_, ?_⟩ <;>
                    (simp only [equalK3Boxes17, List.getElem_cons_zero, List.getElem_cons_succ]; omega)
                · refine ⟨equalK3Boxes17[12]'(by decide), hmem 12 (by decide), rfl, by decide, by decide, by decide, by decide, ?_, ?_, ?_, ?_⟩ <;>
                    (simp only [equalK3Boxes17, List.getElem_cons_zero, List.getElem_cons_succ]; omega)
      · simp only [h1, h2, h3r, ↓reduceIte]
        by_cases hx1 : M ≤ 6 * dx
        · refine ⟨equalK3Boxes17[15]'(by decide), hmem 15 (by decide), rfl, by decide, by decide, by decide, by decide, ?_, ?_, ?_, ?_⟩ <;>
            (simp only [equalK3Boxes17, List.getElem_cons_zero, List.getElem_cons_succ]; omega)
        · refine ⟨equalK3Boxes17[16]'(by decide), hmem 16 (by decide), rfl, by decide, by decide, by decide, by decide, ?_, ?_, ?_, ?_⟩ <;>
            (simp only [equalK3Boxes17, List.getElem_cons_zero, List.getElem_cons_succ]; omega)

/-! ### Exact Rational Scaling Bridge for `checkEqualKBox mult m0` -/

private theorem qAdd_spec' (a b : QPos) (ha : 0 < a.den) (hb : 0 < b.den) :
    0 < (qAdd a b).den ∧
    (qAdd a b).num * (a.den * b.den) = (a.num * b.den + b.num * a.den) * (qAdd a b).den := by
  unfold qAdd; dsimp only
  let n := a.num * b.den + b.num * a.den
  let d := a.den * b.den
  let g := Nat.gcd n d
  have hd_pos : 0 < d := Nat.mul_pos ha hb
  have hg_pos : 0 < g := Nat.gcd_pos_of_pos_right n hd_pos
  have hgn : g ∣ n := Nat.gcd_dvd_left n d
  have hgd : g ∣ d := Nat.gcd_dvd_right n d
  have hden_pos : 0 < d / g := by
    rcases hgd with ⟨q, hq⟩
    have hq_pos : 0 < q := by cases q with | zero => simp at hq; omega | succ k => exact Nat.zero_lt_succ k
    rw [hq, Nat.mul_div_cancel_left q hg_pos]; exact hq_pos
  refine ⟨hden_pos, ?_⟩
  have h1 : (n / g) * g = n := Nat.div_mul_cancel hgn
  have h2 : (d / g) * g = d := Nat.div_mul_cancel hgd
  exact Nat.eq_of_mul_eq_mul_right hg_pos (by
    calc (n / g) * d * g = ((n / g) * g) * d := by ac_rfl
      _ = n * d := by rw [h1]
      _ = n * ((d / g) * g) := by rw [h2]
      _ = n * (d / g) * g := by ac_rfl)

private theorem qMul_spec' (a b : QPos) (ha : 0 < a.den) (hb : 0 < b.den) :
    0 < (qMul a b).den ∧
    (qMul a b).num * (a.den * b.den) = (a.num * b.num) * (qMul a b).den := by
  unfold qMul; dsimp only
  let n := a.num * b.num
  let d := a.den * b.den
  let g := Nat.gcd n d
  have hd_pos : 0 < d := Nat.mul_pos ha hb
  have hg_pos : 0 < g := Nat.gcd_pos_of_pos_right n hd_pos
  have hgn : g ∣ n := Nat.gcd_dvd_left n d
  have hgd : g ∣ d := Nat.gcd_dvd_right n d
  have hden_pos : 0 < d / g := by
    rcases hgd with ⟨q, hq⟩
    have hq_pos : 0 < q := by cases q with | zero => simp at hq; omega | succ k => exact Nat.zero_lt_succ k
    rw [hq, Nat.mul_div_cancel_left q hg_pos]; exact hq_pos
  refine ⟨hden_pos, ?_⟩
  have h1 : (n / g) * g = n := Nat.div_mul_cancel hgn
  have h2 : (d / g) * g = d := Nat.div_mul_cancel hgd
  exact Nat.eq_of_mul_eq_mul_right hg_pos (by
    calc (n / g) * d * g = ((n / g) * g) * d := by ac_rfl
      _ = n * d := by rw [h1]
      _ = n * ((d / g) * g) := by rw [h2]
      _ = n * (d / g) * g := by ac_rfl)

private theorem qSub_spec' (a b : QPos) (ha : 0 < a.den) (hb : 0 < b.den)
    (hle : b.num * a.den ≤ a.num * b.den) :
    0 < (qSub a b).den ∧
    (qSub a b).num * (a.den * b.den) = (a.num * b.den - b.num * a.den) * (qSub a b).den := by
  unfold qSub
  by_cases heq : a.num * b.den ≤ b.num * a.den
  · simp only [heq, ↓reduceIte]
    have h0 : a.num * b.den - b.num * a.den = 0 := by omega
    rw [h0]; simp
  · simp only [heq, ↓reduceIte]
    let n := a.num * b.den - b.num * a.den
    let d := a.den * b.den
    let g := Nat.gcd n d
    have hd_pos : 0 < d := Nat.mul_pos ha hb
    have hg_pos : 0 < g := Nat.gcd_pos_of_pos_right n hd_pos
    have hgn : g ∣ n := Nat.gcd_dvd_left n d
    have hgd : g ∣ d := Nat.gcd_dvd_right n d
    have hden_pos : 0 < d / g := by
      rcases hgd with ⟨q, hq⟩
      have hq_pos : 0 < q := by cases q with | zero => simp at hq; omega | succ k => exact Nat.zero_lt_succ k
      rw [hq, Nat.mul_div_cancel_left q hg_pos]; exact hq_pos
    refine ⟨hden_pos, ?_⟩
    have h1 : (n / g) * g = n := Nat.div_mul_cancel hgn
    have h2 : (d / g) * g = d := Nat.div_mul_cancel hgd
    exact Nat.eq_of_mul_eq_mul_right hg_pos (by
      calc (n / g) * d * g = ((n / g) * g) * d := by ac_rfl
        _ = n * d := by rw [h1]
        _ = n * ((d / g) * g) := by rw [h2]
        _ = n * (d / g) * g := by ac_rfl)

private theorem qAdd_ub' {A B S : Nat} {a b : QPos} (ha : 0 < a.den) (hb : 0 < b.den)
    (hA : A * a.den ≤ S * a.num) (hB : B * b.den ≤ S * b.num) :
    (A + B) * (qAdd a b).den ≤ S * (qAdd a b).num := by
  rcases qAdd_spec' a b ha hb with ⟨_, heq⟩
  have hsum : (A + B) * (a.den * b.den) ≤ S * (a.num * b.den + b.num * a.den) := by
    rw [Nat.add_mul, Nat.mul_add]
    exact Nat.add_le_add
      (by calc A * (a.den * b.den) = (A * a.den) * b.den := by ac_rfl
            _ ≤ (S * a.num) * b.den := Nat.mul_le_mul_right b.den hA
            _ = S * (a.num * b.den) := by ac_rfl)
      (by calc B * (a.den * b.den) = (B * b.den) * a.den := by ac_rfl
            _ ≤ (S * b.num) * a.den := Nat.mul_le_mul_right a.den hB
            _ = S * (b.num * a.den) := by ac_rfl)
  exact Nat.le_of_mul_le_mul_right (by
    calc (A + B) * (qAdd a b).den * (a.den * b.den)
        = (A + B) * (a.den * b.den) * (qAdd a b).den := by ac_rfl
      _ ≤ S * (a.num * b.den + b.num * a.den) * (qAdd a b).den := Nat.mul_le_mul_right _ hsum
      _ = S * ((a.num * b.den + b.num * a.den) * (qAdd a b).den) := by ac_rfl
      _ = S * ((qAdd a b).num * (a.den * b.den)) := by rw [← heq]
      _ = S * (qAdd a b).num * (a.den * b.den) := by ac_rfl) (Nat.mul_pos ha hb)

private theorem qMul_ub' {A B S1 S2 : Nat} {a b : QPos} (ha : 0 < a.den) (hb : 0 < b.den)
    (hA : A * a.den ≤ S1 * a.num) (hB : B * b.den ≤ S2 * b.num) :
    (A * B) * (qMul a b).den ≤ (S1 * S2) * (qMul a b).num := by
  rcases qMul_spec' a b ha hb with ⟨_, heq⟩
  have hprod : (A * B) * (a.den * b.den) ≤ (S1 * S2) * (a.num * b.num) := by
    calc (A * B) * (a.den * b.den) = (A * a.den) * (B * b.den) := by ac_rfl
      _ ≤ (S1 * a.num) * (S2 * b.num) := Nat.mul_le_mul hA hB
      _ = (S1 * S2) * (a.num * b.num) := by ac_rfl
  exact Nat.le_of_mul_le_mul_right (by
    calc (A * B) * (qMul a b).den * (a.den * b.den)
        = (A * B) * (a.den * b.den) * (qMul a b).den := by ac_rfl
      _ ≤ (S1 * S2) * (a.num * b.num) * (qMul a b).den := Nat.mul_le_mul_right _ hprod
      _ = (S1 * S2) * ((a.num * b.num) * (qMul a b).den) := by ac_rfl
      _ = (S1 * S2) * ((qMul a b).num * (a.den * b.den)) := by rw [← heq]
      _ = (S1 * S2) * (qMul a b).num * (a.den * b.den) := by ac_rfl) (Nat.mul_pos ha hb)

private theorem qMin_ub' {A B S : Nat} {a b : QPos}
    (hA : A * a.den ≤ S * a.num) (hB : B * b.den ≤ S * b.num) :
    min A B * (qMin a b).den ≤ S * (qMin a b).num := by
  unfold qMin; split
  · exact Nat.le_trans (Nat.mul_le_mul_right a.den (Nat.min_le_left A B)) hA
  · exact Nat.le_trans (Nat.mul_le_mul_right b.den (Nat.min_le_right A B)) hB

private theorem qMax_ub' {A B S : Nat} {a b : QPos} (ha : 0 < a.den) (hb : 0 < b.den)
    (hA : A * a.den ≤ S * a.num) (hB : B * b.den ≤ S * b.num) :
    max A B * (qMax a b).den ≤ S * (qMax a b).num := by
  unfold qMax; split
  · rename_i hle
    have hA_b : A * b.den ≤ S * b.num := Nat.le_of_mul_le_mul_right (by
      calc A * b.den * a.den = (A * a.den) * b.den := by ac_rfl
        _ ≤ (S * a.num) * b.den := Nat.mul_le_mul_right b.den hA
        _ = S * (a.num * b.den) := by ac_rfl
        _ ≤ S * (b.num * a.den) := Nat.mul_le_mul_left S hle
        _ = S * b.num * a.den := by ac_rfl) ha
    have hmx : max A B * b.den = max (A * b.den) (B * b.den) := by
      by_cases hab : A ≤ B
      · rw [Nat.max_eq_right hab, Nat.max_eq_right (Nat.mul_le_mul_right b.den hab)]
      · rw [Nat.max_eq_left (by omega), Nat.max_eq_left (Nat.mul_le_mul_right b.den (by omega))]
    rw [hmx]; exact Nat.max_le.mpr ⟨hA_b, hB⟩
  · rename_i hgt
    have hge : b.num * a.den ≤ a.num * b.den := by omega
    have hB_a : B * a.den ≤ S * a.num := Nat.le_of_mul_le_mul_right (by
      calc B * a.den * b.den = (B * b.den) * a.den := by ac_rfl
        _ ≤ (S * b.num) * a.den := Nat.mul_le_mul_right a.den hB
        _ = S * (b.num * a.den) := by ac_rfl
        _ ≤ S * (a.num * b.den) := Nat.mul_le_mul_left S hge
        _ = S * a.num * b.den := by ac_rfl) hb
    have hmx : max A B * a.den = max (A * a.den) (B * a.den) := by
      by_cases hab : A ≤ B
      · rw [Nat.max_eq_right hab, Nat.max_eq_right (Nat.mul_le_mul_right a.den hab)]
      · rw [Nat.max_eq_left (by omega), Nat.max_eq_left (Nat.mul_le_mul_right a.den (by omega))]
    rw [hmx]; exact Nat.max_le.mpr ⟨hA, hB_a⟩

/-- Generic scaling bridge: if `b` covers `(dx/M, dy/M)` with `M ≥ max 2048 m0` and
`checkEqualKBox mult m0 b = true`, then `EqualKPairClosed mult M x y` holds! -/
private theorem equalK_box_sound (mult m0 M x y : Nat) (b : TailBox)
    (hM2048 : M ≥ 2048) (hMm0 : M ≥ m0)
    (hx1 : M < x) (hxy : x ≤ y) (_hy2 : y ≤ (4 * M) / 3)
    (htpl : (b.n, b.k) = r5Template M (y - M))
    (hxlo_pos : 0 < b.xlo.den) (hxhi_pos : 0 < b.xhi.den)
    (hylo_pos : 0 < b.ylo.den) (hyhi_pos : 0 < b.yhi.den)
    (hxlo_le : b.xlo.num * M ≤ (x - M) * b.xlo.den)
    (hxhi_le : (x - M) * b.xhi.den ≤ b.xhi.num * M)
    (hylo_le : b.ylo.num * M ≤ (y - M) * b.ylo.den)
    (hyhi_le : (y - M) * b.yhi.den ≤ b.yhi.num * M)
    (hchk : checkEqualKBox mult m0 b = true) :
    EqualKPairClosed mult M x y := by
  let dx := x - M
  let dy := y - M
  have hbk_pos : 0 < b.k ∧ b.n < b.k := by
    have ht := htpl; unfold r5Template at ht
    split at ht
    · simp only [Prod.mk.injEq] at ht; omega
    · split at ht
      · simp only [Prod.mk.injEq] at ht; omega
      · split at ht
        · simp only [Prod.mk.injEq] at ht; omega
        · simp only [Prod.mk.injEq] at ht; omega
  unfold checkEqualKBox at hchk; dsimp only at hchk
  let eps : QPos := ⟨1, 2048⟩
  let eps2 : QPos := ⟨1, 1024⟩
  let third : QPos := ⟨1, 3⟩
  let one : QPos := ⟨1, 1⟩
  let loTerm1 := qMul ⟨b.k - b.n, b.k⟩ (qAdd one b.yhi)
  let loTerm2 := qMul ⟨9, 4⟩ b.yhi
  have hlo_gt : loTerm2.num * loTerm1.den < loTerm1.num * loTerm2.den := by
    by_cases hbad : loTerm1.num * loTerm2.den ≤ loTerm2.num * loTerm1.den
    · change (if loTerm1.num * loTerm2.den ≤ loTerm2.num * loTerm1.den then false else _) = true at hchk
      simp only [hbad, ↓reduceIte] at hchk; cases hchk
    · omega
  have hnotbad : ¬(loTerm1.num * loTerm2.den ≤ loTerm2.num * loTerm1.den) := by omega
  change (if loTerm1.num * loTerm2.den ≤ loTerm2.num * loTerm1.den then false else _) = true at hchk
  simp only [hnotbad, ↓reduceIte, Bool.and_eq_true] at hchk
  rcases hchk with ⟨hok1, hok2⟩
  let lower := qSub loTerm1 loTerm2
  let width := qAdd (qAdd b.xhi b.yhi) eps
  let imb := qSub third b.xlo
  let rad := qSub third (qMul ⟨1, 2⟩ (qAdd b.xlo b.ylo))
  let s1a := qAdd (qMin width (qMul ⟨3, 1⟩ imb)) eps2
  let s1 := qMul s1a s1a
  let s2 := qMul (qAdd width eps2) (qAdd (qMin width (qMul ⟨2, 1⟩ imb)) eps2)
  let single := qMax s1 s2
  let b1 := qAdd (qMin width rad) eps2
  let both := qMul b1 b1
  have h1_lt : (3 * mult) ^ 256 * single.num ^ 123 * lower.den ^ 256 <
               (5 * lower.num) ^ 256 * m0 ^ 10 * single.den ^ 123 :=
    Nat.le_of_ble_eq_true hok1
  have h2_lt : (6 * mult) ^ 256 * both.num ^ 123 * lower.den ^ 256 <
               (5 * lower.num) ^ 256 * m0 ^ 10 * both.den ^ 123 :=
    Nat.le_of_ble_eq_true hok2
  -- Lower bound `M * lower.num ≤ r5AttachLower M dy * lower.den`:
  have hone_add := qAdd_spec' one b.yhi (by decide) hyhi_pos
  have hlt1_spec := qMul_spec' ⟨b.k - b.n, b.k⟩ (qAdd one b.yhi) hbk_pos.1 hone_add.1
  have hlt2_spec := qMul_spec' ⟨9, 4⟩ b.yhi (by decide) hyhi_pos
  have hlower_spec := qSub_spec' loTerm1 loTerm2 hlt1_spec.1 hlt2_spec.1 (Nat.le_of_lt hlo_gt)
  have hlower_M : M * lower.num ≤ r5AttachLower M dy * lower.den := by
    have hr5_mul : (4 * b.k) * r5AttachLower M dy + (5 * b.k + 4 * b.n) * dy ≥ 4 * (b.k - b.n) * M := by
      unfold r5AttachLower; rw [← htpl]; dsimp only
      have h1 : 4 * ((9 * (dy - 1)) / 4) ≤ 9 * dy := by omega
      have h2 : b.k * ((b.n * (M + dy)) / b.k) ≤ b.n * (M + dy) := Nat.mul_div_le (b.n * (M + dy)) b.k
      have hkn : (b.k - b.n) * M + b.n * M = b.k * M := by
        rw [← Nat.add_mul, Nat.sub_add_cancel (Nat.le_of_lt hbk_pos.2)]
      have hsub : (M + dy) - (9 * (dy - 1)) / 4 - (b.n * (M + dy)) / b.k +
                  (9 * (dy - 1)) / 4 + (b.n * (M + dy)) / b.k ≥ M + dy := by omega
      have hA : 4 * b.k * ((9 * (dy - 1)) / 4) ≤ 9 * b.k * dy := by
        calc 4 * b.k * ((9 * (dy - 1)) / 4) = b.k * (4 * ((9 * (dy - 1)) / 4)) := by ac_rfl
          _ ≤ b.k * (9 * dy) := Nat.mul_le_mul_left b.k h1
          _ = 9 * b.k * dy := by ac_rfl
      have hB : 4 * b.k * ((b.n * (M + dy)) / b.k) ≤ 4 * b.n * M + 4 * b.n * dy := by
        calc 4 * b.k * ((b.n * (M + dy)) / b.k) = 4 * (b.k * ((b.n * (M + dy)) / b.k)) := by ac_rfl
          _ ≤ 4 * (b.n * (M + dy)) := Nat.mul_le_mul_left 4 h2
          _ = 4 * b.n * (M + dy) := by ac_rfl
          _ = 4 * b.n * M + 4 * b.n * dy := Nat.mul_add (4 * b.n) M dy
      have hmul' := Nat.mul_le_mul_left (4 * b.k) hsub
      rw [Nat.mul_add, Nat.mul_add, Nat.mul_add] at hmul'
      have hC : 4 * b.k * M = 4 * (b.k - b.n) * M + 4 * b.n * M := by
        calc 4 * b.k * M = 4 * (b.k * M) := Nat.mul_assoc 4 b.k M
          _ = 4 * ((b.k - b.n) * M + b.n * M) := by rw [hkn]
          _ = 4 * ((b.k - b.n) * M) + 4 * (b.n * M) := Nat.mul_add _ _ _
          _ = 4 * (b.k - b.n) * M + 4 * b.n * M := by rw [← Nat.mul_assoc, ← Nat.mul_assoc]
      have hD : (5 * b.k + 4 * b.n) * dy = 5 * b.k * dy + 4 * b.n * dy := Nat.add_mul _ _ _
      have h59 : 5 * b.k * dy + 4 * b.k * dy = 9 * b.k * dy := by rw [← Nat.add_mul, ← Nat.add_mul]
      rw [hD]; omega
    have hlo_id : lower.num * (4 * b.k * b.yhi.den) + (5 * b.k + 4 * b.n) * b.yhi.num * lower.den =
                  4 * (b.k - b.n) * b.yhi.den * lower.den := by
      have hstep1 : loTerm1.num * (b.k * b.yhi.den) = (b.k - b.n) * (b.yhi.den + b.yhi.num) * loTerm1.den := by
        have hq := hone_add.2; simp only [one, Nat.one_mul, Nat.mul_one] at hq
        exact Nat.eq_of_mul_eq_mul_right hone_add.1 (by
          calc loTerm1.num * (b.k * b.yhi.den) * (qAdd one b.yhi).den
              = loTerm1.num * (b.k * (qAdd one b.yhi).den) * b.yhi.den := by ac_rfl
            _ = (b.k - b.n) * (qAdd one b.yhi).num * loTerm1.den * b.yhi.den := by rw [hlt1_spec.2]
            _ = (b.k - b.n) * ((qAdd one b.yhi).num * b.yhi.den) * loTerm1.den := by ac_rfl
            _ = (b.k - b.n) * ((b.yhi.den + b.yhi.num) * (qAdd one b.yhi).den) * loTerm1.den := by rw [hq]
            _ = (b.k - b.n) * (b.yhi.den + b.yhi.num) * loTerm1.den * (qAdd one b.yhi).den := by ac_rfl)
      have hstep2 : loTerm2.num * (4 * b.yhi.den) = 9 * b.yhi.num * loTerm2.den := hlt2_spec.2
      have hmul_sub :
          (lower.num * (4 * b.k * b.yhi.den) + (5 * b.k + 4 * b.n) * b.yhi.num * lower.den) * (loTerm1.den * loTerm2.den) =
          4 * (b.k - b.n) * b.yhi.den * lower.den * (loTerm1.den * loTerm2.den) := by
        rw [Nat.add_mul]
        have hL : lower.num * (4 * b.k * b.yhi.den) * (loTerm1.den * loTerm2.den) =
                  (loTerm1.num * loTerm2.den - loTerm2.num * loTerm1.den) * lower.den * (4 * b.k * b.yhi.den) := by
          calc lower.num * (4 * b.k * b.yhi.den) * (loTerm1.den * loTerm2.den)
              = (lower.num * (loTerm1.den * loTerm2.den)) * (4 * b.k * b.yhi.den) := by ac_rfl
            _ = ((loTerm1.num * loTerm2.den - loTerm2.num * loTerm1.den) * lower.den) * (4 * b.k * b.yhi.den) := by
                rw [hlower_spec.2]
        rw [hL]
        have hA : loTerm1.num * loTerm2.den * (4 * b.k * b.yhi.den) =
                  4 * (b.k - b.n) * (b.yhi.den + b.yhi.num) * (loTerm1.den * loTerm2.den) := by
          calc loTerm1.num * loTerm2.den * (4 * b.k * b.yhi.den)
              = 4 * (loTerm1.num * (b.k * b.yhi.den)) * loTerm2.den := by ac_rfl
            _ = 4 * ((b.k - b.n) * (b.yhi.den + b.yhi.num) * loTerm1.den) * loTerm2.den := by rw [hstep1]
            _ = 4 * (b.k - b.n) * (b.yhi.den + b.yhi.num) * (loTerm1.den * loTerm2.den) := by ac_rfl
        have hB : loTerm2.num * loTerm1.den * (4 * b.k * b.yhi.den) =
                  9 * b.k * b.yhi.num * (loTerm1.den * loTerm2.den) := by
          calc loTerm2.num * loTerm1.den * (4 * b.k * b.yhi.den)
              = b.k * (loTerm2.num * (4 * b.yhi.den)) * loTerm1.den := by ac_rfl
            _ = b.k * (9 * b.yhi.num * loTerm2.den) * loTerm1.den := by rw [hstep2]
            _ = 9 * b.k * b.yhi.num * (loTerm1.den * loTerm2.den) := by ac_rfl
        have hsub_dist :
            (loTerm1.num * loTerm2.den - loTerm2.num * loTerm1.den) * lower.den * (4 * b.k * b.yhi.den) =
            (loTerm1.num * loTerm2.den * (4 * b.k * b.yhi.den) -
             loTerm2.num * loTerm1.den * (4 * b.k * b.yhi.den)) * lower.den := by
          rw [Nat.sub_mul, Nat.sub_mul, Nat.sub_mul]; ac_rfl
        rw [hsub_dist, hA, hB]
        have hkn_add : 4 * (b.k - b.n) * b.yhi.num + (5 * b.k + 4 * b.n) * b.yhi.num = 9 * b.k * b.yhi.num := by
          have hk4 : 4 * (b.k - b.n) + 4 * b.n = 4 * b.k := by
            rw [← Nat.mul_add, Nat.sub_add_cancel (Nat.le_of_lt hbk_pos.2)]
          rw [← Nat.add_mul, show 4 * (b.k - b.n) + (5 * b.k + 4 * b.n) = 9 * b.k by omega]
        have hge_sub : 9 * b.k * b.yhi.num * (loTerm1.den * loTerm2.den) ≤
                       4 * (b.k - b.n) * (b.yhi.den + b.yhi.num) * (loTerm1.den * loTerm2.den) := by
          rw [← hA, ← hB]; exact Nat.mul_le_mul_right _ (Nat.le_of_lt hlo_gt)
        have hD1 : 4 * (b.k - b.n) * (b.yhi.den + b.yhi.num) * (loTerm1.den * loTerm2.den) =
                   4 * (b.k - b.n) * b.yhi.den * (loTerm1.den * loTerm2.den) +
                   4 * (b.k - b.n) * b.yhi.num * (loTerm1.den * loTerm2.den) := by
          rw [Nat.mul_add, Nat.add_mul]
        have hD2 : 9 * b.k * b.yhi.num * (loTerm1.den * loTerm2.den) =
                   4 * (b.k - b.n) * b.yhi.num * (loTerm1.den * loTerm2.den) +
                   (5 * b.k + 4 * b.n) * b.yhi.num * (loTerm1.den * loTerm2.den) := by
          rw [← hkn_add, Nat.add_mul]
        rw [hD1, hD2] at hge_sub ⊢
        have hcancel :
            (4 * (b.k - b.n) * b.yhi.den * (loTerm1.den * loTerm2.den) +
             4 * (b.k - b.n) * b.yhi.num * (loTerm1.den * loTerm2.den)) -
            (4 * (b.k - b.n) * b.yhi.num * (loTerm1.den * loTerm2.den) +
             (5 * b.k + 4 * b.n) * b.yhi.num * (loTerm1.den * loTerm2.den)) =
            4 * (b.k - b.n) * b.yhi.den * (loTerm1.den * loTerm2.den) -
            (5 * b.k + 4 * b.n) * b.yhi.num * (loTerm1.den * loTerm2.den) := by omega
        rw [hcancel, Nat.sub_mul]
        have hge2 : (5 * b.k + 4 * b.n) * b.yhi.num * (loTerm1.den * loTerm2.den) * lower.den ≤
                    4 * (b.k - b.n) * b.yhi.den * (loTerm1.den * loTerm2.den) * lower.den :=
          Nat.mul_le_mul_right lower.den (by omega)
        have hc1 : (5 * b.k + 4 * b.n) * b.yhi.num * lower.den * (loTerm1.den * loTerm2.den) =
                   (5 * b.k + 4 * b.n) * b.yhi.num * (loTerm1.den * loTerm2.den) * lower.den := by ac_rfl
        have hc2 : 4 * (b.k - b.n) * b.yhi.den * (loTerm1.den * loTerm2.den) * lower.den =
                   4 * (b.k - b.n) * b.yhi.den * lower.den * (loTerm1.den * loTerm2.den) := by ac_rfl
        rw [hc1, Nat.sub_add_cancel hge2, hc2]
      exact Nat.eq_of_mul_eq_mul_right (Nat.mul_pos hlt1_spec.1 hlt2_spec.1) hmul_sub
    have hmul_pos : 0 < 4 * b.k * b.yhi.den := Nat.mul_pos (Nat.mul_pos (by decide) hbk_pos.1) hyhi_pos
    have hineq : M * lower.num * (4 * b.k * b.yhi.den) + (5 * b.k + 4 * b.n) * (b.yhi.num * M) * lower.den ≤
                 r5AttachLower M dy * lower.den * (4 * b.k * b.yhi.den) + (5 * b.k + 4 * b.n) * (b.yhi.num * M) * lower.den := by
      have hL : M * lower.num * (4 * b.k * b.yhi.den) + (5 * b.k + 4 * b.n) * (b.yhi.num * M) * lower.den =
                4 * (b.k - b.n) * M * b.yhi.den * lower.den := by
        calc M * lower.num * (4 * b.k * b.yhi.den) + (5 * b.k + 4 * b.n) * (b.yhi.num * M) * lower.den
            = M * (lower.num * (4 * b.k * b.yhi.den) + (5 * b.k + 4 * b.n) * b.yhi.num * lower.den) := by
                rw [Nat.mul_add]; congr 1 <;> ac_rfl
          _ = M * (4 * (b.k - b.n) * b.yhi.den * lower.den) := by rw [hlo_id]
          _ = 4 * (b.k - b.n) * M * b.yhi.den * lower.den := by ac_rfl
      rw [hL]
      have hstep := Nat.mul_le_mul_right (b.yhi.den * lower.den) hr5_mul
      rw [Nat.add_mul] at hstep
      have hdy_ub : (5 * b.k + 4 * b.n) * dy * (b.yhi.den * lower.den) ≤
                    (5 * b.k + 4 * b.n) * (b.yhi.num * M) * lower.den := by
        calc (5 * b.k + 4 * b.n) * dy * (b.yhi.den * lower.den)
            = (5 * b.k + 4 * b.n) * (dy * b.yhi.den) * lower.den := by ac_rfl
          _ ≤ (5 * b.k + 4 * b.n) * (b.yhi.num * M) * lower.den :=
              Nat.mul_le_mul_right lower.den (Nat.mul_le_mul_left _ hyhi_le)
      calc 4 * (b.k - b.n) * M * b.yhi.den * lower.den
          = 4 * (b.k - b.n) * M * (b.yhi.den * lower.den) := by ac_rfl
        _ ≤ 4 * b.k * r5AttachLower M dy * (b.yhi.den * lower.den) +
            (5 * b.k + 4 * b.n) * dy * (b.yhi.den * lower.den) := hstep
        _ ≤ 4 * b.k * r5AttachLower M dy * (b.yhi.den * lower.den) +
            (5 * b.k + 4 * b.n) * (b.yhi.num * M) * lower.den := Nat.add_le_add_left hdy_ub _
        _ = r5AttachLower M dy * lower.den * (4 * b.k * b.yhi.den) +
            (5 * b.k + 4 * b.n) * (b.yhi.num * M) * lower.den := by congr 1; ac_rfl
    exact Nat.le_of_mul_le_mul_right (Nat.le_of_add_le_add_right hineq) hmul_pos
  -- Geometric upper bounds:
  unfold EqualKPairClosed; dsimp only; intro hK
  let K := (4 * M) / 3
  let lo := r5AttachLower M dy
  let r := lo + (if lo ≥ x then (lo - x) % 2 else (x - lo) % 2)
  have hM_lower_r : M * lower.num ≤ r * lower.den :=
    Nat.le_trans hlower_M (Nat.mul_le_mul_right lower.den (by dsimp only [r]; omega))
  let W := x + y + 1 - 2 * M
  have hW_eq : W = dx + dy + 1 := by omega
  have hxy_add := qAdd_spec' b.xhi b.yhi hxhi_pos hyhi_pos
  have hwidth_spec := qAdd_spec' (qAdd b.xhi b.yhi) eps hxy_add.1 (by decide)
  have hW_ub : W * width.den ≤ M * width.num := by
    rw [hW_eq]
    exact qAdd_ub' hxy_add.1 (by decide)
      (qAdd_ub' hxhi_pos hyhi_pos (by rw [Nat.mul_comm M b.xhi.num]; exact hxhi_le)
        (by rw [Nat.mul_comm M b.yhi.num]; exact hyhi_le))
      (by dsimp only [eps]; omega)
  have himb_le : b.xlo.num * third.den ≤ third.num * b.xlo.den :=
    Nat.le_of_mul_le_mul_right (by
      calc b.xlo.num * 3 * M = 3 * (b.xlo.num * M) := by ac_rfl
        _ ≤ 3 * (dx * b.xlo.den) := Nat.mul_le_mul_left 3 hxlo_le
        _ = (3 * dx) * b.xlo.den := by ac_rfl
        _ ≤ M * b.xlo.den := Nat.mul_le_mul_right b.xlo.den (by omega)
        _ = 1 * b.xlo.den * M := by simp [Nat.mul_comm]) (by omega : 0 < M)
  have himb_spec := qSub_spec' third b.xlo (by decide) hxlo_pos himb_le
  let e := K - x - 2
  have he_ub : e * imb.den ≤ M * imb.num := by
    have h3e : 3 * e + 3 * dx ≤ M := by omega
    exact Nat.le_of_mul_le_mul_right (by
      have h1 : e * (3 * b.xlo.den) ≤ M * (1 * b.xlo.den - b.xlo.num * 3) := by
        have hstep : e * (3 * b.xlo.den) + (b.xlo.num * 3) * M ≤ (1 * b.xlo.den) * M := by
          calc e * (3 * b.xlo.den) + (b.xlo.num * 3) * M
              = (3 * e) * b.xlo.den + 3 * (b.xlo.num * M) := by ac_rfl
            _ ≤ (3 * e) * b.xlo.den + 3 * (dx * b.xlo.den) := Nat.add_le_add_left (Nat.mul_le_mul_left 3 hxlo_le) _
            _ = (3 * e + 3 * dx) * b.xlo.den := by rw [Nat.add_mul]; congr 1; ac_rfl
            _ ≤ M * b.xlo.den := Nat.mul_le_mul_right b.xlo.den h3e
            _ = (1 * b.xlo.den) * M := by simp [Nat.mul_comm]
        rw [Nat.mul_sub]
        have hcomm1 : M * (1 * b.xlo.den) = (1 * b.xlo.den) * M := Nat.mul_comm _ _
        have hcomm2 : M * (b.xlo.num * 3) = (b.xlo.num * 3) * M := Nat.mul_comm _ _
        omega
      calc e * imb.den * (3 * b.xlo.den) = e * (3 * b.xlo.den) * imb.den := by ac_rfl
        _ ≤ M * (1 * b.xlo.den - b.xlo.num * 3) * imb.den := Nat.mul_le_mul_right imb.den h1
        _ = M * ((1 * b.xlo.den - b.xlo.num * 3) * imb.den) := by ac_rfl
        _ = M * (imb.num * (3 * b.xlo.den)) := by rw [← himb_spec.2]
        _ = M * imb.num * (3 * b.xlo.den) := by ac_rfl) (Nat.mul_pos (by decide) hxlo_pos)
  have h3imb_spec := qMul_spec' ⟨3, 1⟩ imb (by decide) himb_spec.1
  have h2imb_spec := qMul_spec' ⟨2, 1⟩ imb (by decide) himb_spec.1
  have h3e_ub : (3 * e) * (qMul ⟨3, 1⟩ imb).den ≤ M * (qMul ⟨3, 1⟩ imb).num := by
    have h3 : 3 * (⟨3, 1⟩ : QPos).den ≤ 1 * (⟨3, 1⟩ : QPos).num := by decide
    simpa [Nat.one_mul] using qMul_ub' (a := ⟨3, 1⟩) (b := imb) (by decide) himb_spec.1 h3 he_ub
  have h2e_ub : (2 * e) * (qMul ⟨2, 1⟩ imb).den ≤ M * (qMul ⟨2, 1⟩ imb).num := by
    have h2 : 2 * (⟨2, 1⟩ : QPos).den ≤ 1 * (⟨2, 1⟩ : QPos).num := by decide
    simpa [Nat.one_mul] using qMul_ub' (a := ⟨2, 1⟩) (b := imb) (by decide) himb_spec.1 h2 he_ub
  have h2_ub : 2 * eps2.den ≤ M * eps2.num := by dsimp only [eps2]; omega
  have hmin3_pos : 0 < (qMin width (qMul ⟨3, 1⟩ imb)).den := by
    unfold qMin; split; exact hwidth_spec.1; exact h3imb_spec.1
  have hmin2_pos : 0 < (qMin width (qMul ⟨2, 1⟩ imb)).den := by
    unfold qMin; split; exact hwidth_spec.1; exact h2imb_spec.1
  have hs1a_spec := qAdd_spec' (qMin width (qMul ⟨3, 1⟩ imb)) eps2 hmin3_pos (by decide)
  have hs1_spec := qMul_spec' s1a s1a hs1a_spec.1 hs1a_spec.1
  have hw2_spec := qAdd_spec' width eps2 hwidth_spec.1 (by decide)
  have hs2b_spec := qAdd_spec' (qMin width (qMul ⟨2, 1⟩ imb)) eps2 hmin2_pos (by decide)
  have hs2_spec := qMul_spec' (qAdd width eps2) (qAdd (qMin width (qMul ⟨2, 1⟩ imb)) eps2) hw2_spec.1 hs2b_spec.1
  have hP_ub : max ((min W (3 * e) + 2) * (min W (3 * e) + 2)) ((W + 2) * (min W (2 * e) + 2)) * single.den ≤
               (M * M) * single.num := by
    have hA := qAdd_ub' hmin3_pos (by decide) (qMin_ub' hW_ub h3e_ub) h2_ub
    exact qMax_ub' hs1_spec.1 hs2_spec.1
      (qMul_ub' hs1a_spec.1 hs1a_spec.1 hA hA)
      (qMul_ub' hw2_spec.1 hs2b_spec.1
        (qAdd_ub' hwidth_spec.1 (by decide) hW_ub h2_ub)
        (qAdd_ub' hmin2_pos (by decide) (qMin_ub' hW_ub h2e_ub) h2_ub))
  have hM10 : m0 ^ 10 ≤ M ^ 10 := Nat.pow_le_pow_left hMm0 10
  have hM256 : M ^ 10 * (M * M) ^ 123 = M ^ 256 := by
    rw [← Nat.pow_two, ← Nat.pow_mul, ← Nat.pow_add]
  have hlow_pow : (5 * lower.num) ^ 256 * M ^ 256 ≤ (5 * r) ^ 256 * lower.den ^ 256 := by
    have h5 : 5 * M * lower.num ≤ 5 * r * lower.den := by
      calc 5 * M * lower.num = 5 * (M * lower.num) := by ac_rfl
        _ ≤ 5 * (r * lower.den) := Nat.mul_le_mul_left 5 hM_lower_r
        _ = 5 * r * lower.den := by ac_rfl
    have hp := Nat.pow_le_pow_left h5 256
    simp only [Nat.mul_pow] at hp ⊢
    calc 5 ^ 256 * lower.num ^ 256 * M ^ 256 = 5 ^ 256 * M ^ 256 * lower.num ^ 256 := by ac_rfl
      _ ≤ 5 ^ 256 * r ^ 256 * lower.den ^ 256 := hp
  constructor
  · let P := max ((min W (3 * e) + 2) * (min W (3 * e) + 2)) ((W + 2) * (min W (2 * e) + 2))
    have hP_pow : P ^ 123 * single.den ^ 123 ≤ (M * M) ^ 123 * single.num ^ 123 := by
      rw [← Nat.mul_pow, ← Nat.mul_pow]; exact Nat.pow_le_pow_left hP_ub 123
    have hM2_pos : 0 < (M * M) ^ 123 := Nat.pow_pos (Nat.mul_pos (by omega) (by omega))
    have hlt : (3 * mult) ^ 256 * P ^ 123 * (single.den ^ 123 * lower.den ^ 256) <
               (5 * r) ^ 256 * (single.den ^ 123 * lower.den ^ 256) := by
      generalize (3 * mult) ^ 256 = C3, (5 * lower.num) ^ 256 = L5, (5 * r) ^ 256 = R5,
                 m0 ^ 10 = M010, M ^ 10 = M10, (M * M) ^ 123 = MM, M ^ 256 = M256,
                 P ^ 123 = P123, single.num ^ 123 = SN, single.den ^ 123 = SD,
                 lower.den ^ 256 = LD at h1_lt hM10 hM256 hlow_pow hP_pow hM2_pos ⊢
      calc C3 * P123 * (SD * LD)
          = C3 * (P123 * SD) * LD := by ac_rfl
        _ ≤ C3 * (MM * SN) * LD := Nat.mul_le_mul_right LD (Nat.mul_le_mul_left C3 hP_pow)
        _ = (C3 * SN * LD) * MM := by ac_rfl
        _ < (L5 * M010 * SD) * MM := Nat.mul_lt_mul_of_pos_right h1_lt hM2_pos
        _ ≤ (L5 * M10 * SD) * MM := Nat.mul_le_mul_right MM (Nat.mul_le_mul_right SD (Nat.mul_le_mul_left L5 hM10))
        _ = (L5 * (M10 * MM)) * SD := by ac_rfl
        _ = (L5 * M256) * SD := by rw [hM256]
        _ ≤ (R5 * LD) * SD := Nat.mul_le_mul_right SD hlow_pow
        _ = R5 * (SD * LD) := by ac_rfl
    exact Nat.lt_of_mul_lt_mul_right hlt
  · intro hwrap
    let twoR := min (2 * W) (2 * K - x - y - 4)
    have hxy_lo := qAdd_spec' b.xlo b.ylo hxlo_pos hylo_pos
    have hhalf_lo := qMul_spec' ⟨1, 2⟩ (qAdd b.xlo b.ylo) (by decide) hxy_lo.1
    have hq_le : (qAdd b.xlo b.ylo).num * M ≤ (dx + dy) * (qAdd b.xlo b.ylo).den := by
      have hsum_dx : (b.xlo.num * b.ylo.den + b.ylo.num * b.xlo.den) * M ≤ (dx + dy) * (b.xlo.den * b.ylo.den) := by
        rw [Nat.add_mul, Nat.add_mul]
        exact Nat.add_le_add
          (by calc b.xlo.num * b.ylo.den * M = (b.xlo.num * M) * b.ylo.den := by ac_rfl
                _ ≤ (dx * b.xlo.den) * b.ylo.den := Nat.mul_le_mul_right _ hxlo_le
                _ = dx * (b.xlo.den * b.ylo.den) := by ac_rfl)
          (by calc b.ylo.num * b.xlo.den * M = (b.ylo.num * M) * b.xlo.den := by ac_rfl
                _ ≤ (dy * b.ylo.den) * b.xlo.den := Nat.mul_le_mul_right _ hylo_le
                _ = dy * (b.xlo.den * b.ylo.den) := by ac_rfl)
      exact Nat.le_of_mul_le_mul_right (by
        calc (qAdd b.xlo b.ylo).num * M * (b.xlo.den * b.ylo.den)
            = ((qAdd b.xlo b.ylo).num * (b.xlo.den * b.ylo.den)) * M := by ac_rfl
          _ = ((b.xlo.num * b.ylo.den + b.ylo.num * b.xlo.den) * (qAdd b.xlo b.ylo).den) * M := by rw [hxy_lo.2]
          _ = ((b.xlo.num * b.ylo.den + b.ylo.num * b.xlo.den) * M) * (qAdd b.xlo b.ylo).den := by ac_rfl
          _ ≤ ((dx + dy) * (b.xlo.den * b.ylo.den)) * (qAdd b.xlo b.ylo).den := Nat.mul_le_mul_right _ hsum_dx
          _ = (dx + dy) * (qAdd b.xlo b.ylo).den * (b.xlo.den * b.ylo.den) := by ac_rfl)
        (Nat.mul_pos hxlo_pos hylo_pos)
    have hhalf_lb : (qMul ⟨1, 2⟩ (qAdd b.xlo b.ylo)).num * (2 * M) ≤
                    (dx + dy) * (qMul ⟨1, 2⟩ (qAdd b.xlo b.ylo)).den :=
      Nat.le_of_mul_le_mul_right (by
        calc (qMul ⟨1, 2⟩ (qAdd b.xlo b.ylo)).num * (2 * M) * (qAdd b.xlo b.ylo).den
            = ((qMul ⟨1, 2⟩ (qAdd b.xlo b.ylo)).num * (2 * (qAdd b.xlo b.ylo).den)) * M := by ac_rfl
          _ = ((1 * (qAdd b.xlo b.ylo).num) * (qMul ⟨1, 2⟩ (qAdd b.xlo b.ylo)).den) * M := by rw [hhalf_lo.2]
          _ = ((qAdd b.xlo b.ylo).num * M) * (qMul ⟨1, 2⟩ (qAdd b.xlo b.ylo)).den := by simp; ac_rfl
          _ ≤ ((dx + dy) * (qAdd b.xlo b.ylo).den) * (qMul ⟨1, 2⟩ (qAdd b.xlo b.ylo)).den := Nat.mul_le_mul_right _ hq_le
          _ = (dx + dy) * (qMul ⟨1, 2⟩ (qAdd b.xlo b.ylo)).den * (qAdd b.xlo b.ylo).den := by ac_rfl) hxy_lo.1
    have hhalf_le_third : (qMul ⟨1, 2⟩ (qAdd b.xlo b.ylo)).num * third.den ≤
                          third.num * (qMul ⟨1, 2⟩ (qAdd b.xlo b.ylo)).den := by
      have h3dxdy : 3 * (dx + dy) ≤ 2 * M := by omega
      exact Nat.le_of_mul_le_mul_right (by
        calc (qMul ⟨1, 2⟩ (qAdd b.xlo b.ylo)).num * 3 * (2 * M)
            = 3 * ((qMul ⟨1, 2⟩ (qAdd b.xlo b.ylo)).num * (2 * M)) := by ac_rfl
          _ ≤ 3 * ((dx + dy) * (qMul ⟨1, 2⟩ (qAdd b.xlo b.ylo)).den) := Nat.mul_le_mul_left 3 hhalf_lb
          _ = (3 * (dx + dy)) * (qMul ⟨1, 2⟩ (qAdd b.xlo b.ylo)).den := by ac_rfl
          _ ≤ (2 * M) * (qMul ⟨1, 2⟩ (qAdd b.xlo b.ylo)).den := Nat.mul_le_mul_right _ h3dxdy
          _ = 1 * (qMul ⟨1, 2⟩ (qAdd b.xlo b.ylo)).den * (2 * M) := by simp; ac_rfl) (by omega : 0 < 2 * M)
    have hrad_spec := qSub_spec' third (qMul ⟨1, 2⟩ (qAdd b.xlo b.ylo)) (by decide) hhalf_lo.1 hhalf_le_third
    have hrem_ub : (2 * K - x - y - 4) * rad.den ≤ (2 * M) * rad.num := by
      have h3rem : 3 * (2 * K - x - y - 4) + 3 * (dx + dy) ≤ 2 * M := by omega
      let hq := qMul ⟨1, 2⟩ (qAdd b.xlo b.ylo)
      have h1 : (2 * K - x - y - 4) * (3 * hq.den) ≤ (2 * M) * (1 * hq.den - hq.num * 3) := by
        have hstep : (2 * K - x - y - 4) * (3 * hq.den) + (hq.num * 3) * (2 * M) ≤ (1 * hq.den) * (2 * M) := by
          calc (2 * K - x - y - 4) * (3 * hq.den) + (hq.num * 3) * (2 * M)
              = (3 * (2 * K - x - y - 4)) * hq.den + 3 * (hq.num * (2 * M)) := by ac_rfl
            _ ≤ (3 * (2 * K - x - y - 4)) * hq.den + 3 * ((dx + dy) * hq.den) :=
                Nat.add_le_add_left (Nat.mul_le_mul_left 3 hhalf_lb) _
            _ = (3 * (2 * K - x - y - 4) + 3 * (dx + dy)) * hq.den := by
                rw [← Nat.mul_assoc 3 (dx + dy) hq.den, ← Nat.add_mul]
            _ ≤ (2 * M) * hq.den := Nat.mul_le_mul_right hq.den h3rem
            _ = (1 * hq.den) * (2 * M) := by simp [Nat.mul_comm]
        rw [Nat.mul_sub]
        have hc1 : 2 * M * (1 * hq.den) = (1 * hq.den) * (2 * M) := Nat.mul_comm _ _
        have hc2 : 2 * M * (hq.num * 3) = (hq.num * 3) * (2 * M) := Nat.mul_comm _ _
        omega
      exact Nat.le_of_mul_le_mul_right (by
        calc (2 * K - x - y - 4) * rad.den * (3 * hq.den)
            = (2 * K - x - y - 4) * (3 * hq.den) * rad.den := by ac_rfl
          _ ≤ (2 * M) * (1 * hq.den - hq.num * 3) * rad.den := Nat.mul_le_mul_right rad.den h1
          _ = (2 * M) * ((1 * hq.den - hq.num * 3) * rad.den) := by ac_rfl
          _ = (2 * M) * (rad.num * (3 * hq.den)) := by rw [← hrad_spec.2]
          _ = (2 * M) * rad.num * (3 * hq.den) := by ac_rfl) (Nat.mul_pos (by decide) hhalf_lo.1)
    have h2W_ub : (2 * W) * width.den ≤ (2 * M) * width.num := by
      calc (2 * W) * width.den = 2 * (W * width.den) := by ac_rfl
        _ ≤ 2 * (M * width.num) := Nat.mul_le_mul_left 2 hW_ub
        _ = (2 * M) * width.num := by ac_rfl
    have hmin2_pos' : 0 < (qMin width rad).den := by
      unfold qMin; split; exact hwidth_spec.1; exact hrad_spec.1
    have hb1_spec := qAdd_spec' (qMin width rad) eps2 hmin2_pos' (by decide)
    have htwoR4_ub := qAdd_ub' hmin2_pos' (by decide) (qMin_ub' h2W_ub hrem_ub) (by dsimp only [eps2]; omega : 4 * eps2.den ≤ (2 * M) * eps2.num)
    have htwoR4_sq := qMul_ub' hb1_spec.1 hb1_spec.1 htwoR4_ub htwoR4_ub
    have htwoR_pow : (twoR + 4) ^ 246 * both.den ^ 123 ≤ (2 ^ 246 * (M * M) ^ 123) * both.num ^ 123 := by
      have hp : ((twoR + 4) * (twoR + 4)) ^ 123 * both.den ^ 123 ≤
                ((2 * M) * (2 * M)) ^ 123 * both.num ^ 123 := by
        rw [← Nat.mul_pow, ← Nat.mul_pow]; exact Nat.pow_le_pow_left htwoR4_sq 123
      have hsq : ((twoR + 4) * (twoR + 4)) ^ 123 = (twoR + 4) ^ 246 := by rw [← Nat.pow_two, ← Nat.pow_mul]
      have h2M : ((2 * M) * (2 * M)) ^ 123 = 2 ^ 246 * (M * M) ^ 123 := by
        rw [show (2 * M) * (2 * M) = 2 ^ 2 * (M * M) by rw [Nat.pow_two]; ac_rfl, Nat.mul_pow, ← Nat.pow_mul]
      rw [hsq, h2M] at hp; exact hp
    have hc2_pos : 0 < 2 ^ 246 := by decide
    have hM2_pos : 0 < (M * M) ^ 123 := Nat.pow_pos (Nat.mul_pos (by omega) (by omega))
    have hlt : (6 * mult) ^ 256 * (twoR + 4) ^ 246 * (both.den ^ 123 * lower.den ^ 256) <
               (5 * r) ^ 256 * 2 ^ 246 * (both.den ^ 123 * lower.den ^ 256) := by
      generalize (6 * mult) ^ 256 = C6, 2 ^ 246 = c2, m0 ^ 10 = M010,
                 (5 * lower.num) ^ 256 = L5, (5 * r) ^ 256 = R5,
                 (twoR + 4) ^ 246 = T246, (M * M) ^ 123 = MM,
                 both.num ^ 123 = BN, both.den ^ 123 = BD,
                 lower.den ^ 256 = LD, M ^ 10 = M10, M ^ 256 = M256
                 at h2_lt hM10 hM256 hlow_pow htwoR_pow hc2_pos hM2_pos ⊢
      calc C6 * T246 * (BD * LD)
          = C6 * (T246 * BD) * LD := by ac_rfl
        _ ≤ C6 * ((c2 * MM) * BN) * LD := Nat.mul_le_mul_right LD (Nat.mul_le_mul_left C6 htwoR_pow)
        _ = (C6 * BN * LD) * (c2 * MM) := by ac_rfl
        _ < (L5 * M010 * BD) * (c2 * MM) := Nat.mul_lt_mul_of_pos_right h2_lt (Nat.mul_pos hc2_pos hM2_pos)
        _ ≤ (L5 * M10 * BD) * (c2 * MM) := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right BD (Nat.mul_le_mul_left L5 hM10))
        _ = (L5 * (M10 * MM)) * c2 * BD := by ac_rfl
        _ = (L5 * M256) * c2 * BD := by rw [hM256]
        _ ≤ (R5 * LD) * c2 * BD := Nat.mul_le_mul_right BD (Nat.mul_le_mul_right c2 hlow_pow)
        _ = R5 * c2 * (BD * LD) := by ac_rfl
    exact Nat.lt_of_mul_lt_mul_right hlt

/-- **Equal-Block `k = 3` Closure (ALL `M ≥ 2^36`, `17` Certified Rational Boxes):** -/
theorem equal_k3_closure_all_M_ge_2pow36 (M x y : Nat) (hM : M ≥ 2 ^ 36)
    (hx1 : M < x) (hxy : x ≤ y) (hy2 : y ≤ (4 * M) / 3) :
    EqualKPairClosed 2 M x y := by
  have hM2048 : M ≥ 2048 := Nat.le_trans (by decide : 2048 ≤ 2 ^ 36) hM
  have hord : x - M ≤ y - M := Nat.sub_le_sub_right hxy M
  have h3dy : 3 * (y - M) ≤ M := by clear hM; omega
  rcases equalK3Boxes17_domain_coverage M (x - M) (y - M) hM2048 hord h3dy with
    ⟨b, hb_mem, htpl, hxlo_p, hxhi_p, hylo_p, hyhi_p, hxlo_l, hxhi_l, hylo_l, hyhi_l⟩
  exact equalK_box_sound 2 (2 ^ 36) M x y b hM2048 hM hx1 hxy hy2 htpl
    hxlo_p hxhi_p hylo_p hyhi_p hxlo_l hxhi_l hylo_l hyhi_l
    (List.all_eq_true.mp equalK3Boxes17_certified_bool b hb_mem)

/-- **Equal-Block `k = 4` Closure (ALL `M ≥ 2^51`, `17` Certified Rational Boxes):** -/
theorem equal_k4_closure_all_M_ge_2pow51 (M x y : Nat) (hM : M ≥ 2 ^ 51)
    (hx1 : M < x) (hxy : x ≤ y) (hy2 : y ≤ (4 * M) / 3) :
    EqualKPairClosed 3 M x y := by
  have hM2048 : M ≥ 2048 := Nat.le_trans (by decide : 2048 ≤ 2 ^ 51) hM
  have hord : x - M ≤ y - M := Nat.sub_le_sub_right hxy M
  have h3dy : 3 * (y - M) ≤ M := by clear hM; omega
  have heq : equalK4Boxes17 = equalK3Boxes17 := rfl
  rcases equalK3Boxes17_domain_coverage M (x - M) (y - M) hM2048 hord h3dy with
    ⟨b, hb_mem, htpl, hxlo_p, hxhi_p, hylo_p, hyhi_p, hxlo_l, hxhi_l, hylo_l, hyhi_l⟩
  exact equalK_box_sound 3 (2 ^ 51) M x y b hM2048 hM hx1 hxy hy2 htpl
    hxlo_p hxhi_p hylo_p hyhi_p hxlo_l hxhi_l hylo_l hyhi_l
    (List.all_eq_true.mp equalK4Boxes17_certified_bool b (heq ▸ hb_mem))

/-- **Equal-Block `k = 5` Closure (ALL `M ≥ 2^62`, `16` Certified Rational Boxes):** -/
theorem equal_k5_closure_all_M_ge_2pow62 (M x y : Nat) (hM : M ≥ 2 ^ 62)
    (hx1 : M < x) (hxy : x ≤ y) (hy2 : y ≤ (4 * M) / 3) :
    EqualKPairClosed 4 M x y := by
  have hM2048 : M ≥ 2048 := Nat.le_trans (by decide : 2048 ≤ 2 ^ 62) hM
  have hord : x - M ≤ y - M := Nat.sub_le_sub_right hxy M
  have h3dy : 3 * (y - M) ≤ M := by clear hM; omega
  have heq : equalK5Boxes16 = equalTailBoxes16 := rfl
  rcases equalTailBoxes16_domain_coverage M (x - M) (y - M) hM2048 hord h3dy with
    ⟨b, hb_mem, htpl, hxlo_p, hxhi_p, hylo_p, hyhi_p, hxlo_l, hxhi_l, hylo_l, hyhi_l⟩
  exact equalK_box_sound 4 (2 ^ 62) M x y b hM2048 hM hx1 hxy hy2 htpl
    hxlo_p hxhi_p hylo_p hyhi_p hxlo_l hxhi_l hylo_l hyhi_l
    (List.all_eq_true.mp equalK5Boxes16_certified_bool b (heq ▸ hb_mem))

/-! ## 4. R5 Sturmian, Bipartite `15/16`, & Matching-Complement `ℓ`-Cancellation Assembly -/

/-- **Matching-Complement `ℓ`-Cancellation Lemma (ALL `M = 2^m ≥ 16`, `ℓ ∈ {1, 2, 3, 4}`):**
For every even `M ≥ 16` (`3 ∤ M`), every `1 ≤ delta ≤ M/3`, and every `ell ∈ {1, 2, 3, 4}`,
letting `L = M + delta`, `h = (2*M)/3`, `smin = max (M/2 + 1 - ell) (L - h + ell)`,
`smax = min (h - ell) (M/2 + delta - 1 + ell)`: whenever `smin ≤ smax`,
`12 * smin ≥ 5*M + 6*delta + 8`, `12 * (L - smax) ≥ 5*M + 6*delta + 8`, and `6 * (smax - smin) ≤ M - 8`! -/
theorem matching_complement_ell_cancellation (M delta ell : Nat)
    (hM : M ≥ 16) (hMeven : M % 2 = 0) (hM3 : M % 3 ≠ 0)
    (hd1 : 1 ≤ delta) (hd3 : 3 * delta ≤ M)
    (hell : ell = 1 ∨ ell = 2 ∨ ell = 3 ∨ ell = 4) :
    let L := M + delta
    let h := (2 * M) / 3
    let smin := max (M / 2 + 1 - ell) (L - h + ell)
    let smax := min (h - ell) (M / 2 + delta - 1 + ell)
    smin ≤ smax →
      12 * smin ≥ 5 * M + 6 * delta + 8 ∧
      12 * (L - smax) ≥ 5 * M + 6 * delta + 8 ∧
      6 * (smax - smin) ≤ M - 8 := by
  dsimp only
  intro hle
  rcases hell with rfl | rfl | rfl | rfl <;> refine ⟨by omega, by omega, by omega⟩

/-- **R5 Sturmian & Bipartite-Quotient Circumference Arithmetic Assembly:**
Combines the R5 attachment lower bound (`> 3/17 · y`), the R5 circumference upper bound
(`18 * L < 17 * N`, i.e., `c(G) ≤ 3*c(H) < (17/18)|V(G)|` for any dyadic-cycle-free cubic
claw-free `G = T(H)`, whose contrapositive yields `c(G) ≥ (17/18)|V(G)| →` dyadic cycle),
the R11 bipartite-quotient `H` attachment (`> 1/5 · y`) and circumference (`16 * L < 15 * N`,
contrapositive `c(G) ≥ (15/16)|V(G)|` when `H` is bipartite) bounds, AND the symbolic 4-regime
Sturmian dual-forbidden step membership (`r5_sturmian_steps_in_dual_forb_ge64`) for all even
`M ≥ 64` with `3 ∤ M`. -/
theorem r5_sturmian_and_bipartite_assembly :
    (∀ M delta : Nat, M ≥ 16 → 1 ≤ delta → 3 * delta ≤ M →
      17 * r5AttachLower M delta > 3 * (M + delta)) ∧
    (∀ N L vatt : Nat, L ≤ N → 17 * vatt > 3 * L → vatt ≤ 3 * (N - L) →
      18 * L < 17 * N ∧ 18 * (3 * L) < 17 * (3 * N)) ∧
    (∀ M delta : Nat, M ≥ 16 → 2 ≤ delta → 3 * delta ≤ M →
      5 * r11BipAttachLower M delta > M + delta) ∧
    (∀ N L vatt : Nat, L ≤ N → 5 * vatt > L → vatt ≤ 3 * (N - L) →
      16 * L < 15 * N ∧ 16 * (3 * L) < 15 * (3 * N)) ∧
    (∀ M delta : Nat, M ≥ 64 → M % 2 = 0 → M % 3 ≠ 0 → 1 ≤ delta → 3 * delta ≤ M →
      max (M / 2) (M + delta - (2 * M) / 3 + 1) ≤ min ((2 * M) / 3 - 1) (M / 2 + delta) →
      let L := M + delta
      (5 * delta ≤ M + 4 → InR5DualForb M delta (L / 7) ∧ InR5DualForb M delta ((L + 6) / 7)) ∧
      (¬(5 * delta ≤ M + 4) → 4 * delta ≤ M + 2 →
        InR5DualForb M delta (L / 3) ∧ InR5DualForb M delta ((L + 2) / 3)) ∧
      (¬(4 * delta ≤ M + 2) → 31 * delta ≤ 10 * M →
        ∀ s ∈ ([2, 4] : List Nat),
          InR5DualForb M delta ((s * L) / 11) ∧ InR5DualForb M delta ((s * L + 10) / 11)) ∧
      (¬(31 * delta ≤ 10 * M) →
        ∀ s ∈ ([3, 4, 5, 6, 7, 8] : List Nat),
          InR5DualForb M delta ((s * L) / 23) ∧ InR5DualForb M delta ((s * L + 22) / 23))) :=
  ⟨r5_attachment_lower_gt_3_17, r5_circumference_17_18,
   r11_bipartite_attachment_lower_gt_1_5, r11_bipartite_circumference_15_16,
   r5_sturmian_steps_in_dual_forb_ge64⟩

end ClawFreeEG
