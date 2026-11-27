import ClawFreeEG.LiftWindows
import ClawFreeEG.DyadicPackingData
import ClawFreeEG.TwoCycleData

/-!
# ClawFreeEG.TwoCycleClosure

Pure Lean 4 (`v4.36.0`, ZERO Mathlib, ZERO `Std`, ZERO `sorry`, ZERO `axiom`,
ZERO `native_decide`, ZERO `unsafe`/`implemented_by`/`extern`/`partial`) formalization &
kernel verification for the **all-`M = 2^m ≥ 4` arithmetic & certificate closure inequalities**
of Main Theorem 2 (2-Cycle Cubic Claw-Free Graphs):

1. **Unequal Blocks (`M2 > M1`) — ALL `M1 = 2^m ≥ 4` Arithmetic/Certificate Closure:**
   - `M2 ≥ 8 * M1`: `17 * ((4*M1)/3) < 3 * (M2 + 1)` (`unequal_ge_8x_closure`).
   - `M2 = 4 * M1` (Fourfold): symbolic constants (`341/252 > 4/3`, `54/512 < 3/17`),
     separation `lb > 2*M1/9` for `delta2 > 5*M1/9`, universal diamond-packing closure for
     ALL `M1 ≥ 512`, explicit 2-bridge gaps `(17,7), (18,6), (19,6)` for `y = 77`, and
     exact finite closure for ALL `M1 ∈ {4, 8, 16, 32, 64, 128, 256}` (`38,460` pairs via
     direct check on `M1 ≤ 16` + `46` certified `IBoxTree` leaves [`19 + 11 + 9 + 7`] on
     `M1 = 32..256`).
   - `M2 = 2 * M1` (Twofold): symbolic constants (`24*128 / 140^2 < 3/17`, `2/128 < 3/17`),
     universal diamond-packing closure for ALL `M1 ≥ 128`, and exact finite closure for
     ALL `M1 ∈ {4, 8, 16, 32, 64}` (`1,154` pairs directly in kernel).
2. **Equal Blocks (`M2 = M1`) Exact Geometric Identities (ALL `M = 2^m ≥ 4`):**
   - `K + K/2 + 1 = 2*M`, near-class transitivity `2*M - K - 2*(M/3) ∈ {1, 2}`,
     no 3 pairwise-far bridges `4*M + 6 > 3*K`, two-class wraparound margin
     `2*M - 3*(2*K - 2*M - 6) ≥ 18`, plus exact antipodal cluster width sum
     `R1 + R2 ≤ min (2*W) (2*K - x - y - 4)`.
3. **Equal Blocks (`M2 = M1`) — ALL `M = 2^m ≥ 4` Arithmetic/Certificate Closure:**
   - Small `M ∈ {4, 8, 16, 32, 64, 128}`: ALL `625` same-parity pairs directly in kernel
     with semantic reflection theorem `equal_block_small_625_sound` (`SmallEqualPairClosed`,
     using `exactAttachLower` and `F19` base-table fallback when `W ≤ 19` or `twoR ≤ 19`).
   - Medium `M ∈ {256, 512, 1024}`: ALL `76,492` pairs closed universally (`EqualPairClosed`)
     by `61` certified `IBoxTree` leaves (`22 + 23 + 16`).
   - Infinite Tail `M ≥ 2048`: ALL `M = 2^m ≥ 2048` closed universally (`EqualPairClosed`)
     by the exact `16` rational tail boxes from `cert/witnesses/two_cycle_closure.json`
     (proving exact 4-regime domain coverage, pointwise 1-class & 2-class closure, and the
     integer-to-rational scaling bridge).

*Transparent scope boundary (Layers 1–4):* This module proves all numerical/certificate
inequalities for every dyadic block `M = 2^m ≥ 4`. The graph-level reduction (triangle
quotient `H`, spanning 2-factor, bridge-to-packing encoding, parity & attachment lower bounds,
and cycle lift to `G = T(H)`) is proved in full rigor in the LaTeX manuscript (Layer 4).
Note on `exactAttachLower` vs. Python's `exact_attachment_r11`: Lean uses the conservative
lower bound `y` for `M ≤ 8` and `r5AttachLower M (y - M)` for `M ≥ 16`, whereas Python's
`exact_attachment_r11` computes a tighter finite-`M` chord count on small `M` (e.g., at
`(M=16, y=19)`, Lean uses `7` while Python computes `19`); Lean's check is therefore strictly
more conservative. Lean's `46`-leaf and `61`-leaf `IBoxTree` certificates and Python's
exhaustive pair enumeration represent two independently verified representations.
-/

namespace ClawFreeEG

open ClawFreeEG.DyadicPackingData
open ClawFreeEG.TwoCycleData

/-! ## 1. Unequal Blocks (`M2 > M1`): `M2 ≥ 8*M1`, `M2 = 4*M1`, & `M2 = 2*M1` -/

/-- Exact diamond-packing upper bound on the number of bridges between cycles of lengths
`x` and `y` with minimum cyclic separation `sep > 0`. -/
def diamondBound (x y sep : Nat) : Nat :=
  if sep ≤ x then (2 * x * y) / (sep * sep)
  else (2 * y) / (2 * sep - x)

/-- Exact certified attachment lower bound for `y ∈ (M, 4*M/3]` (`M = 2^m ≥ 4`):
`y` for `M ≤ 8` (no permissible chords exist) and `r5AttachLower M (y - M)` for `M ≥ 16`. -/
def exactAttachLower (M y : Nat) : Nat :=
  if M ≤ 8 then y else r5AttachLower M (y - M)

/-- Computable `InFEG` checker for finite verification. -/
def inFegBool (L : Nat) : Bool :=
  if Nat.blt L 3 then false
  else
    let rec go (b : Nat) (fuel : Nat) : Bool :=
      match fuel with
      | 0 => false
      | f + 1 =>
        if Nat.ble (2 * b) L then go (2 * b) f
        else Nat.blt b L && Nat.ble (3 * L) (4 * b)
    go 4 L

/-- Computable 2-bridge permissibility test matching `two_bridge_permissible(x, y, t, d)`. -/
def twoBridgePermissibleBool (x y t d : Nat) : Bool :=
  inFegBool (t + d + 2) &&
  inFegBool (t + y - d + 2) &&
  inFegBool (x - t + d + 2) &&
  inFegBool (x + y - t - d + 2)

/-- **Unequal Block `M2 ≥ 8 * M1` Closure (ALL `M1 ≥ 4`):**
For every `M1 ≥ 4` and `M2 ≥ 8 * M1`, `4 * M1 / 3 < 3 * (M2 + 1) / 17`, so EVERY
`x ≤ (4 * M1) / 3` and `y ∈ (M2, (4 * M2) / 3]` satisfies `x < r5AttachLower M2 (y - M2)`! -/
theorem unequal_ge_8x_closure (M1 M2 : Nat) (hM1 : M1 ≥ 4) (h8 : M2 ≥ 8 * M1) :
    17 * ((4 * M1) / 3) < 3 * (M2 + 1) ∧
    17 * (4 * M1) < 9 * (M2 + 1) ∧
    (∀ x y : Nat, x ≤ (4 * M1) / 3 → M2 < y → 3 * y ≤ 4 * M2 →
      x < r5AttachLower M2 (y - M2)) := by
  refine ⟨by omega, by omega, ?_⟩
  intro x y hx hy1 hy3
  have hM2 : M2 ≥ 16 := by omega
  have hd1 : 1 ≤ y - M2 := by omega
  have hd3 : 3 * (y - M2) ≤ M2 := by omega
  have hr5 := r5_attachment_lower_gt_3_17 M2 (y - M2) hM2 hd1 hd3
  have hy_eq : M2 + (y - M2) = y := by omega
  rw [hy_eq] at hr5
  omega

/-- Exact Fourfold (`M2 = 4 * M1`) symbolic constant inequalities (`341/252 > 4/3`, `54/512 < 3/17`). -/
theorem fourfold_symbolic_constants :
    25 < 4 * 9 ∧
    341 * 3 > 4 * 252 ∧
    25 * 3 > 8 * 9 ∧
    2 * 4 * 81 = 54 * 12 ∧
    54 * 17 < 3 * 512 := by
  decide

/-- **Fourfold Separation Lower Bound (`lb > 2*M1/9` for `delta2 > 5*M1/9`):**
For every `M1 ≥ 4`, `x > M1`, `y = 4*M1 + delta2` with `9 * delta2 > 5 * M1`,
the cyclic separation `sep = x + y + 2 - (16 * M1) / 3` strictly exceeds `2 * M1 / 9`. -/
theorem fourfold_separation_lb (M1 x delta2 : Nat) (_hM1 : M1 ≥ 4)
    (hx : M1 < x) (hd2 : 9 * delta2 > 5 * M1) :
    (16 * M1) / 3 < x + (4 * M1 + delta2) + 2 ∧
    9 * (x + (4 * M1 + delta2) + 2 - (16 * M1) / 3) > 2 * M1 := by
  omega

/-- **Fourfold Small-`delta2` Closure (`r5AttachLower > x` for `9 * delta2 ≤ 5 * M1`, ALL `M1 ≥ 16`):** -/
theorem fourfold_small_delta2_gt_x (M1 x delta2 : Nat) (hM1 : M1 ≥ 16)
    (hx : x ≤ (4 * M1) / 3) (hd1 : 1 ≤ delta2) (hd2 : 9 * delta2 ≤ 5 * M1) :
    x < r5AttachLower (4 * M1) delta2 := by
  unfold r5AttachLower r5Template
  have hreg0 : 5 * delta2 ≤ 4 * M1 + 4 := by omega
  simp only [hreg0, ↓reduceIte]
  omega

/-- **Fourfold Symbolic Diamond-Packing Closure (ALL `M1 ≥ 512`):**
For EVERY `M1 ≥ 512` and EVERY `x ∈ (M1, (4*M1)/3]`, `y ∈ (4*M1, (16*M1)/3]`,
EITHER `x < r5AttachLower (4*M1) (y - 4*M1)` (attachment lower bound exceeds `|V(C_x)|`),
OR `sep := x + y + 2 - (16*M1)/3 > 0` AND `diamondBound x y sep < r5AttachLower (4*M1) (y - 4*M1)`. -/
theorem fourfold_symbolic_closure_ge512 (M1 x y : Nat) (hM1 : M1 ≥ 512)
    (hx1 : M1 < x) (hx2 : x ≤ (4 * M1) / 3)
    (hy1 : 4 * M1 < y) (hy2 : y ≤ (16 * M1) / 3) :
    x < r5AttachLower (4 * M1) (y - 4 * M1) ∨
    ((16 * M1) / 3 < x + y + 2 ∧
      diamondBound x y (x + y + 2 - (16 * M1) / 3) < r5AttachLower (4 * M1) (y - 4 * M1)) := by
  let delta2 := y - 4 * M1
  by_cases hsmall : 9 * delta2 ≤ 5 * M1
  · exact Or.inl (fourfold_small_delta2_gt_x M1 x delta2 (by omega) hx2 (by omega) hsmall)
  · right
    have hsep := fourfold_separation_lb M1 x delta2 (by omega) hx1 (by omega)
    have hy_eq : 4 * M1 + delta2 = y := by omega
    rw [hy_eq] at hsep
    refine ⟨hsep.1, ?_⟩
    let sep := x + y + 2 - (16 * M1) / 3
    have hsep9 : 2 * M1 < 9 * sep := hsep.2
    have hsep_pos : 0 < sep := by omega
    have hr5 := r5_attachment_lower_gt_3_17 (4 * M1) delta2 (by omega) (by omega) (by omega)
    rw [hy_eq] at hr5
    -- Show `17 * diamondBound x y sep ≤ 3 * y` (actually `< 3 * y`!):
    have hdb : 17 * diamondBound x y sep < 3 * y := by
      unfold diamondBound
      by_cases hle : sep ≤ x
      · simp only [hle, ↓reduceIte]
        have hq : ((2 * x * y) / (sep * sep)) * (sep * sep) ≤ 2 * x * y := by
          rw [Nat.mul_comm]; exact Nat.mul_div_le (2 * x * y) (sep * sep)
        have hsep2 : 4 * M1 * M1 < 81 * (sep * sep) := by
          have hsq : (2 * M1) * (2 * M1) < (9 * sep) * (9 * sep) := by
            have h1 : (2 * M1) * (2 * M1) < (9 * sep) * (2 * M1) :=
              Nat.mul_lt_mul_of_pos_right hsep9 (by omega)
            have h2 : (9 * sep) * (2 * M1) < (9 * sep) * (9 * sep) :=
              Nat.mul_lt_mul_of_pos_left hsep9 (by omega)
            exact Nat.lt_trans h1 h2
          calc 4 * M1 * M1 = (2 * M1) * (2 * M1) := by ac_rfl
            _ < (9 * sep) * (9 * sep) := hsq
            _ = 81 * (sep * sep) := by ac_rfl
        have h3x : 3 * x ≤ 4 * M1 := by omega
        -- `17 * db * (4 * M1 * M1) ≤ 17 * db * (81 * sep^2) ≤ 17 * 81 * 2 * x * y`
        -- Multiply by `3`: `3 * 17 * 81 * 2 * x * y ≤ 17 * 81 * 2 * (4 * M1) * y = 17 * 648 * M1 * y`
        -- Whereas `3 * y * 3 * (4 * M1 * M1) = 36 * M1 * M1 * y`. And `17 * 648 = 11016 < 36 * 512 = 18432`!
        have h1 : 17 * ((2 * x * y) / (sep * sep)) * (3 * (4 * M1 * M1)) ≤
                  17 * ((2 * x * y) / (sep * sep)) * (3 * (81 * (sep * sep))) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_left 3 (Nat.le_of_lt hsep2))
        have h2 : 17 * ((2 * x * y) / (sep * sep)) * (3 * (81 * (sep * sep))) ≤
                  17 * 81 * 2 * (3 * x) * y := by
          calc 17 * ((2 * x * y) / (sep * sep)) * (3 * (81 * (sep * sep)))
              = 17 * 3 * 81 * (((2 * x * y) / (sep * sep)) * (sep * sep)) := by ac_rfl
            _ ≤ 17 * 3 * 81 * (2 * x * y) := Nat.mul_le_mul_left _ hq
            _ = 17 * 81 * 2 * (3 * x) * y := by ac_rfl
        have h3 : 17 * 81 * 2 * (3 * x) * y ≤ 17 * 81 * 2 * (4 * M1) * y :=
          Nat.mul_le_mul_right y (Nat.mul_le_mul_left _ h3x)
        have h4 : 17 * 81 * 2 * (4 * M1) * y < 3 * y * (3 * (4 * M1 * M1)) := by
          have hcoef : 17 * 81 * 2 * 4 < 3 * 3 * 4 * M1 := by omega
          have hmy : 0 < M1 * y := Nat.mul_pos (by omega) (by omega)
          have hm := Nat.mul_lt_mul_of_pos_right hcoef hmy
          calc 17 * 81 * 2 * (4 * M1) * y
              = (17 * 81 * 2 * 4) * (M1 * y) := by ac_rfl
            _ < (3 * 3 * 4 * M1) * (M1 * y) := hm
            _ = 3 * y * (3 * (4 * M1 * M1)) := by ac_rfl
        exact Nat.lt_of_mul_lt_mul_right (Nat.lt_of_le_of_lt (Nat.le_trans h1 (Nat.le_trans h2 h3)) h4)
      · simp only [hle, ↓reduceIte]
        have hden : M1 < 2 * sep - x := by omega
        have hq : ((2 * y) / (2 * sep - x)) * (2 * sep - x) ≤ 2 * y := by
          rw [Nat.mul_comm]; exact Nat.mul_div_le (2 * y) (2 * sep - x)
        have h1 : 17 * ((2 * y) / (2 * sep - x)) * M1 ≤ 17 * ((2 * y) / (2 * sep - x)) * (2 * sep - x) :=
          Nat.mul_le_mul_left _ (Nat.le_of_lt hden)
        have h2 : 17 * ((2 * y) / (2 * sep - x)) * (2 * sep - x) ≤ 34 * y := by
          calc 17 * ((2 * y) / (2 * sep - x)) * (2 * sep - x)
              = 17 * (((2 * y) / (2 * sep - x)) * (2 * sep - x)) := by ac_rfl
            _ ≤ 17 * (2 * y) := Nat.mul_le_mul_left 17 hq
            _ = 34 * y := by omega
        have h3 : 34 * y < 3 * y * M1 := by
          have hc : 34 < 3 * M1 := by omega
          have hm := Nat.mul_lt_mul_of_pos_right hc (by omega : 0 < y)
          calc 34 * y < (3 * M1) * y := hm
            _ = 3 * y * M1 := by ac_rfl
        exact Nat.lt_of_mul_lt_mul_right (Nat.lt_of_le_of_lt (Nat.le_trans h1 h2) h3)
    change diamondBound x y sep < r5AttachLower (4 * M1) delta2
    omega

/-- **Fourfold `M1 = 16, y = 77` Explicit 2-Bridge Gap Certificate:**
For `(x, gap) ∈ {(17, 7), (18, 6), (19, 6)}`, NO permissible 2-bridge configuration exists
at distance `1 ≤ d < gap` (`1 ≤ t ≤ x/2`), and `77 / gap < 17 = exactAttachLower 64 77`! -/
private def checkFourfoldGap (x gap : Nat) : Bool :=
  Nat.blt (77 / gap) 17 &&
  (List.range (gap - 1)).all fun d0 =>
    let d := d0 + 1
    (List.range (x / 2)).all fun t0 =>
      !(twoBridgePermissibleBool x 77 (t0 + 1) d)

theorem fourfold_small_16_y77_gaps :
    checkFourfoldGap 17 7 = true ∧
    checkFourfoldGap 18 6 = true ∧
    checkFourfoldGap 19 6 = true := by
  decide

/-- Direct kernel check for ALL Fourfold pairs on `M1 ∈ {4, 8, 16}` (excluding `(17..19, 77)`
which are closed by `fourfold_small_16_y77_gaps`). -/
private def checkFourfoldSmallM1 (M1 : Nat) : Bool :=
  let M2 := 4 * M1
  let cap1 := (4 * M1) / 3
  let cap2 := (4 * M2) / 3
  (List.range (cap1 - M1)).all fun dx0 =>
    let x := M1 + 1 + dx0
    (List.range (cap2 - M2)).all fun dy0 =>
      let y := M2 + 1 + dy0
      if M1 == 16 && y == 77 && (x == 17 || x == 18 || x == 19) then true
      else
        let att := exactAttachLower M2 y
        if Nat.blt x att then true
        else
          Nat.blt cap2 (x + y + 2) &&
          Nat.blt (diamondBound x y (x + y + 2 - cap2)) att

theorem fourfold_finite_small_4_8_16 :
    checkFourfoldSmallM1 4 = true ∧
    checkFourfoldSmallM1 8 = true ∧
    checkFourfoldSmallM1 16 = true := by
  decide

/-- Exact algebraic lower bound lemma: `algLower M n k yhi ≤ r5AttachLower M (y - M)`
whenever `r5Template M (y - M) = (n, k)` and `y ≤ yhi`. -/
theorem algLower_le_r5AttachLower (M y yhi n k : Nat)
    (_hM : M ≥ 16) (hy1 : M < y) (hyh : y ≤ yhi)
    (htpl : r5Template M (y - M) = (n, k)) :
    algLower M n k yhi ≤ r5AttachLower M (y - M) := by
  unfold r5AttachLower
  rw [htpl]
  have hy_eq : M + (y - M) = y := by omega
  rw [hy_eq]
  have hk_cases : (n = 3 ∧ k = 7) ∨ (n = 1 ∧ k = 3) ∨ (n = 3 ∧ k = 11) ∨ (n = 6 ∧ k = 23) := by
    unfold r5Template at htpl
    split at htpl
    · simp only [Prod.mk.injEq] at htpl; exact Or.inl ⟨htpl.1.symm, htpl.2.symm⟩
    · split at htpl
      · simp only [Prod.mk.injEq] at htpl; exact Or.inr (Or.inl ⟨htpl.1.symm, htpl.2.symm⟩)
      · split at htpl
        · simp only [Prod.mk.injEq] at htpl; exact Or.inr (Or.inr (Or.inl ⟨htpl.1.symm, htpl.2.symm⟩))
        · simp only [Prod.mk.injEq] at htpl; exact Or.inr (Or.inr (Or.inr ⟨htpl.1.symm, htpl.2.symm⟩))
  unfold algLower
  rcases hk_cases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> (dsimp only; split <;> omega)

/-- Propositional bridge for Fourfold `IBoxTree`: every `(x, y)` inside a verified tree
satisfies EITHER `x < r5AttachLower (4*M1) (y - 4*M1)` OR `diamondBound x y sep < r5AttachLower`. -/
private theorem checkFourfoldTree_sound (M1 n k : Nat) (hM1 : M1 ≥ 16) :
    ∀ (t : IBoxTree) (xlo xhi ylo yhi : Nat),
      checkFourfoldTree M1 n k xlo xhi ylo yhi t = true →
      ∀ x y, xlo ≤ x → x ≤ xhi → ylo ≤ y → y ≤ yhi →
        4 * M1 < y → r5Template (4 * M1) (y - 4 * M1) = (n, k) →
        x < r5AttachLower (4 * M1) (y - 4 * M1) ∨
        ((16 * M1) / 3 < x + y + 2 ∧
          diamondBound x y (x + y + 2 - (16 * M1) / 3) < r5AttachLower (4 * M1) (y - 4 * M1))
  | .empty, _, _, _, _, h, _, _, _, _, _, _, _, _ => by simp [checkFourfoldTree] at h
  | .leaf lxlo lxhi lylo lyhi, xlo, xhi, ylo, yhi, h, x, y, hx1, hx2, hy1, hy2, hyM, htpl => by
    unfold checkFourfoldTree at h
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    rcases h with ⟨⟨⟨⟨_, _⟩, _⟩, _⟩, hleaf⟩
    unfold checkFourfoldLeaf at hleaf
    dsimp only at hleaf
    let M2 := 4 * M1
    let cap2 := (4 * M2) / 3
    have hcap2 : cap2 = (16 * M1) / 3 := by dsimp only [cap2, M2]; omega
    let lo :=
      if ylo == yhi then yhi - (9 * (yhi - M2 - 1)) / 4 - (n * yhi) / k
      else algLower M2 n k yhi
    have hlo_le : lo ≤ r5AttachLower M2 (y - M2) := by
      dsimp only [lo]
      by_cases hyEq : ylo = yhi
      · have hy_eq : y = yhi := by omega
        subst hy_eq
        simp only [hyEq, beq_self_eq_true, ↓reduceIte]
        unfold r5AttachLower
        rw [htpl]
        have hadd : M2 + (y - M2) = y := by omega
        rw [hadd]
        exact Nat.le_refl _
      · have hne : (ylo == yhi) = false := beq_false_of_ne hyEq
        simp only [hne, Bool.false_eq_true, ↓reduceIte]
        exact algLower_le_r5AttachLower M2 y yhi n k (by omega) hyM hy2 htpl
    by_cases hgt : Nat.blt xhi lo = true
    · left
      have hlt : xhi < lo := by unfold Nat.blt at hgt; have := Nat.le_of_ble_eq_true hgt; omega
      change x < r5AttachLower M2 (y - M2)
      omega
    · have hgtf : Nat.blt xhi lo = false := by cases h : Nat.blt xhi lo; rfl; exact absurd h hgt
      change (if Nat.blt xhi lo = true then true else _) = true at hleaf
      rw [hgtf] at hleaf
      simp only [Bool.false_eq_true, ↓reduceIte] at hleaf
      cases hsepB : Nat.ble (xlo + ylo + 2) cap2
      · change (if Nat.ble (xlo + ylo + 2) cap2 = true then false else _) = true at hleaf
        rw [hsepB] at hleaf
        simp only [Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true] at hleaf
        have hsep_gt : cap2 < xlo + ylo + 2 := by
          have hnot : ¬(xlo + ylo + 2 ≤ cap2) := fun hle => by rw [Nat.ble_eq_true_of_le hle] at hsepB; cases hsepB
          omega
        right
        refine ⟨by omega, ?_⟩
        rcases hleaf with ⟨hok1, hok2⟩
        let sepMin := xlo + ylo + 2 - cap2
        let sepMax := xhi + yhi + 2 - cap2
        let sep := x + y + 2 - cap2
        have hsep_lo : sepMin ≤ sep := by omega
        have hsep_hi : sep ≤ sepMax := by omega
        have hsep_pos : 0 < sepMin := by omega
        rw [← hcap2]
        change diamondBound x y sep < r5AttachLower M2 (y - M2)
        unfold diamondBound
        by_cases hle : sep ≤ x
        · simp only [hle, ↓reduceIte]
          have h1 : Nat.ble sepMin xhi = true := Nat.ble_eq_true_of_le (by omega)
          change (if Nat.ble sepMin xhi = true then _ else true) = true at hok1
          simp only [h1, ↓reduceIte] at hok1
          have hlt1 : (2 * xhi * yhi) / (sepMin * sepMin) < lo := Nat.le_of_ble_eq_true hok1
          have hmono : (2 * x * y) / (sep * sep) ≤ (2 * xhi * yhi) / (sepMin * sepMin) := by
            have hnum : 2 * x * y ≤ 2 * xhi * yhi :=
              Nat.mul_le_mul (Nat.mul_le_mul_left 2 hx2) hy2
            have hden : sepMin * sepMin ≤ sep * sep := Nat.mul_le_mul hsep_lo hsep_lo
            exact Nat.le_trans (Nat.div_le_div_right hnum)
              (Nat.div_le_div_left hden (Nat.mul_pos hsep_pos hsep_pos))
          omega
        · simp only [hle, ↓reduceIte]
          have hnotmax : Nat.ble sepMax xlo = false := by
            cases hb : Nat.ble sepMax xlo
            · rfl
            · have := Nat.le_of_ble_eq_true hb; omega
          change (if Nat.ble sepMax xlo = true then true else _) = true at hok2
          simp only [hnotmax, Bool.false_eq_true, ↓reduceIte] at hok2
          let d2 := if Nat.blt xhi sepMin then 2 * sepMin - xhi else max (xlo + 2) (2 * sepMin - xhi)
          have hlt2 : (2 * yhi) / d2 < lo := Nat.le_of_ble_eq_true hok2
          have hd2_pos : 0 < d2 := by
            dsimp only [d2]
            split
            · rename_i hlt; unfold Nat.blt at hlt; have := Nat.le_of_ble_eq_true hlt; omega
            · omega
          have hd2_le : d2 ≤ 2 * sep - x := by
            dsimp only [d2]
            split <;> omega
          have hmono : (2 * y) / (2 * sep - x) ≤ (2 * yhi) / d2 :=
            Nat.le_trans (Nat.div_le_div_right (Nat.mul_le_mul_left 2 hy2))
              (Nat.div_le_div_left hd2_le hd2_pos)
          omega
      · rw [hsepB] at hleaf; cases hleaf
  | .splitX mid L R, xlo, xhi, ylo, yhi, h, x, y, hx1, hx2, hy1, hy2, hyM, htpl => by
    unfold checkFourfoldTree at h
    simp only [Bool.and_eq_true] at h
    rcases h with ⟨⟨⟨_, _⟩, hL⟩, hR⟩
    by_cases hxm : x ≤ mid
    · exact checkFourfoldTree_sound M1 n k hM1 L xlo mid ylo yhi hL x y hx1 hxm hy1 hy2 hyM htpl
    · exact checkFourfoldTree_sound M1 n k hM1 R (mid + 1) xhi ylo yhi hR x y (by omega) hx2 hy1 hy2 hyM htpl
  | .splitY mid L R, xlo, xhi, ylo, yhi, h, x, y, hx1, hx2, hy1, hy2, hyM, htpl => by
    unfold checkFourfoldTree at h
    simp only [Bool.and_eq_true] at h
    rcases h with ⟨⟨⟨_, _⟩, hL⟩, hR⟩
    by_cases hym : y ≤ mid
    · exact checkFourfoldTree_sound M1 n k hM1 L xlo xhi ylo mid hL x y hx1 hx2 hy1 hym hyM htpl
    · exact checkFourfoldTree_sound M1 n k hM1 R xlo xhi (mid + 1) yhi hR x y hx1 hx2 (by omega) hy2 hyM htpl

/-- **Fourfold Medium Finite Closure (`M1 ∈ {32, 64, 128, 256}` — ALL `38,330` Pairs via `46` `IBoxTree` Leaves [`19+11+9+7`]):** -/
theorem fourfold_finite_32_to_256 (M1 x y : Nat)
    (hM1 : M1 = 32 ∨ M1 = 64 ∨ M1 = 128 ∨ M1 = 256)
    (hx1 : M1 < x) (hx2 : x ≤ (4 * M1) / 3)
    (hy1 : 4 * M1 < y) (hy2 : y ≤ (16 * M1) / 3) :
    x < r5AttachLower (4 * M1) (y - 4 * M1) ∨
    ((16 * M1) / 3 < x + y + 2 ∧
      diamondBound x y (x + y + 2 - (16 * M1) / 3) < r5AttachLower (4 * M1) (y - 4 * M1)) := by
  rcases hM1 with rfl | rfl | rfl | rfl
  · have hok := fourfold_trees_32_ok
    simp only [Bool.and_eq_true] at hok
    by_cases h1 : 5 * (y - 128) ≤ 128 + 4
    · exact checkFourfoldTree_sound 32 3 7 (by omega) fourfoldTree_32_r0 33 42 129 154 hok.1.1.1 x y
        (by omega) (by omega) (by omega) (by omega) (by omega) (by unfold r5Template; simp [h1])
    · by_cases h2 : 4 * (y - 128) ≤ 128 + 2
      · exact checkFourfoldTree_sound 32 1 3 (by omega) fourfoldTree_32_r1 33 42 155 160 hok.1.1.2 x y
          (by omega) (by omega) (by omega) (by omega) (by omega) (by unfold r5Template; simp [h1, h2])
      · by_cases h3 : 31 * (y - 128) ≤ 10 * 128
        · exact checkFourfoldTree_sound 32 3 11 (by omega) fourfoldTree_32_r2 33 42 161 169 hok.1.2 x y
            (by omega) (by omega) (by omega) (by omega) (by omega) (by unfold r5Template; simp [h1, h2, h3])
        · exact checkFourfoldTree_sound 32 6 23 (by omega) fourfoldTree_32_r3 33 42 170 170 hok.2 x y
            (by omega) (by omega) (by omega) (by omega) (by omega) (by unfold r5Template; simp [h1, h2, h3])
  · have hok := fourfold_trees_64_ok
    simp only [Bool.and_eq_true] at hok
    by_cases h1 : 5 * (y - 256) ≤ 256 + 4
    · exact checkFourfoldTree_sound 64 3 7 (by omega) fourfoldTree_64_r0 65 85 257 308 hok.1.1.1 x y
        (by omega) (by omega) (by omega) (by omega) (by omega) (by unfold r5Template; simp [h1])
    · by_cases h2 : 4 * (y - 256) ≤ 256 + 2
      · exact checkFourfoldTree_sound 64 1 3 (by omega) fourfoldTree_64_r1 65 85 309 320 hok.1.1.2 x y
          (by omega) (by omega) (by omega) (by omega) (by omega) (by unfold r5Template; simp [h1, h2])
      · by_cases h3 : 31 * (y - 256) ≤ 10 * 256
        · exact checkFourfoldTree_sound 64 3 11 (by omega) fourfoldTree_64_r2 65 85 321 338 hok.1.2 x y
            (by omega) (by omega) (by omega) (by omega) (by omega) (by unfold r5Template; simp [h1, h2, h3])
        · exact checkFourfoldTree_sound 64 6 23 (by omega) fourfoldTree_64_r3 65 85 339 341 hok.2 x y
            (by omega) (by omega) (by omega) (by omega) (by omega) (by unfold r5Template; simp [h1, h2, h3])
  · have hok := fourfold_trees_128_ok
    simp only [Bool.and_eq_true] at hok
    by_cases h1 : 5 * (y - 512) ≤ 512 + 4
    · exact checkFourfoldTree_sound 128 3 7 (by omega) fourfoldTree_128_r0 129 170 513 615 hok.1.1.1 x y
        (by omega) (by omega) (by omega) (by omega) (by omega) (by unfold r5Template; simp [h1])
    · by_cases h2 : 4 * (y - 512) ≤ 512 + 2
      · exact checkFourfoldTree_sound 128 1 3 (by omega) fourfoldTree_128_r1 129 170 616 640 hok.1.1.2 x y
          (by omega) (by omega) (by omega) (by omega) (by omega) (by unfold r5Template; simp [h1, h2])
      · by_cases h3 : 31 * (y - 512) ≤ 10 * 512
        · exact checkFourfoldTree_sound 128 3 11 (by omega) fourfoldTree_128_r2 129 170 641 677 hok.1.2 x y
            (by omega) (by omega) (by omega) (by omega) (by omega) (by unfold r5Template; simp [h1, h2, h3])
        · exact checkFourfoldTree_sound 128 6 23 (by omega) fourfoldTree_128_r3 129 170 678 682 hok.2 x y
            (by omega) (by omega) (by omega) (by omega) (by omega) (by unfold r5Template; simp [h1, h2, h3])
  · have hok := fourfold_trees_256_ok
    simp only [Bool.and_eq_true] at hok
    by_cases h1 : 5 * (y - 1024) ≤ 1024 + 4
    · exact checkFourfoldTree_sound 256 3 7 (by omega) fourfoldTree_256_r0 257 341 1025 1229 hok.1.1.1 x y
        (by omega) (by omega) (by omega) (by omega) (by omega) (by unfold r5Template; simp [h1])
    · by_cases h2 : 4 * (y - 1024) ≤ 1024 + 2
      · exact checkFourfoldTree_sound 256 1 3 (by omega) fourfoldTree_256_r1 257 341 1230 1280 hok.1.1.2 x y
          (by omega) (by omega) (by omega) (by omega) (by omega) (by unfold r5Template; simp [h1, h2])
      · by_cases h3 : 31 * (y - 1024) ≤ 10 * 1024
        · exact checkFourfoldTree_sound 256 3 11 (by omega) fourfoldTree_256_r2 257 341 1281 1354 hok.1.2 x y
            (by omega) (by omega) (by omega) (by omega) (by omega) (by unfold r5Template; simp [h1, h2, h3])
        · exact checkFourfoldTree_sound 256 6 23 (by omega) fourfoldTree_256_r3 257 341 1355 1365 hok.2 x y
            (by omega) (by omega) (by omega) (by omega) (by omega) (by unfold r5Template; simp [h1, h2, h3])

/-- Exact Twofold (`M2 = 2 * M1`) symbolic constant inequalities (`24*128 / 140^2 < 3/17`, `2/128 < 3/17`). -/
theorem twofold_symbolic_constants :
    17 * (24 * 128) < 3 * (140 * 140) ∧
    17 * 2 < 3 * 128 := by
  decide

/-- **Twofold Symbolic Diamond-Packing Closure (ALL `M1 ≥ 128`):**
For EVERY `M1 ≥ 128` (`M2 = 2*M1`) and EVERY `x ∈ (M1, (4*M1)/3]`, `y ∈ (2*M1, (8*M1)/3]`:
`lb := x + y + 2 - (8*M1)/3` satisfies `0 < lb < y` AND
`diamondBound x y lb < r5AttachLower (2*M1) (y - 2*M1)`. -/
theorem twofold_symbolic_closure_ge128 (M1 x y : Nat) (hM1 : M1 ≥ 128)
    (hx1 : M1 < x) (hx2 : x ≤ (4 * M1) / 3)
    (hy1 : 2 * M1 < y) (hy2 : y ≤ (8 * M1) / 3) :
    (8 * M1) / 3 < x + y + 2 ∧
    x + y + 2 - (8 * M1) / 3 < y ∧
    diamondBound x y (x + y + 2 - (8 * M1) / 3) < r5AttachLower (2 * M1) (y - 2 * M1) := by
  let lb := x + y + 2 - (8 * M1) / 3
  have hlb_gt : (8 * M1) / 3 < x + y + 2 := by omega
  have hlb_lt : lb < y := by omega
  have h3lb : M1 + 12 ≤ 3 * lb := by omega
  have h3x : 3 * x ≤ 4 * M1 := by omega
  have hr5 := r5_attachment_lower_gt_3_17 (2 * M1) (y - 2 * M1) (by omega) (by omega) (by omega)
  have hy_eq : 2 * M1 + (y - 2 * M1) = y := by omega
  rw [hy_eq] at hr5
  refine ⟨hlb_gt, hlb_lt, ?_⟩
  have hdb : 17 * diamondBound x y lb < 3 * y := by
    unfold diamondBound
    by_cases hle : lb ≤ x
    · simp only [hle, ↓reduceIte]
      have hq : ((2 * x * y) / (lb * lb)) * (lb * lb) ≤ 2 * x * y := by
        rw [Nat.mul_comm]; exact Nat.mul_div_le (2 * x * y) (lb * lb)
      have hsq : (M1 + 12) * (M1 + 12) ≤ 9 * (lb * lb) := by
        have hmul := Nat.mul_le_mul h3lb h3lb
        calc (M1 + 12) * (M1 + 12) ≤ (3 * lb) * (3 * lb) := hmul
          _ = 9 * (lb * lb) := by ac_rfl
      have h1 : 17 * ((2 * x * y) / (lb * lb)) * (M1 + 12) * (M1 + 12) ≤
                17 * 3 * (3 * x) * 2 * y := by
        calc 17 * ((2 * x * y) / (lb * lb)) * (M1 + 12) * (M1 + 12)
            = 17 * ((2 * x * y) / (lb * lb)) * ((M1 + 12) * (M1 + 12)) := by ac_rfl
          _ ≤ 17 * ((2 * x * y) / (lb * lb)) * (9 * (lb * lb)) := Nat.mul_le_mul_left _ hsq
          _ = 17 * 9 * (((2 * x * y) / (lb * lb)) * (lb * lb)) := by ac_rfl
          _ ≤ 17 * 9 * (2 * x * y) := Nat.mul_le_mul_left _ hq
          _ = 17 * 3 * (3 * x) * 2 * y := by ac_rfl
      have h2 : 17 * 3 * (3 * x) * 2 * y ≤ 17 * 24 * M1 * y := by
        calc 17 * 3 * (3 * x) * 2 * y
            ≤ 17 * 3 * (4 * M1) * 2 * y := Nat.mul_le_mul_right y (Nat.mul_le_mul_right 2 (Nat.mul_le_mul_left _ h3x))
          _ = 17 * 24 * M1 * y := by ac_rfl
      have h3 : 17 * 24 * M1 < 3 * ((M1 + 12) * (M1 + 12)) := by
        have hexp : (M1 + 12) * (M1 + 12) = M1 * M1 + 24 * M1 + 144 := by
          rw [Nat.add_mul, Nat.mul_add, Nat.mul_add]; omega
        rw [hexp]
        have hM128 : 128 * M1 ≤ M1 * M1 := Nat.mul_le_mul_right M1 hM1
        omega
      have h4 : 17 * 24 * M1 * y < 3 * y * ((M1 + 12) * (M1 + 12)) := by
        have hm := Nat.mul_lt_mul_of_pos_right h3 (by omega : 0 < y)
        calc 17 * 24 * M1 * y < 3 * ((M1 + 12) * (M1 + 12)) * y := hm
          _ = 3 * y * ((M1 + 12) * (M1 + 12)) := by ac_rfl
      have hcomb : 17 * ((2 * x * y) / (lb * lb)) * ((M1 + 12) * (M1 + 12)) <
                   3 * y * ((M1 + 12) * (M1 + 12)) := by
        have h1' : 17 * ((2 * x * y) / (lb * lb)) * ((M1 + 12) * (M1 + 12)) ≤ 17 * 24 * M1 * y := by
          calc 17 * ((2 * x * y) / (lb * lb)) * ((M1 + 12) * (M1 + 12))
              = 17 * ((2 * x * y) / (lb * lb)) * (M1 + 12) * (M1 + 12) := by ac_rfl
            _ ≤ 17 * 24 * M1 * y := Nat.le_trans h1 h2
        exact Nat.lt_of_le_of_lt h1' h4
      exact Nat.lt_of_mul_lt_mul_right hcomb
    · simp only [hle, ↓reduceIte]
      have hden : M1 < 2 * lb - x := by omega
      have hq : ((2 * y) / (2 * lb - x)) * (2 * lb - x) ≤ 2 * y := by
        rw [Nat.mul_comm]; exact Nat.mul_div_le (2 * y) (2 * lb - x)
      have h1 : 17 * ((2 * y) / (2 * lb - x)) * M1 ≤ 34 * y := by
        calc 17 * ((2 * y) / (2 * lb - x)) * M1
            ≤ 17 * ((2 * y) / (2 * lb - x)) * (2 * lb - x) := Nat.mul_le_mul_left _ (Nat.le_of_lt hden)
          _ = 17 * (((2 * y) / (2 * lb - x)) * (2 * lb - x)) := by ac_rfl
          _ ≤ 17 * (2 * y) := Nat.mul_le_mul_left 17 hq
          _ = 34 * y := by omega
      have h2 : 34 * y < 3 * y * M1 := by
        have hc : 34 < 3 * M1 := by omega
        have hm := Nat.mul_lt_mul_of_pos_right hc (by omega : 0 < y)
        calc 34 * y < (3 * M1) * y := hm
          _ = 3 * y * M1 := by ac_rfl
      exact Nat.lt_of_mul_lt_mul_right (Nat.lt_of_le_of_lt h1 h2)
  change diamondBound x y lb < r5AttachLower (2 * M1) (y - 2 * M1)
  omega

/-- Direct kernel check for ALL `1,154` Twofold (`M2 = 2*M1`) pairs with `M1 ∈ {4, 8, 16, 32, 64}`. -/
private def checkTwofoldSmallM1 (M1 : Nat) : Bool :=
  let M2 := 2 * M1
  let cap1 := (4 * M1) / 3
  let cap2 := (4 * M2) / 3
  (List.range (cap1 - M1)).all fun dx0 =>
    let x := M1 + 1 + dx0
    (List.range (cap2 - M2)).all fun dy0 =>
      let y := M2 + 1 + dy0
      let lb := x + y + 2 - cap2
      let r1 := diamondBound x y lb
      let rUb := if Nat.blt (x / 2) lb then natMin r1 (y / (lb - x / 2)) else r1
      Nat.blt cap2 (x + y + 2) && Nat.blt lb y && Nat.blt rUb (exactAttachLower M2 y)

theorem twofold_finite_le64 :
    checkTwofoldSmallM1 4 = true ∧
    checkTwofoldSmallM1 8 = true ∧
    checkTwofoldSmallM1 16 = true ∧
    checkTwofoldSmallM1 32 = true ∧
    checkTwofoldSmallM1 64 = true := by
  decide

/-! ## 2. Equal-Block (`M2 = M1`) Exact Geometric Identities (ALL `M = 2^m ≥ 4`) -/

/-- **Equal-Block Exact Geometric Identities (ALL `M = 2^m ≥ 4`):**
For every `m ≥ 2`, `M := 2^m`, `K := (4*M)/3`, `q := M/3`:
1. `K + K/2 + 1 = 2*M` (exact max mixed-cycle length `≤ 2*M`),
2. `2*M - K - 2*q ∈ {1, 2}` (near-class transitivity),
3. `4*M + 6 > 3*K` (no 3 pairwise-far bridges),
4. `2*M - 3*(2*K - 2*M - 6) ≥ 18` in `Int` (two-class wraparound margin),
5. `2*(2*q + 1) < 2*M + 2*q + 2 - K`,
6. `3*(2*M + 4 - K) > 2*M + 2`. -/
private theorem equal_block_geom_identities_aux (M : Nat)
    (hM4 : M ≥ 4) (hM3 : M % 3 ≠ 0) (hMeven : M % 2 = 0) :
    (4 * M) / 3 + ((4 * M) / 3) / 2 + 1 = 2 * M ∧
    (2 * M - (4 * M) / 3 - 2 * (M / 3) = 1 ∨ 2 * M - (4 * M) / 3 - 2 * (M / 3) = 2) ∧
    4 * M + 6 > 3 * ((4 * M) / 3) ∧
    2 * (M : Int) - 3 * (2 * (((4 * M) / 3 : Nat) : Int) - 2 * (M : Int) - 6) ≥ 18 ∧
    2 * (2 * (M / 3) + 1) < 2 * M + 2 * (M / 3) + 2 - (4 * M) / 3 ∧
    3 * (2 * M + 4 - (4 * M) / 3) > 2 * M + 2 := by
  obtain ⟨t, ht⟩ : ∃ t, M = 6 * t + 2 ∨ M = 6 * t + 4 := ⟨M / 6, by omega⟩
  rcases ht with rfl | rfl
  · have hK : 4 * (6 * t + 2) / 3 = 8 * t + 2 := by omega
    have hq : (6 * t + 2) / 3 = 2 * t := by omega
    rw [hK, hq]
    refine ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩
  · have hK : 4 * (6 * t + 4) / 3 = 8 * t + 5 := by omega
    have hq : (6 * t + 4) / 3 = 2 * t + 1 := by omega
    rw [hK, hq]
    refine ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩

theorem equal_block_geom_identities (m : Nat) (hm : m ≥ 2) :
    let M : Nat := 2 ^ m
    let K : Nat := (4 * M) / 3
    let q : Nat := M / 3
    K + K / 2 + 1 = 2 * M ∧
    (2 * M - K - 2 * q = 1 ∨ 2 * M - K - 2 * q = 2) ∧
    4 * M + 6 > 3 * K ∧
    2 * (M : Int) - 3 * (2 * (K : Int) - 2 * (M : Int) - 6) ≥ 18 ∧
    2 * (2 * q + 1) < 2 * M + 2 * q + 2 - K ∧
    3 * (2 * M + 4 - K) > 2 * M + 2 := by
  have hM4 : 2 ^ m ≥ 4 := Nat.le_trans (by decide : 4 ≤ 2 ^ 2) (Nat.pow_le_pow_right (by omega) hm)
  have hM3 := pow2_mod_three_ne_zero m
  have hMeven : 2 ^ m % 2 = 0 := by
    obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
    rw [Nat.pow_succ]; omega
  have h := equal_block_geom_identities_aux (2 ^ m) hM4 hM3 hMeven
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩

/-- **Exact Antipodal Cluster Width Sum Bound:**
If two antipodal bridge clusters have widths `R1 ≤ W` and `R2 ≤ W` and satisfy the
mixed-cycle wraparound bound `R1 + R2 + x + y + 4 ≤ 2*K`, then
`R1 + R2 ≤ min (2*W) (2*K - x - y - 4)`. -/
theorem equal_block_antipodal_width_sum (K W x y R1 R2 : Nat)
    (h1 : R1 ≤ W) (h2 : R2 ≤ W) (hwrap : R1 + R2 + x + y + 4 ≤ 2 * K) :
    R1 + R2 ≤ min (2 * W) (2 * K - x - y - 4) := by
  omega

/-! ## 3. Equal-Block Small (`M ∈ {4, 8, 16, 32, 64, 128}` — ALL `625` Same-Parity Pairs) -/

/-- Strict short-circuit check that `bestF19TwoClass twoR < r` for `twoR ≤ 19` (O(1) stack depth). -/
private def checkF19TwoClassLt (twoR r : Nat) : Bool :=
  let rec goH (w : Nat) : Nat → Bool
    | 0 => Nat.blt (f19Val w 0 + f19Val (twoR - w) twoR) r
    | h1' + 1 =>
      let h := h1' + 1
      if Nat.blt (f19Val w h + f19Val (twoR - w) (twoR - h)) r then goH w h1' else false
  let rec goW : Nat → Bool
    | 0 => goH 0 twoR
    | w1' + 1 => if goH (w1' + 1) twoR then goW w1' else false
  goW twoR

/-- Check one small equal-block pair `(M, x, y)` (matching `verify_clawfree_eg.py` lines 1052–1076). -/
def checkEqualSmallPair (M x y : Nat) : Bool :=
  let K := (4 * M) / 3
  let lo := exactAttachLower M y
  if Nat.blt lo 2 then false
  else
    let r := lo + (if lo ≥ x then (lo - x) % 2 else (x - lo) % 2)
    let W := x + y + 1 - 2 * M
    if Nat.blt K (x + 2) then true
    else
      let e := K - x - 2
      let w1a := natMin W (3 * e)
      let w2b := natMin W (2 * e)
      let P := natMax ((w1a + 2) * (w1a + 2)) ((W + 2) * (w2b + 2))
      let ok1Pow := Nat.blt (3 ^ 256 * P ^ 123) ((5 * r) ^ 256)
      let ok1 :=
        if ok1Pow then true
        else if Nat.ble W 19 then Nat.blt (natMax (f19Val w1a w1a) (f19Val W w2b)) r
        else false
      let ok2 :=
        if Nat.blt (2 * K) (x + y + 4) then true
        else
          let twoR := natMin (2 * W) (2 * K - x - y - 4)
          let ok2Pow := Nat.blt (6 ^ 256 * (twoR + 4) ^ 246) ((5 * r) ^ 256 * 2 ^ 246)
          if ok2Pow then true
          else if Nat.ble twoR 19 then checkF19TwoClassLt twoR r
          else false
      ok1 && ok2

/-- Strict short-circuit checker for same-parity pairs `(x, y)` with `y ∈ [yStart, yStart + yLen - 1]`. -/
private def checkEqualSmallRange (M yStart yLen : Nat) : Bool :=
  let rec goX (y : Nat) : Nat → Bool
    | 0 => true
    | dx' + 1 =>
      let x := M + 1 + dx'
      if (y - x) % 2 == 0 then
        if checkEqualSmallPair M x y then goX y dx' else false
      else goX y dx'
  let rec goY : Nat → Bool
    | 0 => true
    | off' + 1 =>
      let y := yStart + off'
      if goX y (y - M) then goY off' else false
  goY yLen

/-- Count same-parity pairs `(x, y)` with `M + 1 ≤ x ≤ y ≤ (4 * M) / 3`. -/
private def countEqualSmall (M : Nat) : Nat :=
  let K := (4 * M) / 3
  let rec goY (dy : Nat) (acc : Nat) : Nat :=
    match dy with
    | 0 => acc
    | dy' + 1 =>
      let y := M + 1 + dy'
      -- Number of `x ∈ [M+1, y]` with same parity as `y` is `(y - M + 1) / 2`
      goY dy' (acc + (y - M + 1) / 2)
  goY (K - M) 0

private def checkEqualSmall (M : Nat) : Bool :=
  checkEqualSmallRange M (M + 1) ((4 * M) / 3 - M)

private theorem equal_small_4_to_64_ok :
    checkEqualSmall 4 = true ∧
    checkEqualSmall 8 = true ∧
    checkEqualSmall 16 = true ∧
    checkEqualSmall 32 = true ∧
    checkEqualSmall 64 = true := by
  decide

private theorem equal_small_128_ok :
    checkEqualSmallRange 128 129 21 = true ∧
    checkEqualSmallRange 128 150 21 = true := by
  decide

private theorem equal_small_count_625 :
    countEqualSmall 4 + countEqualSmall 8 + countEqualSmall 16 +
    countEqualSmall 32 + countEqualSmall 64 + countEqualSmall 128 = 625 := by
  decide

/-- **Equal-Block Small Closure (`M ∈ {4, 8, 16, 32, 64, 128}` — ALL `625` Same-Parity Pairs, Boolean Check):**
Every single same-parity equal-block pair for `M ∈ {4, 8, 16, 32, 64, 128}` passes `checkEqualSmallPair`
and the exact total count equals `625`. Reflected to the semantic predicate `SmallEqualPairClosed` by
`equal_block_small_625_sound` below. -/
theorem equal_block_small_625_certified :
    checkEqualSmall 4 = true ∧
    checkEqualSmall 8 = true ∧
    checkEqualSmall 16 = true ∧
    checkEqualSmall 32 = true ∧
    checkEqualSmall 64 = true ∧
    checkEqualSmallRange 128 129 21 = true ∧
    checkEqualSmallRange 128 150 21 = true ∧
    countEqualSmall 4 + countEqualSmall 8 + countEqualSmall 16 +
    countEqualSmall 32 + countEqualSmall 64 + countEqualSmall 128 = 625 :=
  ⟨equal_small_4_to_64_ok.1, equal_small_4_to_64_ok.2.1, equal_small_4_to_64_ok.2.2.1,
   equal_small_4_to_64_ok.2.2.2.1, equal_small_4_to_64_ok.2.2.2.2,
   equal_small_128_ok.1, equal_small_128_ok.2, equal_small_count_625⟩

/-- **Semantic Equal-Block Small Closure Predicate (`M ∈ {4, 8, 16, 32, 64, 128}`):**
Uses `exactAttachLower M y` (`y` for `M ≤ 8`, `r5AttachLower M (y - M)` for `M ≥ 16`) and allows
the `F19` base-table fallback when `W ≤ 19` (1-class) or `twoR ≤ 19` (2-class). Together with
`EqualPairClosed` (`M = 2^m ≥ 256`, which uses `r5AttachLower` and pure power inequalities),
this covers every dyadic block `M = 2^m ≥ 4`. -/
def SmallEqualPairClosed (M x y : Nat) : Prop :=
  let K := (4 * M) / 3
  let lo := exactAttachLower M y
  2 ≤ lo ∧
  (x + 2 ≤ K →
    let r := lo + (if lo ≥ x then (lo - x) % 2 else (x - lo) % 2)
    let W := x + y + 1 - 2 * M
    let e := K - x - 2
    let w1a := min W (3 * e)
    let w2b := min W (2 * e)
    let P := max ((w1a + 2) * (w1a + 2)) ((W + 2) * (w2b + 2))
    (3 ^ 256 * P ^ 123 < (5 * r) ^ 256 ∨
      (W ≤ 19 ∧ max (f19Val w1a w1a) (f19Val W w2b) < r)) ∧
    (x + y + 4 ≤ 2 * K →
      let twoR := min (2 * W) (2 * K - x - y - 4)
      6 ^ 256 * (twoR + 4) ^ 246 < (5 * r) ^ 256 * 2 ^ 246 ∨
      (twoR ≤ 19 ∧ ∀ w h : Nat, w ≤ twoR → h ≤ twoR →
        f19Val w h + f19Val (twoR - w) (twoR - h) < r)))

private theorem natMin_eq_min' (a b : Nat) : natMin a b = min a b := by
  unfold natMin
  cases hb : Nat.ble a b
  · have hnot : ¬(a ≤ b) := fun h => by rw [Nat.ble_eq_true_of_le h] at hb; cases hb
    simp [Nat.min_eq_right (by omega : b ≤ a)]
  · simp [Nat.min_eq_left (Nat.le_of_ble_eq_true hb)]

private theorem natMax_eq_max' (a b : Nat) : natMax a b = max a b := by
  unfold natMax
  cases hb : Nat.ble a b
  · have hnot : ¬(a ≤ b) := fun h => by rw [Nat.ble_eq_true_of_le h] at hb; cases hb
    simp [Nat.max_eq_left (by omega : b ≤ a)]
  · simp [Nat.max_eq_right (Nat.le_of_ble_eq_true hb)]

private theorem checkF19TwoClassLt_goH_sound (twoR r w : Nat) :
    ∀ k, checkF19TwoClassLt.goH twoR r w k = true → ∀ h, h ≤ k →
      f19Val w h + f19Val (twoR - w) (twoR - h) < r
  | 0, hc, h, hh => by
    have hh0 : h = 0 := by omega
    subst hh0
    unfold checkF19TwoClassLt.goH at hc
    exact Nat.lt_of_succ_le (Nat.le_of_ble_eq_true hc)
  | k' + 1, hc, h, hh => by
    unfold checkF19TwoClassLt.goH at hc
    dsimp only at hc
    cases hok : Nat.blt (f19Val w (k' + 1) + f19Val (twoR - w) (twoR - (k' + 1))) r
    · rw [hok] at hc; cases hc
    · rw [hok] at hc; simp only [↓reduceIte] at hc
      by_cases heq : h = k' + 1
      · subst heq; exact Nat.lt_of_succ_le (Nat.le_of_ble_eq_true hok)
      · exact checkF19TwoClassLt_goH_sound twoR r w k' hc h (by omega)

private theorem checkF19TwoClassLt_goW_sound (twoR r : Nat) :
    ∀ k, checkF19TwoClassLt.goW twoR r k = true → ∀ w h, w ≤ k → h ≤ twoR →
      f19Val w h + f19Val (twoR - w) (twoR - h) < r
  | 0, hc, w, h, hw, hh => by
    have hw0 : w = 0 := by omega
    subst hw0
    unfold checkF19TwoClassLt.goW at hc
    exact checkF19TwoClassLt_goH_sound twoR r 0 twoR hc h hh
  | k' + 1, hc, w, h, hw, hh => by
    unfold checkF19TwoClassLt.goW at hc
    cases hok : checkF19TwoClassLt.goH twoR r (k' + 1) twoR
    · rw [hok] at hc; cases hc
    · rw [hok] at hc; simp only [↓reduceIte] at hc
      by_cases heq : w = k' + 1
      · subst heq; exact checkF19TwoClassLt_goH_sound twoR r (k' + 1) twoR hok h hh
      · exact checkF19TwoClassLt_goW_sound twoR r k' hc w h (by omega) hh

/-- Reflection theorem lifting `checkEqualSmallPair M x y = true` to `SmallEqualPairClosed M x y`. -/
theorem checkEqualSmallPair_sound (M x y : Nat) (h : checkEqualSmallPair M x y = true) :
    SmallEqualPairClosed M x y := by
  unfold checkEqualSmallPair at h
  dsimp only at h
  unfold SmallEqualPairClosed
  dsimp only
  cases hlo2 : Nat.blt (exactAttachLower M y) 2
  · rw [hlo2] at h; simp only [Bool.false_eq_true, ↓reduceIte] at h
    have hge2 : 2 ≤ exactAttachLower M y := by
      by_cases hlt : exactAttachLower M y < 2
      · have : Nat.blt (exactAttachLower M y) 2 = true := Nat.ble_eq_true_of_le (by omega)
        rw [this] at hlo2; cases hlo2
      · omega
    refine ⟨hge2, ?_⟩
    intro hK
    have hKf : Nat.blt ((4 * M) / 3) (x + 2) = false := by
      cases hb : Nat.blt ((4 * M) / 3) (x + 2)
      · rfl
      · have := Nat.le_of_ble_eq_true hb; omega
    rw [hKf] at h; simp only [Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true] at h
    rcases h with ⟨hok1, hok2⟩
    rw [natMin_eq_min', natMin_eq_min', natMax_eq_max', natMax_eq_max'] at hok1
    constructor
    · cases hp1 : Nat.blt (3 ^ 256 * max ((min (x + y + 1 - 2 * M) (3 * ((4 * M) / 3 - x - 2)) + 2) *
          (min (x + y + 1 - 2 * M) (3 * ((4 * M) / 3 - x - 2)) + 2))
          ((x + y + 1 - 2 * M + 2) * (min (x + y + 1 - 2 * M) (2 * ((4 * M) / 3 - x - 2)) + 2)) ^ 123)
          ((5 * (exactAttachLower M y + if exactAttachLower M y ≥ x then (exactAttachLower M y - x) % 2 else (x - exactAttachLower M y) % 2)) ^ 256)
      · rw [hp1] at hok1; simp only [Bool.false_eq_true, ↓reduceIte] at hok1
        cases hw19 : Nat.ble (x + y + 1 - 2 * M) 19
        · rw [hw19] at hok1; cases hok1
        · rw [hw19] at hok1; simp only [↓reduceIte] at hok1
          exact Or.inr ⟨Nat.le_of_ble_eq_true hw19, Nat.le_of_ble_eq_true hok1⟩
      · exact Or.inl (Nat.le_of_ble_eq_true hp1)
    · intro hwrap
      have hwf : Nat.blt (2 * ((4 * M) / 3)) (x + y + 4) = false := by
        cases hb : Nat.blt (2 * ((4 * M) / 3)) (x + y + 4)
        · rfl
        · have := Nat.le_of_ble_eq_true hb; omega
      rw [hwf] at hok2; simp only [Bool.false_eq_true, ↓reduceIte] at hok2
      rw [natMin_eq_min'] at hok2
      cases hp2 : Nat.blt (6 ^ 256 * (min (2 * (x + y + 1 - 2 * M)) (2 * ((4 * M) / 3) - x - y - 4) + 4) ^ 246)
          ((5 * (exactAttachLower M y + if exactAttachLower M y ≥ x then (exactAttachLower M y - x) % 2 else (x - exactAttachLower M y) % 2)) ^ 256 * 2 ^ 246)
      · rw [hp2] at hok2; simp only [Bool.false_eq_true, ↓reduceIte] at hok2
        cases hr19 : Nat.ble (min (2 * (x + y + 1 - 2 * M)) (2 * ((4 * M) / 3) - x - y - 4)) 19
        · rw [hr19] at hok2; cases hok2
        · rw [hr19] at hok2; simp only [↓reduceIte] at hok2
          exact Or.inr ⟨Nat.le_of_ble_eq_true hr19,
            checkF19TwoClassLt_goW_sound _ _ _ hok2⟩
      · exact Or.inl (Nat.le_of_ble_eq_true hp2)
  · rw [hlo2] at h; cases h

private theorem checkEqualSmallRange_goX_sound (M y : Nat) :
    ∀ k, checkEqualSmallRange.goX M y k = true →
      ∀ x, M < x → x ≤ M + k → (y - x) % 2 = 0 → SmallEqualPairClosed M x y
  | 0, _, _, hx1, hx2, _ => by omega
  | dx' + 1, h, x, hx1, hx2, hpar => by
    unfold checkEqualSmallRange.goX at h
    dsimp only at h
    by_cases heq : x = M + 1 + dx'
    · subst heq
      have hp : ((y - (M + 1 + dx')) % 2 == 0) = true := beq_iff_eq.mpr hpar
      rw [hp] at h; simp only [↓reduceIte] at h
      cases hpair : checkEqualSmallPair M (M + 1 + dx') y
      · rw [hpair] at h; cases h
      · exact checkEqualSmallPair_sound M (M + 1 + dx') y hpair
    · cases hp : ((y - (M + 1 + dx')) % 2 == 0)
      · rw [hp] at h; simp only [Bool.false_eq_true, ↓reduceIte] at h
        exact checkEqualSmallRange_goX_sound M y dx' h x hx1 (by omega) hpar
      · rw [hp] at h; simp only [↓reduceIte] at h
        cases hpair : checkEqualSmallPair M (M + 1 + dx') y
        · rw [hpair] at h; cases h
        · rw [hpair] at h; simp only [↓reduceIte] at h
          exact checkEqualSmallRange_goX_sound M y dx' h x hx1 (by omega) hpar

private theorem checkEqualSmallRange_goY_sound (M yStart : Nat) :
    ∀ k, checkEqualSmallRange.goY M yStart k = true →
      ∀ x y, M < x → x ≤ y → yStart ≤ y → y < yStart + k → (y - x) % 2 = 0 →
        SmallEqualPairClosed M x y
  | 0, _, _, _, _, _, h1, h2, _ => by omega
  | off' + 1, h, x, y, hx1, hxy, hy1, hy2, hpar => by
    unfold checkEqualSmallRange.goY at h
    dsimp only at h
    cases hgx : checkEqualSmallRange.goX M (yStart + off') (yStart + off' - M)
    · rw [hgx] at h; cases h
    · rw [hgx] at h; simp only [↓reduceIte] at h
      by_cases heq : y = yStart + off'
      · subst heq
        exact checkEqualSmallRange_goX_sound M (yStart + off') (yStart + off' - M) hgx x hx1 (by omega) hpar
      · exact checkEqualSmallRange_goY_sound M yStart off' h x y hx1 hxy hy1 (by omega) hpar

/-- **Equal-Block Small Semantic Reflection Theorem (`M ∈ {4, 8, 16, 32, 64, 128}` — ALL `625` Pairs):**
Lifts `equal_block_small_625_certified` to `SmallEqualPairClosed M x y` for EVERY same-parity pair
`(x, y)` with `M < x ≤ y ≤ (4 * M) / 3` and `M ∈ {4, 8, 16, 32, 64, 128}`. -/
theorem equal_block_small_625_sound :
    ∀ M ∈ ([4, 8, 16, 32, 64, 128] : List Nat),
      ∀ x y : Nat, M < x → x ≤ y → y ≤ (4 * M) / 3 → (y - x) % 2 = 0 →
        SmallEqualPairClosed M x y := by
  intro M hM x y hx1 hxy hy2 hpar
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hM
  rcases hM with rfl | rfl | rfl | rfl | rfl | rfl
  · exact checkEqualSmallRange_goY_sound 4 5 _ equal_block_small_625_certified.1 x y hx1 hxy (by omega) (by omega) hpar
  · exact checkEqualSmallRange_goY_sound 8 9 _ equal_block_small_625_certified.2.1 x y hx1 hxy (by omega) (by omega) hpar
  · exact checkEqualSmallRange_goY_sound 16 17 _ equal_block_small_625_certified.2.2.1 x y hx1 hxy (by omega) (by omega) hpar
  · exact checkEqualSmallRange_goY_sound 32 33 _ equal_block_small_625_certified.2.2.2.1 x y hx1 hxy (by omega) (by omega) hpar
  · exact checkEqualSmallRange_goY_sound 64 65 _ equal_block_small_625_certified.2.2.2.2.1 x y hx1 hxy (by omega) (by omega) hpar
  · by_cases hmid : y < 150
    · exact checkEqualSmallRange_goY_sound 128 129 21 equal_block_small_625_certified.2.2.2.2.2.1 x y hx1 hxy (by omega) hmid hpar
    · exact checkEqualSmallRange_goY_sound 128 150 21 equal_block_small_625_certified.2.2.2.2.2.2.1 x y hx1 hxy (by omega) (by omega) hpar

/-! ## 4. Equal-Block Medium (`M ∈ {256, 512, 1024}` — ALL `76,492` Pairs via `61` Box-Tree Leaves!) -/

/-- Exact 1-class and 2-class equal-block closure predicate for an integer pair `(M, x, y)`. -/
def EqualPairClosed (M x y : Nat) : Prop :=
  let K := (4 * M) / 3
  let lo := r5AttachLower M (y - M)
  let r := lo + (if lo ≥ x then (lo - x) % 2 else (x - lo) % 2)
  let W := x + y + 1 - 2 * M
  x + 2 ≤ K →
    let e := K - x - 2
    let P := max ((min W (3 * e) + 2) * (min W (3 * e) + 2)) ((W + 2) * (min W (2 * e) + 2))
    3 ^ 256 * P ^ 123 < (5 * r) ^ 256 ∧
    (x + y + 4 ≤ 2 * K →
      let twoR := min (2 * W) (2 * K - x - y - 4)
      6 ^ 256 * (twoR + 4) ^ 246 < (5 * r) ^ 256 * 2 ^ 246)

private theorem lt_of_blt_eq_true {a b : Nat} (h : Nat.blt a b = true) : a < b :=
  Nat.le_of_ble_eq_true h

private theorem pow_lt_of_blt_and_le {c p a b d e : Nat}
    (hblt : Nat.blt (c * b ^ p) (d ^ 256) = true)
    (hab : a ≤ b) (hde : d ≤ e) : c * a ^ p < e ^ 256 :=
  Nat.lt_of_le_of_lt (Nat.mul_le_mul_left c (Nat.pow_le_pow_left hab p))
    (Nat.lt_of_lt_of_le (lt_of_blt_eq_true hblt) (Nat.pow_le_pow_left hde 256))

private theorem pow_lt_mul_of_blt_and_le {c p a b d e f : Nat}
    (hblt : Nat.blt (c * b ^ p) (d ^ 256 * f) = true)
    (hab : a ≤ b) (hde : d ≤ e) : c * a ^ p < e ^ 256 * f :=
  Nat.lt_of_le_of_lt (Nat.mul_le_mul_left c (Nat.pow_le_pow_left hab p))
    (Nat.lt_of_lt_of_le (lt_of_blt_eq_true hblt) (Nat.mul_le_mul_right f (Nat.pow_le_pow_left hde 256)))

private theorem checkEqualMedTree_sound (M n k : Nat) (hM : M ≥ 16) :
    ∀ (t : IBoxTree) (xlo xhi ylo yhi : Nat),
      checkEqualMedTree M n k xlo xhi ylo yhi t = true →
      ∀ x y, xlo ≤ x → x ≤ xhi → ylo ≤ y → y ≤ yhi → x ≤ y →
        M < x → r5Template M (y - M) = (n, k) →
        EqualPairClosed M x y
  | .empty, xlo, _, _, yhi, h, x, y, hx1, _, _, hy2, hxy, _, _ => by
    unfold checkEqualMedTree at h
    unfold Nat.blt at h
    have := Nat.le_of_ble_eq_true h
    omega
  | .leaf lxlo lxhi lylo lyhi, xlo, xhi, ylo, yhi, h, x, y, hx1, hx2, hy1, hy2, hxy, hxM, htpl => by
    unfold checkEqualMedTree at h
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    rcases h with ⟨⟨⟨⟨_, _⟩, _⟩, _⟩, hleaf⟩
    unfold checkEqualMedLeaf at hleaf
    dsimp only at hleaf
    unfold EqualPairClosed
    dsimp only
    intro hK
    let K := (4 * M) / 3
    have hnot_lt : ¬(K < xlo + 2) := by dsimp only [K]; omega
    change (if K < xlo + 2 then true else _) = true at hleaf
    simp only [hnot_lt, ↓reduceIte] at hleaf
    let loB :=
      if xlo == min xhi yhi && max ylo xlo == yhi then
        let loEx := yhi - (9 * (yhi - M - 1)) / 4 - (n * yhi) / k
        loEx + (if loEx ≥ xlo then (loEx - xlo) % 2 else (xlo - loEx) % 2)
      else if max ylo xlo == yhi then
        yhi - (9 * (yhi - M - 1)) / 4 - (n * yhi) / k
      else
        algLower M n k yhi
    have hloB_ne : loB ≠ 0 := by
      intro h0
      have hbeq : (loB == 0) = true := beq_iff_eq.mpr h0
      change (if (loB == 0) = true then false else _) = true at hleaf
      rw [hbeq] at hleaf; cases hleaf
    have hloB_f : (loB == 0) = false := beq_false_of_ne hloB_ne
    change (if (loB == 0) = true then false else _) = true at hleaf
    rw [hloB_f] at hleaf
    simp only [Bool.false_eq_true, ↓reduceIte] at hleaf
    have ⟨hok1, hok2⟩ := Bool.and_eq_true_iff.mp hleaf
    let lo := r5AttachLower M (y - M)
    let r := lo + (if lo ≥ x then (lo - x) % 2 else (x - lo) % 2)
    have hlo_le_r : loB ≤ r := by
      dsimp only [loB]
      by_cases hpt : xlo = min xhi yhi ∧ max ylo xlo = yhi
      · have hxEq : x = xlo := by omega
        have hyEq : y = yhi := by omega
        have hcond : (xlo == min xhi yhi && max ylo xlo == yhi) = true := by
          rw [beq_iff_eq.mpr hpt.1, beq_iff_eq.mpr hpt.2]; rfl
        simp only [hcond, ↓reduceIte]
        subst hxEq; subst hyEq
        have hlo_eq : lo = y - (9 * (y - M - 1)) / 4 - (n * y) / k := by
          dsimp only [lo]; unfold r5AttachLower; rw [htpl]
          have : M + (y - M) = y := by omega
          rw [this]
        dsimp only [r]; rw [hlo_eq]; exact Nat.le_refl _
      · have hcondF : (xlo == min xhi yhi && max ylo xlo == yhi) = false := by
          cases hb : (xlo == min xhi yhi && max ylo xlo == yhi)
          · rfl
          · simp only [Bool.and_eq_true, beq_iff_eq] at hb; exact absurd hb hpt
        simp only [hcondF, Bool.false_eq_true, ↓reduceIte]
        by_cases hyEq : max ylo xlo = yhi
        · have hyE : y = yhi := by omega
          subst hyE
          simp only [hyEq, beq_self_eq_true, ↓reduceIte]
          have hlo_eq : lo = y - (9 * (y - M - 1)) / 4 - (n * y) / k := by
            dsimp only [lo]; unfold r5AttachLower; rw [htpl]
            have : M + (y - M) = y := by omega
            rw [this]
          dsimp only [r]; omega
        · have hyF : (max ylo xlo == yhi) = false := beq_false_of_ne hyEq
          simp only [hyF, Bool.false_eq_true, ↓reduceIte]
          have halg := algLower_le_r5AttachLower M y yhi n k hM (by omega) hy2 htpl
          dsimp only [r, lo]; omega
    let widthB := min xhi yhi + yhi + 1 - 2 * M
    let imbB := K - xlo - 2
    let PB := max ((min widthB (3 * imbB) + 2) * (min widthB (3 * imbB) + 2))
                  ((widthB + 2) * (min widthB (2 * imbB) + 2))
    let W := x + y + 1 - 2 * M
    let e := K - x - 2
    let P := max ((min W (3 * e) + 2) * (min W (3 * e) + 2)) ((W + 2) * (min W (2 * e) + 2))
    have hW_le : W ≤ widthB := by omega
    have he_le : e ≤ imbB := by omega
    have hP_le : P ≤ PB := by
      have h1 : min W (3 * e) + 2 ≤ min widthB (3 * imbB) + 2 := by omega
      have h2 : min W (2 * e) + 2 ≤ min widthB (2 * imbB) + 2 := by omega
      have hp1 := Nat.mul_le_mul h1 h1
      have hp2 := Nat.mul_le_mul (by omega : W + 2 ≤ widthB + 2) h2
      dsimp only [P, PB]; omega
    constructor
    · exact pow_lt_of_blt_and_le hok1 hP_le (Nat.mul_le_mul_left 5 hlo_le_r)
    · intro hwrap
      have hnot_w : ¬(2 * K < xlo + max ylo xlo + 4) := by dsimp only [K]; omega
      change (if 2 * K < xlo + max ylo xlo + 4 then true else _) = true at hok2
      simp only [hnot_w, ↓reduceIte] at hok2
      let twoRB := min (2 * widthB) (2 * K - xlo - max ylo xlo - 4)
      let twoR := min (2 * W) (2 * K - x - y - 4)
      have htwoR_le : twoR ≤ twoRB := by omega
      exact pow_lt_mul_of_blt_and_le hok2 (by omega : twoR + 4 ≤ twoRB + 4) (Nat.mul_le_mul_left 5 hlo_le_r)
  | .splitX mid L R, xlo, xhi, ylo, yhi, h, x, y, hx1, hx2, hy1, hy2, hxy, hxM, htpl => by
    unfold checkEqualMedTree at h
    dsimp only at h
    simp only [Bool.and_eq_true] at h
    rcases h with ⟨⟨⟨_, _⟩, hL⟩, hR⟩
    by_cases hxm : x ≤ mid
    · exact checkEqualMedTree_sound M n k hM L xlo mid (max ylo xlo) yhi hL x y
        hx1 hxm (by omega) hy2 hxy hxM htpl
    · exact checkEqualMedTree_sound M n k hM R (mid + 1) (min xhi yhi) (max ylo xlo) yhi hR x y
        (by omega) (by omega) (by omega) hy2 hxy hxM htpl
  | .splitY mid L R, xlo, xhi, ylo, yhi, h, x, y, hx1, hx2, hy1, hy2, hxy, hxM, htpl => by
    unfold checkEqualMedTree at h
    dsimp only at h
    simp only [Bool.and_eq_true] at h
    rcases h with ⟨⟨⟨_, _⟩, hL⟩, hR⟩
    by_cases hym : y ≤ mid
    · exact checkEqualMedTree_sound M n k hM L xlo (min xhi yhi) (max ylo xlo) mid hL x y
        hx1 (by omega) (by omega) hym hxy hxM htpl
    · exact checkEqualMedTree_sound M n k hM R xlo (min xhi yhi) (mid + 1) yhi hR x y
        hx1 (by omega) (by omega) hy2 hxy hxM htpl

/-- **Equal-Block Medium Closure (`M ∈ {256, 512, 1024}` — ALL `76,492` Pairs via `61` Box-Tree Leaves [`22+23+16`]):**
Every integer pair `(x, y)` with `M + 1 ≤ x ≤ y ≤ (4 * M) / 3` satisfies BOTH the 1-class
and 2-class inequalities (`EqualPairClosed M x y`)! -/
theorem equal_block_med_256_512_1024 (M x y : Nat)
    (hM : M = 256 ∨ M = 512 ∨ M = 1024)
    (hx1 : M < x) (hxy : x ≤ y) (hy2 : y ≤ (4 * M) / 3) :
    EqualPairClosed M x y := by
  rcases hM with rfl | rfl | rfl
  · have hok := equalMed_trees_256_ok
    simp only [Bool.and_eq_true] at hok
    by_cases h1 : 5 * (y - 256) ≤ 256 + 4
    · exact checkEqualMedTree_sound 256 3 7 (by omega) equalMedTree_256_r0 257 308 257 308 hok.1.1.1
        x y (by omega) (by omega) (by omega) (by omega) hxy hx1 (by unfold r5Template; simp [h1])
    · by_cases h2 : 4 * (y - 256) ≤ 256 + 2
      · exact checkEqualMedTree_sound 256 1 3 (by omega) equalMedTree_256_r1 257 320 309 320 hok.1.1.2
          x y (by omega) (by omega) (by omega) (by omega) hxy hx1 (by unfold r5Template; simp [h1, h2])
      · by_cases h3 : 31 * (y - 256) ≤ 10 * 256
        · exact checkEqualMedTree_sound 256 3 11 (by omega) equalMedTree_256_r2 257 338 321 338 hok.1.2
            x y (by omega) (by omega) (by omega) (by omega) hxy hx1 (by unfold r5Template; simp [h1, h2, h3])
        · exact checkEqualMedTree_sound 256 6 23 (by omega) equalMedTree_256_r3 257 341 339 341 hok.2
            x y (by omega) (by omega) (by omega) (by omega) hxy hx1 (by unfold r5Template; simp [h1, h2, h3])
  · have hok := equalMed_trees_512_ok
    simp only [Bool.and_eq_true] at hok
    by_cases h1 : 5 * (y - 512) ≤ 512 + 4
    · exact checkEqualMedTree_sound 512 3 7 (by omega) equalMedTree_512_r0 513 615 513 615 hok.1.1.1
        x y (by omega) (by omega) (by omega) (by omega) hxy hx1 (by unfold r5Template; simp [h1])
    · by_cases h2 : 4 * (y - 512) ≤ 512 + 2
      · exact checkEqualMedTree_sound 512 1 3 (by omega) equalMedTree_512_r1 513 640 616 640 hok.1.1.2
          x y (by omega) (by omega) (by omega) (by omega) hxy hx1 (by unfold r5Template; simp [h1, h2])
      · by_cases h3 : 31 * (y - 512) ≤ 10 * 512
        · exact checkEqualMedTree_sound 512 3 11 (by omega) equalMedTree_512_r2 513 677 641 677 hok.1.2
            x y (by omega) (by omega) (by omega) (by omega) hxy hx1 (by unfold r5Template; simp [h1, h2, h3])
        · exact checkEqualMedTree_sound 512 6 23 (by omega) equalMedTree_512_r3 513 682 678 682 hok.2
            x y (by omega) (by omega) (by omega) (by omega) hxy hx1 (by unfold r5Template; simp [h1, h2, h3])
  · have hok := equalMed_trees_1024_ok
    simp only [Bool.and_eq_true] at hok
    by_cases h1 : 5 * (y - 1024) ≤ 1024 + 4
    · exact checkEqualMedTree_sound 1024 3 7 (by omega) equalMedTree_1024_r0 1025 1229 1025 1229 hok.1.1.1
        x y (by omega) (by omega) (by omega) (by omega) hxy hx1 (by unfold r5Template; simp [h1])
    · by_cases h2 : 4 * (y - 1024) ≤ 1024 + 2
      · exact checkEqualMedTree_sound 1024 1 3 (by omega) equalMedTree_1024_r1 1025 1280 1230 1280 hok.1.1.2
          x y (by omega) (by omega) (by omega) (by omega) hxy hx1 (by unfold r5Template; simp [h1, h2])
      · by_cases h3 : 31 * (y - 1024) ≤ 10 * 1024
        · exact checkEqualMedTree_sound 1024 3 11 (by omega) equalMedTree_1024_r2 1025 1354 1281 1354 hok.1.2
            x y (by omega) (by omega) (by omega) (by omega) hxy hx1 (by unfold r5Template; simp [h1, h2, h3])
        · exact checkEqualMedTree_sound 1024 6 23 (by omega) equalMedTree_1024_r3 1025 1365 1355 1365 hok.2
            x y (by omega) (by omega) (by omega) (by omega) hxy hx1 (by unfold r5Template; simp [h1, h2, h3])

/-! ## 5. Equal-Block Infinite Tail (`M ≥ 2048` — ALL `16` Exact Rational Tail Boxes!) -/

/-- Exact count of the rational tail boxes from `cert/witnesses/two_cycle_closure.json`. -/
theorem equalTailBoxes16_count : equalTailBoxes16.length = 16 := by decide

/-- Pointwise soundness of `equalTailBoxes16`: every one of the `16` boxes passes `checkTailBox`. -/
theorem equalTailBoxes16_all_pass : ∀ b ∈ equalTailBoxes16, checkTailBox b = true :=
  fun b hb => List.all_eq_true.mp equalTailBoxes16_certified_bool b hb

/-- **Exact 4-Regime Domain Coverage of the `16` Rational Tail Boxes (`M ≥ 2048`):**
For EVERY `M ≥ 2048` and EVERY `dx ≤ dy` with `3 * dy ≤ M`, there exists a box
`b ∈ equalTailBoxes16` matching `(b.n, b.k) = r5Template M dy` whose rectangle
`[b.xlo, b.xhi] × [b.ylo, b.yhi]` contains `(dx / M, dy / M)`! -/
theorem equalTailBoxes16_domain_coverage (M dx dy : Nat) (hM : M ≥ 2048)
    (hord : dx ≤ dy) (h3 : 3 * dy ≤ M) :
    ∃ b ∈ equalTailBoxes16,
      (b.n, b.k) = r5Template M dy ∧
      0 < b.xlo.den ∧ 0 < b.xhi.den ∧ 0 < b.ylo.den ∧ 0 < b.yhi.den ∧
      b.xlo.num * M ≤ dx * b.xlo.den ∧ dx * b.xhi.den ≤ b.xhi.num * M ∧
      b.ylo.num * M ≤ dy * b.ylo.den ∧ dy * b.yhi.den ≤ b.yhi.num * M := by
  have hmem : ∀ (i : Nat) (hi : i < equalTailBoxes16.length), equalTailBoxes16[i]'hi ∈ equalTailBoxes16 :=
    fun i hi => List.getElem_mem hi
  unfold r5Template
  by_cases h1 : 5 * dy ≤ M + 4
  · simp only [h1, ↓reduceIte]
    have hdy_hi : 2560 * dy ≤ 513 * M := by omega
    by_cases hy1 : 5120 * dy ≤ 513 * M
    · refine ⟨equalTailBoxes16[6]'(by decide), hmem 6 (by decide), rfl, by decide, by decide, by decide, by decide, ?_, ?_, ?_, ?_⟩ <;>
        (simp only [equalTailBoxes16, List.getElem_cons_zero, List.getElem_cons_succ]; omega)
    · by_cases hx1 : 513 * M ≤ 5120 * dx
      · refine ⟨equalTailBoxes16[0]'(by decide), hmem 0 (by decide), rfl, by decide, by decide, by decide, by decide, ?_, ?_, ?_, ?_⟩ <;>
          (simp only [equalTailBoxes16, List.getElem_cons_zero]; omega)
      · by_cases hy2 : 10240 * dy ≤ 1539 * M
        · by_cases hx2 : 513 * M ≤ 10240 * dx
          · refine ⟨equalTailBoxes16[2]'(by decide), hmem 2 (by decide), rfl, by decide, by decide, by decide, by decide, ?_, ?_, ?_, ?_⟩ <;>
              (simp only [equalTailBoxes16, List.getElem_cons_zero, List.getElem_cons_succ]; omega)
          · refine ⟨equalTailBoxes16[5]'(by decide), hmem 5 (by decide), rfl, by decide, by decide, by decide, by decide, ?_, ?_, ?_, ?_⟩ <;>
              (simp only [equalTailBoxes16, List.getElem_cons_zero, List.getElem_cons_succ]; omega)
        · by_cases hx2 : 513 * M ≤ 10240 * dx
          · refine ⟨equalTailBoxes16[1]'(by decide), hmem 1 (by decide), rfl, by decide, by decide, by decide, by decide, ?_, ?_, ?_, ?_⟩ <;>
              (simp only [equalTailBoxes16, List.getElem_cons_zero, List.getElem_cons_succ]; omega)
          · by_cases hx3 : 513 * M ≤ 20480 * dx
            · refine ⟨equalTailBoxes16[3]'(by decide), hmem 3 (by decide), rfl, by decide, by decide, by decide, by decide, ?_, ?_, ?_, ?_⟩ <;>
                (simp only [equalTailBoxes16, List.getElem_cons_zero, List.getElem_cons_succ]; omega)
            · refine ⟨equalTailBoxes16[4]'(by decide), hmem 4 (by decide), rfl, by decide, by decide, by decide, by decide, ?_, ?_, ?_, ?_⟩ <;>
                (simp only [equalTailBoxes16, List.getElem_cons_zero, List.getElem_cons_succ]; omega)
  · by_cases h2 : 4 * dy ≤ M + 2
    · simp only [h1, h2, ↓reduceIte]
      refine ⟨equalTailBoxes16[7]'(by decide), hmem 7 (by decide), rfl, by decide, by decide, by decide, by decide, ?_, ?_, ?_, ?_⟩ <;>
        (simp only [equalTailBoxes16, List.getElem_cons_zero, List.getElem_cons_succ]; omega)
    · by_cases h3r : 31 * dy ≤ 10 * M
      · simp only [h1, h2, h3r, ↓reduceIte]
        by_cases hx1 : 15 * M ≤ 62 * dx
        · refine ⟨equalTailBoxes16[8]'(by decide), hmem 8 (by decide), rfl, by decide, by decide, by decide, by decide, ?_, ?_, ?_, ?_⟩ <;>
            (simp only [equalTailBoxes16, List.getElem_cons_zero, List.getElem_cons_succ]; omega)
        · by_cases hx2 : 25 * M ≤ 124 * dx
          · refine ⟨equalTailBoxes16[9]'(by decide), hmem 9 (by decide), rfl, by decide, by decide, by decide, by decide, ?_, ?_, ?_, ?_⟩ <;>
              (simp only [equalTailBoxes16, List.getElem_cons_zero, List.getElem_cons_succ]; omega)
          · by_cases hx3 : 31 * dx ≤ 5 * M
            · refine ⟨equalTailBoxes16[13]'(by decide), hmem 13 (by decide), rfl, by decide, by decide, by decide, by decide, ?_, ?_, ?_, ?_⟩ <;>
                (simp only [equalTailBoxes16, List.getElem_cons_zero, List.getElem_cons_succ]; omega)
            · by_cases hy1 : 248 * dy ≤ 71 * M
              · refine ⟨equalTailBoxes16[12]'(by decide), hmem 12 (by decide), rfl, by decide, by decide, by decide, by decide, ?_, ?_, ?_, ?_⟩ <;>
                  (simp only [equalTailBoxes16, List.getElem_cons_zero, List.getElem_cons_succ]; omega)
              · by_cases hx4 : 45 * M ≤ 248 * dx
                · refine ⟨equalTailBoxes16[10]'(by decide), hmem 10 (by decide), rfl, by decide, by decide, by decide, by decide, ?_, ?_, ?_, ?_⟩ <;>
                    (simp only [equalTailBoxes16, List.getElem_cons_zero, List.getElem_cons_succ]; omega)
                · refine ⟨equalTailBoxes16[11]'(by decide), hmem 11 (by decide), rfl, by decide, by decide, by decide, by decide, ?_, ?_, ?_, ?_⟩ <;>
                    (simp only [equalTailBoxes16, List.getElem_cons_zero, List.getElem_cons_succ]; omega)
      · simp only [h1, h2, h3r, ↓reduceIte]
        by_cases hx1 : M ≤ 6 * dx
        · refine ⟨equalTailBoxes16[14]'(by decide), hmem 14 (by decide), rfl, by decide, by decide, by decide, by decide, ?_, ?_, ?_, ?_⟩ <;>
            (simp only [equalTailBoxes16, List.getElem_cons_zero, List.getElem_cons_succ]; omega)
        · refine ⟨equalTailBoxes16[15]'(by decide), hmem 15 (by decide), rfl, by decide, by decide, by decide, by decide, ?_, ?_, ?_, ?_⟩ <;>
            (simp only [equalTailBoxes16, List.getElem_cons_zero, List.getElem_cons_succ]; omega)

/-! ### Exact Rational Arithmetic Lemmas for the Integer-to-TailBox Scaling Bridge -/

private theorem qAdd_spec (a b : QPos) (ha : 0 < a.den) (hb : 0 < b.den) :
    0 < (qAdd a b).den ∧
    (qAdd a b).num * (a.den * b.den) = (a.num * b.den + b.num * a.den) * (qAdd a b).den := by
  unfold qAdd
  dsimp only
  let n := a.num * b.den + b.num * a.den
  let d := a.den * b.den
  let g := Nat.gcd n d
  have hd_pos : 0 < d := Nat.mul_pos ha hb
  have hg_pos : 0 < g := Nat.gcd_pos_of_pos_right n hd_pos
  have hgn : g ∣ n := Nat.gcd_dvd_left n d
  have hgd : g ∣ d := Nat.gcd_dvd_right n d
  have hden_pos : 0 < d / g := by
    rcases hgd with ⟨q, hq⟩
    have hq_pos : 0 < q := by
      cases q with
      | zero => simp at hq; omega
      | succ k => exact Nat.zero_lt_succ k
    rw [hq, Nat.mul_div_cancel_left q hg_pos]
    exact hq_pos
  refine ⟨hden_pos, ?_⟩
  have h1 : (n / g) * g = n := Nat.div_mul_cancel hgn
  have h2 : (d / g) * g = d := Nat.div_mul_cancel hgd
  have hmul : (n / g) * d * g = n * (d / g) * g := by
    calc (n / g) * d * g = ((n / g) * g) * d := by ac_rfl
      _ = n * d := by rw [h1]
      _ = n * ((d / g) * g) := by rw [h2]
      _ = n * (d / g) * g := by ac_rfl
  exact Nat.eq_of_mul_eq_mul_right hg_pos hmul

private theorem qMul_spec (a b : QPos) (ha : 0 < a.den) (hb : 0 < b.den) :
    0 < (qMul a b).den ∧
    (qMul a b).num * (a.den * b.den) = (a.num * b.num) * (qMul a b).den := by
  unfold qMul
  dsimp only
  let n := a.num * b.num
  let d := a.den * b.den
  let g := Nat.gcd n d
  have hd_pos : 0 < d := Nat.mul_pos ha hb
  have hg_pos : 0 < g := Nat.gcd_pos_of_pos_right n hd_pos
  have hgn : g ∣ n := Nat.gcd_dvd_left n d
  have hgd : g ∣ d := Nat.gcd_dvd_right n d
  have hden_pos : 0 < d / g := by
    rcases hgd with ⟨q, hq⟩
    have hq_pos : 0 < q := by
      cases q with
      | zero => simp at hq; omega
      | succ k => exact Nat.zero_lt_succ k
    rw [hq, Nat.mul_div_cancel_left q hg_pos]
    exact hq_pos
  refine ⟨hden_pos, ?_⟩
  have h1 : (n / g) * g = n := Nat.div_mul_cancel hgn
  have h2 : (d / g) * g = d := Nat.div_mul_cancel hgd
  have hmul : (n / g) * d * g = n * (d / g) * g := by
    calc (n / g) * d * g = ((n / g) * g) * d := by ac_rfl
      _ = n * d := by rw [h1]
      _ = n * ((d / g) * g) := by rw [h2]
      _ = n * (d / g) * g := by ac_rfl
  exact Nat.eq_of_mul_eq_mul_right hg_pos hmul

private theorem qSub_spec (a b : QPos) (ha : 0 < a.den) (hb : 0 < b.den)
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
      have hq_pos : 0 < q := by
        cases q with
        | zero => simp at hq; omega
        | succ k => exact Nat.zero_lt_succ k
      rw [hq, Nat.mul_div_cancel_left q hg_pos]
      exact hq_pos
    refine ⟨hden_pos, ?_⟩
    have h1 : (n / g) * g = n := Nat.div_mul_cancel hgn
    have h2 : (d / g) * g = d := Nat.div_mul_cancel hgd
    have hmul : (n / g) * d * g = n * (d / g) * g := by
      calc (n / g) * d * g = ((n / g) * g) * d := by ac_rfl
        _ = n * d := by rw [h1]
        _ = n * ((d / g) * g) := by rw [h2]
        _ = n * (d / g) * g := by ac_rfl
    exact Nat.eq_of_mul_eq_mul_right hg_pos hmul

/-- Helper: scale-up of `A * q.den ≤ S * q.num` under `qAdd`. -/
private theorem qAdd_ub {A B S : Nat} {a b : QPos} (ha : 0 < a.den) (hb : 0 < b.den)
    (hA : A * a.den ≤ S * a.num) (hB : B * b.den ≤ S * b.num) :
    (A + B) * (qAdd a b).den ≤ S * (qAdd a b).num := by
  rcases qAdd_spec a b ha hb with ⟨_, heq⟩
  have hsum : (A + B) * (a.den * b.den) ≤ S * (a.num * b.den + b.num * a.den) := by
    rw [Nat.add_mul, Nat.mul_add]
    have h1 : A * (a.den * b.den) ≤ S * (a.num * b.den) := by
      calc A * (a.den * b.den) = (A * a.den) * b.den := by ac_rfl
        _ ≤ (S * a.num) * b.den := Nat.mul_le_mul_right b.den hA
        _ = S * (a.num * b.den) := by ac_rfl
    have h2 : B * (a.den * b.den) ≤ S * (b.num * a.den) := by
      calc B * (a.den * b.den) = (B * b.den) * a.den := by ac_rfl
        _ ≤ (S * b.num) * a.den := Nat.mul_le_mul_right a.den hB
        _ = S * (b.num * a.den) := by ac_rfl
    exact Nat.add_le_add h1 h2
  have hmul : (A + B) * (qAdd a b).den * (a.den * b.den) ≤ S * (qAdd a b).num * (a.den * b.den) := by
    calc (A + B) * (qAdd a b).den * (a.den * b.den)
        = (A + B) * (a.den * b.den) * (qAdd a b).den := by ac_rfl
      _ ≤ S * (a.num * b.den + b.num * a.den) * (qAdd a b).den := Nat.mul_le_mul_right _ hsum
      _ = S * ((a.num * b.den + b.num * a.den) * (qAdd a b).den) := by ac_rfl
      _ = S * ((qAdd a b).num * (a.den * b.den)) := by rw [← heq]
      _ = S * (qAdd a b).num * (a.den * b.den) := by ac_rfl
  exact Nat.le_of_mul_le_mul_right hmul (Nat.mul_pos ha hb)

private theorem qMul_ub {A B S1 S2 : Nat} {a b : QPos} (ha : 0 < a.den) (hb : 0 < b.den)
    (hA : A * a.den ≤ S1 * a.num) (hB : B * b.den ≤ S2 * b.num) :
    (A * B) * (qMul a b).den ≤ (S1 * S2) * (qMul a b).num := by
  rcases qMul_spec a b ha hb with ⟨_, heq⟩
  have hprod : (A * B) * (a.den * b.den) ≤ (S1 * S2) * (a.num * b.num) := by
    calc (A * B) * (a.den * b.den) = (A * a.den) * (B * b.den) := by ac_rfl
      _ ≤ (S1 * a.num) * (S2 * b.num) := Nat.mul_le_mul hA hB
      _ = (S1 * S2) * (a.num * b.num) := by ac_rfl
  have hmul : (A * B) * (qMul a b).den * (a.den * b.den) ≤ (S1 * S2) * (qMul a b).num * (a.den * b.den) := by
    calc (A * B) * (qMul a b).den * (a.den * b.den)
        = (A * B) * (a.den * b.den) * (qMul a b).den := by ac_rfl
      _ ≤ (S1 * S2) * (a.num * b.num) * (qMul a b).den := Nat.mul_le_mul_right _ hprod
      _ = (S1 * S2) * ((a.num * b.num) * (qMul a b).den) := by ac_rfl
      _ = (S1 * S2) * ((qMul a b).num * (a.den * b.den)) := by rw [← heq]
      _ = (S1 * S2) * (qMul a b).num * (a.den * b.den) := by ac_rfl
  exact Nat.le_of_mul_le_mul_right hmul (Nat.mul_pos ha hb)

private theorem qMin_ub {A B S : Nat} {a b : QPos}
    (hA : A * a.den ≤ S * a.num) (hB : B * b.den ≤ S * b.num) :
    min A B * (qMin a b).den ≤ S * (qMin a b).num := by
  unfold qMin
  split
  · exact Nat.le_trans (Nat.mul_le_mul_right a.den (Nat.min_le_left A B)) hA
  · exact Nat.le_trans (Nat.mul_le_mul_right b.den (Nat.min_le_right A B)) hB

private theorem qMax_ub {A B S : Nat} {a b : QPos} (ha : 0 < a.den) (hb : 0 < b.den)
    (hA : A * a.den ≤ S * a.num) (hB : B * b.den ≤ S * b.num) :
    max A B * (qMax a b).den ≤ S * (qMax a b).num := by
  unfold qMax
  split
  · rename_i hle
    have hA_b : A * b.den ≤ S * b.num := by
      have hm : A * b.den * a.den ≤ S * b.num * a.den := by
        calc A * b.den * a.den = (A * a.den) * b.den := by ac_rfl
          _ ≤ (S * a.num) * b.den := Nat.mul_le_mul_right b.den hA
          _ = S * (a.num * b.den) := by ac_rfl
          _ ≤ S * (b.num * a.den) := Nat.mul_le_mul_left S hle
          _ = S * b.num * a.den := by ac_rfl
      exact Nat.le_of_mul_le_mul_right hm ha
    have hmx : max A B * b.den = max (A * b.den) (B * b.den) := by
      by_cases hab : A ≤ B
      · rw [Nat.max_eq_right hab, Nat.max_eq_right (Nat.mul_le_mul_right b.den hab)]
      · have hba : B ≤ A := by omega
        rw [Nat.max_eq_left hba, Nat.max_eq_left (Nat.mul_le_mul_right b.den hba)]
    rw [hmx]; exact Nat.max_le.mpr ⟨hA_b, hB⟩
  · rename_i hgt
    have hge : b.num * a.den ≤ a.num * b.den := by omega
    have hB_a : B * a.den ≤ S * a.num := by
      have hm : B * a.den * b.den ≤ S * a.num * b.den := by
        calc B * a.den * b.den = (B * b.den) * a.den := by ac_rfl
          _ ≤ (S * b.num) * a.den := Nat.mul_le_mul_right a.den hB
          _ = S * (b.num * a.den) := by ac_rfl
          _ ≤ S * (a.num * b.den) := Nat.mul_le_mul_left S hge
          _ = S * a.num * b.den := by ac_rfl
      exact Nat.le_of_mul_le_mul_right hm hb
    have hmx : max A B * a.den = max (A * a.den) (B * a.den) := by
      by_cases hab : A ≤ B
      · rw [Nat.max_eq_right hab, Nat.max_eq_right (Nat.mul_le_mul_right a.den hab)]
      · have hba : B ≤ A := by omega
        rw [Nat.max_eq_left hba, Nat.max_eq_left (Nat.mul_le_mul_right a.den hba)]
    rw [hmx]; exact Nat.max_le.mpr ⟨hA, hB_a⟩

/-- **Equal-Block Infinite Tail Closure (ALL `M ≥ 2048` via the Exact `16` Rational Tail Boxes!):**
For EVERY `M ≥ 2048` and EVERY integer pair `(x, y)` with `M + 1 ≤ x ≤ y ≤ (4 * M) / 3`,
`EqualPairClosed M x y` holds! -/
theorem equal_block_tail_closure_all_M_ge_2048 (M x y : Nat) (hM : M ≥ 2048)
    (hx1 : M < x) (hxy : x ≤ y) (hy2 : y ≤ (4 * M) / 3) :
    EqualPairClosed M x y := by
  let dx := x - M
  let dy := y - M
  have hdx_pos : 1 ≤ dx := by omega
  have hord : dx ≤ dy := by omega
  have h3dy : 3 * dy ≤ M := by omega
  rcases equalTailBoxes16_domain_coverage M dx dy hM hord h3dy with
    ⟨b, hb_mem, htpl, hxlo_pos, hxhi_pos, hylo_pos, hyhi_pos, hxlo_le, hxhi_le, hylo_le, hyhi_le⟩
  have hchk := equalTailBoxes16_all_pass b hb_mem
  have hbk_pos : 0 < b.k ∧ b.n < b.k := by
    have ht := htpl
    unfold r5Template at ht
    split at ht
    · simp only [Prod.mk.injEq] at ht; omega
    · split at ht
      · simp only [Prod.mk.injEq] at ht; omega
      · split at ht
        · simp only [Prod.mk.injEq] at ht; omega
        · simp only [Prod.mk.injEq] at ht; omega
  unfold checkTailBox at hchk
  dsimp only at hchk
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
  have h1_lt : 3 ^ 256 * single.num ^ 123 * lower.den ^ 256 <
               (5 * lower.num) ^ 256 * 2048 ^ 10 * single.den ^ 123 :=
    Nat.le_of_ble_eq_true hok1
  have h2_lt : 6 ^ 256 * both.num ^ 123 * lower.den ^ 256 <
               (5 * lower.num) ^ 256 * 2048 ^ 10 * both.den ^ 123 :=
    Nat.le_of_ble_eq_true hok2
  -- 1. Lower bound: `M * lower.num ≤ r5AttachLower M dy * lower.den`
  have hone_add := qAdd_spec one b.yhi (by decide) hyhi_pos
  have hlt1_spec := qMul_spec ⟨b.k - b.n, b.k⟩ (qAdd one b.yhi) hbk_pos.1 hone_add.1
  have hlt2_spec := qMul_spec ⟨9, 4⟩ b.yhi (by decide) hyhi_pos
  have hlower_spec := qSub_spec loTerm1 loTerm2 hlt1_spec.1 hlt2_spec.1 (Nat.le_of_lt hlo_gt)
  have hlower_M : M * lower.num ≤ r5AttachLower M dy * lower.den := by
    -- Compute `r5AttachLower M dy`:
    have hr5_mul : (4 * b.k) * r5AttachLower M dy + (5 * b.k + 4 * b.n) * dy ≥ 4 * (b.k - b.n) * M := by
      unfold r5AttachLower
      rw [← htpl]
      dsimp only
      have h1 : 4 * ((9 * (dy - 1)) / 4) ≤ 9 * dy := by omega
      have h2 : b.k * ((b.n * (M + dy)) / b.k) ≤ b.n * (M + dy) := Nat.mul_div_le (b.n * (M + dy)) b.k
      have hkn : (b.k - b.n) * M + b.n * M = b.k * M := by
        rw [← Nat.add_mul, Nat.sub_add_cancel (Nat.le_of_lt hbk_pos.2)]
      have hsub : (M + dy) - (9 * (dy - 1)) / 4 - (b.n * (M + dy)) / b.k +
                  (9 * (dy - 1)) / 4 + (b.n * (M + dy)) / b.k ≥ M + dy := by omega
      -- Multiply `hsub` by `4 * b.k` cleanly:
      have hmul := Nat.mul_le_mul_left (4 * b.k) hsub
      rw [Nat.mul_add, Nat.mul_add] at hmul
      have hA : 4 * b.k * ((9 * (dy - 1)) / 4) ≤ 9 * b.k * dy := by
        calc 4 * b.k * ((9 * (dy - 1)) / 4) = b.k * (4 * ((9 * (dy - 1)) / 4)) := by ac_rfl
          _ ≤ b.k * (9 * dy) := Nat.mul_le_mul_left b.k h1
          _ = 9 * b.k * dy := by ac_rfl
      have hB : 4 * b.k * ((b.n * (M + dy)) / b.k) ≤ 4 * b.n * M + 4 * b.n * dy := by
        calc 4 * b.k * ((b.n * (M + dy)) / b.k) = 4 * (b.k * ((b.n * (M + dy)) / b.k)) := by ac_rfl
          _ ≤ 4 * (b.n * (M + dy)) := Nat.mul_le_mul_left 4 h2
          _ = 4 * b.n * (M + dy) := by ac_rfl
          _ = 4 * b.n * M + 4 * b.n * dy := Nat.mul_add (4 * b.n) M dy
      have hmul' : 4 * b.k * (M + dy - 9 * (dy - 1) / 4 - b.n * (M + dy) / b.k) +
                   4 * b.k * (9 * (dy - 1) / 4) + 4 * b.k * (b.n * (M + dy) / b.k) ≥
                   4 * b.k * M + 4 * b.k * dy := by
        have h1' := Nat.mul_le_mul_left (4 * b.k) hsub
        rw [Nat.mul_add, Nat.mul_add, Nat.mul_add] at h1'
        exact h1'
      have hC : 4 * b.k * M = 4 * (b.k - b.n) * M + 4 * b.n * M := by
        calc 4 * b.k * M = 4 * (b.k * M) := Nat.mul_assoc 4 b.k M
          _ = 4 * ((b.k - b.n) * M + b.n * M) := by rw [hkn]
          _ = 4 * ((b.k - b.n) * M) + 4 * (b.n * M) := Nat.mul_add _ _ _
          _ = 4 * (b.k - b.n) * M + 4 * b.n * M := by rw [← Nat.mul_assoc, ← Nat.mul_assoc]
      have hD : (5 * b.k + 4 * b.n) * dy = 5 * b.k * dy + 4 * b.n * dy := Nat.add_mul _ _ _
      have h59 : 5 * b.k * dy + 4 * b.k * dy = 9 * b.k * dy := by
        rw [← Nat.add_mul, ← Nat.add_mul]
      rw [hD]; omega
    -- Also `dy * b.yhi.den ≤ b.yhi.num * M`, so:
    -- `4 * b.k * b.yhi.den * M * lower.num / lower.den = (4*(b.k - b.n)*(b.yhi.den + b.yhi.num) - 9*b.k*b.yhi.num) * M`
    -- `= (4*(b.k - b.n)*b.yhi.den - (5*b.k + 4*b.n)*b.yhi.num) * M`
    -- `≤ 4*b.k * r5AttachLower M dy * b.yhi.den`!
    -- Verify the exact rational identity for `lower`:
    have hlo_id : lower.num * (4 * b.k * b.yhi.den) + (5 * b.k + 4 * b.n) * b.yhi.num * lower.den =
                  4 * (b.k - b.n) * b.yhi.den * lower.den := by
      -- Multiply by `loTerm1.den * loTerm2.den * (qAdd one b.yhi).den` and cancel!
      let F1 := loTerm1.den * loTerm2.den * (qAdd one b.yhi).den
      have hF1_pos : 0 < F1 := Nat.mul_pos (Nat.mul_pos hlt1_spec.1 hlt2_spec.1) hone_add.1
      have hstep1 : loTerm1.num * (b.k * b.yhi.den) = (b.k - b.n) * (b.yhi.den + b.yhi.num) * loTerm1.den := by
        have h := congrArg (· * b.yhi.den) hlt1_spec.2
        have hq := hone_add.2
        simp only [one, Nat.one_mul, Nat.mul_one] at hq
        have h2 : loTerm1.num * (b.k * b.yhi.den) * (qAdd one b.yhi).den =
                  (b.k - b.n) * (b.yhi.den + b.yhi.num) * loTerm1.den * (qAdd one b.yhi).den := by
          calc loTerm1.num * (b.k * b.yhi.den) * (qAdd one b.yhi).den
              = loTerm1.num * (b.k * (qAdd one b.yhi).den) * b.yhi.den := by ac_rfl
            _ = (b.k - b.n) * (qAdd one b.yhi).num * loTerm1.den * b.yhi.den := by rw [hlt1_spec.2]
            _ = (b.k - b.n) * ((qAdd one b.yhi).num * b.yhi.den) * loTerm1.den := by ac_rfl
            _ = (b.k - b.n) * ((b.yhi.den + b.yhi.num) * (qAdd one b.yhi).den) * loTerm1.den := by rw [hq]
            _ = (b.k - b.n) * (b.yhi.den + b.yhi.num) * loTerm1.den * (qAdd one b.yhi).den := by ac_rfl
        exact Nat.eq_of_mul_eq_mul_right hone_add.1 h2
      have hstep2 : loTerm2.num * (4 * b.yhi.den) = 9 * b.yhi.num * loTerm2.den := hlt2_spec.2
      have hmul_sub :
          lower.num * (4 * b.k * b.yhi.den) * (loTerm1.den * loTerm2.den) +
          (5 * b.k + 4 * b.n) * b.yhi.num * lower.den * (loTerm1.den * loTerm2.den) =
          4 * (b.k - b.n) * b.yhi.den * lower.den * (loTerm1.den * loTerm2.den) := by
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
          rw [← Nat.add_mul]
          have : 4 * (b.k - b.n) + (5 * b.k + 4 * b.n) = 9 * b.k := by omega
          rw [this]
        have hge_sub : 9 * b.k * b.yhi.num * (loTerm1.den * loTerm2.den) ≤
                       4 * (b.k - b.n) * (b.yhi.den + b.yhi.num) * (loTerm1.den * loTerm2.den) := by
          rw [← hA, ← hB]
          exact Nat.mul_le_mul_right _ (Nat.le_of_lt hlo_gt)
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
        have hadd_eq :
            4 * (b.k - b.n) * b.yhi.den * (loTerm1.den * loTerm2.den) * lower.den -
            (5 * b.k + 4 * b.n) * b.yhi.num * (loTerm1.den * loTerm2.den) * lower.den +
            (5 * b.k + 4 * b.n) * b.yhi.num * lower.den * (loTerm1.den * loTerm2.den) =
            4 * (b.k - b.n) * b.yhi.den * lower.den * (loTerm1.den * loTerm2.den) := by
          have hc1 : (5 * b.k + 4 * b.n) * b.yhi.num * lower.den * (loTerm1.den * loTerm2.den) =
                     (5 * b.k + 4 * b.n) * b.yhi.num * (loTerm1.den * loTerm2.den) * lower.den := by ac_rfl
          have hc2 : 4 * (b.k - b.n) * b.yhi.den * (loTerm1.den * loTerm2.den) * lower.den =
                     4 * (b.k - b.n) * b.yhi.den * lower.den * (loTerm1.den * loTerm2.den) := by ac_rfl
          rw [hc1, Nat.sub_add_cancel hge2, hc2]
        exact hadd_eq
      rw [← Nat.add_mul] at hmul_sub
      exact Nat.eq_of_mul_eq_mul_right (Nat.mul_pos hlt1_spec.1 hlt2_spec.1) hmul_sub
    -- Now combine `hlo_id`, `hr5_mul`, and `hyhi_le` (`dy * b.yhi.den ≤ b.yhi.num * M`)!
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
  -- 2. Geometric upper bounds (`W`, `e`, `P`, `twoR + 4`):
  unfold EqualPairClosed
  dsimp only
  intro hK
  let K := (4 * M) / 3
  let lo := r5AttachLower M dy
  let r := lo + (if lo ≥ x then (lo - x) % 2 else (x - lo) % 2)
  have hlo_le_r : lo ≤ r := by dsimp only [r]; omega
  have hM_lower_r : M * lower.num ≤ r * lower.den :=
    Nat.le_trans hlower_M (Nat.mul_le_mul_right lower.den hlo_le_r)
  let W := x + y + 1 - 2 * M
  have hW_eq : W = dx + dy + 1 := by omega
  have hxy_add := qAdd_spec b.xhi b.yhi hxhi_pos hyhi_pos
  have hwidth_spec := qAdd_spec (qAdd b.xhi b.yhi) eps hxy_add.1 (by decide)
  have hW_ub : W * width.den ≤ M * width.num := by
    rw [hW_eq]
    have h1 : (dx + dy) * (qAdd b.xhi b.yhi).den ≤ M * (qAdd b.xhi b.yhi).num :=
      qAdd_ub hxhi_pos hyhi_pos
        (by rw [Nat.mul_comm M b.xhi.num]; exact hxhi_le)
        (by rw [Nat.mul_comm M b.yhi.num]; exact hyhi_le)
    have h2 : 1 * eps.den ≤ M * eps.num := by dsimp only [eps]; omega
    exact qAdd_ub hxy_add.1 (by decide) h1 h2
  have himb_le : b.xlo.num * third.den ≤ third.num * b.xlo.den := by
    -- `b.xlo ≤ dx/M ≤ dy/M ≤ 1/3`!
    have hm : b.xlo.num * 3 * M ≤ 1 * b.xlo.den * M := by
      calc b.xlo.num * 3 * M = 3 * (b.xlo.num * M) := by ac_rfl
        _ ≤ 3 * (dx * b.xlo.den) := Nat.mul_le_mul_left 3 hxlo_le
        _ = (3 * dx) * b.xlo.den := by ac_rfl
        _ ≤ M * b.xlo.den := Nat.mul_le_mul_right b.xlo.den (by omega)
        _ = 1 * b.xlo.den * M := by simp [Nat.mul_comm]
    exact Nat.le_of_mul_le_mul_right hm (by omega : 0 < M)
  have himb_spec := qSub_spec third b.xlo (by decide) hxlo_pos himb_le
  let e := K - x - 2
  have he_ub : e * imb.den ≤ M * imb.num := by
    -- `3 * e ≤ M - 3 * dx` and `b.xlo.num * M ≤ dx * b.xlo.den`
    have h3e : 3 * e + 3 * dx ≤ M := by omega
    have hmul : e * imb.den * (3 * b.xlo.den) ≤ M * imb.num * (3 * b.xlo.den) := by
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
        _ = M * imb.num * (3 * b.xlo.den) := by ac_rfl
    exact Nat.le_of_mul_le_mul_right hmul (Nat.mul_pos (by decide) hxlo_pos)
  have h3imb_spec := qMul_spec ⟨3, 1⟩ imb (by decide) himb_spec.1
  have h2imb_spec := qMul_spec ⟨2, 1⟩ imb (by decide) himb_spec.1
  have h3e_ub : (3 * e) * (qMul ⟨3, 1⟩ imb).den ≤ M * (qMul ⟨3, 1⟩ imb).num := by
    have h3 : 3 * (⟨3, 1⟩ : QPos).den ≤ 1 * (⟨3, 1⟩ : QPos).num := by decide
    have h := qMul_ub (by decide) himb_spec.1 h3 he_ub
    simpa [Nat.one_mul] using h
  have h2e_ub : (2 * e) * (qMul ⟨2, 1⟩ imb).den ≤ M * (qMul ⟨2, 1⟩ imb).num := by
    have h2 : 2 * (⟨2, 1⟩ : QPos).den ≤ 1 * (⟨2, 1⟩ : QPos).num := by decide
    have h := qMul_ub (by decide) himb_spec.1 h2 he_ub
    simpa [Nat.one_mul] using h
  have h2_ub : 2 * eps2.den ≤ M * eps2.num := by dsimp only [eps2]; omega
  have hmin3_pos : 0 < (qMin width (qMul ⟨3, 1⟩ imb)).den := by
    unfold qMin; split; exact hwidth_spec.1; exact h3imb_spec.1
  have hmin2_pos : 0 < (qMin width (qMul ⟨2, 1⟩ imb)).den := by
    unfold qMin; split; exact hwidth_spec.1; exact h2imb_spec.1
  have hs1a_spec := qAdd_spec (qMin width (qMul ⟨3, 1⟩ imb)) eps2 hmin3_pos (by decide)
  have hs1_spec := qMul_spec s1a s1a hs1a_spec.1 hs1a_spec.1
  have hw2_spec := qAdd_spec width eps2 hwidth_spec.1 (by decide)
  have hs2b_spec := qAdd_spec (qMin width (qMul ⟨2, 1⟩ imb)) eps2 hmin2_pos (by decide)
  have hs2_spec := qMul_spec (qAdd width eps2) (qAdd (qMin width (qMul ⟨2, 1⟩ imb)) eps2) hw2_spec.1 hs2b_spec.1
  have hP_ub : max ((min W (3 * e) + 2) * (min W (3 * e) + 2)) ((W + 2) * (min W (2 * e) + 2)) * single.den ≤
               (M * M) * single.num := by
    have hA : (min W (3 * e) + 2) * s1a.den ≤ M * s1a.num :=
      qAdd_ub hmin3_pos (by decide) (qMin_ub hW_ub h3e_ub) h2_ub
    have hP1 : ((min W (3 * e) + 2) * (min W (3 * e) + 2)) * s1.den ≤ (M * M) * s1.num :=
      qMul_ub hs1a_spec.1 hs1a_spec.1 hA hA
    have hB1 : (W + 2) * (qAdd width eps2).den ≤ M * (qAdd width eps2).num :=
      qAdd_ub hwidth_spec.1 (by decide) hW_ub h2_ub
    have hB2 : (min W (2 * e) + 2) * (qAdd (qMin width (qMul ⟨2, 1⟩ imb)) eps2).den ≤
               M * (qAdd (qMin width (qMul ⟨2, 1⟩ imb)) eps2).num :=
      qAdd_ub hmin2_pos (by decide) (qMin_ub hW_ub h2e_ub) h2_ub
    have hP2 : ((W + 2) * (min W (2 * e) + 2)) * s2.den ≤ (M * M) * s2.num :=
      qMul_ub hw2_spec.1 hs2b_spec.1 hB1 hB2
    exact qMax_ub hs1_spec.1 hs2_spec.1 hP1 hP2
  have hM10 : 2048 ^ 10 ≤ M ^ 10 := Nat.pow_le_pow_left hM 10
  have hM256 : M ^ 10 * (M * M) ^ 123 = M ^ 256 := by
    rw [← Nat.pow_two, ← Nat.pow_mul, ← Nat.pow_add]
  have hlow_pow : (5 * lower.num) ^ 256 * M ^ 256 ≤ (5 * r) ^ 256 * lower.den ^ 256 := by
    have h5 : (5 * M * lower.num) ≤ (5 * r * lower.den) := by
      calc 5 * M * lower.num = 5 * (M * lower.num) := by ac_rfl
        _ ≤ 5 * (r * lower.den) := Nat.mul_le_mul_left 5 hM_lower_r
        _ = 5 * r * lower.den := by ac_rfl
    have hp := Nat.pow_le_pow_left h5 256
    simp only [Nat.mul_pow] at hp ⊢
    calc 5 ^ 256 * lower.num ^ 256 * M ^ 256 = 5 ^ 256 * M ^ 256 * lower.num ^ 256 := by ac_rfl
      _ ≤ 5 ^ 256 * r ^ 256 * lower.den ^ 256 := hp
  constructor
  · -- 1-class inequality: `3^256 * P^123 < (5*r)^256`
    let P := max ((min W (3 * e) + 2) * (min W (3 * e) + 2)) ((W + 2) * (min W (2 * e) + 2))
    have hP_pow : P ^ 123 * single.den ^ 123 ≤ (M * M) ^ 123 * single.num ^ 123 := by
      rw [← Nat.mul_pow, ← Nat.mul_pow]
      exact Nat.pow_le_pow_left hP_ub 123
    have hlt : 3 ^ 256 * P ^ 123 * (single.den ^ 123 * lower.den ^ 256) <
               (5 * r) ^ 256 * (single.den ^ 123 * lower.den ^ 256) := by
      calc 3 ^ 256 * P ^ 123 * (single.den ^ 123 * lower.den ^ 256)
          = 3 ^ 256 * (P ^ 123 * single.den ^ 123) * lower.den ^ 256 := by ac_rfl
        _ ≤ 3 ^ 256 * ((M * M) ^ 123 * single.num ^ 123) * lower.den ^ 256 :=
            Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hP_pow)
        _ = (3 ^ 256 * single.num ^ 123 * lower.den ^ 256) * (M * M) ^ 123 := by ac_rfl
        _ < ((5 * lower.num) ^ 256 * 2048 ^ 10 * single.den ^ 123) * (M * M) ^ 123 :=
            Nat.mul_lt_mul_of_pos_right h1_lt (Nat.pow_pos (Nat.mul_pos (by omega) (by omega)))
        _ ≤ ((5 * lower.num) ^ 256 * M ^ 10 * single.den ^ 123) * (M * M) ^ 123 :=
            Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hM10))
        _ = ((5 * lower.num) ^ 256 * (M ^ 10 * (M * M) ^ 123)) * single.den ^ 123 := by ac_rfl
        _ = ((5 * lower.num) ^ 256 * M ^ 256) * single.den ^ 123 := by rw [hM256]
        _ ≤ ((5 * r) ^ 256 * lower.den ^ 256) * single.den ^ 123 := Nat.mul_le_mul_right _ hlow_pow
        _ = (5 * r) ^ 256 * (single.den ^ 123 * lower.den ^ 256) := by ac_rfl
    exact Nat.lt_of_mul_lt_mul_right hlt
  · -- 2-class inequality: `6^256 * (twoR + 4)^246 < (5*r)^256 * 2^246`
    intro hwrap
    let twoR := min (2 * W) (2 * K - x - y - 4)
    have hxy_lo := qAdd_spec b.xlo b.ylo hxlo_pos hylo_pos
    have hhalf_lo := qMul_spec ⟨1, 2⟩ (qAdd b.xlo b.ylo) (by decide) hxy_lo.1
    have hhalf_le_third : (qMul ⟨1, 2⟩ (qAdd b.xlo b.ylo)).num * third.den ≤
                          third.num * (qMul ⟨1, 2⟩ (qAdd b.xlo b.ylo)).den := by
      have hsum_dx : (b.xlo.num * b.ylo.den + b.ylo.num * b.xlo.den) * M ≤ (dx + dy) * (b.xlo.den * b.ylo.den) := by
        rw [Nat.add_mul, Nat.add_mul]
        have hA : b.xlo.num * b.ylo.den * M ≤ dx * (b.xlo.den * b.ylo.den) := by
          calc b.xlo.num * b.ylo.den * M = (b.xlo.num * M) * b.ylo.den := by ac_rfl
            _ ≤ (dx * b.xlo.den) * b.ylo.den := Nat.mul_le_mul_right _ hxlo_le
            _ = dx * (b.xlo.den * b.ylo.den) := by ac_rfl
        have hB : b.ylo.num * b.xlo.den * M ≤ dy * (b.xlo.den * b.ylo.den) := by
          calc b.ylo.num * b.xlo.den * M = (b.ylo.num * M) * b.xlo.den := by ac_rfl
            _ ≤ (dy * b.ylo.den) * b.xlo.den := Nat.mul_le_mul_right _ hylo_le
            _ = dy * (b.xlo.den * b.ylo.den) := by ac_rfl
        exact Nat.add_le_add hA hB
      have hq_le : (qAdd b.xlo b.ylo).num * M ≤ (dx + dy) * (qAdd b.xlo b.ylo).den := by
        have hm : (qAdd b.xlo b.ylo).num * M * (b.xlo.den * b.ylo.den) ≤
                  (dx + dy) * (qAdd b.xlo b.ylo).den * (b.xlo.den * b.ylo.den) := by
          calc (qAdd b.xlo b.ylo).num * M * (b.xlo.den * b.ylo.den)
              = ((qAdd b.xlo b.ylo).num * (b.xlo.den * b.ylo.den)) * M := by ac_rfl
            _ = ((b.xlo.num * b.ylo.den + b.ylo.num * b.xlo.den) * (qAdd b.xlo b.ylo).den) * M := by rw [hxy_lo.2]
            _ = ((b.xlo.num * b.ylo.den + b.ylo.num * b.xlo.den) * M) * (qAdd b.xlo b.ylo).den := by ac_rfl
            _ ≤ ((dx + dy) * (b.xlo.den * b.ylo.den)) * (qAdd b.xlo b.ylo).den := Nat.mul_le_mul_right _ hsum_dx
            _ = (dx + dy) * (qAdd b.xlo b.ylo).den * (b.xlo.den * b.ylo.den) := by ac_rfl
        exact Nat.le_of_mul_le_mul_right hm (Nat.mul_pos hxlo_pos hylo_pos)
      have h3dxdy : 3 * (dx + dy) ≤ 2 * M := by omega
      have hfac_pos : 0 < 2 * (qAdd b.xlo b.ylo).den * M :=
        Nat.mul_pos (Nat.mul_pos (by decide) hxy_lo.1) (by omega)
      have hm : (qMul ⟨1, 2⟩ (qAdd b.xlo b.ylo)).num * 3 * (2 * (qAdd b.xlo b.ylo).den * M) ≤
                1 * (qMul ⟨1, 2⟩ (qAdd b.xlo b.ylo)).den * (2 * (qAdd b.xlo b.ylo).den * M) := by
        calc (qMul ⟨1, 2⟩ (qAdd b.xlo b.ylo)).num * 3 * (2 * (qAdd b.xlo b.ylo).den * M)
            = ((qMul ⟨1, 2⟩ (qAdd b.xlo b.ylo)).num * (2 * (qAdd b.xlo b.ylo).den)) * 3 * M := by ac_rfl
          _ = ((1 * (qAdd b.xlo b.ylo).num) * (qMul ⟨1, 2⟩ (qAdd b.xlo b.ylo)).den) * 3 * M := by rw [hhalf_lo.2]
          _ = 3 * ((qAdd b.xlo b.ylo).num * M) * (qMul ⟨1, 2⟩ (qAdd b.xlo b.ylo)).den := by simp; ac_rfl
          _ ≤ 3 * ((dx + dy) * (qAdd b.xlo b.ylo).den) * (qMul ⟨1, 2⟩ (qAdd b.xlo b.ylo)).den :=
              Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 3 hq_le)
          _ = (3 * (dx + dy)) * (qAdd b.xlo b.ylo).den * (qMul ⟨1, 2⟩ (qAdd b.xlo b.ylo)).den := by ac_rfl
          _ ≤ (2 * M) * (qAdd b.xlo b.ylo).den * (qMul ⟨1, 2⟩ (qAdd b.xlo b.ylo)).den :=
              Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ h3dxdy)
          _ = 1 * (qMul ⟨1, 2⟩ (qAdd b.xlo b.ylo)).den * (2 * (qAdd b.xlo b.ylo).den * M) := by simp; ac_rfl
      exact Nat.le_of_mul_le_mul_right hm hfac_pos
    have hrad_spec := qSub_spec third (qMul ⟨1, 2⟩ (qAdd b.xlo b.ylo)) (by decide) hhalf_lo.1 hhalf_le_third
    have hhalf_lb : (qMul ⟨1, 2⟩ (qAdd b.xlo b.ylo)).num * (2 * M) ≤
                    (dx + dy) * (qMul ⟨1, 2⟩ (qAdd b.xlo b.ylo)).den := by
      have hsum_dx : (b.xlo.num * b.ylo.den + b.ylo.num * b.xlo.den) * M ≤ (dx + dy) * (b.xlo.den * b.ylo.den) := by
        rw [Nat.add_mul, Nat.add_mul]
        have hA : b.xlo.num * b.ylo.den * M ≤ dx * (b.xlo.den * b.ylo.den) := by
          calc b.xlo.num * b.ylo.den * M = (b.xlo.num * M) * b.ylo.den := by ac_rfl
            _ ≤ (dx * b.xlo.den) * b.ylo.den := Nat.mul_le_mul_right _ hxlo_le
            _ = dx * (b.xlo.den * b.ylo.den) := by ac_rfl
        have hB : b.ylo.num * b.xlo.den * M ≤ dy * (b.xlo.den * b.ylo.den) := by
          calc b.ylo.num * b.xlo.den * M = (b.ylo.num * M) * b.xlo.den := by ac_rfl
            _ ≤ (dy * b.ylo.den) * b.xlo.den := Nat.mul_le_mul_right _ hylo_le
            _ = dy * (b.xlo.den * b.ylo.den) := by ac_rfl
        exact Nat.add_le_add hA hB
      have hq_le : (qAdd b.xlo b.ylo).num * M ≤ (dx + dy) * (qAdd b.xlo b.ylo).den := by
        have hm : (qAdd b.xlo b.ylo).num * M * (b.xlo.den * b.ylo.den) ≤
                  (dx + dy) * (qAdd b.xlo b.ylo).den * (b.xlo.den * b.ylo.den) := by
          calc (qAdd b.xlo b.ylo).num * M * (b.xlo.den * b.ylo.den)
              = ((qAdd b.xlo b.ylo).num * (b.xlo.den * b.ylo.den)) * M := by ac_rfl
            _ = ((b.xlo.num * b.ylo.den + b.ylo.num * b.xlo.den) * (qAdd b.xlo b.ylo).den) * M := by rw [hxy_lo.2]
            _ = ((b.xlo.num * b.ylo.den + b.ylo.num * b.xlo.den) * M) * (qAdd b.xlo b.ylo).den := by ac_rfl
            _ ≤ ((dx + dy) * (b.xlo.den * b.ylo.den)) * (qAdd b.xlo b.ylo).den := Nat.mul_le_mul_right _ hsum_dx
            _ = (dx + dy) * (qAdd b.xlo b.ylo).den * (b.xlo.den * b.ylo.den) := by ac_rfl
        exact Nat.le_of_mul_le_mul_right hm (Nat.mul_pos hxlo_pos hylo_pos)
      have hm : (qMul ⟨1, 2⟩ (qAdd b.xlo b.ylo)).num * (2 * M) * (qAdd b.xlo b.ylo).den ≤
                (dx + dy) * (qMul ⟨1, 2⟩ (qAdd b.xlo b.ylo)).den * (qAdd b.xlo b.ylo).den := by
        calc (qMul ⟨1, 2⟩ (qAdd b.xlo b.ylo)).num * (2 * M) * (qAdd b.xlo b.ylo).den
            = ((qMul ⟨1, 2⟩ (qAdd b.xlo b.ylo)).num * (2 * (qAdd b.xlo b.ylo).den)) * M := by ac_rfl
          _ = ((1 * (qAdd b.xlo b.ylo).num) * (qMul ⟨1, 2⟩ (qAdd b.xlo b.ylo)).den) * M := by rw [hhalf_lo.2]
          _ = ((qAdd b.xlo b.ylo).num * M) * (qMul ⟨1, 2⟩ (qAdd b.xlo b.ylo)).den := by simp; ac_rfl
          _ ≤ ((dx + dy) * (qAdd b.xlo b.ylo).den) * (qMul ⟨1, 2⟩ (qAdd b.xlo b.ylo)).den := Nat.mul_le_mul_right _ hq_le
          _ = (dx + dy) * (qMul ⟨1, 2⟩ (qAdd b.xlo b.ylo)).den * (qAdd b.xlo b.ylo).den := by ac_rfl
      exact Nat.le_of_mul_le_mul_right hm hxy_lo.1
    have hrem_ub : (2 * K - x - y - 4) * rad.den ≤ (2 * M) * rad.num := by
      -- `3 * (2*K - x - y - 4) + 3 * (dx + dy) ≤ 2 * M`
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
      have hm : (2 * K - x - y - 4) * rad.den * (3 * hq.den) ≤ (2 * M) * rad.num * (3 * hq.den) := by
        calc (2 * K - x - y - 4) * rad.den * (3 * hq.den)
            = (2 * K - x - y - 4) * (3 * hq.den) * rad.den := by ac_rfl
          _ ≤ (2 * M) * (1 * hq.den - hq.num * 3) * rad.den := Nat.mul_le_mul_right rad.den h1
          _ = (2 * M) * ((1 * hq.den - hq.num * 3) * rad.den) := by ac_rfl
          _ = (2 * M) * (rad.num * (3 * hq.den)) := by rw [← hrad_spec.2]
          _ = (2 * M) * rad.num * (3 * hq.den) := by ac_rfl
      exact Nat.le_of_mul_le_mul_right hm (Nat.mul_pos (by decide) hhalf_lo.1)
    have h2W_ub : (2 * W) * width.den ≤ (2 * M) * width.num := by
      calc (2 * W) * width.den = 2 * (W * width.den) := by ac_rfl
        _ ≤ 2 * (M * width.num) := Nat.mul_le_mul_left 2 hW_ub
        _ = (2 * M) * width.num := by ac_rfl
    have hmin2_pos' : 0 < (qMin width rad).den := by
      unfold qMin; split; exact hwidth_spec.1; exact hrad_spec.1
    have hb1_spec := qAdd_spec (qMin width rad) eps2 hmin2_pos' (by decide)
    have h4_ub : 4 * eps2.den ≤ (2 * M) * eps2.num := by dsimp only [eps2]; omega
    have htwoR4_ub : (twoR + 4) * b1.den ≤ (2 * M) * b1.num :=
      qAdd_ub hmin2_pos' (by decide) (qMin_ub h2W_ub hrem_ub) h4_ub
    have htwoR4_sq : ((twoR + 4) * (twoR + 4)) * both.den ≤ ((2 * M) * (2 * M)) * both.num :=
      qMul_ub hb1_spec.1 hb1_spec.1 htwoR4_ub htwoR4_ub
    have htwoR_pow : (twoR + 4) ^ 246 * both.den ^ 123 ≤ (2 ^ 246 * (M * M) ^ 123) * both.num ^ 123 := by
      have hp : ((twoR + 4) * (twoR + 4)) ^ 123 * both.den ^ 123 ≤
                ((2 * M) * (2 * M)) ^ 123 * both.num ^ 123 := by
        rw [← Nat.mul_pow, ← Nat.mul_pow]
        exact Nat.pow_le_pow_left htwoR4_sq 123
      have hsq : ((twoR + 4) * (twoR + 4)) ^ 123 = (twoR + 4) ^ 246 := by
        rw [← Nat.pow_two, ← Nat.pow_mul]
      have h2M : ((2 * M) * (2 * M)) ^ 123 = 2 ^ 246 * (M * M) ^ 123 := by
        have h1 : (2 * M) * (2 * M) = 2 ^ 2 * (M * M) := by rw [Nat.pow_two]; ac_rfl
        rw [h1, Nat.mul_pow, ← Nat.pow_mul]
      rw [hsq, h2M] at hp
      exact hp
    have hlt : 6 ^ 256 * (twoR + 4) ^ 246 * (both.den ^ 123 * lower.den ^ 256) <
               (5 * r) ^ 256 * 2 ^ 246 * (both.den ^ 123 * lower.den ^ 256) := by
      have hc2_pos : 0 < 2 ^ 246 := by decide
      have hM2_pos : 0 < (M * M) ^ 123 := Nat.pow_pos (Nat.mul_pos (by omega) (by omega))
      generalize 6 ^ 256 = c6, 2 ^ 246 = c2, 2048 ^ 10 = c2048 at h2_lt hM10 htwoR_pow hc2_pos ⊢
      generalize (5 * lower.num) ^ 256 = L5, (5 * r) ^ 256 = R5,
                 (twoR + 4) ^ 246 = T246, (M * M) ^ 123 = MM,
                 both.num ^ 123 = BN, both.den ^ 123 = BD,
                 lower.den ^ 256 = LD, M ^ 10 = M10, M ^ 256 = M256
                 at h2_lt hM10 hM256 hlow_pow htwoR_pow hM2_pos ⊢
      calc c6 * T246 * (BD * LD)
          = c6 * (T246 * BD) * LD := by ac_rfl
        _ ≤ c6 * ((c2 * MM) * BN) * LD := Nat.mul_le_mul_right LD (Nat.mul_le_mul_left c6 htwoR_pow)
        _ = (c6 * BN * LD) * (c2 * MM) := by ac_rfl
        _ < (L5 * c2048 * BD) * (c2 * MM) := Nat.mul_lt_mul_of_pos_right h2_lt (Nat.mul_pos hc2_pos hM2_pos)
        _ ≤ (L5 * M10 * BD) * (c2 * MM) := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right BD (Nat.mul_le_mul_left L5 hM10))
        _ = (L5 * (M10 * MM)) * c2 * BD := by ac_rfl
        _ = (L5 * M256) * c2 * BD := by rw [hM256]
        _ ≤ (R5 * LD) * c2 * BD := Nat.mul_le_mul_right BD (Nat.mul_le_mul_right c2 hlow_pow)
        _ = R5 * c2 * (BD * LD) := by ac_rfl
    exact Nat.lt_of_mul_lt_mul_right hlt

/-- **Master Equal-Block Closure Theorem (`M = 2^m` for ALL `m ≥ 8`, i.e. ALL `M ≥ 256`):**
Combines `equal_block_med_256_512_1024` (`76,492` pairs) and `equal_block_tail_closure_all_M_ge_2048`
(`16` rational tail boxes), closing EVERY equal-block pair `(x, y)` for ALL `M = 2^m ≥ 256`
(while `equal_block_small_625_certified` closes ALL `625` same-parity pairs for `M ∈ {4..128}`)! -/
theorem equal_block_closure_all_pow2_ge_256 (m x y : Nat) (hm : m ≥ 8)
    (hx1 : 2 ^ m < x) (hxy : x ≤ y) (hy2 : y ≤ (4 * 2 ^ m) / 3) :
    EqualPairClosed (2 ^ m) x y := by
  by_cases h11 : m ≥ 11
  · have hM2048 : 2 ^ m ≥ 2048 :=
      Nat.le_trans (by decide : 2048 ≤ 2 ^ 11) (Nat.pow_le_pow_right (by omega) h11)
    exact equal_block_tail_closure_all_M_ge_2048 (2 ^ m) x y hM2048 hx1 hxy hy2
  · have hcases : m = 8 ∨ m = 9 ∨ m = 10 := by omega
    rcases hcases with rfl | rfl | rfl
    · exact equal_block_med_256_512_1024 256 x y (Or.inl rfl) hx1 hxy hy2
    · exact equal_block_med_256_512_1024 512 x y (Or.inr (Or.inl rfl)) hx1 hxy hy2
    · exact equal_block_med_256_512_1024 1024 x y (Or.inr (Or.inr rfl)) hx1 hxy hy2

end ClawFreeEG
