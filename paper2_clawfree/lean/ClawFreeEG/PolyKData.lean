import ClawFreeEG.TwoCycleData

/-!
# ClawFreeEG.PolyKData

Zero-`Std` (pure `Init`) proof-carrying data module for `ClawFreeEG.PolyKAndSublinear`:
embeds the exact `17 + 17 + 16 = 50` rational tail boxes from
`cert/witnesses/two_cycle_closure.json` (`equal_k_boxes` for `k = 3, 4, 5` at
`M ≥ 2^36, 2^51, 2^62`) and kernel-verifies every box inequality in exact `Nat` arithmetic.

Omits `import Std` to keep peak RSS low during compilation.
-/

namespace ClawFreeEG.PolyKData

open ClawFreeEG.TwoCycleData

/-- Exact `Nat` box verifier for equal-block `k`-cycle tail closure with multiplicity
`mult = k - 1` and threshold `m0`: checks `(5 * lower)^256 * m0^10 > (3 * mult)^256 * single^123`
AND `(5 * lower)^256 * m0^10 > (6 * mult)^256 * both^123`. -/
def checkEqualKBox (mult m0 : Nat) (b : TailBox) : Bool :=
  let eps : QPos := ⟨1, 2048⟩
  let eps2 : QPos := ⟨1, 1024⟩
  let third : QPos := ⟨1, 3⟩
  let one : QPos := ⟨1, 1⟩
  let loTerm1 := qMul ⟨b.k - b.n, b.k⟩ (qAdd one b.yhi)
  let loTerm2 := qMul ⟨9, 4⟩ b.yhi
  if loTerm1.num * loTerm2.den ≤ loTerm2.num * loTerm1.den then false
  else
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
    let ok1 := Nat.blt
      ((3 * mult) ^ 256 * single.num ^ 123 * lower.den ^ 256)
      ((5 * lower.num) ^ 256 * m0 ^ 10 * single.den ^ 123)
    let ok2 := Nat.blt
      ((6 * mult) ^ 256 * both.num ^ 123 * lower.den ^ 256)
      ((5 * lower.num) ^ 256 * m0 ^ 10 * both.den ^ 123)
    ok1 && ok2

/-- Exact `17` rational tail boxes for equal-block `k = 3` (`mult = 2`, `M ≥ 2^36`)
from `cert/witnesses/two_cycle_closure.json`. -/
def equalK3Boxes17 : List TailBox := [
  ⟨0, 3, 7, ⟨513, 5120⟩, ⟨513, 2560⟩, ⟨513, 5120⟩, ⟨513, 2560⟩⟩,
  ⟨0, 3, 7, ⟨513, 10240⟩, ⟨513, 5120⟩, ⟨1539, 10240⟩, ⟨513, 2560⟩⟩,
  ⟨0, 3, 7, ⟨513, 10240⟩, ⟨513, 5120⟩, ⟨513, 5120⟩, ⟨1539, 10240⟩⟩,
  ⟨0, 3, 7, ⟨513, 20480⟩, ⟨513, 10240⟩, ⟨3591, 20480⟩, ⟨513, 2560⟩⟩,
  ⟨0, 3, 7, ⟨513, 20480⟩, ⟨513, 10240⟩, ⟨1539, 10240⟩, ⟨3591, 20480⟩⟩,
  ⟨0, 3, 7, ⟨0, 1⟩, ⟨513, 20480⟩, ⟨1539, 10240⟩, ⟨513, 2560⟩⟩,
  ⟨0, 3, 7, ⟨0, 1⟩, ⟨513, 10240⟩, ⟨513, 5120⟩, ⟨1539, 10240⟩⟩,
  ⟨0, 3, 7, ⟨0, 1⟩, ⟨513, 5120⟩, ⟨0, 1⟩, ⟨513, 5120⟩⟩,
  ⟨1, 1, 3, ⟨0, 1⟩, ⟨1025, 4096⟩, ⟨1, 5⟩, ⟨1025, 4096⟩⟩,
  ⟨2, 3, 11, ⟨15, 62⟩, ⟨10, 31⟩, ⟨1, 4⟩, ⟨10, 31⟩⟩,
  ⟨2, 3, 11, ⟨25, 124⟩, ⟨15, 62⟩, ⟨1, 4⟩, ⟨10, 31⟩⟩,
  ⟨2, 3, 11, ⟨45, 248⟩, ⟨25, 124⟩, ⟨71, 248⟩, ⟨10, 31⟩⟩,
  ⟨2, 3, 11, ⟨5, 31⟩, ⟨45, 248⟩, ⟨71, 248⟩, ⟨10, 31⟩⟩,
  ⟨2, 3, 11, ⟨5, 31⟩, ⟨25, 124⟩, ⟨1, 4⟩, ⟨71, 248⟩⟩,
  ⟨2, 3, 11, ⟨0, 1⟩, ⟨5, 31⟩, ⟨1, 4⟩, ⟨10, 31⟩⟩,
  ⟨3, 6, 23, ⟨1, 6⟩, ⟨1, 3⟩, ⟨10, 31⟩, ⟨1, 3⟩⟩,
  ⟨3, 6, 23, ⟨0, 1⟩, ⟨1, 6⟩, ⟨10, 31⟩, ⟨1, 3⟩⟩
]

/-- Exact `17` rational tail boxes for equal-block `k = 4` (`mult = 3`, `M ≥ 2^51`)
from `cert/witnesses/two_cycle_closure.json`. -/
def equalK4Boxes17 : List TailBox := [
  ⟨0, 3, 7, ⟨513, 5120⟩, ⟨513, 2560⟩, ⟨513, 5120⟩, ⟨513, 2560⟩⟩,
  ⟨0, 3, 7, ⟨513, 10240⟩, ⟨513, 5120⟩, ⟨1539, 10240⟩, ⟨513, 2560⟩⟩,
  ⟨0, 3, 7, ⟨513, 10240⟩, ⟨513, 5120⟩, ⟨513, 5120⟩, ⟨1539, 10240⟩⟩,
  ⟨0, 3, 7, ⟨513, 20480⟩, ⟨513, 10240⟩, ⟨3591, 20480⟩, ⟨513, 2560⟩⟩,
  ⟨0, 3, 7, ⟨513, 20480⟩, ⟨513, 10240⟩, ⟨1539, 10240⟩, ⟨3591, 20480⟩⟩,
  ⟨0, 3, 7, ⟨0, 1⟩, ⟨513, 20480⟩, ⟨1539, 10240⟩, ⟨513, 2560⟩⟩,
  ⟨0, 3, 7, ⟨0, 1⟩, ⟨513, 10240⟩, ⟨513, 5120⟩, ⟨1539, 10240⟩⟩,
  ⟨0, 3, 7, ⟨0, 1⟩, ⟨513, 5120⟩, ⟨0, 1⟩, ⟨513, 5120⟩⟩,
  ⟨1, 1, 3, ⟨0, 1⟩, ⟨1025, 4096⟩, ⟨1, 5⟩, ⟨1025, 4096⟩⟩,
  ⟨2, 3, 11, ⟨15, 62⟩, ⟨10, 31⟩, ⟨1, 4⟩, ⟨10, 31⟩⟩,
  ⟨2, 3, 11, ⟨25, 124⟩, ⟨15, 62⟩, ⟨1, 4⟩, ⟨10, 31⟩⟩,
  ⟨2, 3, 11, ⟨45, 248⟩, ⟨25, 124⟩, ⟨71, 248⟩, ⟨10, 31⟩⟩,
  ⟨2, 3, 11, ⟨5, 31⟩, ⟨45, 248⟩, ⟨71, 248⟩, ⟨10, 31⟩⟩,
  ⟨2, 3, 11, ⟨5, 31⟩, ⟨25, 124⟩, ⟨1, 4⟩, ⟨71, 248⟩⟩,
  ⟨2, 3, 11, ⟨0, 1⟩, ⟨5, 31⟩, ⟨1, 4⟩, ⟨10, 31⟩⟩,
  ⟨3, 6, 23, ⟨1, 6⟩, ⟨1, 3⟩, ⟨10, 31⟩, ⟨1, 3⟩⟩,
  ⟨3, 6, 23, ⟨0, 1⟩, ⟨1, 6⟩, ⟨10, 31⟩, ⟨1, 3⟩⟩
]

/-- Exact `16` rational tail boxes for equal-block `k = 5` (`mult = 4`, `M ≥ 2^62`)
from `cert/witnesses/two_cycle_closure.json`. -/
def equalK5Boxes16 : List TailBox := [
  ⟨0, 3, 7, ⟨513, 5120⟩, ⟨513, 2560⟩, ⟨513, 5120⟩, ⟨513, 2560⟩⟩,
  ⟨0, 3, 7, ⟨513, 10240⟩, ⟨513, 5120⟩, ⟨1539, 10240⟩, ⟨513, 2560⟩⟩,
  ⟨0, 3, 7, ⟨513, 10240⟩, ⟨513, 5120⟩, ⟨513, 5120⟩, ⟨1539, 10240⟩⟩,
  ⟨0, 3, 7, ⟨513, 20480⟩, ⟨513, 10240⟩, ⟨1539, 10240⟩, ⟨513, 2560⟩⟩,
  ⟨0, 3, 7, ⟨0, 1⟩, ⟨513, 20480⟩, ⟨1539, 10240⟩, ⟨513, 2560⟩⟩,
  ⟨0, 3, 7, ⟨0, 1⟩, ⟨513, 10240⟩, ⟨513, 5120⟩, ⟨1539, 10240⟩⟩,
  ⟨0, 3, 7, ⟨0, 1⟩, ⟨513, 5120⟩, ⟨0, 1⟩, ⟨513, 5120⟩⟩,
  ⟨1, 1, 3, ⟨0, 1⟩, ⟨1025, 4096⟩, ⟨1, 5⟩, ⟨1025, 4096⟩⟩,
  ⟨2, 3, 11, ⟨15, 62⟩, ⟨10, 31⟩, ⟨1, 4⟩, ⟨10, 31⟩⟩,
  ⟨2, 3, 11, ⟨25, 124⟩, ⟨15, 62⟩, ⟨1, 4⟩, ⟨10, 31⟩⟩,
  ⟨2, 3, 11, ⟨45, 248⟩, ⟨25, 124⟩, ⟨71, 248⟩, ⟨10, 31⟩⟩,
  ⟨2, 3, 11, ⟨5, 31⟩, ⟨45, 248⟩, ⟨71, 248⟩, ⟨10, 31⟩⟩,
  ⟨2, 3, 11, ⟨5, 31⟩, ⟨25, 124⟩, ⟨1, 4⟩, ⟨71, 248⟩⟩,
  ⟨2, 3, 11, ⟨0, 1⟩, ⟨5, 31⟩, ⟨1, 4⟩, ⟨10, 31⟩⟩,
  ⟨3, 6, 23, ⟨1, 6⟩, ⟨1, 3⟩, ⟨10, 31⟩, ⟨1, 3⟩⟩,
  ⟨3, 6, 23, ⟨0, 1⟩, ⟨1, 6⟩, ⟨10, 31⟩, ⟨1, 3⟩⟩
]

theorem equalK3Boxes17_certified_bool : equalK3Boxes17.all (checkEqualKBox 2 (2 ^ 36)) = true := by decide
theorem equalK4Boxes17_certified_bool : equalK4Boxes17.all (checkEqualKBox 3 (2 ^ 51)) = true := by decide
theorem equalK5Boxes16_certified_bool : equalK5Boxes16.all (checkEqualKBox 4 (2 ^ 62)) = true := by decide

end ClawFreeEG.PolyKData
