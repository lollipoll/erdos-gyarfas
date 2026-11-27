/-!
# ClawFreeEG.TwoCycleData

Zero-`Std` (pure `Init`) proof-carrying box-tree data module for `ClawFreeEG.TwoCycleClosure`:
- Exact recursive integer box-subdivision trees `IBoxTree` covering:
  - ALL `38,330` Fourfold (`M2 = 4*M1`) pairs for `M1 ∈ {32, 64, 128, 256}` (`46` leaves total,
    distributed `19 + 11 + 9 + 7`),
  - ALL `76,492` Equal-Block (`M2 = M1`) medium pairs for `M ∈ {256, 512, 1024}` (`61` leaves total,
    distributed `22 + 23 + 16`).
- Exact `16` Rational Tail Boxes (`M ≥ 2048`) from `cert/witnesses/two_cycle_closure.json`,
  with kernel-verified exact `Nat` 1-class and 2-class inequalities.
- Two independent representations: Lean verifies these `46`-leaf and `61`-leaf integer box trees,
  while `cert/verify_clawfree_eg.py` independently enumerates every individual integer pair.

Omits `import Std` to keep peak RSS low during compilation.
-/

namespace ClawFreeEG.TwoCycleData

/-- Recursive integer rectangle subdivision tree on `[xlo, xhi] × [ylo, yhi]`. -/
inductive IBoxTree where
  | empty
  | leaf (xlo xhi ylo yhi : Nat)
  | splitX (mid : Nat) (left right : IBoxTree)
  | splitY (mid : Nat) (lo hi : IBoxTree)

/-- Exact count of `.leaf` constructors in an `IBoxTree`. -/
def IBoxTree.leafCount : IBoxTree → Nat
  | .empty => 0
  | .leaf _ _ _ _ => 1
  | .splitX _ l r => l.leafCount + r.leafCount
  | .splitY _ l r => l.leafCount + r.leafCount

/-- Exact rational number `num / den` (`den > 0`). -/
structure QPos where
  num : Nat
  den : Nat

/-- Exact rational tail box from `cert/witnesses/two_cycle_closure.json`. -/
structure TailBox where
  regime : Nat
  n : Nat
  k : Nat
  xlo : QPos
  xhi : QPos
  ylo : QPos
  yhi : QPos

/-- The exact `16` rational tail boxes covering ALL `M ≥ 2048` across all 4 R5 regimes. -/
def equalTailBoxes16 : List TailBox := [
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

/-- Exact algebraic lower bound on `r5AttachLower M (y - M)` for all `y ≤ yhi` in regime `(n, k)`:
`4*k * (y - ⌊9*(y-M-1)/4⌋ - ⌊n*y/k⌋) ≥ 9*k*(M+1) - (5*k + 4*n)*yhi`. -/
@[inline] def algLower (M n k yhi : Nat) : Nat :=
  let lhs := 9 * k * (M + 1)
  let rhs := (5 * k + 4 * n) * yhi
  if lhs ≤ rhs then 0 else (lhs - rhs) / (4 * k)

/-- Check one Fourfold (`M2 = 4*M1`) integer leaf box `[xlo, xhi] × [ylo, yhi]`. -/
def checkFourfoldLeaf (M1 n k xlo xhi ylo yhi : Nat) : Bool :=
  let M2 := 4 * M1
  let cap2 := (4 * M2) / 3
  let lo :=
    if ylo == yhi then yhi - (9 * (yhi - M2 - 1)) / 4 - (n * yhi) / k
    else algLower M2 n k yhi
  if Nat.blt xhi lo then true
  else
    let lhsSep := xlo + ylo + 2
    if Nat.ble lhsSep cap2 then false
    else
      let sep := lhsSep - cap2
      let sepMax := xhi + yhi + 2 - cap2
      let ok1 :=
        if Nat.ble sep xhi then Nat.blt ((2 * xhi * yhi) / (sep * sep)) lo
        else true
      let ok2 :=
        if Nat.ble sepMax xlo then true
        else
          let d2 := if Nat.blt xhi sep then 2 * sep - xhi else max (xlo + 2) (2 * sep - xhi)
          Nat.blt ((2 * yhi) / d2) lo
      ok1 && ok2

/-- Check a Fourfold `IBoxTree` covers `[xlo, xhi] × [ylo, yhi]` and every leaf passes. -/
def checkFourfoldTree (M1 n k : Nat) : Nat → Nat → Nat → Nat → IBoxTree → Bool
  | _, _, _, _, .empty => false
  | xlo, xhi, ylo, yhi, .leaf lxlo lxhi lylo lyhi =>
    (lxlo == xlo) && (lxhi == xhi) && (lylo == ylo) && (lyhi == yhi) &&
    checkFourfoldLeaf M1 n k xlo xhi ylo yhi
  | xlo, xhi, ylo, yhi, .splitX mid L R =>
    Nat.ble xlo mid && Nat.blt mid xhi &&
    checkFourfoldTree M1 n k xlo mid ylo yhi L &&
    checkFourfoldTree M1 n k (mid + 1) xhi ylo yhi R
  | xlo, xhi, ylo, yhi, .splitY mid L R =>
    Nat.ble ylo mid && Nat.blt mid yhi &&
    checkFourfoldTree M1 n k xlo xhi ylo mid L &&
    checkFourfoldTree M1 n k xlo xhi (mid + 1) yhi R

/-- Check one Equal-Block medium (`M ∈ {256, 512, 1024}`) leaf box `[xlo, xhi] × [ylo, yhi]`. -/
def checkEqualMedLeaf (M n k xlo xhi ylo yhi : Nat) : Bool :=
  let cap := (4 * M) / 3
  if cap < xlo + 2 then true
  else
    let lo :=
      if xlo == xhi && ylo == yhi then
        let loEx := yhi - (9 * (yhi - M - 1)) / 4 - (n * yhi) / k
        loEx + (if loEx ≥ xlo then (loEx - xlo) % 2 else (xlo - loEx) % 2)
      else if ylo == yhi then
        yhi - (9 * (yhi - M - 1)) / 4 - (n * yhi) / k
      else
        algLower M n k yhi
    if lo == 0 then false
    else
      let width := xhi + yhi + 1 - 2 * M
      let imb := cap - xlo - 2
      let p1 := (min width (3 * imb) + 2) * (min width (3 * imb) + 2)
      let p2 := (width + 2) * (min width (2 * imb) + 2)
      let P := max p1 p2
      let ok1 := Nat.blt (3 ^ 256 * P ^ 123) ((5 * lo) ^ 256)
      let ok2 :=
        if 2 * cap < xlo + ylo + 4 then true
        else
          let twoR := min (2 * width) (2 * cap - xlo - ylo - 4)
          Nat.blt (6 ^ 256 * (twoR + 4) ^ 246) ((5 * lo) ^ 256 * 2 ^ 246)
      ok1 && ok2

/-- Check an Equal-Block medium `IBoxTree` covers `{(x, y) ∈ [xlo, xhi] × [ylo, yhi] | x ≤ y}`
and every leaf passes. -/
def checkEqualMedTree (M n k : Nat) : Nat → Nat → Nat → Nat → IBoxTree → Bool
  | xlo, _, _, yhi, .empty => Nat.blt yhi xlo
  | xlo, xhi, ylo, yhi, .leaf lxlo lxhi lylo lyhi =>
    let xhiC := min xhi yhi
    let yloC := max ylo xlo
    (lxlo == xlo) && (lxhi == xhiC) && (lylo == yloC) && (lyhi == yhi) &&
    checkEqualMedLeaf M n k xlo xhiC yloC yhi
  | xlo, xhi, ylo, yhi, .splitX mid L R =>
    let xhiC := min xhi yhi
    let yloC := max ylo xlo
    Nat.ble xlo mid && Nat.blt mid xhiC &&
    checkEqualMedTree M n k xlo mid yloC yhi L &&
    checkEqualMedTree M n k (mid + 1) xhiC yloC yhi R
  | xlo, xhi, ylo, yhi, .splitY mid L R =>
    let xhiC := min xhi yhi
    let yloC := max ylo xlo
    Nat.ble yloC mid && Nat.blt mid yhi &&
    checkEqualMedTree M n k xlo xhiC yloC mid L &&
    checkEqualMedTree M n k xlo xhiC (mid + 1) yhi R

def fourfoldTree_32_r0 : IBoxTree :=
  (.splitY 141 (.leaf 33 42 129 141) (.splitY 148 (.splitX 37 (.leaf 33 37 142 148) (.splitY 145 (.leaf 38 42 142 145) (.splitX 40 (.leaf 38 40 146 148) (.leaf 41 42 146 148)))) (.splitX 37 (.splitY 151 (.splitX 35 (.leaf 33 35 149 151) (.splitY 150 (.leaf 36 37 149 150) (.leaf 36 37 151 151))) (.splitX 35 (.splitX 34 (.splitY 153 (.splitX 33 (.splitY 152 (.leaf 33 33 152 152) (.leaf 33 33 153 153)) (.leaf 34 34 152 153)) (.leaf 33 34 154 154)) (.leaf 35 35 152 154)) (.leaf 36 37 152 154))) (.splitY 151 (.leaf 38 42 149 151) (.leaf 38 42 152 154)))))

def fourfoldTree_32_r1 : IBoxTree :=
  (.leaf 33 42 155 160)

def fourfoldTree_32_r2 : IBoxTree :=
  (.leaf 33 42 161 169)

def fourfoldTree_32_r3 : IBoxTree :=
  (.leaf 33 42 170 170)

theorem fourfold_trees_32_ok : (checkFourfoldTree 32 3 7 33 42 129 154 fourfoldTree_32_r0 && checkFourfoldTree 32 1 3 33 42 155 160 fourfoldTree_32_r1 && checkFourfoldTree 32 3 11 33 42 161 169 fourfoldTree_32_r2 && checkFourfoldTree 32 6 23 33 42 170 170 fourfoldTree_32_r3) = true := by decide

def fourfoldTree_64_r0 : IBoxTree :=
  (.splitY 282 (.leaf 65 85 257 282) (.splitY 295 (.splitX 75 (.leaf 65 75 283 295) (.splitY 289 (.leaf 76 85 283 289) (.leaf 76 85 290 295))) (.splitX 75 (.splitY 302 (.splitX 70 (.leaf 65 70 296 302) (.leaf 71 75 296 302)) (.leaf 65 75 303 308)) (.leaf 76 85 296 308))))

def fourfoldTree_64_r1 : IBoxTree :=
  (.leaf 65 85 309 320)

def fourfoldTree_64_r2 : IBoxTree :=
  (.leaf 65 85 321 338)

def fourfoldTree_64_r3 : IBoxTree :=
  (.leaf 65 85 339 341)

theorem fourfold_trees_64_ok : (checkFourfoldTree 64 3 7 65 85 257 308 fourfoldTree_64_r0 && checkFourfoldTree 64 1 3 65 85 309 320 fourfoldTree_64_r1 && checkFourfoldTree 64 3 11 65 85 321 338 fourfoldTree_64_r2 && checkFourfoldTree 64 6 23 65 85 339 341 fourfoldTree_64_r3) = true := by decide

def fourfoldTree_128_r0 : IBoxTree :=
  (.splitY 564 (.leaf 129 170 513 564) (.splitY 590 (.splitX 149 (.leaf 129 149 565 590) (.splitY 577 (.leaf 150 170 565 577) (.leaf 150 170 578 590))) (.splitX 149 (.leaf 129 149 591 615) (.leaf 150 170 591 615))))

def fourfoldTree_128_r1 : IBoxTree :=
  (.leaf 129 170 616 640)

def fourfoldTree_128_r2 : IBoxTree :=
  (.leaf 129 170 641 677)

def fourfoldTree_128_r3 : IBoxTree :=
  (.leaf 129 170 678 682)

theorem fourfold_trees_128_ok : (checkFourfoldTree 128 3 7 129 170 513 615 fourfoldTree_128_r0 && checkFourfoldTree 128 1 3 129 170 616 640 fourfoldTree_128_r1 && checkFourfoldTree 128 3 11 129 170 641 677 fourfoldTree_128_r2 && checkFourfoldTree 128 6 23 129 170 678 682 fourfoldTree_128_r3) = true := by decide

def fourfoldTree_256_r0 : IBoxTree :=
  (.splitY 1127 (.leaf 257 341 1025 1127) (.splitY 1178 (.splitX 299 (.leaf 257 299 1128 1178) (.leaf 300 341 1128 1178)) (.leaf 257 341 1179 1229)))

def fourfoldTree_256_r1 : IBoxTree :=
  (.leaf 257 341 1230 1280)

def fourfoldTree_256_r2 : IBoxTree :=
  (.leaf 257 341 1281 1354)

def fourfoldTree_256_r3 : IBoxTree :=
  (.leaf 257 341 1355 1365)

theorem fourfold_trees_256_ok : (checkFourfoldTree 256 3 7 257 341 1025 1229 fourfoldTree_256_r0 && checkFourfoldTree 256 1 3 257 341 1230 1280 fourfoldTree_256_r1 && checkFourfoldTree 256 3 11 257 341 1281 1354 fourfoldTree_256_r2 && checkFourfoldTree 256 6 23 257 341 1355 1365 fourfoldTree_256_r3) = true := by decide

def equalMedTree_256_r0 : IBoxTree :=
  (.splitX 282 (.splitY 282 (.leaf 257 282 257 282) (.splitX 269 (.splitY 295 (.leaf 257 269 283 295) (.splitX 263 (.splitY 302 (.leaf 257 263 296 302) (.splitX 260 (.leaf 257 260 303 308) (.leaf 261 263 303 308))) (.splitY 302 (.leaf 264 269 296 302) (.leaf 264 269 303 308)))) (.splitY 295 (.leaf 270 282 283 295) (.leaf 270 282 296 308)))) (.leaf 283 308 283 308))

def equalMedTree_256_r1 : IBoxTree :=
  (.leaf 257 320 309 320)

def equalMedTree_256_r2 : IBoxTree :=
  (.splitX 297 (.leaf 257 297 321 338) (.leaf 298 338 321 338))

def equalMedTree_256_r3 : IBoxTree :=
  (.splitX 299 (.splitX 278 (.leaf 257 278 339 341) (.splitX 289 (.leaf 279 289 339 341) (.splitX 294 (.leaf 290 294 339 341) (.splitX 297 (.splitX 296 (.splitY 340 (.leaf 295 296 339 340) (.leaf 295 296 341 341)) (.splitY 340 (.leaf 297 297 339 340) (.leaf 297 297 341 341))) (.leaf 298 299 339 341))))) (.leaf 300 341 339 341))

theorem equalMed_trees_256_ok : (checkEqualMedTree 256 3 7 257 308 257 308 equalMedTree_256_r0 && checkEqualMedTree 256 1 3 257 320 309 320 equalMedTree_256_r1 && checkEqualMedTree 256 3 11 257 338 321 338 equalMedTree_256_r2 && checkEqualMedTree 256 6 23 257 341 339 341 equalMedTree_256_r3) = true := by decide

def equalMedTree_512_r0 : IBoxTree :=
  (.splitX 564 (.splitY 564 (.leaf 513 564 513 564) (.splitX 538 (.splitY 590 (.leaf 513 538 565 590) (.splitX 525 (.leaf 513 525 591 615) (.splitY 603 (.leaf 526 538 591 603) (.leaf 526 538 604 615)))) (.splitY 590 (.leaf 539 564 565 590) (.leaf 539 564 591 615)))) (.leaf 565 615 565 615))

def equalMedTree_512_r1 : IBoxTree :=
  (.leaf 513 640 616 640)

def equalMedTree_512_r2 : IBoxTree :=
  (.splitX 595 (.leaf 513 595 641 677) (.leaf 596 677 641 677))

def equalMedTree_512_r3 : IBoxTree :=
  (.splitX 597 (.splitX 555 (.leaf 513 555 678 682) (.splitX 576 (.leaf 556 576 678 682) (.splitX 587 (.leaf 577 587 678 682) (.splitX 592 (.leaf 588 592 678 682) (.splitX 595 (.splitY 680 (.leaf 593 595 678 680) (.splitX 594 (.splitX 593 (.leaf 593 593 681 682) (.splitY 681 (.leaf 594 594 681 681) (.leaf 594 594 682 682))) (.splitY 681 (.leaf 595 595 681 681) (.leaf 595 595 682 682)))) (.leaf 596 597 678 682)))))) (.leaf 598 682 678 682))

theorem equalMed_trees_512_ok : (checkEqualMedTree 512 3 7 513 615 513 615 equalMedTree_512_r0 && checkEqualMedTree 512 1 3 513 640 616 640 equalMedTree_512_r1 && checkEqualMedTree 512 3 11 513 677 641 677 equalMedTree_512_r2 && checkEqualMedTree 512 6 23 513 682 678 682 equalMedTree_512_r3) = true := by decide

def equalMedTree_1024_r0 : IBoxTree :=
  (.splitX 1127 (.splitY 1127 (.leaf 1025 1127 1025 1127) (.splitX 1076 (.splitY 1178 (.leaf 1025 1076 1128 1178) (.splitX 1050 (.leaf 1025 1050 1179 1229) (.leaf 1051 1076 1179 1229))) (.splitY 1178 (.leaf 1077 1127 1128 1178) (.leaf 1077 1127 1179 1229)))) (.leaf 1128 1229 1128 1229))

def equalMedTree_1024_r1 : IBoxTree :=
  (.leaf 1025 1280 1230 1280)

def equalMedTree_1024_r2 : IBoxTree :=
  (.splitX 1189 (.leaf 1025 1189 1281 1354) (.splitX 1272 (.splitX 1231 (.splitY 1317 (.leaf 1190 1231 1281 1317) (.splitX 1210 (.leaf 1190 1210 1318 1354) (.leaf 1211 1231 1318 1354))) (.leaf 1232 1272 1281 1354)) (.leaf 1273 1354 1281 1354)))

def equalMedTree_1024_r3 : IBoxTree :=
  (.splitX 1195 (.leaf 1025 1195 1355 1365) (.leaf 1196 1365 1355 1365))

theorem equalMed_trees_1024_ok : (checkEqualMedTree 1024 3 7 1025 1229 1025 1229 equalMedTree_1024_r0 && checkEqualMedTree 1024 1 3 1025 1280 1230 1280 equalMedTree_1024_r1 && checkEqualMedTree 1024 3 11 1025 1354 1281 1354 equalMedTree_1024_r2 && checkEqualMedTree 1024 6 23 1025 1365 1355 1365 equalMedTree_1024_r3) = true := by decide

/-- Exact kernel-checked leaf count of the 16 Fourfold `IBoxTree` roots: `19 + 11 + 9 + 7 = 46`. -/
theorem fourfoldTrees_leaf_count :
    fourfoldTree_32_r0.leafCount + fourfoldTree_32_r1.leafCount + fourfoldTree_32_r2.leafCount + fourfoldTree_32_r3.leafCount = 19 ∧
    fourfoldTree_64_r0.leafCount + fourfoldTree_64_r1.leafCount + fourfoldTree_64_r2.leafCount + fourfoldTree_64_r3.leafCount = 11 ∧
    fourfoldTree_128_r0.leafCount + fourfoldTree_128_r1.leafCount + fourfoldTree_128_r2.leafCount + fourfoldTree_128_r3.leafCount = 9 ∧
    fourfoldTree_256_r0.leafCount + fourfoldTree_256_r1.leafCount + fourfoldTree_256_r2.leafCount + fourfoldTree_256_r3.leafCount = 7 ∧
    (fourfoldTree_32_r0.leafCount + fourfoldTree_32_r1.leafCount + fourfoldTree_32_r2.leafCount + fourfoldTree_32_r3.leafCount) +
    (fourfoldTree_64_r0.leafCount + fourfoldTree_64_r1.leafCount + fourfoldTree_64_r2.leafCount + fourfoldTree_64_r3.leafCount) +
    (fourfoldTree_128_r0.leafCount + fourfoldTree_128_r1.leafCount + fourfoldTree_128_r2.leafCount + fourfoldTree_128_r3.leafCount) +
    (fourfoldTree_256_r0.leafCount + fourfoldTree_256_r1.leafCount + fourfoldTree_256_r2.leafCount + fourfoldTree_256_r3.leafCount) = 46 := by
  decide

/-- Exact kernel-checked leaf count of the 12 Equal-Block medium `IBoxTree` roots: `22 + 23 + 16 = 61`. -/
theorem equalMedTrees_leaf_count :
    equalMedTree_256_r0.leafCount + equalMedTree_256_r1.leafCount + equalMedTree_256_r2.leafCount + equalMedTree_256_r3.leafCount = 22 ∧
    equalMedTree_512_r0.leafCount + equalMedTree_512_r1.leafCount + equalMedTree_512_r2.leafCount + equalMedTree_512_r3.leafCount = 23 ∧
    equalMedTree_1024_r0.leafCount + equalMedTree_1024_r1.leafCount + equalMedTree_1024_r2.leafCount + equalMedTree_1024_r3.leafCount = 16 ∧
    (equalMedTree_256_r0.leafCount + equalMedTree_256_r1.leafCount + equalMedTree_256_r2.leafCount + equalMedTree_256_r3.leafCount) +
    (equalMedTree_512_r0.leafCount + equalMedTree_512_r1.leafCount + equalMedTree_512_r2.leafCount + equalMedTree_512_r3.leafCount) +
    (equalMedTree_1024_r0.leafCount + equalMedTree_1024_r1.leafCount + equalMedTree_1024_r2.leafCount + equalMedTree_1024_r3.leafCount) = 61 := by
  decide

/-- Exact rational addition `a + b` on `QPos`. -/
@[inline] def qAdd (a b : QPos) : QPos :=
  let n := a.num * b.den + b.num * a.den
  let d := a.den * b.den
  let g := Nat.gcd n d
  ⟨n / g, d / g⟩

/-- Exact rational subtraction `a - b` (clamped at 0 if `a ≤ b`) on `QPos`. -/
@[inline] def qSub (a b : QPos) : QPos :=
  if a.num * b.den ≤ b.num * a.den then ⟨0, 1⟩
  else
    let n := a.num * b.den - b.num * a.den
    let d := a.den * b.den
    let g := Nat.gcd n d
    ⟨n / g, d / g⟩

/-- Exact rational multiplication `a * b` on `QPos`. -/
@[inline] def qMul (a b : QPos) : QPos :=
  let n := a.num * b.num
  let d := a.den * b.den
  let g := Nat.gcd n d
  ⟨n / g, d / g⟩

/-- Exact rational minimum `min a b` on `QPos`. -/
@[inline] def qMin (a b : QPos) : QPos :=
  if a.num * b.den ≤ b.num * a.den then a else b

/-- Exact rational maximum `max a b` on `QPos`. -/
@[inline] def qMax (a b : QPos) : QPos :=
  if a.num * b.den ≤ b.num * a.den then b else a

/-- Exact `Nat` strict comparison `a > b` on `QPos` raised to `256`th / `123`rd powers:
checks `(5 * lower)^256 * 2048^10 > 3^256 * single^123` AND
`(5 * lower)^256 * 2048^10 > 6^256 * both^123` for one `TailBox`. -/
def checkTailBox (b : TailBox) : Bool :=
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
      (3 ^ 256 * single.num ^ 123 * lower.den ^ 256)
      ((5 * lower.num) ^ 256 * 2048 ^ 10 * single.den ^ 123)
    let ok2 := Nat.blt
      (6 ^ 256 * both.num ^ 123 * lower.den ^ 256)
      ((5 * lower.num) ^ 256 * 2048 ^ 10 * both.den ^ 123)
    ok1 && ok2

theorem equalTailBoxes16_certified_bool : equalTailBoxes16.all checkTailBox = true := by decide

end ClawFreeEG.TwoCycleData
