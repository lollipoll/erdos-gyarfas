/-!
# ClawFreeEG.DyadicPackingData

Zero-`Std` (pure `Init`) base data module for `ClawFreeEG.DyadicPacking2D` and
`ClawFreeEG.TwoCycleClosure`:
- Balanced LSB-routed binary lookup tree `NTree` for `O(log N)` pure-`Nat` lookup.
- Base `F19` packing table (`210` lower-triangular stored numeric entries for `0 ≤ w2 ≤ w1 ≤ 19`,
  with symmetric `20 × 20` extension and `F19[19, 19] = 8`): Lean kernel-checks the stored
  numeric entries, monotonicity, and packing-bound inequalities, while `cert/verify_clawfree_eg.py`
  computes the exact finite maxima over the same-parity, no-diagonal `|u1 - u2| ≠ |v1 - v2|`
  2D `L_∞`-packing domain via clique search.
- Precomputed `65`-anchor (`c_j = (64 + j) / 64`, `j = 0..64`) and `32`-octave (`2^(-k)`,
  `k = 0..31`) exact `123/256`-power bounds at scale `S2 = 10^9`, kernel-certified via
  pure GMP `Nat` `256`-th power inequalities.
- Fast pure-`Nat` AM-GM power enclosure operators (`pupFast`, `ploFast`, `pupE`,
  `holderPairE`, `effAE`).

Omits `import Std` to save ~260 MiB RSS during compilation.
-/

namespace ClawFreeEG.DyadicPackingData

/-- Balanced LSB-routed binary lookup tree for fast `O(log N)` pure-`Nat` kernel reduction. -/
inductive NTree where
  | l (v : Nat)
  | n (even odd : NTree)

def NTree.get : NTree → Nat → Nat
  | .l v, _ => v
  | .n a b, idx =>
    if idx % 2 == 0 then NTree.get a (idx / 2) else NTree.get b (idx / 2)

abbrev S2 : Nat := 1000000000
abbrev ANCHOR_N : Nat := 64
abbrev SCALE_DATA : Nat := 100000

@[inline] def natMin (a b : Nat) : Nat := if Nat.ble a b then a else b
@[inline] def natMax (a b : Nat) : Nat := if Nat.ble a b then b else a

def f19Tree : NTree :=
  (.n (.n (.n (.n (.n (.n (.n (.n (.n (.l 1) (.l 6)) (.n (.l 3) (.l 4))) (.n (.n (.l 2) (.l 3)) (.n (.l 4) (.l 8)))) (.n (.n (.n (.l 2) (.l 4)) (.n (.l 2) (.l 8))) (.n (.n (.l 4) (.l 6)) (.n (.l 3) (.l 8))))) (.n (.n (.n (.n (.l 3) (.l 4)) (.n (.l 2) (.l 8))) (.n (.n (.l 1) (.l 6)) (.n (.l 4) (.l 8)))) (.n (.n (.n (.l 2) (.l 4)) (.n (.l 5) (.l 8))) (.n (.n (.l 3) (.l 5)) (.n (.l 2) (.l 8)))))) (.n (.n (.n (.n (.n (.l 2) (.l 3)) (.n (.l 4) (.l 6))) (.n (.n (.l 3) (.l 5)) (.n (.l 2) (.l 8)))) (.n (.n (.n (.l 1) (.l 6)) (.n (.l 4) (.l 8))) (.n (.n (.l 2) (.l 3)) (.n (.l 4) (.l 8))))) (.n (.n (.n (.n (.l 2) (.l 2)) (.n (.l 3) (.l 8))) (.n (.n (.l 3) (.l 4)) (.n (.l 6) (.l 8)))) (.n (.n (.n (.l 3) (.l 6)) (.n (.l 3) (.l 8))) (.n (.n (.l 1) (.l 7)) (.n (.l 4) (.l 8))))))) (.n (.n (.n (.n (.n (.n (.l 1) (.l 2)) (.n (.l 3) (.l 5))) (.n (.n (.l 3) (.l 4)) (.n (.l 6) (.l 8)))) (.n (.n (.n (.l 3) (.l 4)) (.n (.l 3) (.l 8))) (.n (.n (.l 1) (.l 6)) (.n (.l 4) (.l 8))))) (.n (.n (.n (.n (.l 1) (.l 6)) (.n (.l 3) (.l 8))) (.n (.n (.l 2) (.l 3)) (.n (.l 4) (.l 8)))) (.n (.n (.n (.l 2) (.l 5)) (.n (.l 2) (.l 8))) (.n (.n (.l 4) (.l 6)) (.n (.l 3) (.l 8)))))) (.n (.n (.n (.n (.n (.l 2) (.l 4)) (.n (.l 1) (.l 7))) (.n (.n (.l 4) (.l 6)) (.n (.l 3) (.l 8)))) (.n (.n (.n (.l 2) (.l 2)) (.n (.l 4) (.l 8))) (.n (.n (.l 3) (.l 4)) (.n (.l 6) (.l 8))))) (.n (.n (.n (.n (.l 2) (.l 3)) (.n (.l 4) (.l 8))) (.n (.n (.l 3) (.l 5)) (.n (.l 2) (.l 8)))) (.n (.n (.n (.l 1) (.l 6)) (.n (.l 4) (.l 8))) (.n (.n (.l 2) (.l 3)) (.n (.l 4) (.l 8)))))))) (.n (.n (.n (.n (.n (.n (.n (.l 1) (.l 6)) (.n (.l 3) (.l 4))) (.n (.n (.l 2) (.l 3)) (.n (.l 4) (.l 8)))) (.n (.n (.n (.l 2) (.l 4)) (.n (.l 2) (.l 8))) (.n (.n (.l 4) (.l 6)) (.n (.l 3) (.l 8))))) (.n (.n (.n (.n (.l 3) (.l 4)) (.n (.l 2) (.l 8))) (.n (.n (.l 2) (.l 7)) (.n (.l 4) (.l 8)))) (.n (.n (.n (.l 2) (.l 4)) (.n (.l 5) (.l 8))) (.n (.n (.l 3) (.l 6)) (.n (.l 2) (.l 8)))))) (.n (.n (.n (.n (.n (.l 2) (.l 3)) (.n (.l 4) (.l 6))) (.n (.n (.l 3) (.l 6)) (.n (.l 2) (.l 8)))) (.n (.n (.n (.l 1) (.l 6)) (.n (.l 4) (.l 8))) (.n (.n (.l 2) (.l 3)) (.n (.l 4) (.l 8))))) (.n (.n (.n (.n (.l 2) (.l 2)) (.n (.l 3) (.l 8))) (.n (.n (.l 3) (.l 4)) (.n (.l 6) (.l 8)))) (.n (.n (.n (.l 3) (.l 6)) (.n (.l 3) (.l 8))) (.n (.n (.l 2) (.l 7)) (.n (.l 4) (.l 8))))))) (.n (.n (.n (.n (.n (.n (.l 1) (.l 2)) (.n (.l 3) (.l 6))) (.n (.n (.l 3) (.l 4)) (.n (.l 6) (.l 8)))) (.n (.n (.n (.l 3) (.l 4)) (.n (.l 3) (.l 8))) (.n (.n (.l 2) (.l 7)) (.n (.l 4) (.l 8))))) (.n (.n (.n (.n (.l 1) (.l 6)) (.n (.l 3) (.l 8))) (.n (.n (.l 2) (.l 3)) (.n (.l 4) (.l 8)))) (.n (.n (.n (.l 2) (.l 6)) (.n (.l 2) (.l 8))) (.n (.n (.l 4) (.l 6)) (.n (.l 3) (.l 8)))))) (.n (.n (.n (.n (.n (.l 2) (.l 4)) (.n (.l 2) (.l 8))) (.n (.n (.l 4) (.l 6)) (.n (.l 3) (.l 8)))) (.n (.n (.n (.l 2) (.l 3)) (.n (.l 4) (.l 8))) (.n (.n (.l 3) (.l 4)) (.n (.l 6) (.l 8))))) (.n (.n (.n (.n (.l 2) (.l 3)) (.n (.l 4) (.l 8))) (.n (.n (.l 3) (.l 6)) (.n (.l 2) (.l 8)))) (.n (.n (.n (.l 2) (.l 6)) (.n (.l 4) (.l 8))) (.n (.n (.l 2) (.l 3)) (.n (.l 4) (.l 8))))))))) (.n (.n (.n (.n (.n (.n (.n (.n (.l 1) (.l 6)) (.n (.l 3) (.l 4))) (.n (.n (.l 2) (.l 3)) (.n (.l 4) (.l 8)))) (.n (.n (.n (.l 2) (.l 4)) (.n (.l 2) (.l 8))) (.n (.n (.l 4) (.l 6)) (.n (.l 3) (.l 8))))) (.n (.n (.n (.n (.l 3) (.l 4)) (.n (.l 2) (.l 8))) (.n (.n (.l 2) (.l 6)) (.n (.l 4) (.l 8)))) (.n (.n (.n (.l 2) (.l 4)) (.n (.l 5) (.l 8))) (.n (.n (.l 3) (.l 6)) (.n (.l 2) (.l 8)))))) (.n (.n (.n (.n (.n (.l 2) (.l 3)) (.n (.l 4) (.l 6))) (.n (.n (.l 3) (.l 6)) (.n (.l 2) (.l 8)))) (.n (.n (.n (.l 1) (.l 6)) (.n (.l 4) (.l 8))) (.n (.n (.l 2) (.l 3)) (.n (.l 4) (.l 8))))) (.n (.n (.n (.n (.l 2) (.l 2)) (.n (.l 3) (.l 8))) (.n (.n (.l 3) (.l 4)) (.n (.l 6) (.l 8)))) (.n (.n (.n (.l 3) (.l 6)) (.n (.l 3) (.l 8))) (.n (.n (.l 2) (.l 7)) (.n (.l 4) (.l 8))))))) (.n (.n (.n (.n (.n (.n (.l 1) (.l 2)) (.n (.l 3) (.l 6))) (.n (.n (.l 3) (.l 4)) (.n (.l 6) (.l 8)))) (.n (.n (.n (.l 3) (.l 4)) (.n (.l 3) (.l 8))) (.n (.n (.l 2) (.l 6)) (.n (.l 4) (.l 8))))) (.n (.n (.n (.n (.l 1) (.l 6)) (.n (.l 3) (.l 8))) (.n (.n (.l 2) (.l 3)) (.n (.l 4) (.l 8)))) (.n (.n (.n (.l 2) (.l 6)) (.n (.l 2) (.l 8))) (.n (.n (.l 4) (.l 6)) (.n (.l 3) (.l 8)))))) (.n (.n (.n (.n (.n (.l 2) (.l 4)) (.n (.l 2) (.l 8))) (.n (.n (.l 4) (.l 6)) (.n (.l 3) (.l 8)))) (.n (.n (.n (.l 2) (.l 3)) (.n (.l 4) (.l 8))) (.n (.n (.l 3) (.l 4)) (.n (.l 6) (.l 8))))) (.n (.n (.n (.n (.l 2) (.l 3)) (.n (.l 4) (.l 8))) (.n (.n (.l 3) (.l 6)) (.n (.l 2) (.l 8)))) (.n (.n (.n (.l 2) (.l 6)) (.n (.l 4) (.l 8))) (.n (.n (.l 2) (.l 3)) (.n (.l 4) (.l 8)))))))) (.n (.n (.n (.n (.n (.n (.n (.l 1) (.l 6)) (.n (.l 3) (.l 4))) (.n (.n (.l 2) (.l 4)) (.n (.l 6) (.l 8)))) (.n (.n (.n (.l 3) (.l 4)) (.n (.l 3) (.l 8))) (.n (.n (.l 4) (.l 6)) (.n (.l 3) (.l 8))))) (.n (.n (.n (.n (.l 3) (.l 6)) (.n (.l 2) (.l 8))) (.n (.n (.l 2) (.l 7)) (.n (.l 4) (.l 8)))) (.n (.n (.n (.l 2) (.l 4)) (.n (.l 5) (.l 8))) (.n (.n (.l 4) (.l 6)) (.n (.l 3) (.l 8)))))) (.n (.n (.n (.n (.n (.l 2) (.l 3)) (.n (.l 4) (.l 7))) (.n (.n (.l 4) (.l 6)) (.n (.l 3) (.l 8)))) (.n (.n (.n (.l 2) (.l 6)) (.n (.l 4) (.l 8))) (.n (.n (.l 2) (.l 4)) (.n (.l 6) (.l 8))))) (.n (.n (.n (.n (.l 2) (.l 3)) (.n (.l 4) (.l 8))) (.n (.n (.l 3) (.l 4)) (.n (.l 6) (.l 8)))) (.n (.n (.n (.l 3) (.l 6)) (.n (.l 3) (.l 8))) (.n (.n (.l 2) (.l 8)) (.n (.l 4) (.l 8))))))) (.n (.n (.n (.n (.n (.n (.l 1) (.l 3)) (.n (.l 4) (.l 6))) (.n (.n (.l 3) (.l 4)) (.n (.l 6) (.l 8)))) (.n (.n (.n (.l 3) (.l 6)) (.n (.l 3) (.l 8))) (.n (.n (.l 2) (.l 8)) (.n (.l 4) (.l 8))))) (.n (.n (.n (.n (.l 2) (.l 6)) (.n (.l 3) (.l 8))) (.n (.n (.l 2) (.l 4)) (.n (.l 6) (.l 8)))) (.n (.n (.n (.l 3) (.l 6)) (.n (.l 3) (.l 8))) (.n (.n (.l 4) (.l 6)) (.n (.l 3) (.l 8)))))) (.n (.n (.n (.n (.n (.l 2) (.l 4)) (.n (.l 2) (.l 8))) (.n (.n (.l 4) (.l 6)) (.n (.l 3) (.l 8)))) (.n (.n (.n (.l 2) (.l 4)) (.n (.l 5) (.l 8))) (.n (.n (.l 3) (.l 4)) (.n (.l 6) (.l 8))))) (.n (.n (.n (.n (.l 2) (.l 3)) (.n (.l 4) (.l 8))) (.n (.n (.l 4) (.l 6)) (.n (.l 3) (.l 8)))) (.n (.n (.n (.l 2) (.l 7)) (.n (.l 4) (.l 8))) (.n (.n (.l 2) (.l 4)) (.n (.l 6) (.l 8))))))))))

@[inline] def f19Val (w1 w2 : Nat) : Nat := f19Tree.get (w1 * 20 + w2)

def ancLoTree : NTree :=
  (.n (.n (.n (.n (.n (.n (.n (.l 1000000000) (.l 1395196909)) (.n (.l 1215084125) (.l 1395196909))) (.n (.n (.l 1113171894) (.l 1395196909)) (.n (.l 1308495361) (.l 1395196909)))) (.n (.n (.n (.l 1058222980) (.l 1395196909)) (.n (.l 1262724052) (.l 1395196909))) (.n (.n (.l 1165333213) (.l 1395196909)) (.n (.l 1352597498) (.l 1395196909))))) (.n (.n (.n (.n (.l 1029556612) (.l 1395196909)) (.n (.l 1239151667) (.l 1395196909))) (.n (.n (.l 1139575303) (.l 1395196909)) (.n (.l 1330743995) (.l 1395196909)))) (.n (.n (.n (.l 1086073260) (.l 1395196909)) (.n (.l 1285829945) (.l 1395196909))) (.n (.n (.l 1190489716) (.l 1395196909)) (.n (.l 1374075720) (.l 1395196909)))))) (.n (.n (.n (.n (.n (.l 1014894656) (.l 1395196909)) (.n (.l 1227181696) (.l 1395196909))) (.n (.n (.l 1126457251) (.l 1395196909)) (.n (.l 1319670378) (.l 1395196909)))) (.n (.n (.n (.l 1072245897) (.l 1395196909)) (.n (.l 1274333626) (.l 1395196909))) (.n (.n (.l 1177984080) (.l 1395196909)) (.n (.l 1363382343) (.l 1395196909))))) (.n (.n (.n (.n (.l 1043996191) (.l 1395196909)) (.n (.l 1250997896) (.l 1395196909))) (.n (.n (.l 1152532068) (.l 1395196909)) (.n (.l 1341718857) (.l 1395196909)))) (.n (.n (.n (.l 1099712836) (.l 1395196909)) (.n (.l 1297216181) (.l 1395196909))) (.n (.n (.l 1202854892) (.l 1395196909)) (.n (.l 1384679861) (.l 1395196909))))))) (.n (.n (.n (.n (.n (.n (.l 1007477092) (.l 1395196909)) (.n (.l 1221149110) (.l 1395196909))) (.n (.n (.l 1119835876) (.l 1395196909)) (.n (.l 1314095714) (.l 1395196909)))) (.n (.n (.n (.l 1065259389) (.l 1395196909)) (.n (.l 1268543200) (.l 1395196909))) (.n (.n (.l 1171677109) (.l 1395196909)) (.n (.l 1358001498) (.l 1395196909))))) (.n (.n (.n (.n (.l 1036803583) (.l 1395196909)) (.n (.l 1245090016) (.l 1395196909))) (.n (.n (.l 1146073485) (.l 1395196909)) (.n (.l 1336243609) (.l 1395196909)))) (.n (.n (.n (.l 1092916056) (.l 1395196909)) (.n (.l 1291536631) (.l 1395196909))) (.n (.n (.l 1196689574) (.l 1395196909)) (.n (.l 1379388809) (.l 1395196909)))))) (.n (.n (.n (.n (.n (.l 1022254058) (.l 1395196909)) (.n (.l 1233182386) (.l 1395196909))) (.n (.n (.l 1133036805) (.l 1395196909)) (.n (.l 1325219693) (.l 1395196909)))) (.n (.n (.n (.l 1079183525) (.l 1395196909)) (.n (.l 1280095740) (.l 1395196909))) (.n (.n (.l 1184254747) (.l 1395196909)) (.n (.l 1368740324) (.l 1395196909))))) (.n (.n (.n (.n (.l 1051135612) (.l 1395196909)) (.n (.l 1256875761) (.l 1395196909))) (.n (.n (.l 1158951752) (.l 1395196909)) (.n (.l 1347170051) (.l 1395196909)))) (.n (.n (.n (.l 1106464493) (.l 1395196909)) (.n (.l 1302868969) (.l 1395196909))) (.n (.n (.l 1208986229) (.l 1395196909)) (.n (.l 1389949141) (.l 1395196909))))))))

def ancHiTree : NTree :=
  (.n (.n (.n (.n (.n (.n (.n (.l 1000000000) (.l 1395196910)) (.n (.l 1215084126) (.l 1395196910))) (.n (.n (.l 1113171895) (.l 1395196910)) (.n (.l 1308495362) (.l 1395196910)))) (.n (.n (.n (.l 1058222981) (.l 1395196910)) (.n (.l 1262724053) (.l 1395196910))) (.n (.n (.l 1165333214) (.l 1395196910)) (.n (.l 1352597499) (.l 1395196910))))) (.n (.n (.n (.n (.l 1029556613) (.l 1395196910)) (.n (.l 1239151668) (.l 1395196910))) (.n (.n (.l 1139575304) (.l 1395196910)) (.n (.l 1330743996) (.l 1395196910)))) (.n (.n (.n (.l 1086073261) (.l 1395196910)) (.n (.l 1285829946) (.l 1395196910))) (.n (.n (.l 1190489717) (.l 1395196910)) (.n (.l 1374075721) (.l 1395196910)))))) (.n (.n (.n (.n (.n (.l 1014894657) (.l 1395196910)) (.n (.l 1227181697) (.l 1395196910))) (.n (.n (.l 1126457252) (.l 1395196910)) (.n (.l 1319670379) (.l 1395196910)))) (.n (.n (.n (.l 1072245898) (.l 1395196910)) (.n (.l 1274333627) (.l 1395196910))) (.n (.n (.l 1177984081) (.l 1395196910)) (.n (.l 1363382344) (.l 1395196910))))) (.n (.n (.n (.n (.l 1043996192) (.l 1395196910)) (.n (.l 1250997897) (.l 1395196910))) (.n (.n (.l 1152532069) (.l 1395196910)) (.n (.l 1341718858) (.l 1395196910)))) (.n (.n (.n (.l 1099712837) (.l 1395196910)) (.n (.l 1297216182) (.l 1395196910))) (.n (.n (.l 1202854893) (.l 1395196910)) (.n (.l 1384679862) (.l 1395196910))))))) (.n (.n (.n (.n (.n (.n (.l 1007477093) (.l 1395196910)) (.n (.l 1221149111) (.l 1395196910))) (.n (.n (.l 1119835877) (.l 1395196910)) (.n (.l 1314095715) (.l 1395196910)))) (.n (.n (.n (.l 1065259390) (.l 1395196910)) (.n (.l 1268543201) (.l 1395196910))) (.n (.n (.l 1171677110) (.l 1395196910)) (.n (.l 1358001499) (.l 1395196910))))) (.n (.n (.n (.n (.l 1036803584) (.l 1395196910)) (.n (.l 1245090017) (.l 1395196910))) (.n (.n (.l 1146073486) (.l 1395196910)) (.n (.l 1336243610) (.l 1395196910)))) (.n (.n (.n (.l 1092916057) (.l 1395196910)) (.n (.l 1291536632) (.l 1395196910))) (.n (.n (.l 1196689575) (.l 1395196910)) (.n (.l 1379388810) (.l 1395196910)))))) (.n (.n (.n (.n (.n (.l 1022254059) (.l 1395196910)) (.n (.l 1233182387) (.l 1395196910))) (.n (.n (.l 1133036806) (.l 1395196910)) (.n (.l 1325219694) (.l 1395196910)))) (.n (.n (.n (.l 1079183526) (.l 1395196910)) (.n (.l 1280095741) (.l 1395196910))) (.n (.n (.l 1184254748) (.l 1395196910)) (.n (.l 1368740325) (.l 1395196910))))) (.n (.n (.n (.n (.l 1051135613) (.l 1395196910)) (.n (.l 1256875762) (.l 1395196910))) (.n (.n (.l 1158951753) (.l 1395196910)) (.n (.l 1347170052) (.l 1395196910)))) (.n (.n (.n (.l 1106464494) (.l 1395196910)) (.n (.l 1302868970) (.l 1395196910))) (.n (.n (.l 1208986230) (.l 1395196910)) (.n (.l 1389949142) (.l 1395196910))))))))

def octHiTree : NTree :=
  (.n (.n (.n (.n (.n (.l 1000000000) (.l 4851008)) (.n (.l 69649172) (.l 337869))) (.n (.n (.l 263911295) (.l 1280236)) (.n (.l 18381203) (.l 89168)))) (.n (.n (.n (.l 513722975) (.l 2492074)) (.n (.l 35780380) (.l 173571))) (.n (.n (.l 135577296) (.l 657687)) (.n (.l 9442847) (.l 45808))))) (.n (.n (.n (.n (.l 716744707) (.l 3476934)) (.n (.l 49920675) (.l 242166))) (.n (.n (.l 189157024) (.l 917603)) (.n (.l 13174630) (.l 63911)))) (.n (.n (.n (.l 368208223) (.l 1786181)) (.n (.l 25645398) (.l 124407))) (.n (.n (.l 97174309) (.l 471394)) (.n (.l 6768111) (.l 32833))))))

@[inline] def ancLo (j : Nat) : Nat := ancLoTree.get j
@[inline] def ancHi (j : Nat) : Nat := ancHiTree.get j
@[inline] def octHi (k : Nat) : Nat := octHiTree.get k

def checkAnchorEntry (j : Nat) : Bool :=
  let cNum := ANCHOR_N + j
  let p := cNum ^ 123 * S2 ^ 256
  let q := ANCHOR_N ^ 123
  Nat.ble ((ancLo j) ^ 256 * q) p && Nat.ble p ((ancHi j) ^ 256 * q)

def checkAnchorsAux : Nat → Bool
  | 0 => checkAnchorEntry 0
  | j + 1 => if checkAnchorEntry (j + 1) then checkAnchorsAux j else false

theorem anc_table_certified_bool : checkAnchorsAux 64 = true := by decide

def checkOctaveEntry (k : Nat) : Bool :=
  Nat.ble (S2 ^ 256) ((octHi k) ^ 256 * (2 ^ k) ^ 123)

def checkOctavesAux : Nat → Bool
  | 0 => checkOctaveEntry 0
  | k + 1 => if checkOctaveEntry (k + 1) then checkOctavesAux k else false

theorem oct_table_certified_bool : checkOctavesAux 31 = true := by decide

def checkF19Row (w1 : Nat) : Nat → Bool
  | 0 =>
    let v := f19Val w1 0
    Nat.ble (v ^ 256 * 5 ^ 256) (3 ^ 256 * ((w1 + 2) * 2) ^ 123) &&
    (if w1 == 0 then true else Nat.ble (f19Val (w1 - 1) 0) v)
  | w2 + 1 =>
    let v := f19Val w1 (w2 + 1)
    let okBnd := Nat.ble (v ^ 256 * 5 ^ 256) (3 ^ 256 * ((w1 + 2) * (w2 + 3)) ^ 123)
    let okMonoY := Nat.ble (f19Val w1 w2) v
    let okMonoX :=
      if w1 == 0 then true
      else Nat.ble (f19Val (w1 - 1) (natMin (w2 + 1) (w1 - 1))) v
    if okBnd && okMonoY && okMonoX then checkF19Row w1 w2 else false

def checkF19All : Nat → Bool
  | 0 => checkF19Row 0 0
  | w1 + 1 => if checkF19Row (w1 + 1) (w1 + 1) then checkF19All w1 else false

theorem f19_all_certified_bool : checkF19All 19 = true := by decide

@[inline] def findShift31 (num den : Nat) : Nat :=
  let (k, x) := if Nat.blt (num * 65536) den then (16, num * 65536) else (0, num)
  let (k, x) := if Nat.blt (x * 256) den then (k + 8, x * 256) else (k, x)
  let (k, x) := if Nat.blt (x * 16) den then (k + 4, x * 16) else (k, x)
  let (k, x) := if Nat.blt (x * 4) den then (k + 2, x * 4) else (k, x)
  let (k, x) := if Nat.blt (x * 2) den then (k + 1, x * 2) else (k, x)
  let k := if Nat.blt x den then k + 1 else k
  natMin 31 k

@[inline] def pupFast (num den : Nat) : Nat :=
  if num == 0 then 0
  else
    let k := findShift31 num den
    let rNum := num * (2 ^ k)
    let j :=
      if Nat.ble rNum den then 0
      else natMin ANCHOR_N (((rNum - den) * ANCHOR_N * 2 + den) / (2 * den))
    let cNum := ANCHOR_N + j
    let top := ancHi j * octHi k * (123 * rNum * ANCHOR_N + 133 * den * cNum) * SCALE_DATA
    let bot := S2 * S2 * 256 * den * cNum
    (top + bot - 1) / bot

@[inline] def ploFast (num den : Nat) : Nat :=
  if num == 0 then 0
  else
    let j :=
      if Nat.ble num den then 0
      else natMin ANCHOR_N (((num - den) * ANCHOR_N * 2 + den) / (2 * den))
    let cNum := ANCHOR_N + j
    let top := ancLo j * 256 * num * ANCHOR_N * SCALE_DATA
    let bot := S2 * (123 * den * cNum + 133 * num * ANCHOR_N)
    top / bot

@[inline] def prodUpD (a b : Nat) : Nat := (a * b + SCALE_DATA - 1) / SCALE_DATA
@[inline] def prodLoD (a b : Nat) : Nat := (a * b) / SCALE_DATA

@[inline] def pupE (n d kEps : Nat) : Nat :=
  if kEps == 0 then pupFast n d
  else pupFast (n * 4096 + kEps * d) (d * 4096)

def holderPairE (pw1 pw2 sHi sDen h1mRaw h2mRaw : Nat) : Nat :=
  if (pw1 == 0) && (pw2 == 0) then 0
  else
    let h1m := natMin h1mRaw sHi
    let h2m := natMin h2mRaw sHi
    if Nat.ble (h1m + h2m) sHi then
      prodUpD pw1 (pupE h1m sDen 2) + prodUpD pw2 (pupE h2m sDen 2)
    else
      let lo := sHi - h2m
      let hi := h1m
      if Nat.ble hi lo then
        prodUpD pw1 (pupE lo sDen 2) + prodUpD pw2 (pupE (sHi - lo) sDen 2)
      else if (pw1 == pw2) && Nat.ble (2 * lo) sHi && Nat.ble sHi (2 * hi) then
        2 * prodUpD pw1 (pupE sHi (2 * sDen) 2)
      else
        let rec go (k : Nat) (best : Nat) : Nat :=
          match k with
          | 0 => best
          | k' + 1 =>
            let an := lo * 8 + (hi - lo) * k'
            let bn := lo * 8 + (hi - lo) * (k' + 1)
            let v := prodUpD pw1 (pupE bn (sDen * 8) 2) +
                     prodUpD pw2 (pupE (sHi * 8 - an) (sDen * 8) 2)
            go k' (natMax best v)
        go 8 0

def effAE (uHi den : Nat) : Nat :=
  let b0 := natMin (pupE uHi den 2) (pupE 1 3 0)
  if Nat.ble (den * 4094) (2 * uHi * 4096) then
    let smax := if Nat.ble (6 * uHi) (3 * den) then 0 else natMin den (6 * uHi - 3 * den)
    let sDen := 6 * den
    let v0 := 2 * pupFast 2 4096 + pupE 1 6 0
    let rec go (k : Nat) (best : Nat) : Nat :=
      match k with
      | 0 => best
      | k' + 1 =>
        let loN := smax * k'
        let hiN := smax * (k' + 1)
        let tL := 2 * pupFast (hiN * 4096 + 5 * sDen * 16) (2 * sDen * 16 * 4096)
        let tM := pupE (den * 16 - loN) (sDen * 16) 0
        go k' (natMax best (tL + tM))
    go 16 (natMax b0 v0)
  else b0

def peff23 : Nat := 77272
theorem peff23_certified : effAE 2 3 = peff23 := by decide

end ClawFreeEG.DyadicPackingData
