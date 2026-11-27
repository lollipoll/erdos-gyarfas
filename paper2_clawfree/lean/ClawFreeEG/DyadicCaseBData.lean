import ClawFreeEG.DyadicPackingData

/-!
# ClawFreeEG.DyadicCaseBData

Zero-`Std` (pure `Init`) kernel-certified Case B simple-orbit quad-tree data module
covering ALL `6` simple symmetry orbits (`0000`, `1000`, `1100`, `1010`, `1110`, `1111`;
total `813` leaves) on the triangle `0 ≤ s2 ≤ s1 ≤ 1/3` for all `m ≥ 4096`.

Uses precomputed `1/144`-grid and `1/2048`-grid `NTree` upper-bound tables certified once
against `DyadicPackingData.pupFast` / `ploFast` / `effAE` / `holderPairE` so every leaf
check executes with bounded stack depth and minimal kernel time. Strict precondition guards
(`leafGeomValid` plus strictly positive packed subdivision counts for `1110` and `1111`)
prevent vacuous passes on malformed inputs; kernel-proved semantic soundness theorems for
`pupGrid`, `pupEGrid`, `holderPairEGrid`, `aMax256Tree`, factored AM-GM (`1110`), and the
`379,133`-weighted tangent bound (`1111`) are proved in `ClawFreeEG.DyadicPacking2D`.
-/

namespace ClawFreeEG.DyadicCaseBData

open ClawFreeEG.DyadicPackingData

def plo144Tree : NTree :=
  (.n (.n (.n (.n (.n (.n (.l 100000) (.l 110121)) (.n (.l 105192) (.l 114535))) (.n (.n (.l 102631) (.l 112498)) (.n (.l 107687) (.l 114535)))) (.n (.n (.n (.l 101324) (.l 111317)) (.n (.l 106447) (.l 114535))) (.n (.n (.l 103920) (.l 113667)) (.n (.l 108911) (.l 114535))))) (.n (.n (.n (.n (.l 100664) (.l 110721)) (.n (.l 105822) (.l 114535))) (.n (.n (.l 103277) (.l 113084)) (.n (.l 108301) (.l 114535)))) (.n (.n (.n (.l 101980) (.l 111909)) (.n (.l 107069) (.l 114535))) (.n (.n (.l 104558) (.l 114246)) (.n (.l 109518) (.l 114535)))))) (.n (.n (.n (.n (.n (.l 100332) (.l 110421)) (.n (.l 105507) (.l 114535))) (.n (.n (.l 102955) (.l 112792)) (.n (.l 107995) (.l 114535)))) (.n (.n (.n (.l 101653) (.l 111613)) (.n (.l 106759) (.l 114535))) (.n (.n (.l 104240) (.l 113957)) (.n (.l 109215) (.l 114535))))) (.n (.n (.n (.n (.l 100995) (.l 111019)) (.n (.l 106135) (.l 114535))) (.n (.n (.l 103600) (.l 113376)) (.n (.l 108607) (.l 114535)))) (.n (.n (.n (.l 102306) (.l 112204)) (.n (.l 107379) (.l 114535))) (.n (.n (.l 104875) (.l 114535)) (.n (.l 109820) (.l 114535)))))))

def pw11_144Tree : NTree :=
  (.n (.n (.n (.n (.n (.n (.l 58988) (.l 34795)) (.n (.l 48546) (.l 9183))) (.n (.n (.l 54040) (.l 24940)) (.n (.l 42279) (.l 9183)))) (.n (.n (.n (.l 56573) (.l 30304)) (.n (.l 45530) (.l 9183))) (.n (.n (.l 51373) (.l 17875)) (.n (.l 38733) (.l 9183))))) (.n (.n (.n (.n (.l 57794) (.l 32633)) (.n (.l 47064) (.l 9183))) (.n (.n (.l 52725) (.l 21720)) (.n (.l 40548) (.l 9183)))) (.n (.n (.n (.l 55322) (.l 27762)) (.n (.l 43937) (.l 9183))) (.n (.n (.l 49981) (.l 12812)) (.n (.l 36821) (.l 9183)))))) (.n (.n (.n (.n (.n (.l 58394) (.l 33733)) (.n (.l 47811) (.l 9183))) (.n (.n (.l 53387) (.l 23390)) (.n (.l 41424) (.l 9183)))) (.n (.n (.n (.l 55951) (.l 29063)) (.n (.l 44741) (.l 9183))) (.n (.n (.l 50682) (.l 15568)) (.n (.l 37791) (.l 9183))))) (.n (.n (.n (.n (.l 57187) (.l 31492)) (.n (.l 46304) (.l 9183))) (.n (.n (.l 52054) (.l 19898)) (.n (.l 39652) (.l 9183)))) (.n (.n (.n (.l 54685) (.l 26392)) (.n (.l 43117) (.l 9183))) (.n (.n (.l 49269) (.l 9183)) (.n (.l 35824) (.l 9183)))))))

def eff1000_144Tree : NTree :=
  (.n (.n (.n (.n (.n (.n (.l 77272) (.l 58988)) (.n (.l 71440) (.l 58988))) (.n (.n (.l 76534) (.l 58988)) (.n (.l 58988) (.l 58988)))) (.n (.n (.n (.l 76904) (.l 58988)) (.n (.l 65125) (.l 58988))) (.n (.n (.l 74943) (.l 58988)) (.n (.l 58988) (.l 58988))))) (.n (.n (.n (.n (.l 77095) (.l 58988)) (.n (.l 68758) (.l 58988))) (.n (.n (.l 75964) (.l 58988)) (.n (.l 58988) (.l 58988)))) (.n (.n (.n (.l 76739) (.l 58988)) (.n (.l 59785) (.l 58988))) (.n (.n (.l 73457) (.l 58988)) (.n (.l 58988) (.l 58988)))))) (.n (.n (.n (.n (.n (.l 77187) (.l 58988)) (.n (.l 70196) (.l 58988))) (.n (.n (.l 76307) (.l 58988)) (.n (.l 58988) (.l 58988)))) (.n (.n (.n (.l 76831) (.l 58988)) (.n (.l 62758) (.l 58988))) (.n (.n (.l 74261) (.l 58988)) (.n (.l 58988) (.l 58988))))) (.n (.n (.n (.n (.l 77009) (.l 58988)) (.n (.l 67090) (.l 58988))) (.n (.n (.l 75511) (.l 58988)) (.n (.l 58988) (.l 58988)))) (.n (.n (.n (.l 76641) (.l 58988)) (.n (.l 58988) (.l 58988))) (.n (.n (.l 72521) (.l 58988)) (.n (.l 58988) (.l 58988)))))))

def holder23_144Tree : NTree :=
  (.n (.n (.n (.n (.n (.n (.l 3966) (.l 53888)) (.n (.l 38706) (.l 65434))) (.n (.n (.l 27860) (.l 59962)) (.n (.l 46966) (.l 65434)))) (.n (.n (.n (.l 20134) (.l 57012)) (.n (.l 43050) (.l 65434))) (.n (.n (.l 33756) (.l 62762)) (.n (.l 50556) (.l 65434))))) (.n (.n (.n (.n (.l 14664) (.l 55474)) (.n (.l 40942) (.l 65434))) (.n (.n (.l 30960) (.l 61380)) (.n (.l 48796) (.l 65434)))) (.n (.n (.n (.l 24330) (.l 58508)) (.n (.l 45054) (.l 65434))) (.n (.n (.l 36322) (.l 64112)) (.n (.l 52250) (.l 65434)))))) (.n (.n (.n (.n (.n (.l 10838) (.l 54688)) (.n (.l 39840) (.l 65434))) (.n (.n (.l 29454) (.l 60674)) (.n (.l 47890) (.l 65434)))) (.n (.n (.n (.l 22338) (.l 57764)) (.n (.l 44064) (.l 65434))) (.n (.n (.l 35066) (.l 63442)) (.n (.l 51410) (.l 65434))))) (.n (.n (.n (.n (.l 17630) (.l 56248)) (.n (.l 42010) (.l 65434))) (.n (.n (.l 32390) (.l 62076)) (.n (.l 49684) (.l 65434)))) (.n (.n (.n (.l 26160) (.l 59240)) (.n (.l 46020) (.l 65434))) (.n (.n (.l 37536) (.l 64776)) (.n (.l 53076) (.l 65434)))))))

def gridUp2048Tree : NTree :=
  (.n (.n (.n (.n (.n (.n (.n (.n (.n (.n (.l 0) (.l 51373)) (.n (.l 36821) (.l 59374))) (.n (.n (.l 26392) (.l 57187)) (.n (.l 44741) (.l 59374)))) (.n (.n (.n (.l 18916) (.l 54364)) (.n (.l 40988) (.l 59374))) (.n (.n (.l 32068) (.l 59374)) (.n (.l 48180) (.l 59374))))) (.n (.n (.n (.n (.l 13558) (.l 52891)) (.n (.l 38965) (.l 59374))) (.n (.n (.l 29378) (.l 58543)) (.n (.l 46495) (.l 59374)))) (.n (.n (.n (.l 22985) (.l 55795)) (.n (.l 42909) (.l 59374))) (.n (.n (.l 34533) (.l 59374)) (.n (.l 49804) (.l 59374)))))) (.n (.n (.n (.n (.n (.l 9718) (.l 52138)) (.n (.l 37910) (.l 59374))) (.n (.n (.l 27928) (.l 57869)) (.n (.l 45627) (.l 59374)))) (.n (.n (.n (.l 21057) (.l 55084)) (.n (.l 41961) (.l 59374))) (.n (.n (.l 33325) (.l 59374)) (.n (.l 49000) (.l 59374))))) (.n (.n (.n (.n (.l 16474) (.l 53633)) (.n (.l 39991) (.l 59374))) (.n (.n (.l 30755) (.l 59209)) (.n (.l 47346) (.l 59374)))) (.n (.n (.n (.l 24752) (.l 56495)) (.n (.l 43835) (.l 59374))) (.n (.n (.l 35697) (.l 59374)) (.n (.l 50595) (.l 59374))))))) (.n (.n (.n (.n (.n (.n (.l 6965) (.l 51757)) (.n (.l 37370) (.l 59374))) (.n (.n (.l 27172) (.l 57529)) (.n (.l 45186) (.l 59374)))) (.n (.n (.n (.l 20018) (.l 54725)) (.n (.l 41478) (.l 59374))) (.n (.n (.l 32703) (.l 59374)) (.n (.l 48592) (.l 59374))))) (.n (.n (.n (.n (.l 15093) (.l 53263)) (.n (.l 39481) (.l 59374))) (.n (.n (.l 30075) (.l 58877)) (.n (.l 46923) (.l 59374)))) (.n (.n (.n (.l 23886) (.l 56146)) (.n (.l 43375) (.l 59374))) (.n (.n (.l 35120) (.l 59374)) (.n (.l 50201) (.l 59374)))))) (.n (.n (.n (.n (.n (.l 11808) (.l 52516)) (.n (.l 38441) (.l 59374))) (.n (.n (.l 28663) (.l 58207)) (.n (.l 46063) (.l 59374)))) (.n (.n (.n (.l 22044) (.l 55441)) (.n (.l 42438) (.l 59374))) (.n (.n (.l 33935) (.l 59374)) (.n (.l 49404) (.l 59374))))) (.n (.n (.n (.n (.l 17741) (.l 54000)) (.n (.l 40493) (.l 59374))) (.n (.n (.l 31419) (.l 59374)) (.n (.l 47765) (.l 59374)))) (.n (.n (.n (.l 25586) (.l 56842)) (.n (.l 44291) (.l 59374))) (.n (.n (.l 36264) (.l 59374)) (.n (.l 50986) (.l 59374)))))))) (.n (.n (.n (.n (.n (.n (.n (.l 4993) (.l 51566)) (.n (.l 37097) (.l 59374))) (.n (.n (.l 26785) (.l 57358)) (.n (.l 44964) (.l 59374)))) (.n (.n (.n (.l 19475) (.l 54545)) (.n (.l 41234) (.l 59374))) (.n (.n (.l 32387) (.l 59374)) (.n (.l 48387) (.l 59374))))) (.n (.n (.n (.n (.l 14348) (.l 53078)) (.n (.l 39224) (.l 59374))) (.n (.n (.l 29729) (.l 58711)) (.n (.l 46709) (.l 59374)))) (.n (.n (.n (.l 23440) (.l 55971)) (.n (.l 43143) (.l 59374))) (.n (.n (.l 34828) (.l 59374)) (.n (.l 50003) (.l 59374)))))) (.n (.n (.n (.n (.n (.l 10818) (.l 52328)) (.n (.l 38176) (.l 59374))) (.n (.n (.l 28298) (.l 58039)) (.n (.l 45846) (.l 59374)))) (.n (.n (.n (.l 21556) (.l 55263)) (.n (.l 42200) (.l 59374))) (.n (.n (.l 33632) (.l 59374)) (.n (.l 49202) (.l 59374))))) (.n (.n (.n (.n (.l 17120) (.l 53817)) (.n (.l 40243) (.l 59374))) (.n (.n (.l 31089) (.l 59374)) (.n (.l 47556) (.l 59374)))) (.n (.n (.n (.l 25172) (.l 56669)) (.n (.l 44064) (.l 59374))) (.n (.n (.l 35982) (.l 59374)) (.n (.l 50791) (.l 59374))))))) (.n (.n (.n (.n (.n (.n (.l 8463) (.l 51948)) (.n (.l 37641) (.l 59374))) (.n (.n (.l 27553) (.l 57700)) (.n (.l 45407) (.l 59374)))) (.n (.n (.n (.l 20544) (.l 54905)) (.n (.l 41720) (.l 59374))) (.n (.n (.l 33016) (.l 59374)) (.n (.l 48796) (.l 59374))))) (.n (.n (.n (.n (.l 15800) (.l 53449)) (.n (.l 39737) (.l 59374))) (.n (.n (.l 30417) (.l 59043)) (.n (.l 47135) (.l 59374)))) (.n (.n (.n (.l 24323) (.l 56321)) (.n (.l 43606) (.l 59374))) (.n (.n (.l 35410) (.l 59374)) (.n (.l 50399) (.l 59374)))))) (.n (.n (.n (.n (.n (.l 12716) (.l 52704)) (.n (.l 38704) (.l 59374))) (.n (.n (.l 29023) (.l 58376)) (.n (.l 46280) (.l 59374)))) (.n (.n (.n (.l 22519) (.l 55618)) (.n (.l 42674) (.l 59374))) (.n (.n (.l 34236) (.l 59374)) (.n (.l 49604) (.l 59374))))) (.n (.n (.n (.n (.l 18339) (.l 54182)) (.n (.l 40741) (.l 59374))) (.n (.n (.l 31745) (.l 59374)) (.n (.l 47973) (.l 59374)))) (.n (.n (.n (.l 25992) (.l 57015)) (.n (.l 44516) (.l 59374))) (.n (.n (.l 36544) (.l 59374)) (.n (.l 51180) (.l 59374))))))))) (.n (.n (.n (.n (.n (.n (.n (.n (.l 3579) (.l 51469)) (.n (.l 36960) (.l 59374))) (.n (.n (.l 26589) (.l 57273)) (.n (.l 44853) (.l 59374)))) (.n (.n (.n (.l 19198) (.l 54455)) (.n (.l 41111) (.l 59374))) (.n (.n (.l 32228) (.l 59374)) (.n (.l 48284) (.l 59374))))) (.n (.n (.n (.n (.l 13959) (.l 52985)) (.n (.l 39095) (.l 59374))) (.n (.n (.l 29554) (.l 58627)) (.n (.l 46602) (.l 59374)))) (.n (.n (.n (.l 23214) (.l 55883)) (.n (.l 43026) (.l 59374))) (.n (.n (.l 34681) (.l 59374)) (.n (.l 49904) (.l 59374)))))) (.n (.n (.n (.n (.n (.l 10284) (.l 52233)) (.n (.l 38044) (.l 59374))) (.n (.n (.l 28114) (.l 57954)) (.n (.l 45737) (.l 59374)))) (.n (.n (.n (.l 21308) (.l 55174)) (.n (.l 42081) (.l 59374))) (.n (.n (.l 33479) (.l 59374)) (.n (.l 49101) (.l 59374))))) (.n (.n (.n (.n (.l 16801) (.l 53725)) (.n (.l 40117) (.l 59374))) (.n (.n (.l 30922) (.l 59291)) (.n (.l 47451) (.l 59374)))) (.n (.n (.n (.l 24963) (.l 56582)) (.n (.l 43950) (.l 59374))) (.n (.n (.l 35840) (.l 59374)) (.n (.l 50693) (.l 59374))))))) (.n (.n (.n (.n (.n (.n (.l 7754) (.l 51853)) (.n (.l 37506) (.l 59374))) (.n (.n (.l 27363) (.l 57614)) (.n (.l 45297) (.l 59374)))) (.n (.n (.n (.l 20283) (.l 54815)) (.n (.l 41599) (.l 59374))) (.n (.n (.l 32860) (.l 59374)) (.n (.l 48694) (.l 59374))))) (.n (.n (.n (.n (.l 15451) (.l 53356)) (.n (.l 39610) (.l 59374))) (.n (.n (.l 30247) (.l 58960)) (.n (.l 47029) (.l 59374)))) (.n (.n (.n (.l 24105) (.l 56234)) (.n (.l 43491) (.l 59374))) (.n (.n (.l 35265) (.l 59374)) (.n (.l 50300) (.l 59374)))))) (.n (.n (.n (.n (.n (.l 12271) (.l 52610)) (.n (.l 38573) (.l 59374))) (.n (.n (.l 28844) (.l 58291)) (.n (.l 46172) (.l 59374)))) (.n (.n (.n (.l 22283) (.l 55529)) (.n (.l 42556) (.l 59374))) (.n (.n (.l 34086) (.l 59374)) (.n (.l 49504) (.l 59374))))) (.n (.n (.n (.n (.l 18042) (.l 54091)) (.n (.l 40618) (.l 59374))) (.n (.n (.l 31582) (.l 59374)) (.n (.l 47869) (.l 59374)))) (.n (.n (.n (.l 25790) (.l 56929)) (.n (.l 44404) (.l 59374))) (.n (.n (.l 36404) (.l 59374)) (.n (.l 51083) (.l 59374)))))))) (.n (.n (.n (.n (.n (.n (.n (.l 6066) (.l 51661)) (.n (.l 37234) (.l 59374))) (.n (.n (.l 26979) (.l 57444)) (.n (.l 45076) (.l 59374)))) (.n (.n (.n (.l 19748) (.l 54635)) (.n (.l 41356) (.l 59374))) (.n (.n (.l 32546) (.l 59374)) (.n (.l 48489) (.l 59374))))) (.n (.n (.n (.n (.l 14725) (.l 53171)) (.n (.l 39353) (.l 59374))) (.n (.n (.l 29903) (.l 58794)) (.n (.l 46816) (.l 59374)))) (.n (.n (.n (.l 23664) (.l 56059)) (.n (.l 43259) (.l 59374))) (.n (.n (.l 34975) (.l 59374)) (.n (.l 50103) (.l 59374)))))) (.n (.n (.n (.n (.n (.l 11325) (.l 52422)) (.n (.l 38309) (.l 59374))) (.n (.n (.l 28481) (.l 58123)) (.n (.l 45955) (.l 59374)))) (.n (.n (.n (.l 21801) (.l 55352)) (.n (.l 42319) (.l 59374))) (.n (.n (.l 33784) (.l 59374)) (.n (.l 49303) (.l 59374))))) (.n (.n (.n (.n (.l 17433) (.l 53908)) (.n (.l 40368) (.l 59374))) (.n (.n (.l 31254) (.l 59374)) (.n (.l 47661) (.l 59374)))) (.n (.n (.n (.l 25380) (.l 56756)) (.n (.l 44177) (.l 59374))) (.n (.n (.l 36123) (.l 59374)) (.n (.l 50888) (.l 59374))))))) (.n (.n (.n (.n (.n (.n (.l 9114) (.l 52043)) (.n (.l 37776) (.l 59374))) (.n (.n (.l 27741) (.l 57784)) (.n (.l 45517) (.l 59374)))) (.n (.n (.n (.l 20802) (.l 54995)) (.n (.l 41841) (.l 59374))) (.n (.n (.l 33171) (.l 59374)) (.n (.l 48898) (.l 59374))))) (.n (.n (.n (.n (.l 16141) (.l 53541)) (.n (.l 39864) (.l 59374))) (.n (.n (.l 30587) (.l 59126)) (.n (.l 47241) (.l 59374)))) (.n (.n (.n (.l 24538) (.l 56408)) (.n (.l 43721) (.l 59374))) (.n (.n (.l 35554) (.l 59374)) (.n (.l 50497) (.l 59374)))))) (.n (.n (.n (.n (.n (.l 13144) (.l 52798)) (.n (.l 38835) (.l 59374))) (.n (.n (.l 29201) (.l 58459)) (.n (.l 46388) (.l 59374)))) (.n (.n (.n (.l 22753) (.l 55706)) (.n (.l 42792) (.l 59374))) (.n (.n (.l 34385) (.l 59374)) (.n (.l 49705) (.l 59374))))) (.n (.n (.n (.n (.l 18630) (.l 54273)) (.n (.l 40865) (.l 59374))) (.n (.n (.l 31907) (.l 59374)) (.n (.l 48077) (.l 59374)))) (.n (.n (.n (.l 26193) (.l 57101)) (.n (.l 44629) (.l 59374))) (.n (.n (.l 36683) (.l 59374)) (.n (.l 51276) (.l 59374)))))))))) (.n (.n (.n (.n (.n (.n (.n (.n (.n (.l 2565) (.l 51421)) (.n (.l 36890) (.l 59374))) (.n (.n (.l 26491) (.l 57230)) (.n (.l 44797) (.l 59374)))) (.n (.n (.n (.l 19058) (.l 54409)) (.n (.l 41050) (.l 59374))) (.n (.n (.l 32148) (.l 59374)) (.n (.l 48232) (.l 59374))))) (.n (.n (.n (.n (.l 13760) (.l 52938)) (.n (.l 39030) (.l 59374))) (.n (.n (.l 29467) (.l 58585)) (.n (.l 46549) (.l 59374)))) (.n (.n (.n (.l 23099) (.l 55839)) (.n (.l 42968) (.l 59374))) (.n (.n (.l 34607) (.l 59374)) (.n (.l 49854) (.l 59374)))))) (.n (.n (.n (.n (.n (.l 10005) (.l 52185)) (.n (.l 37977) (.l 59374))) (.n (.n (.l 28021) (.l 57912)) (.n (.l 45682) (.l 59374)))) (.n (.n (.n (.l 21183) (.l 55129)) (.n (.l 42021) (.l 59374))) (.n (.n (.l 33402) (.l 59374)) (.n (.l 49050) (.l 59374))))) (.n (.n (.n (.n (.l 16638) (.l 53679)) (.n (.l 40054) (.l 59374))) (.n (.n (.l 30839) (.l 59250)) (.n (.l 47398) (.l 59374)))) (.n (.n (.n (.l 24858) (.l 56539)) (.n (.l 43893) (.l 59374))) (.n (.n (.l 35769) (.l 59374)) (.n (.l 50644) (.l 59374))))))) (.n (.n (.n (.n (.n (.n (.l 7371) (.l 51805)) (.n (.l 37438) (.l 59374))) (.n (.n (.l 27268) (.l 57572)) (.n (.l 45242) (.l 59374)))) (.n (.n (.n (.l 20151) (.l 54770)) (.n (.l 41538) (.l 59374))) (.n (.n (.l 32782) (.l 59374)) (.n (.l 48643) (.l 59374))))) (.n (.n (.n (.n (.l 15273) (.l 53310)) (.n (.l 39546) (.l 59374))) (.n (.n (.l 30161) (.l 58919)) (.n (.l 46976) (.l 59374)))) (.n (.n (.n (.l 23996) (.l 56190)) (.n (.l 43433) (.l 59374))) (.n (.n (.l 35193) (.l 59374)) (.n (.l 50251) (.l 59374)))))) (.n (.n (.n (.n (.n (.l 12042) (.l 52563)) (.n (.l 38507) (.l 59374))) (.n (.n (.l 28754) (.l 58249)) (.n (.l 46118) (.l 59374)))) (.n (.n (.n (.l 22164) (.l 55485)) (.n (.l 42497) (.l 59374))) (.n (.n (.l 34010) (.l 59374)) (.n (.l 49454) (.l 59374))))) (.n (.n (.n (.n (.l 17892) (.l 54045)) (.n (.l 40555) (.l 59374))) (.n (.n (.l 31501) (.l 59374)) (.n (.l 47817) (.l 59374)))) (.n (.n (.n (.l 25688) (.l 56885)) (.n (.l 44347) (.l 59374))) (.n (.n (.l 36334) (.l 59374)) (.n (.l 51034) (.l 59374)))))))) (.n (.n (.n (.n (.n (.n (.n (.l 5558) (.l 51613)) (.n (.l 37165) (.l 59374))) (.n (.n (.l 26882) (.l 57401)) (.n (.l 45020) (.l 59374)))) (.n (.n (.n (.l 19612) (.l 54590)) (.n (.l 41295) (.l 59374))) (.n (.n (.l 32467) (.l 59374)) (.n (.l 48438) (.l 59374))))) (.n (.n (.n (.n (.l 14538) (.l 53124)) (.n (.l 39289) (.l 59374))) (.n (.n (.l 29816) (.l 58752)) (.n (.l 46763) (.l 59374)))) (.n (.n (.n (.l 23552) (.l 56015)) (.n (.l 43201) (.l 59374))) (.n (.n (.l 34901) (.l 59374)) (.n (.l 50053) (.l 59374)))))) (.n (.n (.n (.n (.n (.l 11074) (.l 52375)) (.n (.l 38243) (.l 59374))) (.n (.n (.l 28390) (.l 58081)) (.n (.l 45900) (.l 59374)))) (.n (.n (.n (.l 21679) (.l 55307)) (.n (.l 42260) (.l 59374))) (.n (.n (.l 33708) (.l 59374)) (.n (.l 49253) (.l 59374))))) (.n (.n (.n (.n (.l 17278) (.l 53863)) (.n (.l 40305) (.l 59374))) (.n (.n (.l 31172) (.l 59374)) (.n (.l 47608) (.l 59374)))) (.n (.n (.n (.l 25276) (.l 56712)) (.n (.l 44121) (.l 59374))) (.n (.n (.l 36053) (.l 59374)) (.n (.l 50840) (.l 59374))))))) (.n (.n (.n (.n (.n (.n (.l 8795) (.l 51996)) (.n (.l 37708) (.l 59374))) (.n (.n (.l 27647) (.l 57742)) (.n (.l 45462) (.l 59374)))) (.n (.n (.n (.l 20674) (.l 54950)) (.n (.l 41780) (.l 59374))) (.n (.n (.l 33094) (.l 59374)) (.n (.l 48847) (.l 59374))))) (.n (.n (.n (.n (.l 15971) (.l 53495)) (.n (.l 39801) (.l 59374))) (.n (.n (.l 30502) (.l 59085)) (.n (.l 47188) (.l 59374)))) (.n (.n (.n (.l 24431) (.l 56365)) (.n (.l 43663) (.l 59374))) (.n (.n (.l 35482) (.l 59374)) (.n (.l 50448) (.l 59374)))))) (.n (.n (.n (.n (.n (.l 12932) (.l 52751)) (.n (.l 38770) (.l 59374))) (.n (.n (.l 29113) (.l 58418)) (.n (.l 46334) (.l 59374)))) (.n (.n (.n (.l 22637) (.l 55662)) (.n (.l 42733) (.l 59374))) (.n (.n (.l 34310) (.l 59374)) (.n (.l 49654) (.l 59374))))) (.n (.n (.n (.n (.l 18485) (.l 54228)) (.n (.l 40803) (.l 59374))) (.n (.n (.l 31826) (.l 59374)) (.n (.l 48025) (.l 59374)))) (.n (.n (.n (.l 26093) (.l 57058)) (.n (.l 44573) (.l 59374))) (.n (.n (.l 36613) (.l 59374)) (.n (.l 51228) (.l 59374))))))))) (.n (.n (.n (.n (.n (.n (.n (.n (.l 4348) (.l 51517)) (.n (.l 37028) (.l 59374))) (.n (.n (.l 26687) (.l 57315)) (.n (.l 44909) (.l 59374)))) (.n (.n (.n (.l 19337) (.l 54500)) (.n (.l 41173) (.l 59374))) (.n (.n (.l 32308) (.l 59374)) (.n (.l 48335) (.l 59374))))) (.n (.n (.n (.n (.l 14155) (.l 53031)) (.n (.l 39160) (.l 59374))) (.n (.n (.l 29642) (.l 58669)) (.n (.l 46656) (.l 59374)))) (.n (.n (.n (.l 23327) (.l 55927)) (.n (.l 43084) (.l 59374))) (.n (.n (.l 34755) (.l 59374)) (.n (.l 49954) (.l 59374)))))) (.n (.n (.n (.n (.n (.l 10554) (.l 52280)) (.n (.l 38110) (.l 59374))) (.n (.n (.l 28206) (.l 57996)) (.n (.l 45791) (.l 59374)))) (.n (.n (.n (.l 21433) (.l 55218)) (.n (.l 42140) (.l 59374))) (.n (.n (.l 33555) (.l 59374)) (.n (.l 49152) (.l 59374))))) (.n (.n (.n (.n (.l 16961) (.l 53771)) (.n (.l 40180) (.l 59374))) (.n (.n (.l 31006) (.l 59333)) (.n (.l 47504) (.l 59374)))) (.n (.n (.n (.l 25068) (.l 56626)) (.n (.l 44007) (.l 59374))) (.n (.n (.l 35911) (.l 59374)) (.n (.l 50742) (.l 59374))))))) (.n (.n (.n (.n (.n (.n (.l 8117) (.l 51900)) (.n (.l 37573) (.l 59374))) (.n (.n (.l 27458) (.l 57657)) (.n (.l 45352) (.l 59374)))) (.n (.n (.n (.l 20414) (.l 54860)) (.n (.l 41659) (.l 59374))) (.n (.n (.l 32938) (.l 59374)) (.n (.l 48745) (.l 59374))))) (.n (.n (.n (.n (.l 15626) (.l 53403)) (.n (.l 39673) (.l 59374))) (.n (.n (.l 30332) (.l 59002)) (.n (.l 47082) (.l 59374)))) (.n (.n (.n (.l 24214) (.l 56277)) (.n (.l 43548) (.l 59374))) (.n (.n (.l 35338) (.l 59374)) (.n (.l 50349) (.l 59374)))))) (.n (.n (.n (.n (.n (.l 12495) (.l 52657)) (.n (.l 38639) (.l 59374))) (.n (.n (.l 28934) (.l 58334)) (.n (.l 46226) (.l 59374)))) (.n (.n (.n (.l 22402) (.l 55574)) (.n (.l 42615) (.l 59374))) (.n (.n (.l 34161) (.l 59374)) (.n (.l 49554) (.l 59374))))) (.n (.n (.n (.n (.l 18191) (.l 54137)) (.n (.l 40679) (.l 59374))) (.n (.n (.l 31664) (.l 59374)) (.n (.l 47921) (.l 59374)))) (.n (.n (.n (.l 25891) (.l 56972)) (.n (.l 44460) (.l 59374))) (.n (.n (.l 36474) (.l 59374)) (.n (.l 51131) (.l 59374)))))))) (.n (.n (.n (.n (.n (.n (.n (.l 6533) (.l 51709)) (.n (.l 37302) (.l 59374))) (.n (.n (.l 27076) (.l 57486)) (.n (.l 45131) (.l 59374)))) (.n (.n (.n (.l 19883) (.l 54680)) (.n (.l 41417) (.l 59374))) (.n (.n (.l 32625) (.l 59374)) (.n (.l 48541) (.l 59374))))) (.n (.n (.n (.n (.l 14910) (.l 53217)) (.n (.l 39417) (.l 59374))) (.n (.n (.l 29989) (.l 58835)) (.n (.l 46869) (.l 59374)))) (.n (.n (.n (.l 23775) (.l 56102)) (.n (.l 43317) (.l 59374))) (.n (.n (.l 35048) (.l 59374)) (.n (.l 50152) (.l 59374)))))) (.n (.n (.n (.n (.n (.l 11569) (.l 52469)) (.n (.l 38375) (.l 59374))) (.n (.n (.l 28573) (.l 58165)) (.n (.l 46009) (.l 59374)))) (.n (.n (.n (.l 21923) (.l 55396)) (.n (.l 42378) (.l 59374))) (.n (.n (.l 33860) (.l 59374)) (.n (.l 49353) (.l 59374))))) (.n (.n (.n (.n (.l 17588) (.l 53954)) (.n (.l 40430) (.l 59374))) (.n (.n (.l 31337) (.l 59374)) (.n (.l 47713) (.l 59374)))) (.n (.n (.n (.l 25483) (.l 56799)) (.n (.l 44234) (.l 59374))) (.n (.n (.l 36194) (.l 59374)) (.n (.l 50937) (.l 59374))))))) (.n (.n (.n (.n (.n (.n (.l 9421) (.l 52091)) (.n (.l 37843) (.l 59374))) (.n (.n (.l 27835) (.l 57827)) (.n (.l 45572) (.l 59374)))) (.n (.n (.n (.l 20930) (.l 55040)) (.n (.l 41901) (.l 59374))) (.n (.n (.l 33248) (.l 59374)) (.n (.l 48949) (.l 59374))))) (.n (.n (.n (.n (.l 16308) (.l 53587)) (.n (.l 39927) (.l 59374))) (.n (.n (.l 30671) (.l 59167)) (.n (.l 47293) (.l 59374)))) (.n (.n (.n (.l 24645) (.l 56452)) (.n (.l 43778) (.l 59374))) (.n (.n (.l 35626) (.l 59374)) (.n (.l 50546) (.l 59374)))))) (.n (.n (.n (.n (.n (.l 13353) (.l 52844)) (.n (.l 38900) (.l 59374))) (.n (.n (.l 29290) (.l 58501)) (.n (.l 46441) (.l 59374)))) (.n (.n (.n (.l 22869) (.l 55750)) (.n (.l 42850) (.l 59374))) (.n (.n (.l 34459) (.l 59374)) (.n (.l 49754) (.l 59374))))) (.n (.n (.n (.n (.l 18774) (.l 54318)) (.n (.l 40927) (.l 59374))) (.n (.n (.l 31988) (.l 59374)) (.n (.l 48129) (.l 59374)))) (.n (.n (.n (.l 26292) (.l 57144)) (.n (.l 44685) (.l 59374))) (.n (.n (.l 36752) (.l 59374)) (.n (.l 51325) (.l 59374)))))))))))

@[inline] def plo144 (a : Nat) : Nat := plo144Tree.get a
@[inline] def pw11_144 (a : Nat) : Nat := pw11_144Tree.get a
@[inline] def eff1000_144 (a : Nat) : Nat := eff1000_144Tree.get a
@[inline] def eff1100_144 (_ : Nat) : Nat := peff23
@[inline] def holder23_144 (a : Nat) : Nat := holder23_144Tree.get a

private def checkPloPw : Nat → Bool
  | 0 => (plo144 0 == ploFast 144 144) && (pw11_144 0 == pupE 144 432 0)
  | a + 1 =>
    if (plo144 (a + 1) == ploFast (144 + a + 1) 144) &&
       (pw11_144 (a + 1) == pupE (144 - 3 * (a + 1)) 432 0) then checkPloPw a else false

private def checkEff1000 : Nat → Bool
  | 0 => eff1000_144 0 == effAE 288 432
  | a + 1 => if eff1000_144 (a + 1) == effAE (288 - 3 * (a + 1)) 432 then checkEff1000 a else false

private def checkHolder23 : Nat → Bool
  | 0 => holder23_144 0 == holderPairE peff23 peff23 0 144 0 0
  | a + 1 => if holder23_144 (a + 1) == holderPairE peff23 peff23 (a + 1) 144 (a + 1) (a + 1) then checkHolder23 a else false

def checkGridTree (start : Nat) : Nat → Bool
  | 0 => if Nat.ble start 692 then gridUp2048Tree.get start == pupFast start 2048 else true
  | d + 1 =>
    let half := 2 ^ d
    if checkGridTree start d then checkGridTree (start + half) d else false

def checkGridMonoTree (start : Nat) : Nat → Bool
  | 0 =>
    if Nat.blt start 692 then
      Nat.ble (gridUp2048Tree.get start) (gridUp2048Tree.get (start + 1))
    else true
  | d + 1 =>
    let half := 2 ^ d
    if checkGridMonoTree start d then checkGridMonoTree (start + half) d else false

theorem tables_144_certified :
    checkPloPw 47 = true ∧
    checkEff1000 47 = true ∧
    (effAE 288 432 == peff23) = true ∧
    checkHolder23 48 = true := by
  decide

theorem gridUp2048_c0_ok : checkGridTree 0 8 = true := by decide
theorem gridUp2048_c1_ok : checkGridTree 256 8 = true := by decide
theorem gridUp2048_c2_ok : checkGridTree 512 8 = true := by decide
theorem gridUp2048_all_ok : checkGridTree 0 10 = true := by
  have h3 : checkGridTree 768 8 = true := by decide
  change (if (if checkGridTree 0 8 then checkGridTree 256 8 else false)
          then (if checkGridTree 512 8 then checkGridTree 768 8 else false)
          else false) = true
  rw [gridUp2048_c0_ok, gridUp2048_c1_ok, gridUp2048_c2_ok, h3]
  rfl

theorem gridUp2048_mono_ok : checkGridMonoTree 0 10 = true := by decide

/-- Strict geometric admissibility guard for Case B leaf checkers: checks positive dividing
denominator (`curD > 0`, `curD ∣ 144`), ordered box bounds (`s1l ≤ s1h`, `s2l ≤ s2h`), non-empty
intersection with the ordered triangle `0 ≤ s2 ≤ s1 ≤ 1/3` (clipped region), and all
`1/144`-table indices in bounds. -/
@[inline] def leafGeomValid (s1l s1h s2l s2h curD : Nat) : Bool :=
  Nat.blt 0 curD && (144 % curD == 0) &&
  Nat.ble s1l s1h && Nat.ble s2l s2h && Nat.ble s2l s1h &&
  Nat.ble (3 * s1h) curD && Nat.ble (3 * s2h) curD &&
  Nat.blt (s1l * (144 / curD)) 48 && Nat.blt (s2l * (144 / curD)) 48

/-- Bounded-instance sound monotone upper bound on `(num / den)^(123/256) * SCALE` via the `1/2048` table. -/
@[inline] def pupGrid (num den : Nat) : Nat :=
  if num == 0 then 0
  else
    let idx := (num * 2048 + den - 1) / den
    if Nat.ble idx 692 then gridUp2048Tree.get idx else pupFast num den

@[inline] def pupEGrid (n d kEps : Nat) : Nat :=
  if kEps == 0 then pupGrid n d
  else pupGrid (n * 4096 + kEps * d) (d * 4096)

def holderPairEGrid (pw1 pw2 sHi sDen h1mRaw h2mRaw : Nat) : Nat :=
  if (pw1 == 0) && (pw2 == 0) then 0
  else
    let h1m := natMin h1mRaw sHi
    let h2m := natMin h2mRaw sHi
    if Nat.ble (h1m + h2m) sHi then
      prodUpD pw1 (pupEGrid h1m sDen 2) + prodUpD pw2 (pupEGrid h2m sDen 2)
    else
      let lo := sHi - h2m
      let hi := h1m
      if Nat.ble hi lo then
        prodUpD pw1 (pupEGrid lo sDen 2) + prodUpD pw2 (pupEGrid (sHi - lo) sDen 2)
      else if (pw1 == pw2) && Nat.ble (2 * lo) sHi && Nat.ble sHi (2 * hi) then
        2 * prodUpD pw1 (pupEGrid sHi (2 * sDen) 2)
      else
        let rec go (k : Nat) (best : Nat) : Nat :=
          match k with
          | 0 => best
          | k' + 1 =>
            let an := lo * 8 + (hi - lo) * k'
            let bn := lo * 8 + (hi - lo) * (k' + 1)
            let v := prodUpD pw1 (pupEGrid bn (sDen * 8) 2) +
                     prodUpD pw2 (pupEGrid (sHi * 8 - an) (sDen * 8) 2)
            go k' (natMax best v)
        go 8 0

def checkLeaf0000 (s1l s1h s2l s2h curD _ _ : Nat) : Bool :=
  if !(leafGeomValid s1l s1h s2l s2h curD) then false
  else
    let m := 144 / curD
    let a1l := s1l * m; let a2l := s2l * m
    let denLo := prodLoD (plo144 a1l) (plo144 a2l)
    let lim := (99920 * denLo) / SCALE_DATA
    let pw11 := pw11_144 a1l
    let ph11 := pw11_144 a2l
    let tot := prodUpD pw11 ph11 + holderPairEGrid pw11 pw11 s2h curD s2h s2h + holderPairEGrid ph11 ph11 s1h curD s1h s1h
    Nat.ble tot lim

def checkLeaf1000 (s1l s1h s2l s2h curD _ _ : Nat) : Bool :=
  if !(leafGeomValid s1l s1h s2l s2h curD) then false
  else
    let m := 144 / curD
    let a1l := s1l * m; let a2l := s2l * m
    let denLo := prodLoD (plo144 a1l) (plo144 a2l)
    let lim := (99920 * denLo) / SCALE_DATA
    let pw11 := pw11_144 a1l
    let ph11 := pw11_144 a2l
    let mUp := prodUpD pw11 ph11
    let pw12 := eff1000_144 a1l
    let ph21 := eff1000_144 a2l
    let rec goU : Nat → Bool
      | 0 => true
      | ku' + 1 =>
        let w0l := s1h * ku'
        let w0h := s1h * (ku' + 1)
        let elr := holderPairEGrid ph11 ph21 (s1h * 4) (curD * 4) (s1h * 4) (s1h * 4 - w0l)
        let pw0 := pupEGrid w0h (curD * 4) 2
        let rec goV : Nat → Bool
          | 0 => true
          | kv' + 1 =>
            let h0l := s2h * kv'
            let h0h := s2h * (kv' + 1)
            let ebt := holderPairEGrid pw11 pw12 (s2h * 4) (curD * 4) (s2h * 4) (s2h * 4 - h0l)
            let tot := prodUpD pw0 (pupEGrid h0h (curD * 4) 2) + ebt + elr + mUp
            if Nat.ble tot lim then goV kv' else false
        if goV 4 then goU ku' else false
    goU 4

def checkLeaf1100 (s1l s1h s2l s2h curD _ _ : Nat) : Bool :=
  if !(leafGeomValid s1l s1h s2l s2h curD) then false
  else
    let m := 144 / curD
    let a1l := s1l * m; let a2l := s2l * m
    let denLo := prodLoD (plo144 a1l) (plo144 a2l)
    let lim := (99920 * denLo) / SCALE_DATA
    let pw11 := pw11_144 a1l
    let ph11 := pw11_144 a2l
    let blr := holder23_144 (s1h * m)
    let pw10 := pw11_144 0
    let pw12 := eff1100_144 a1l
    let tot := blr + holderPairEGrid pw10 pw12 s2h curD s2h s2h + prodUpD pw11 ph11
    Nat.ble tot lim

def checkLeaf1010 (s1l s1h s2l s2h curD _ _ : Nat) : Bool :=
  if !(leafGeomValid s1l s1h s2l s2h curD) then false
  else
    let m := 144 / curD
    let a1l := s1l * m; let a2l := s2l * m
    let denLo := prodLoD (plo144 a1l) (plo144 a2l)
    let lim := (99920 * denLo) / SCALE_DATA
    let pw11 := pw11_144 a1l
    let ph11 := pw11_144 a2l
    let bbt := holder23_144 (s2h * m)
    let ph01 := pw11_144 0
    let ph21 := eff1100_144 a2l
    let tot := bbt + holderPairEGrid ph01 ph21 s1h curD s1h s1h + prodUpD pw11 ph11
    Nat.ble tot lim

private def mkTab (n : Nat) (f : Nat → α) : List α :=
  let rec go (i : Nat) (acc : List α) : List α :=
    match i with
    | 0 => acc
    | i' + 1 => go i' (f i' :: acc)
  go n []

def maxFactoredAMGM (u1h dUw pu1 : Nat) : Nat → Nat → Nat
  | 0, best => best
  | kw' + 1, best =>
    let pw0 := pupEGrid (u1h * (kw' + 1)) dUw 2
    let pw10 := pupEGrid (dUw - 3 * u1h * kw') (3 * dUw) 0
    let v := pw10 + (pw0 * pw0 + 2 * pu1 - 1) / (2 * pu1)
    maxFactoredAMGM u1h dUw pu1 kw' (natMax best v)

/-- Precomputed 1D factored AM-GM upper-bound table on the `1/256` grid (`idx ∈ 1..86`, `kwS = 8`). -/
def aMax256Tree : NTree :=
  (.n (.n (.n (.n (.n (.n (.n (.l 0) (.l 63582)) (.n (.l 67190) (.l 0))) (.n (.n (.l 67383) (.l 63161)) (.n (.l 65061) (.l 0)))) (.n (.n (.n (.l 66155) (.l 63287)) (.n (.l 66316) (.l 0))) (.n (.n (.l 67591) (.l 0)) (.n (.l 64117) (.l 0))))) (.n (.n (.n (.n (.l 64707) (.l 63377)) (.n (.l 66808) (.l 0))) (.n (.n (.l 67578) (.l 63160)) (.n (.l 64536) (.l 0)))) (.n (.n (.n (.l 66946) (.l 63188)) (.n (.l 65718) (.l 0))) (.n (.n (.l 67456) (.l 0)) (.n (.l 63809) (.l 0)))))) (.n (.n (.n (.n (.n (.l 63421) (.l 63483)) (.n (.l 67014) (.l 0))) (.n (.n (.l 67506) (.l 63161)) (.n (.l 64782) (.l 0)))) (.n (.n (.n (.l 66607) (.l 63239)) (.n (.l 66031) (.l 0))) (.n (.n (.l 67541) (.l 0)) (.n (.l 63968) (.l 0))))) (.n (.n (.n (.n (.l 65549) (.l 63332)) (.n (.l 66576) (.l 0))) (.n (.n (.l 67605) (.l 63159)) (.n (.l 64323) (.l 0)))) (.n (.n (.n (.l 67199) (.l 63158)) (.n (.l 65380) (.l 0))) (.n (.n (.l 67339) (.l 0)) (.n (.l 63678) (.l 0))))))) (.n (.n (.n (.n (.n (.n (.l 62397) (.l 63533)) (.n (.l 67106) (.l 0))) (.n (.n (.l 67451) (.l 63160)) (.n (.l 64924) (.l 0)))) (.n (.n (.n (.l 66397) (.l 63264)) (.n (.l 66176) (.l 0))) (.n (.n (.l 67571) (.l 0)) (.n (.l 64044) (.l 0))))) (.n (.n (.n (.n (.l 65166) (.l 63355)) (.n (.l 66696) (.l 0))) (.n (.n (.l 67597) (.l 63160)) (.n (.l 64431) (.l 0)))) (.n (.n (.n (.l 67082) (.l 63161)) (.n (.l 65552) (.l 0))) (.n (.n (.l 67401) (.l 0)) (.n (.l 63727) (.l 0)))))) (.n (.n (.n (.n (.n (.l 64144) (.l 63430)) (.n (.l 66915) (.l 0))) (.n (.n (.l 67548) (.l 63161)) (.n (.l 64639) (.l 0)))) (.n (.n (.n (.l 66788) (.l 63214)) (.n (.l 65878) (.l 0))) (.n (.n (.l 67502) (.l 0)) (.n (.l 63889) (.l 0))))) (.n (.n (.n (.n (.l 65875) (.l 63311)) (.n (.l 66450) (.l 0))) (.n (.n (.l 67604) (.l 0)) (.n (.l 64211) (.l 0)))) (.n (.n (.n (.l 67299) (.l 63159)) (.n (.l 65200) (.l 0))) (.n (.n (.l 67268) (.l 0)) (.n (.l 63631) (.l 0))))))))

def checkAMax256Tree (start : Nat) : Nat → Bool
  | 0 =>
    if Nat.ble 1 start && Nat.ble start 86 then
      let pu1 := gridUp2048Tree.get (8 * start + 1)
      Nat.blt 0 pu1 &&
      (pu1 == pupEGrid start 256 2) &&
      (aMax256Tree.get start == maxFactoredAMGM start 2048 pu1 8 0)
    else true
  | d + 1 =>
    let half := 2 ^ d
    if checkAMax256Tree start d then checkAMax256Tree (start + half) d else false

theorem aMax256_certified : checkAMax256Tree 0 7 = true := by decide

def checkLeaf1110 (s1l s1h s2l s2h curD k1 k2 : Nat) : Bool :=
  if !(leafGeomValid s1l s1h s2l s2h curD) then false
  else
    let kU := k1 / 16; let kV := k1 % 16
    let kwS := k2 / 16; let khS := k2 % 16
    if !(Nat.blt 0 kU && Nat.blt 0 kV && Nat.blt 0 kwS && Nat.blt 0 khS) then false
    else
      let m := 144 / curD
      let a1l := s1l * m; let a2l := s2l * m
      let denLo := prodLoD (plo144 a1l) (plo144 a2l)
      let lim := (99920 * denLo) / SCALE_DATA
      let mUp := prodUpD (pw11_144 a1l) (pw11_144 a2l)
      let dU := curD * kU; let dV := curD * kV
      let dUw := dU * kwS; let dVh := dV * khS
      let uData := mkTab kU fun ku =>
        let u1h := s1h * (ku + 1)
        let idx := (u1h * 256 + dU - 1) / dU
        let pu1 := if Nat.ble 1 idx && Nat.ble idx 86 then gridUp2048Tree.get (8 * idx + 1) else pupEGrid u1h dU 2
        let pu2 := prodUpD (pupEGrid (s1h * (kU - ku)) dU 2) peff23
        let aMax := if Nat.ble 1 idx && Nat.ble idx 86 then aMax256Tree.get idx else maxFactoredAMGM u1h dUw pu1 kwS 0
        (pu1, pu2, aMax)
      let vData := mkTab kV fun kv =>
        let v1h := s2h * (kv + 1)
        let idx := (v1h * 256 + dV - 1) / dV
        let pv1 := if Nat.ble 1 idx && Nat.ble idx 86 then gridUp2048Tree.get (8 * idx + 1) else pupEGrid v1h dV 2
        let pv2 := prodUpD peff23 (pupEGrid (s2h * (kV - kv)) dV 2)
        let bMax := if Nat.ble 1 idx && Nat.ble idx 86 then aMax256Tree.get idx else maxFactoredAMGM v1h dVh pv1 khS 0
        (pv1, pv2, bMax)
      let rec goU : List (Nat × Nat × Nat) → Bool
        | [] => true
        | (pu1, pu2, aMax) :: us' =>
          let rec goV : List (Nat × Nat × Nat) → Bool
            | [] => true
            | (pv1, pv2, bMax) :: vs' =>
              if Nat.ble (pu2 + pv2 + mUp + prodUpD aMax pv1 + prodUpD pu1 bMax + 1) lim then goV vs' else false
          if goV vData then goU us' else false
      goU uData

def listGetD : List Nat → Nat → Nat
  | [], _ => 0
  | x :: _, 0 => x
  | _ :: xs, n + 1 => listGetD xs n

def maxTangentForSum (pws : List Nat) (s : Nat) : Nat → Nat → Nat → Nat
  | 0, _, best => best
  | steps + 1, i, best =>
    let wi := listGetD pws i
    let wj := listGetD pws (s - i)
    let v := (379 * wi + 133 * wj + 255) / 256
    maxTangentForSum pws s steps (i + 1) (natMax best v)

def checkLeaf1111 (s1l s1h s2l s2h curD k1 _ : Nat) : Bool :=
  if !(leafGeomValid s1l s1h s2l s2h curD) then false
  else
    let kU := k1 / 16; let kV := k1 % 16
    if !(Nat.blt 0 kU && Nat.blt 0 kV) then false
    else
      let m := 144 / curD
      let a1l := s1l * m; let a2l := s2l * m
      let denLo := prodLoD (plo144 a1l) (plo144 a2l)
      let lim := (99920 * denLo) / SCALE_DATA
      let mUp := prodUpD (pw11_144 a1l) (pw11_144 a2l)
      let dU := curD * kU; let dV := curD * kV
      let pw10s := mkTab kU fun k => pupEGrid (dU - 3 * s1h * k) (3 * dU) 0
      let ph01s := mkTab kV fun k => pupEGrid (dV - 3 * s2h * k) (3 * dV) 0
      let pS2Half := pupEGrid s2h (2 * curD) 2
      let pS1Half := pupEGrid s1h (2 * curD) 2
      let uPairs := mkTab (2 * kU - 1) fun s =>
        let iLo := if Nat.ble s (kU - 1) then 0 else s + 1 - kU
        let iHi := s / 2
        let wMax := maxTangentForSum pw10s s (iHi + 1 - iLo) iLo 0
        (prodUpD wMax pS2Half, pupEGrid (s1h * (s + 2)) (4 * dU) 2)
      let vPairs := mkTab (2 * kV - 1) fun s =>
        let iLo := if Nat.ble s (kV - 1) then 0 else s + 1 - kV
        let iHi := s / 2
        let wMax := maxTangentForSum ph01s s (iHi + 1 - iLo) iLo 0
        (prodUpD wMax pS1Half, pupEGrid (s2h * (s + 2)) (4 * dV) 2)
      let rec goU : List (Nat × Nat) → Bool
        | [] => true
        | (ebt, puAvg) :: us' =>
          let rec goV : List (Nat × Nat) → Bool
            | [] => true
            | (elr, pvAvg) :: vs' =>
              if Nat.ble (4 * prodUpD puAvg pvAvg + ebt + elr + mUp) lim then goV vs' else false
          if goV vPairs then goU us' else false
      goU uPairs

/-- Regression checks: malformed / zero-parameter inputs are strictly rejected by all leaf checkers. -/
theorem checkLeaf1110_rejects_zero : checkLeaf1110 0 1 0 1 36 0 0 = false := by decide
theorem checkLeaf1111_rejects_zero : checkLeaf1111 0 1 0 1 36 0 0 = false := by decide
theorem checkLeaf_rejects_invalid_geom :
    checkLeaf0000 0 1 0 1 0 0 0 = false ∧
    checkLeaf0000 0 1 0 1 37 0 0 = false ∧
    checkLeaf1000 0 1 0 1 0 0 0 = false ∧
    checkLeaf1100 0 1 0 1 0 0 0 = false ∧
    checkLeaf1010 0 1 0 1 0 0 0 = false := by
  decide

inductive QuadTree where
  | empty
  | leaf (s1l s1h s2l s2h curD k1 k2 : Nat)
  | split (c00 c01 c10 c11 : QuadTree)

inductive CellForest where
  | cell (i j : Nat) (t : QuadTree)
  | node (l r : CellForest)

def checkQuadTree (chk : Nat → Nat → Nat → Nat → Nat → Nat → Nat → Bool) :
    Nat → Nat → Nat → Nat → Nat → QuadTree → Bool
  | _, s1h, s2l, _, _, .empty => Nat.blt s1h s2l
  | s1l, s1h, s2l, s2h, curD, .leaf a b c d e k1 k2 =>
    (a == s1l) && (b == s1h) && (c == s2l) && (d == s2h) && (e == curD) &&
    chk a b c d e k1 k2
  | s1l, s1h, s2l, s2h, curD, .split c00 c01 c10 c11 =>
    (s1h == s1l + 1) && (s2h == s2l + 1) &&
    checkQuadTree chk (2 * s1l) (2 * s1l + 1) (2 * s2l) (natMin (2 * s2l + 1) (2 * s1l + 1)) (2 * curD) c00 &&
    checkQuadTree chk (2 * s1l) (2 * s1l + 1) (2 * s2l + 1) (natMin (2 * s2l + 2) (2 * s1l + 1)) (2 * curD) c01 &&
    checkQuadTree chk (2 * s1l + 1) (2 * s1l + 2) (2 * s2l) (natMin (2 * s2l + 1) (2 * s1l + 2)) (2 * curD) c10 &&
    checkQuadTree chk (2 * s1l + 1) (2 * s1l + 2) (2 * s2l + 1) (natMin (2 * s2l + 2) (2 * s1l + 2)) (2 * curD) c11

def checkForestBounds (chk : Nat → Nat → Nat → Nat → Nat → Nat → Nat → Bool) : CellForest → Bool
  | .cell i j t => checkQuadTree chk i (i + 1) j (j + 1) 36 t
  | .node l r => if checkForestBounds chk l then checkForestBounds chk r else false

def forestHasCell (i j : Nat) : CellForest → Bool
  | .cell ci cj _ => (ci == i) && (cj == j)
  | .node l r => forestHasCell i j l || forestHasCell i j r

def checkForestCoversRow (f : CellForest) (i : Nat) : Nat → Bool
  | 0 => forestHasCell i 0 f
  | j + 1 => if forestHasCell i (j + 1) f then checkForestCoversRow f i j else false

def checkForestCoversAll (f : CellForest) : Nat → Bool
  | 0 => checkForestCoversRow f 0 0
  | i + 1 => if checkForestCoversRow f (i + 1) (i + 1) then checkForestCoversAll f i else false

def forest0000 : CellForest :=
  (.node (.node (.node (.node (.node (.node (.cell 0 0 (.leaf 0 1 0 1 36 0 0)) (.cell 1 0 (.leaf 1 2 0 1 36 0 0))) (.node (.cell 1 1 (.leaf 1 2 1 2 36 0 0)) (.cell 2 0 (.leaf 2 3 0 1 36 0 0)))) (.node (.node (.cell 2 1 (.leaf 2 3 1 2 36 0 0)) (.cell 2 2 (.leaf 2 3 2 3 36 0 0))) (.node (.cell 3 0 (.leaf 3 4 0 1 36 0 0)) (.node (.cell 3 1 (.leaf 3 4 1 2 36 0 0)) (.cell 3 2 (.leaf 3 4 2 3 36 0 0)))))) (.node (.node (.node (.cell 3 3 (.leaf 3 4 3 4 36 0 0)) (.cell 4 0 (.leaf 4 5 0 1 36 0 0))) (.node (.cell 4 1 (.leaf 4 5 1 2 36 0 0)) (.node (.cell 4 2 (.leaf 4 5 2 3 36 0 0)) (.cell 4 3 (.leaf 4 5 3 4 36 0 0))))) (.node (.node (.cell 4 4 (.leaf 4 5 4 5 36 0 0)) (.cell 5 0 (.leaf 5 6 0 1 36 0 0))) (.node (.cell 5 1 (.leaf 5 6 1 2 36 0 0)) (.node (.cell 5 2 (.leaf 5 6 2 3 36 0 0)) (.cell 5 3 (.leaf 5 6 3 4 36 0 0))))))) (.node (.node (.node (.node (.cell 5 4 (.leaf 5 6 4 5 36 0 0)) (.cell 5 5 (.leaf 5 6 5 6 36 0 0))) (.node (.cell 6 0 (.leaf 6 7 0 1 36 0 0)) (.node (.cell 6 1 (.leaf 6 7 1 2 36 0 0)) (.cell 6 2 (.leaf 6 7 2 3 36 0 0))))) (.node (.node (.cell 6 3 (.leaf 6 7 3 4 36 0 0)) (.cell 6 4 (.leaf 6 7 4 5 36 0 0))) (.node (.cell 6 5 (.leaf 6 7 5 6 36 0 0)) (.node (.cell 6 6 (.leaf 6 7 6 7 36 0 0)) (.cell 7 0 (.leaf 7 8 0 1 36 0 0)))))) (.node (.node (.node (.cell 7 1 (.leaf 7 8 1 2 36 0 0)) (.cell 7 2 (.leaf 7 8 2 3 36 0 0))) (.node (.cell 7 3 (.leaf 7 8 3 4 36 0 0)) (.node (.cell 7 4 (.leaf 7 8 4 5 36 0 0)) (.cell 7 5 (.leaf 7 8 5 6 36 0 0))))) (.node (.node (.cell 7 6 (.leaf 7 8 6 7 36 0 0)) (.cell 7 7 (.leaf 7 8 7 8 36 0 0))) (.node (.cell 8 0 (.leaf 8 9 0 1 36 0 0)) (.node (.cell 8 1 (.leaf 8 9 1 2 36 0 0)) (.cell 8 2 (.leaf 8 9 2 3 36 0 0)))))))) (.node (.node (.node (.node (.node (.cell 8 3 (.leaf 8 9 3 4 36 0 0)) (.cell 8 4 (.leaf 8 9 4 5 36 0 0))) (.node (.cell 8 5 (.leaf 8 9 5 6 36 0 0)) (.cell 8 6 (.leaf 8 9 6 7 36 0 0)))) (.node (.node (.cell 8 7 (.leaf 8 9 7 8 36 0 0)) (.cell 8 8 (.leaf 8 9 8 9 36 0 0))) (.node (.cell 9 0 (.leaf 9 10 0 1 36 0 0)) (.node (.cell 9 1 (.leaf 9 10 1 2 36 0 0)) (.cell 9 2 (.leaf 9 10 2 3 36 0 0)))))) (.node (.node (.node (.cell 9 3 (.leaf 9 10 3 4 36 0 0)) (.cell 9 4 (.leaf 9 10 4 5 36 0 0))) (.node (.cell 9 5 (.leaf 9 10 5 6 36 0 0)) (.node (.cell 9 6 (.leaf 9 10 6 7 36 0 0)) (.cell 9 7 (.leaf 9 10 7 8 36 0 0))))) (.node (.node (.cell 9 8 (.leaf 9 10 8 9 36 0 0)) (.cell 9 9 (.leaf 9 10 9 10 36 0 0))) (.node (.cell 10 0 (.leaf 10 11 0 1 36 0 0)) (.node (.cell 10 1 (.leaf 10 11 1 2 36 0 0)) (.cell 10 2 (.leaf 10 11 2 3 36 0 0))))))) (.node (.node (.node (.node (.cell 10 3 (.leaf 10 11 3 4 36 0 0)) (.cell 10 4 (.leaf 10 11 4 5 36 0 0))) (.node (.cell 10 5 (.leaf 10 11 5 6 36 0 0)) (.node (.cell 10 6 (.leaf 10 11 6 7 36 0 0)) (.cell 10 7 (.leaf 10 11 7 8 36 0 0))))) (.node (.node (.cell 10 8 (.leaf 10 11 8 9 36 0 0)) (.cell 10 9 (.leaf 10 11 9 10 36 0 0))) (.node (.cell 10 10 (.leaf 10 11 10 11 36 0 0)) (.node (.cell 11 0 (.leaf 11 12 0 1 36 0 0)) (.cell 11 1 (.leaf 11 12 1 2 36 0 0)))))) (.node (.node (.node (.cell 11 2 (.leaf 11 12 2 3 36 0 0)) (.cell 11 3 (.leaf 11 12 3 4 36 0 0))) (.node (.cell 11 4 (.leaf 11 12 4 5 36 0 0)) (.node (.cell 11 5 (.leaf 11 12 5 6 36 0 0)) (.cell 11 6 (.leaf 11 12 6 7 36 0 0))))) (.node (.node (.cell 11 7 (.leaf 11 12 7 8 36 0 0)) (.cell 11 8 (.leaf 11 12 8 9 36 0 0))) (.node (.cell 11 9 (.leaf 11 12 9 10 36 0 0)) (.node (.cell 11 10 (.leaf 11 12 10 11 36 0 0)) (.cell 11 11 (.leaf 11 12 11 12 36 0 0)))))))))
theorem forest0000_covers_bool : checkForestCoversAll forest0000 11 = true := by decide
theorem forest0000_bounds_bool : checkForestBounds checkLeaf0000 forest0000 = true := by decide

def forest1000 : CellForest :=
  (.node (.node (.node (.node (.node (.node (.cell 0 0 (.leaf 0 1 0 1 36 0 0)) (.cell 1 0 (.leaf 1 2 0 1 36 0 0))) (.node (.cell 1 1 (.leaf 1 2 1 2 36 0 0)) (.cell 2 0 (.leaf 2 3 0 1 36 0 0)))) (.node (.node (.cell 2 1 (.leaf 2 3 1 2 36 0 0)) (.cell 2 2 (.leaf 2 3 2 3 36 0 0))) (.node (.cell 3 0 (.leaf 3 4 0 1 36 0 0)) (.node (.cell 3 1 (.leaf 3 4 1 2 36 0 0)) (.cell 3 2 (.leaf 3 4 2 3 36 0 0)))))) (.node (.node (.node (.cell 3 3 (.leaf 3 4 3 4 36 0 0)) (.cell 4 0 (.leaf 4 5 0 1 36 0 0))) (.node (.cell 4 1 (.leaf 4 5 1 2 36 0 0)) (.node (.cell 4 2 (.leaf 4 5 2 3 36 0 0)) (.cell 4 3 (.leaf 4 5 3 4 36 0 0))))) (.node (.node (.cell 4 4 (.leaf 4 5 4 5 36 0 0)) (.cell 5 0 (.leaf 5 6 0 1 36 0 0))) (.node (.cell 5 1 (.leaf 5 6 1 2 36 0 0)) (.node (.cell 5 2 (.leaf 5 6 2 3 36 0 0)) (.cell 5 3 (.leaf 5 6 3 4 36 0 0))))))) (.node (.node (.node (.node (.cell 5 4 (.leaf 5 6 4 5 36 0 0)) (.cell 5 5 (.leaf 5 6 5 6 36 0 0))) (.node (.cell 6 0 (.leaf 6 7 0 1 36 0 0)) (.node (.cell 6 1 (.leaf 6 7 1 2 36 0 0)) (.cell 6 2 (.leaf 6 7 2 3 36 0 0))))) (.node (.node (.cell 6 3 (.leaf 6 7 3 4 36 0 0)) (.cell 6 4 (.leaf 6 7 4 5 36 0 0))) (.node (.cell 6 5 (.leaf 6 7 5 6 36 0 0)) (.node (.cell 6 6 (.leaf 6 7 6 7 36 0 0)) (.cell 7 0 (.leaf 7 8 0 1 36 0 0)))))) (.node (.node (.node (.cell 7 1 (.leaf 7 8 1 2 36 0 0)) (.cell 7 2 (.leaf 7 8 2 3 36 0 0))) (.node (.cell 7 3 (.leaf 7 8 3 4 36 0 0)) (.node (.cell 7 4 (.leaf 7 8 4 5 36 0 0)) (.cell 7 5 (.leaf 7 8 5 6 36 0 0))))) (.node (.node (.cell 7 6 (.leaf 7 8 6 7 36 0 0)) (.cell 7 7 (.leaf 7 8 7 8 36 0 0))) (.node (.cell 8 0 (.leaf 8 9 0 1 36 0 0)) (.node (.cell 8 1 (.leaf 8 9 1 2 36 0 0)) (.cell 8 2 (.leaf 8 9 2 3 36 0 0)))))))) (.node (.node (.node (.node (.node (.cell 8 3 (.leaf 8 9 3 4 36 0 0)) (.cell 8 4 (.leaf 8 9 4 5 36 0 0))) (.node (.cell 8 5 (.leaf 8 9 5 6 36 0 0)) (.cell 8 6 (.leaf 8 9 6 7 36 0 0)))) (.node (.node (.cell 8 7 (.leaf 8 9 7 8 36 0 0)) (.cell 8 8 (.leaf 8 9 8 9 36 0 0))) (.node (.cell 9 0 (.leaf 9 10 0 1 36 0 0)) (.node (.cell 9 1 (.leaf 9 10 1 2 36 0 0)) (.cell 9 2 (.leaf 9 10 2 3 36 0 0)))))) (.node (.node (.node (.cell 9 3 (.leaf 9 10 3 4 36 0 0)) (.cell 9 4 (.leaf 9 10 4 5 36 0 0))) (.node (.cell 9 5 (.leaf 9 10 5 6 36 0 0)) (.node (.cell 9 6 (.leaf 9 10 6 7 36 0 0)) (.cell 9 7 (.leaf 9 10 7 8 36 0 0))))) (.node (.node (.cell 9 8 (.leaf 9 10 8 9 36 0 0)) (.cell 9 9 (.leaf 9 10 9 10 36 0 0))) (.node (.cell 10 0 (.leaf 10 11 0 1 36 0 0)) (.node (.cell 10 1 (.leaf 10 11 1 2 36 0 0)) (.cell 10 2 (.leaf 10 11 2 3 36 0 0))))))) (.node (.node (.node (.node (.cell 10 3 (.leaf 10 11 3 4 36 0 0)) (.cell 10 4 (.leaf 10 11 4 5 36 0 0))) (.node (.cell 10 5 (.leaf 10 11 5 6 36 0 0)) (.node (.cell 10 6 (.leaf 10 11 6 7 36 0 0)) (.cell 10 7 (.leaf 10 11 7 8 36 0 0))))) (.node (.node (.cell 10 8 (.leaf 10 11 8 9 36 0 0)) (.cell 10 9 (.leaf 10 11 9 10 36 0 0))) (.node (.cell 10 10 (.leaf 10 11 10 11 36 0 0)) (.node (.cell 11 0 (.leaf 11 12 0 1 36 0 0)) (.cell 11 1 (.leaf 11 12 1 2 36 0 0)))))) (.node (.node (.node (.cell 11 2 (.leaf 11 12 2 3 36 0 0)) (.cell 11 3 (.leaf 11 12 3 4 36 0 0))) (.node (.cell 11 4 (.leaf 11 12 4 5 36 0 0)) (.node (.cell 11 5 (.leaf 11 12 5 6 36 0 0)) (.cell 11 6 (.leaf 11 12 6 7 36 0 0))))) (.node (.node (.cell 11 7 (.leaf 11 12 7 8 36 0 0)) (.cell 11 8 (.leaf 11 12 8 9 36 0 0))) (.node (.cell 11 9 (.leaf 11 12 9 10 36 0 0)) (.node (.cell 11 10 (.leaf 11 12 10 11 36 0 0)) (.cell 11 11 (.leaf 11 12 11 12 36 0 0)))))))))
theorem forest1000_covers_bool : checkForestCoversAll forest1000 11 = true := by decide
theorem forest1000_bounds_bool : checkForestBounds checkLeaf1000 forest1000 = true := by decide

def forest1100 : CellForest :=
  (.node (.node (.node (.node (.node (.node (.cell 0 0 (.leaf 0 1 0 1 36 0 0)) (.cell 1 0 (.leaf 1 2 0 1 36 0 0))) (.node (.cell 1 1 (.leaf 1 2 1 2 36 0 0)) (.cell 2 0 (.leaf 2 3 0 1 36 0 0)))) (.node (.node (.cell 2 1 (.leaf 2 3 1 2 36 0 0)) (.cell 2 2 (.leaf 2 3 2 3 36 0 0))) (.node (.cell 3 0 (.leaf 3 4 0 1 36 0 0)) (.node (.cell 3 1 (.leaf 3 4 1 2 36 0 0)) (.cell 3 2 (.leaf 3 4 2 3 36 0 0)))))) (.node (.node (.node (.cell 3 3 (.leaf 3 4 3 4 36 0 0)) (.cell 4 0 (.leaf 4 5 0 1 36 0 0))) (.node (.cell 4 1 (.leaf 4 5 1 2 36 0 0)) (.node (.cell 4 2 (.leaf 4 5 2 3 36 0 0)) (.cell 4 3 (.leaf 4 5 3 4 36 0 0))))) (.node (.node (.cell 4 4 (.leaf 4 5 4 5 36 0 0)) (.cell 5 0 (.leaf 5 6 0 1 36 0 0))) (.node (.cell 5 1 (.leaf 5 6 1 2 36 0 0)) (.node (.cell 5 2 (.leaf 5 6 2 3 36 0 0)) (.cell 5 3 (.leaf 5 6 3 4 36 0 0))))))) (.node (.node (.node (.node (.cell 5 4 (.leaf 5 6 4 5 36 0 0)) (.cell 5 5 (.leaf 5 6 5 6 36 0 0))) (.node (.cell 6 0 (.leaf 6 7 0 1 36 0 0)) (.node (.cell 6 1 (.leaf 6 7 1 2 36 0 0)) (.cell 6 2 (.leaf 6 7 2 3 36 0 0))))) (.node (.node (.cell 6 3 (.leaf 6 7 3 4 36 0 0)) (.cell 6 4 (.leaf 6 7 4 5 36 0 0))) (.node (.cell 6 5 (.leaf 6 7 5 6 36 0 0)) (.node (.cell 6 6 (.split (.leaf 12 13 12 13 72 0 0) (.leaf 12 13 13 13 72 0 0) (.leaf 13 14 12 13 72 0 0) (.leaf 13 14 13 14 72 0 0))) (.cell 7 0 (.leaf 7 8 0 1 36 0 0)))))) (.node (.node (.node (.cell 7 1 (.leaf 7 8 1 2 36 0 0)) (.cell 7 2 (.leaf 7 8 2 3 36 0 0))) (.node (.cell 7 3 (.leaf 7 8 3 4 36 0 0)) (.node (.cell 7 4 (.leaf 7 8 4 5 36 0 0)) (.cell 7 5 (.leaf 7 8 5 6 36 0 0))))) (.node (.node (.cell 7 6 (.split (.leaf 14 15 12 13 72 0 0) (.leaf 14 15 13 14 72 0 0) (.leaf 15 16 12 13 72 0 0) (.leaf 15 16 13 14 72 0 0))) (.cell 7 7 (.split (.leaf 14 15 14 15 72 0 0) (.leaf 14 15 15 15 72 0 0) (.leaf 15 16 14 15 72 0 0) (.leaf 15 16 15 16 72 0 0)))) (.node (.cell 8 0 (.leaf 8 9 0 1 36 0 0)) (.node (.cell 8 1 (.leaf 8 9 1 2 36 0 0)) (.cell 8 2 (.leaf 8 9 2 3 36 0 0)))))))) (.node (.node (.node (.node (.node (.cell 8 3 (.leaf 8 9 3 4 36 0 0)) (.cell 8 4 (.leaf 8 9 4 5 36 0 0))) (.node (.cell 8 5 (.leaf 8 9 5 6 36 0 0)) (.cell 8 6 (.split (.leaf 16 17 12 13 72 0 0) (.leaf 16 17 13 14 72 0 0) (.leaf 17 18 12 13 72 0 0) (.leaf 17 18 13 14 72 0 0))))) (.node (.node (.cell 8 7 (.split (.leaf 16 17 14 15 72 0 0) (.leaf 16 17 15 16 72 0 0) (.leaf 17 18 14 15 72 0 0) (.leaf 17 18 15 16 72 0 0))) (.cell 8 8 (.split (.leaf 16 17 16 17 72 0 0) (.leaf 16 17 17 17 72 0 0) (.leaf 17 18 16 17 72 0 0) (.leaf 17 18 17 18 72 0 0)))) (.node (.cell 9 0 (.leaf 9 10 0 1 36 0 0)) (.node (.cell 9 1 (.leaf 9 10 1 2 36 0 0)) (.cell 9 2 (.leaf 9 10 2 3 36 0 0)))))) (.node (.node (.node (.cell 9 3 (.leaf 9 10 3 4 36 0 0)) (.cell 9 4 (.leaf 9 10 4 5 36 0 0))) (.node (.cell 9 5 (.leaf 9 10 5 6 36 0 0)) (.node (.cell 9 6 (.split (.leaf 18 19 12 13 72 0 0) (.leaf 18 19 13 14 72 0 0) (.leaf 19 20 12 13 72 0 0) (.leaf 19 20 13 14 72 0 0))) (.cell 9 7 (.split (.leaf 18 19 14 15 72 0 0) (.leaf 18 19 15 16 72 0 0) (.leaf 19 20 14 15 72 0 0) (.leaf 19 20 15 16 72 0 0)))))) (.node (.node (.cell 9 8 (.split (.leaf 18 19 16 17 72 0 0) (.leaf 18 19 17 18 72 0 0) (.leaf 19 20 16 17 72 0 0) (.leaf 19 20 17 18 72 0 0))) (.cell 9 9 (.split (.leaf 18 19 18 19 72 0 0) (.leaf 18 19 19 19 72 0 0) (.leaf 19 20 18 19 72 0 0) (.leaf 19 20 19 20 72 0 0)))) (.node (.cell 10 0 (.leaf 10 11 0 1 36 0 0)) (.node (.cell 10 1 (.leaf 10 11 1 2 36 0 0)) (.cell 10 2 (.leaf 10 11 2 3 36 0 0))))))) (.node (.node (.node (.node (.cell 10 3 (.leaf 10 11 3 4 36 0 0)) (.cell 10 4 (.leaf 10 11 4 5 36 0 0))) (.node (.cell 10 5 (.leaf 10 11 5 6 36 0 0)) (.node (.cell 10 6 (.leaf 10 11 6 7 36 0 0)) (.cell 10 7 (.split (.leaf 20 21 14 15 72 0 0) (.leaf 20 21 15 16 72 0 0) (.leaf 21 22 14 15 72 0 0) (.leaf 21 22 15 16 72 0 0)))))) (.node (.node (.cell 10 8 (.split (.leaf 20 21 16 17 72 0 0) (.leaf 20 21 17 18 72 0 0) (.leaf 21 22 16 17 72 0 0) (.leaf 21 22 17 18 72 0 0))) (.cell 10 9 (.split (.leaf 20 21 18 19 72 0 0) (.leaf 20 21 19 20 72 0 0) (.leaf 21 22 18 19 72 0 0) (.leaf 21 22 19 20 72 0 0)))) (.node (.cell 10 10 (.split (.leaf 20 21 20 21 72 0 0) (.leaf 20 21 21 21 72 0 0) (.leaf 21 22 20 21 72 0 0) (.leaf 21 22 21 22 72 0 0))) (.node (.cell 11 0 (.leaf 11 12 0 1 36 0 0)) (.cell 11 1 (.leaf 11 12 1 2 36 0 0)))))) (.node (.node (.node (.cell 11 2 (.leaf 11 12 2 3 36 0 0)) (.cell 11 3 (.leaf 11 12 3 4 36 0 0))) (.node (.cell 11 4 (.leaf 11 12 4 5 36 0 0)) (.node (.cell 11 5 (.leaf 11 12 5 6 36 0 0)) (.cell 11 6 (.leaf 11 12 6 7 36 0 0))))) (.node (.node (.cell 11 7 (.leaf 11 12 7 8 36 0 0)) (.cell 11 8 (.split (.leaf 22 23 16 17 72 0 0) (.leaf 22 23 17 18 72 0 0) (.leaf 23 24 16 17 72 0 0) (.leaf 23 24 17 18 72 0 0)))) (.node (.cell 11 9 (.split (.leaf 22 23 18 19 72 0 0) (.leaf 22 23 19 20 72 0 0) (.leaf 23 24 18 19 72 0 0) (.leaf 23 24 19 20 72 0 0))) (.node (.cell 11 10 (.split (.leaf 22 23 20 21 72 0 0) (.leaf 22 23 21 22 72 0 0) (.leaf 23 24 20 21 72 0 0) (.leaf 23 24 21 22 72 0 0))) (.cell 11 11 (.split (.leaf 22 23 22 23 72 0 0) (.leaf 22 23 23 23 72 0 0) (.leaf 23 24 22 23 72 0 0) (.leaf 23 24 23 24 72 0 0))))))))))
theorem forest1100_covers_bool : checkForestCoversAll forest1100 11 = true := by decide
theorem forest1100_bounds_bool : checkForestBounds checkLeaf1100 forest1100 = true := by decide

def forest1010 : CellForest :=
  (.node (.node (.node (.node (.node (.node (.cell 0 0 (.leaf 0 1 0 1 36 0 0)) (.cell 1 0 (.leaf 1 2 0 1 36 0 0))) (.node (.cell 1 1 (.leaf 1 2 1 2 36 0 0)) (.cell 2 0 (.leaf 2 3 0 1 36 0 0)))) (.node (.node (.cell 2 1 (.leaf 2 3 1 2 36 0 0)) (.cell 2 2 (.leaf 2 3 2 3 36 0 0))) (.node (.cell 3 0 (.leaf 3 4 0 1 36 0 0)) (.node (.cell 3 1 (.leaf 3 4 1 2 36 0 0)) (.cell 3 2 (.leaf 3 4 2 3 36 0 0)))))) (.node (.node (.node (.cell 3 3 (.leaf 3 4 3 4 36 0 0)) (.cell 4 0 (.leaf 4 5 0 1 36 0 0))) (.node (.cell 4 1 (.leaf 4 5 1 2 36 0 0)) (.node (.cell 4 2 (.leaf 4 5 2 3 36 0 0)) (.cell 4 3 (.leaf 4 5 3 4 36 0 0))))) (.node (.node (.cell 4 4 (.leaf 4 5 4 5 36 0 0)) (.cell 5 0 (.leaf 5 6 0 1 36 0 0))) (.node (.cell 5 1 (.leaf 5 6 1 2 36 0 0)) (.node (.cell 5 2 (.leaf 5 6 2 3 36 0 0)) (.cell 5 3 (.leaf 5 6 3 4 36 0 0))))))) (.node (.node (.node (.node (.cell 5 4 (.leaf 5 6 4 5 36 0 0)) (.cell 5 5 (.leaf 5 6 5 6 36 0 0))) (.node (.cell 6 0 (.leaf 6 7 0 1 36 0 0)) (.node (.cell 6 1 (.leaf 6 7 1 2 36 0 0)) (.cell 6 2 (.leaf 6 7 2 3 36 0 0))))) (.node (.node (.cell 6 3 (.leaf 6 7 3 4 36 0 0)) (.cell 6 4 (.leaf 6 7 4 5 36 0 0))) (.node (.cell 6 5 (.leaf 6 7 5 6 36 0 0)) (.node (.cell 6 6 (.split (.leaf 12 13 12 13 72 0 0) (.leaf 12 13 13 13 72 0 0) (.leaf 13 14 12 13 72 0 0) (.leaf 13 14 13 14 72 0 0))) (.cell 7 0 (.leaf 7 8 0 1 36 0 0)))))) (.node (.node (.node (.cell 7 1 (.leaf 7 8 1 2 36 0 0)) (.cell 7 2 (.leaf 7 8 2 3 36 0 0))) (.node (.cell 7 3 (.leaf 7 8 3 4 36 0 0)) (.node (.cell 7 4 (.leaf 7 8 4 5 36 0 0)) (.cell 7 5 (.leaf 7 8 5 6 36 0 0))))) (.node (.node (.cell 7 6 (.split (.leaf 14 15 12 13 72 0 0) (.leaf 14 15 13 14 72 0 0) (.leaf 15 16 12 13 72 0 0) (.leaf 15 16 13 14 72 0 0))) (.cell 7 7 (.split (.leaf 14 15 14 15 72 0 0) (.leaf 14 15 15 15 72 0 0) (.leaf 15 16 14 15 72 0 0) (.leaf 15 16 15 16 72 0 0)))) (.node (.cell 8 0 (.leaf 8 9 0 1 36 0 0)) (.node (.cell 8 1 (.leaf 8 9 1 2 36 0 0)) (.cell 8 2 (.leaf 8 9 2 3 36 0 0)))))))) (.node (.node (.node (.node (.node (.cell 8 3 (.leaf 8 9 3 4 36 0 0)) (.cell 8 4 (.leaf 8 9 4 5 36 0 0))) (.node (.cell 8 5 (.leaf 8 9 5 6 36 0 0)) (.cell 8 6 (.split (.leaf 16 17 12 13 72 0 0) (.leaf 16 17 13 14 72 0 0) (.leaf 17 18 12 13 72 0 0) (.leaf 17 18 13 14 72 0 0))))) (.node (.node (.cell 8 7 (.split (.leaf 16 17 14 15 72 0 0) (.leaf 16 17 15 16 72 0 0) (.leaf 17 18 14 15 72 0 0) (.leaf 17 18 15 16 72 0 0))) (.cell 8 8 (.split (.leaf 16 17 16 17 72 0 0) (.leaf 16 17 17 17 72 0 0) (.leaf 17 18 16 17 72 0 0) (.leaf 17 18 17 18 72 0 0)))) (.node (.cell 9 0 (.leaf 9 10 0 1 36 0 0)) (.node (.cell 9 1 (.leaf 9 10 1 2 36 0 0)) (.cell 9 2 (.leaf 9 10 2 3 36 0 0)))))) (.node (.node (.node (.cell 9 3 (.leaf 9 10 3 4 36 0 0)) (.cell 9 4 (.leaf 9 10 4 5 36 0 0))) (.node (.cell 9 5 (.leaf 9 10 5 6 36 0 0)) (.node (.cell 9 6 (.leaf 9 10 6 7 36 0 0)) (.cell 9 7 (.split (.leaf 18 19 14 15 72 0 0) (.leaf 18 19 15 16 72 0 0) (.leaf 19 20 14 15 72 0 0) (.leaf 19 20 15 16 72 0 0)))))) (.node (.node (.cell 9 8 (.split (.leaf 18 19 16 17 72 0 0) (.leaf 18 19 17 18 72 0 0) (.leaf 19 20 16 17 72 0 0) (.leaf 19 20 17 18 72 0 0))) (.cell 9 9 (.split (.leaf 18 19 18 19 72 0 0) (.leaf 18 19 19 19 72 0 0) (.leaf 19 20 18 19 72 0 0) (.leaf 19 20 19 20 72 0 0)))) (.node (.cell 10 0 (.leaf 10 11 0 1 36 0 0)) (.node (.cell 10 1 (.leaf 10 11 1 2 36 0 0)) (.cell 10 2 (.leaf 10 11 2 3 36 0 0))))))) (.node (.node (.node (.node (.cell 10 3 (.leaf 10 11 3 4 36 0 0)) (.cell 10 4 (.leaf 10 11 4 5 36 0 0))) (.node (.cell 10 5 (.leaf 10 11 5 6 36 0 0)) (.node (.cell 10 6 (.leaf 10 11 6 7 36 0 0)) (.cell 10 7 (.split (.leaf 20 21 14 15 72 0 0) (.leaf 20 21 15 16 72 0 0) (.leaf 21 22 14 15 72 0 0) (.leaf 21 22 15 16 72 0 0)))))) (.node (.node (.cell 10 8 (.split (.leaf 20 21 16 17 72 0 0) (.leaf 20 21 17 18 72 0 0) (.leaf 21 22 16 17 72 0 0) (.leaf 21 22 17 18 72 0 0))) (.cell 10 9 (.split (.leaf 20 21 18 19 72 0 0) (.leaf 20 21 19 20 72 0 0) (.leaf 21 22 18 19 72 0 0) (.leaf 21 22 19 20 72 0 0)))) (.node (.cell 10 10 (.split (.leaf 20 21 20 21 72 0 0) (.leaf 20 21 21 21 72 0 0) (.leaf 21 22 20 21 72 0 0) (.leaf 21 22 21 22 72 0 0))) (.node (.cell 11 0 (.leaf 11 12 0 1 36 0 0)) (.cell 11 1 (.leaf 11 12 1 2 36 0 0)))))) (.node (.node (.node (.cell 11 2 (.leaf 11 12 2 3 36 0 0)) (.cell 11 3 (.leaf 11 12 3 4 36 0 0))) (.node (.cell 11 4 (.leaf 11 12 4 5 36 0 0)) (.node (.cell 11 5 (.leaf 11 12 5 6 36 0 0)) (.cell 11 6 (.leaf 11 12 6 7 36 0 0))))) (.node (.node (.cell 11 7 (.leaf 11 12 7 8 36 0 0)) (.cell 11 8 (.leaf 11 12 8 9 36 0 0))) (.node (.cell 11 9 (.split (.leaf 22 23 18 19 72 0 0) (.leaf 22 23 19 20 72 0 0) (.leaf 23 24 18 19 72 0 0) (.leaf 23 24 19 20 72 0 0))) (.node (.cell 11 10 (.split (.leaf 22 23 20 21 72 0 0) (.leaf 22 23 21 22 72 0 0) (.leaf 23 24 20 21 72 0 0) (.leaf 23 24 21 22 72 0 0))) (.cell 11 11 (.split (.leaf 22 23 22 23 72 0 0) (.leaf 22 23 23 23 72 0 0) (.leaf 23 24 22 23 72 0 0) (.leaf 23 24 23 24 72 0 0))))))))))
theorem forest1010_covers_bool : checkForestCoversAll forest1010 11 = true := by decide
theorem forest1010_bounds_bool : checkForestBounds checkLeaf1010 forest1010 = true := by decide

def forest1110_c0 : CellForest :=
  (.node (.node (.node (.cell 0 0 (.leaf 0 1 0 1 36 17 17)) (.cell 1 0 (.leaf 1 2 0 1 36 17 17))) (.node (.cell 1 1 (.leaf 1 2 1 2 36 33 17)) (.node (.cell 2 0 (.leaf 2 3 0 1 36 33 17)) (.cell 2 1 (.leaf 2 3 1 2 36 34 17))))) (.node (.node (.cell 2 2 (.leaf 2 3 2 3 36 66 17)) (.cell 3 0 (.leaf 3 4 0 1 36 33 17))) (.node (.cell 3 1 (.leaf 3 4 1 2 36 50 17)) (.node (.cell 3 2 (.leaf 3 4 2 3 36 68 17)) (.cell 3 3 (.leaf 3 4 3 4 36 102 17))))))
theorem forest1110_c0_ok : checkForestBounds checkLeaf1110 forest1110_c0 = true := by decide

def forest1110_c1 : CellForest :=
  (.node (.node (.node (.cell 4 0 (.leaf 4 5 0 1 36 33 17)) (.cell 4 1 (.leaf 4 5 1 2 36 66 17))) (.node (.cell 4 2 (.leaf 4 5 2 3 36 100 17)) (.node (.cell 4 3 (.leaf 4 5 3 4 36 102 34)) (.cell 4 4 (.split (.leaf 8 9 8 9 72 68 34) (.leaf 8 9 9 9 72 68 33) (.leaf 9 10 8 9 72 100 34) (.leaf 9 10 9 10 72 166 17)))))) (.node (.node (.cell 5 0 (.leaf 5 6 0 1 36 49 17)) (.cell 5 1 (.leaf 5 6 1 2 36 67 17))) (.node (.cell 5 2 (.leaf 5 6 2 3 36 164 17)) (.node (.cell 5 3 (.leaf 5 6 3 4 36 166 34)) (.cell 5 4 (.split (.leaf 10 11 8 9 72 100 34) (.leaf 10 11 9 10 72 102 34) (.leaf 11 12 8 9 72 132 34) (.leaf 11 12 9 10 72 102 50)))))))
theorem forest1110_c1_ok : checkForestBounds checkLeaf1110 forest1110_c1 = true := by decide

def forest1110_c2 : CellForest :=
  (.node (.node (.node (.cell 5 5 (.split (.leaf 10 11 10 11 72 102 50) (.leaf 10 11 11 11 72 132 34) (.leaf 11 12 10 11 72 166 34) (.leaf 11 12 11 12 72 136 50))) (.cell 6 0 (.leaf 6 7 0 1 36 49 17))) (.node (.cell 6 1 (.leaf 6 7 1 2 36 68 17)) (.node (.cell 6 2 (.leaf 6 7 2 3 36 102 33)) (.cell 6 3 (.split (.leaf 12 13 6 7 72 102 17) (.leaf 12 13 7 8 72 100 34) (.leaf 13 14 6 7 72 100 34) (.leaf 13 14 7 8 72 100 50)))))) (.node (.node (.cell 6 4 (.split (.leaf 12 13 8 9 72 102 34) (.leaf 12 13 9 10 72 134 34) (.leaf 13 14 8 9 72 102 50) (.leaf 13 14 9 10 72 166 34))) (.cell 6 5 (.split (.leaf 12 13 10 11 72 136 34) (.leaf 12 13 11 12 72 166 51) (.leaf 13 14 10 11 72 136 50) (.leaf 13 14 11 12 72 170 34)))) (.node (.cell 6 6 (.split (.leaf 12 13 12 13 72 168 51) (.leaf 12 13 13 13 72 136 34) (.leaf 13 14 12 13 72 168 67) (.leaf 13 14 13 14 72 170 67))) (.node (.cell 7 0 (.leaf 7 8 0 1 36 34 17)) (.cell 7 1 (.leaf 7 8 1 2 36 68 17))))))
theorem forest1110_c2_ok : checkForestBounds checkLeaf1110 forest1110_c2 = true := by decide

def forest1110_c3 : CellForest :=
  (.node (.node (.node (.cell 7 2 (.leaf 7 8 2 3 36 166 17)) (.cell 7 3 (.split (.leaf 14 15 6 7 72 100 34) (.leaf 14 15 7 8 72 132 34) (.leaf 15 16 6 7 72 100 34) (.leaf 15 16 7 8 72 132 34)))) (.node (.cell 7 4 (.split (.leaf 14 15 8 9 72 102 50) (.leaf 14 15 9 10 72 166 34) (.leaf 15 16 8 9 72 134 34) (.leaf 15 16 9 10 72 136 34))) (.node (.cell 7 5 (.split (.leaf 14 15 10 11 72 166 51) (.leaf 14 15 11 12 72 168 51) (.leaf 15 16 10 11 72 136 51) (.leaf 15 16 11 12 72 170 50))) (.cell 7 6 (.split (.leaf 14 15 12 13 72 170 51) (.leaf 14 15 13 14 72 202 51) (.leaf 15 16 12 13 72 170 67) (.leaf 15 16 13 14 72 202 67)))))) (.node (.node (.cell 7 7 (.split (.leaf 14 15 14 15 72 204 51) (.leaf 14 15 15 15 72 168 51) (.leaf 15 16 14 15 72 202 68) (.leaf 15 16 15 16 72 204 68))) (.cell 8 0 (.leaf 8 9 0 1 36 34 17))) (.node (.cell 8 1 (.leaf 8 9 1 2 36 68 17)) (.node (.cell 8 2 (.leaf 8 9 2 3 36 102 33)) (.cell 8 3 (.split (.leaf 16 17 6 7 72 100 34) (.leaf 16 17 7 8 72 132 34) (.leaf 17 18 6 7 72 100 34) (.leaf 17 18 7 8 72 132 34)))))))
theorem forest1110_c3_ok : checkForestBounds checkLeaf1110 forest1110_c3 = true := by decide

def forest1110_c4 : CellForest :=
  (.node (.node (.node (.cell 8 4 (.split (.leaf 16 17 8 9 72 134 34) (.leaf 16 17 9 10 72 134 51) (.leaf 17 18 8 9 72 102 50) (.leaf 17 18 9 10 72 136 34))) (.cell 8 5 (.split (.leaf 16 17 10 11 72 136 51) (.leaf 16 17 11 12 72 168 67) (.leaf 17 18 10 11 72 166 51) (.leaf 17 18 11 12 72 168 51)))) (.node (.cell 8 6 (.split (.leaf 16 17 12 13 72 170 67) (.leaf 16 17 13 14 72 202 67) (.leaf 17 18 12 13 72 170 67) (.leaf 17 18 13 14 72 202 67))) (.node (.cell 8 7 (.split (.leaf 16 17 14 15 72 204 68) (.leaf 16 17 15 16 72 204 68) (.leaf 17 18 14 15 72 204 67) (.split (.leaf 34 35 30 31 144 170 51) (.leaf 34 35 31 32 144 168 68) (.leaf 35 36 30 31 144 170 51) (.leaf 35 36 31 32 144 170 67)))) (.cell 8 8 (.split (.split (.leaf 32 33 32 33 144 170 67) (.leaf 32 33 33 33 144 168 51) (.leaf 33 34 32 33 144 170 67) (.leaf 33 34 33 34 144 170 67)) (.leaf 16 17 17 17 72 170 67) (.split (.leaf 34 35 32 33 144 170 67) (.leaf 34 35 33 34 144 170 67) (.leaf 35 36 32 33 144 170 67) (.leaf 35 36 33 34 144 202 51)) (.split (.leaf 34 35 34 35 144 200 68) (.leaf 34 35 35 35 144 168 67) (.leaf 35 36 34 35 144 200 68) (.leaf 35 36 35 36 144 200 68))))))) (.node (.node (.cell 9 0 (.leaf 9 10 0 1 36 34 17)) (.cell 9 1 (.leaf 9 10 1 2 36 68 17))) (.node (.cell 9 2 (.leaf 9 10 2 3 36 100 34)) (.node (.cell 9 3 (.split (.leaf 18 19 6 7 72 100 34) (.leaf 18 19 7 8 72 100 50) (.leaf 19 20 6 7 72 100 33) (.leaf 19 20 7 8 72 100 50))) (.cell 9 4 (.split (.leaf 18 19 8 9 72 102 50) (.leaf 18 19 9 10 72 134 50) (.leaf 19 20 8 9 72 164 34) (.leaf 19 20 9 10 72 166 34)))))))
theorem forest1110_c4_ok : checkForestBounds checkLeaf1110 forest1110_c4 = true := by decide

def forest1110_c5 : CellForest :=
  (.node (.node (.node (.cell 9 5 (.split (.leaf 18 19 10 11 72 166 51) (.leaf 18 19 11 12 72 168 51) (.leaf 19 20 10 11 72 136 50) (.leaf 19 20 11 12 72 136 67))) (.cell 9 6 (.split (.leaf 18 19 12 13 72 168 68) (.leaf 18 19 13 14 72 170 68) (.leaf 19 20 12 13 72 168 67) (.leaf 19 20 13 14 72 202 51)))) (.node (.cell 9 7 (.split (.leaf 18 19 14 15 72 204 67) (.leaf 18 19 15 16 72 204 68) (.leaf 19 20 14 15 72 202 68) (.leaf 19 20 15 16 72 204 68))) (.node (.cell 9 8 (.split (.split (.leaf 36 37 32 33 144 170 67) (.leaf 36 37 33 34 144 200 68) (.leaf 37 38 32 33 144 170 67) (.leaf 37 38 33 34 144 200 68)) (.split (.leaf 36 37 34 35 144 200 68) (.leaf 36 37 35 36 144 170 68) (.leaf 37 38 34 35 144 200 68) (.leaf 37 38 35 36 144 170 68)) (.split (.leaf 38 39 32 33 144 170 67) (.leaf 38 39 33 34 144 202 51) (.leaf 39 40 32 33 144 168 68) (.leaf 39 40 33 34 144 170 67)) (.split (.leaf 38 39 34 35 144 200 68) (.leaf 38 39 35 36 144 200 68) (.leaf 39 40 34 35 144 200 68) (.leaf 39 40 35 36 144 200 68)))) (.cell 9 9 (.split (.split (.leaf 36 37 36 37 144 170 68) (.leaf 36 37 37 37 144 168 68) (.leaf 37 38 36 37 144 170 68) (.leaf 37 38 37 38 144 202 68)) (.leaf 18 19 19 19 72 170 68) (.split (.leaf 38 39 36 37 144 170 68) (.leaf 38 39 37 38 144 170 99) (.leaf 39 40 36 37 144 170 68) (.leaf 39 40 37 38 144 170 68)) (.split (.leaf 38 39 38 39 144 170 68) (.leaf 38 39 39 39 144 168 68) (.leaf 39 40 38 39 144 202 67) (.leaf 39 40 39 40 144 202 68))))))) (.node (.node (.cell 10 0 (.leaf 10 11 0 1 36 49 17)) (.cell 10 1 (.leaf 10 11 1 2 36 67 17))) (.node (.cell 10 2 (.leaf 10 11 2 3 36 100 33)) (.node (.cell 10 3 (.leaf 10 11 3 4 36 102 50)) (.cell 10 4 (.split (.leaf 20 21 8 9 72 132 34) (.leaf 20 21 9 10 72 134 34) (.leaf 21 22 8 9 72 100 50) (.leaf 21 22 9 10 72 164 34)))))))
theorem forest1110_c5_ok : checkForestBounds checkLeaf1110 forest1110_c5 = true := by decide

def forest1110_c6 : CellForest :=
  (.node (.node (.node (.cell 10 5 (.split (.leaf 20 21 10 11 72 134 51) (.leaf 20 21 11 12 72 166 51) (.leaf 21 22 10 11 72 166 34) (.leaf 21 22 11 12 72 134 51))) (.cell 10 6 (.split (.leaf 20 21 12 13 72 168 51) (.leaf 20 21 13 14 72 168 68) (.leaf 21 22 12 13 72 136 51) (.leaf 21 22 13 14 72 168 51)))) (.node (.cell 10 7 (.split (.leaf 20 21 14 15 72 200 68) (.leaf 20 21 15 16 72 202 68) (.leaf 21 22 14 15 72 168 68) (.leaf 21 22 15 16 72 200 68))) (.node (.cell 10 8 (.split (.leaf 20 21 16 17 72 204 68) (.split (.leaf 40 41 34 35 144 170 67) (.leaf 40 41 35 36 144 200 68) (.leaf 41 42 34 35 144 170 67) (.leaf 41 42 35 36 144 170 67)) (.leaf 21 22 16 17 72 202 68) (.leaf 21 22 17 18 72 204 68))) (.cell 10 9 (.split (.split (.leaf 40 41 36 37 144 170 68) (.leaf 40 41 37 38 144 170 68) (.leaf 41 42 36 37 144 200 68) (.leaf 41 42 37 38 144 200 68)) (.split (.leaf 40 41 38 39 144 170 68) (.leaf 40 41 39 40 144 170 68) (.leaf 41 42 38 39 144 170 68) (.leaf 41 42 39 40 144 170 68)) (.leaf 21 22 18 19 72 204 100) (.split (.leaf 42 43 38 39 144 200 68) (.leaf 42 43 39 40 144 170 68) (.leaf 43 44 38 39 144 200 68) (.leaf 43 44 39 40 144 200 68))))))) (.node (.node (.cell 10 10 (.split (.split (.leaf 40 41 40 41 144 170 68) (.leaf 40 41 41 41 144 168 68) (.leaf 41 42 40 41 144 170 68) (.leaf 41 42 41 42 144 170 68)) (.leaf 20 21 21 21 72 170 68) (.split (.leaf 42 43 40 41 144 170 68) (.leaf 42 43 41 42 144 170 68) (.leaf 43 44 40 41 144 200 68) (.leaf 43 44 41 42 144 170 68)) (.split (.leaf 42 43 42 43 144 170 68) (.leaf 42 43 43 43 144 168 68) (.leaf 43 44 42 43 144 170 68) (.leaf 43 44 43 44 144 200 68)))) (.cell 11 0 (.leaf 11 12 0 1 36 33 17))) (.node (.cell 11 1 (.leaf 11 12 1 2 36 66 17)) (.node (.cell 11 2 (.leaf 11 12 2 3 36 68 33)) (.cell 11 3 (.leaf 11 12 3 4 36 100 50))))))
theorem forest1110_c6_ok : checkForestBounds checkLeaf1110 forest1110_c6 = true := by decide

def forest1110_c7 : CellForest :=
  (.node (.node (.node (.cell 11 4 (.leaf 11 12 4 5 36 166 34)) (.cell 11 5 (.split (.leaf 22 23 10 11 72 102 50) (.leaf 22 23 11 12 72 166 34) (.leaf 23 24 10 11 72 100 50) (.leaf 23 24 11 12 72 164 34)))) (.node (.cell 11 6 (.split (.leaf 22 23 12 13 72 134 51) (.leaf 22 23 13 14 72 136 51) (.leaf 23 24 12 13 72 102 51) (.leaf 23 24 13 14 72 134 51))) (.cell 11 7 (.split (.leaf 22 23 14 15 72 168 51) (.leaf 22 23 15 16 72 170 51) (.leaf 23 24 14 15 72 134 67) (.leaf 23 24 15 16 72 136 67))))) (.node (.node (.cell 11 8 (.split (.leaf 22 23 16 17 72 200 68) (.leaf 22 23 17 18 72 170 99) (.leaf 23 24 16 17 72 136 68) (.leaf 23 24 17 18 72 170 51))) (.cell 11 9 (.split (.leaf 22 23 18 19 72 170 100) (.leaf 22 23 19 20 72 204 68) (.leaf 23 24 18 19 72 170 67) (.leaf 23 24 19 20 72 170 68)))) (.node (.cell 11 10 (.split (.leaf 22 23 20 21 72 170 102) (.leaf 22 23 21 22 72 204 100) (.leaf 23 24 20 21 72 202 68) (.leaf 23 24 21 22 72 170 100))) (.cell 11 11 (.split (.leaf 22 23 22 23 72 170 102) (.leaf 22 23 23 23 72 170 67) (.leaf 23 24 22 23 72 204 68) (.leaf 23 24 23 24 72 204 68))))))
theorem forest1110_c7_ok : checkForestBounds checkLeaf1110 forest1110_c7 = true := by decide

def forest1110 : CellForest := (.node (.node (.node forest1110_c0 forest1110_c1) (.node forest1110_c2 forest1110_c3)) (.node (.node forest1110_c4 forest1110_c5) (.node forest1110_c6 forest1110_c7)))
theorem forest1110_covers_bool : checkForestCoversAll forest1110 11 = true := by decide
theorem forest1110_bounds_bool : checkForestBounds checkLeaf1110 forest1110 = true := by
  simp only [forest1110, checkForestBounds, forest1110_c0_ok, forest1110_c1_ok, forest1110_c2_ok, forest1110_c3_ok, forest1110_c4_ok, forest1110_c5_ok, forest1110_c6_ok, forest1110_c7_ok]
  rfl

def forest1111_c0 : CellForest :=
  (.node (.node (.node (.node (.cell 0 0 (.leaf 0 1 0 1 36 17 0)) (.cell 1 0 (.leaf 1 2 0 1 36 17 0))) (.node (.cell 1 1 (.leaf 1 2 1 2 36 17 0)) (.node (.cell 2 0 (.leaf 2 3 0 1 36 17 0)) (.cell 2 1 (.leaf 2 3 1 2 36 17 0))))) (.node (.node (.cell 2 2 (.leaf 2 3 2 3 36 17 0)) (.cell 3 0 (.leaf 3 4 0 1 36 17 0))) (.node (.cell 3 1 (.leaf 3 4 1 2 36 17 0)) (.node (.cell 3 2 (.leaf 3 4 2 3 36 17 0)) (.cell 3 3 (.leaf 3 4 3 4 36 19 0)))))) (.node (.node (.node (.cell 4 0 (.leaf 4 5 0 1 36 17 0)) (.cell 4 1 (.leaf 4 5 1 2 36 17 0))) (.node (.cell 4 2 (.leaf 4 5 2 3 36 18 0)) (.node (.cell 4 3 (.leaf 4 5 3 4 36 35 0)) (.cell 4 4 (.leaf 4 5 4 5 36 52 0))))) (.node (.node (.cell 5 0 (.leaf 5 6 0 1 36 17 0)) (.cell 5 1 (.leaf 5 6 1 2 36 17 0))) (.node (.cell 5 2 (.leaf 5 6 2 3 36 49 0)) (.node (.cell 5 3 (.leaf 5 6 3 4 36 66 0)) (.cell 5 4 (.split (.leaf 10 11 8 9 72 34 0) (.leaf 10 11 9 10 72 50 0) (.leaf 11 12 8 9 72 35 0) (.leaf 11 12 9 10 72 66 0))))))))
theorem forest1111_c0_ok : checkForestBounds checkLeaf1111 forest1111_c0 = true := by decide

def forest1111_c1 : CellForest :=
  (.node (.node (.node (.node (.cell 5 5 (.split (.leaf 10 11 10 11 72 51 0) (.leaf 10 11 11 11 72 35 0) (.leaf 11 12 10 11 72 52 0) (.leaf 11 12 11 12 72 52 0))) (.cell 6 0 (.leaf 6 7 0 1 36 17 0))) (.node (.cell 6 1 (.leaf 6 7 1 2 36 17 0)) (.node (.cell 6 2 (.leaf 6 7 2 3 36 34 0)) (.cell 6 3 (.leaf 6 7 3 4 36 52 0))))) (.node (.node (.cell 6 4 (.split (.leaf 12 13 8 9 72 50 0) (.leaf 12 13 9 10 72 51 0) (.leaf 13 14 8 9 72 66 0) (.leaf 13 14 9 10 72 52 0))) (.cell 6 5 (.split (.leaf 12 13 10 11 72 52 0) (.leaf 12 13 11 12 72 68 0) (.leaf 13 14 10 11 72 68 0) (.leaf 13 14 11 12 72 68 0)))) (.node (.cell 6 6 (.split (.leaf 12 13 12 13 72 68 0) (.leaf 12 13 13 13 72 52 0) (.leaf 13 14 12 13 72 70 0) (.leaf 13 14 13 14 72 70 0))) (.node (.cell 7 0 (.leaf 7 8 0 1 36 17 0)) (.cell 7 1 (.leaf 7 8 1 2 36 17 0)))))) (.node (.node (.node (.cell 7 2 (.leaf 7 8 2 3 36 34 0)) (.cell 7 3 (.leaf 7 8 3 4 36 52 0))) (.node (.cell 7 4 (.split (.leaf 14 15 8 9 72 66 0) (.leaf 14 15 9 10 72 52 0) (.leaf 15 16 8 9 72 66 0) (.leaf 15 16 9 10 72 52 0))) (.node (.cell 7 5 (.split (.leaf 14 15 10 11 72 68 0) (.leaf 14 15 11 12 72 99 0) (.leaf 15 16 10 11 72 68 0) (.leaf 15 16 11 12 72 70 0))) (.cell 7 6 (.split (.leaf 14 15 12 13 72 70 0) (.leaf 14 15 13 14 72 70 0) (.leaf 15 16 12 13 72 70 0) (.leaf 15 16 13 14 72 72 0)))))) (.node (.node (.cell 7 7 (.split (.leaf 14 15 14 15 72 72 0) (.leaf 14 15 15 15 72 70 0) (.leaf 15 16 14 15 72 72 0) (.leaf 15 16 15 16 72 102 0))) (.cell 8 0 (.leaf 8 9 0 1 36 17 0))) (.node (.cell 8 1 (.leaf 8 9 1 2 36 17 0)) (.node (.cell 8 2 (.leaf 8 9 2 3 36 34 0)) (.cell 8 3 (.leaf 8 9 3 4 36 52 0)))))))
theorem forest1111_c1_ok : checkForestBounds checkLeaf1111 forest1111_c1 = true := by decide

def forest1111_c2 : CellForest :=
  (.node (.node (.node (.node (.cell 8 4 (.split (.leaf 16 17 8 9 72 66 0) (.leaf 16 17 9 10 72 52 0) (.leaf 17 18 8 9 72 66 0) (.leaf 17 18 9 10 72 52 0))) (.cell 8 5 (.split (.leaf 16 17 10 11 72 68 0) (.leaf 16 17 11 12 72 70 0) (.leaf 17 18 10 11 72 68 0) (.leaf 17 18 11 12 72 99 0)))) (.node (.cell 8 6 (.split (.leaf 16 17 12 13 72 70 0) (.leaf 16 17 13 14 72 72 0) (.leaf 17 18 12 13 72 70 0) (.leaf 17 18 13 14 72 72 0))) (.node (.cell 8 7 (.split (.leaf 16 17 14 15 72 72 0) (.leaf 16 17 15 16 72 102 0) (.leaf 17 18 14 15 72 132 0) (.leaf 17 18 15 16 72 102 0))) (.cell 8 8 (.split (.leaf 16 17 16 17 72 102 0) (.leaf 16 17 17 17 72 70 0) (.leaf 17 18 16 17 72 102 0) (.leaf 17 18 17 18 72 102 0)))))) (.node (.node (.cell 9 0 (.leaf 9 10 0 1 36 17 0)) (.cell 9 1 (.leaf 9 10 1 2 36 17 0))) (.node (.cell 9 2 (.leaf 9 10 2 3 36 34 0)) (.node (.cell 9 3 (.leaf 9 10 3 4 36 52 0)) (.cell 9 4 (.leaf 9 10 4 5 36 100 0)))))) (.node (.node (.node (.cell 9 5 (.split (.leaf 18 19 10 11 72 68 0) (.leaf 18 19 11 12 72 99 0) (.leaf 19 20 10 11 72 68 0) (.leaf 19 20 11 12 72 68 0))) (.cell 9 6 (.split (.leaf 18 19 12 13 72 70 0) (.leaf 18 19 13 14 72 163 0) (.leaf 19 20 12 13 72 70 0) (.leaf 19 20 13 14 72 100 0)))) (.node (.cell 9 7 (.split (.leaf 18 19 14 15 72 132 0) (.leaf 18 19 15 16 72 102 0) (.leaf 19 20 14 15 72 72 0) (.leaf 19 20 15 16 72 132 0))) (.node (.cell 9 8 (.split (.leaf 18 19 16 17 72 102 0) (.leaf 18 19 17 18 72 102 0) (.leaf 19 20 16 17 72 102 0) (.leaf 19 20 17 18 72 102 0))) (.cell 9 9 (.split (.leaf 18 19 18 19 72 104 0) (.leaf 18 19 19 19 72 72 0) (.leaf 19 20 18 19 72 104 0) (.leaf 19 20 19 20 72 104 0)))))) (.node (.node (.cell 10 0 (.leaf 10 11 0 1 36 17 0)) (.cell 10 1 (.leaf 10 11 1 2 36 17 0))) (.node (.cell 10 2 (.leaf 10 11 2 3 36 49 0)) (.node (.cell 10 3 (.leaf 10 11 3 4 36 66 0)) (.cell 10 4 (.leaf 10 11 4 5 36 68 0)))))))
theorem forest1111_c2_ok : checkForestBounds checkLeaf1111 forest1111_c2 = true := by decide

def forest1111_c3 : CellForest :=
  (.node (.node (.node (.node (.cell 10 5 (.leaf 10 11 5 6 36 163 0)) (.cell 10 6 (.split (.leaf 20 21 12 13 72 99 0) (.leaf 20 21 13 14 72 70 0) (.leaf 21 22 12 13 72 68 0) (.leaf 21 22 13 14 72 99 0)))) (.node (.cell 10 7 (.split (.leaf 20 21 14 15 72 100 0) (.leaf 20 21 15 16 72 72 0) (.leaf 21 22 14 15 72 70 0) (.leaf 21 22 15 16 72 100 0))) (.cell 10 8 (.split (.leaf 20 21 16 17 72 132 0) (.leaf 20 21 17 18 72 102 0) (.leaf 21 22 16 17 72 72 0) (.leaf 21 22 17 18 72 132 0))))) (.node (.node (.cell 10 9 (.split (.leaf 20 21 18 19 72 104 0) (.leaf 20 21 19 20 72 104 0) (.leaf 21 22 18 19 72 102 0) (.leaf 21 22 19 20 72 102 0))) (.cell 10 10 (.split (.leaf 20 21 20 21 72 104 0) (.leaf 20 21 21 21 72 72 0) (.leaf 21 22 20 21 72 102 0) (.leaf 21 22 21 22 72 102 0)))) (.node (.cell 11 0 (.leaf 11 12 0 1 36 17 0)) (.node (.cell 11 1 (.leaf 11 12 1 2 36 17 0)) (.cell 11 2 (.leaf 11 12 2 3 36 33 0)))))) (.node (.node (.node (.cell 11 3 (.leaf 11 12 3 4 36 35 0)) (.cell 11 4 (.leaf 11 12 4 5 36 52 0))) (.node (.cell 11 5 (.leaf 11 12 5 6 36 68 0)) (.cell 11 6 (.leaf 11 12 6 7 36 100 0)))) (.node (.node (.cell 11 7 (.leaf 11 12 7 8 36 102 0)) (.cell 11 8 (.leaf 11 12 8 9 36 104 0))) (.node (.cell 11 9 (.leaf 11 12 9 10 36 166 0)) (.node (.cell 11 10 (.leaf 11 12 10 11 36 166 0)) (.cell 11 11 (.leaf 11 12 11 12 36 106 0)))))))
theorem forest1111_c3_ok : checkForestBounds checkLeaf1111 forest1111_c3 = true := by decide

def forest1111 : CellForest := (.node (.node forest1111_c0 forest1111_c1) (.node forest1111_c2 forest1111_c3))
theorem forest1111_covers_bool : checkForestCoversAll forest1111 11 = true := by decide
theorem forest1111_bounds_bool : checkForestBounds checkLeaf1111 forest1111 = true := by
  simp only [forest1111, checkForestBounds, forest1111_c0_ok, forest1111_c1_ok, forest1111_c2_ok, forest1111_c3_ok]
  rfl

end ClawFreeEG.DyadicCaseBData
