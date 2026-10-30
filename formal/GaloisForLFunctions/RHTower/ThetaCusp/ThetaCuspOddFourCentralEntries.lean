import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspPairRadialValues
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspOddCentralTailPayment

/-!
# Moving central coordinates for the three-atom odd block

In the first-atom central coordinates `c = B(1/q) y` (`B` the corpus central basis), the radial
energy `Σ c_r c_s R^{ab}_{r+s+1}(q)` of each atom pair becomes `q⁻⁶ Σ y_i y_j N^{ab}_{ij}(q)` with
explicit integer-scaled numerator polynomials `N^{ab}_{ij}` of degree at most sixteen. These are the
entries certified piecewise on the seam and the bulk.
-/

open Polynomial
namespace RHTower.ThetaCuspOddFourCentralEntries
noncomputable section
open ThetaCuspOddCentralTail

theorem fin4_v0 : ((0 : Fin 4) : ℕ) = 0 := rfl
theorem fin4_v1 : ((1 : Fin 4) : ℕ) = 1 := rfl
theorem fin4_v2 : ((2 : Fin 4) : ℕ) = 2 := rfl
theorem fin4_v3 : ((3 : Fin 4) : ℕ) = 3 := rfl

theorem cB_00 (v : ℝ) : centralBasis v 0 0 = 1 := rfl

theorem cB_01 (v : ℝ) : centralBasis v 0 1 = 1-v/6 := rfl

theorem cB_02 (v : ℝ) : centralBasis v 0 2 = 5/4-5*v/12+v^2/12 := rfl

theorem cB_03 (v : ℝ) : centralBasis v 0 3 = 5/4-5*v/8+v^2/4-3*v^3/56 := rfl

theorem cB_10 (v : ℝ) : centralBasis v 1 0 = 0 := rfl

theorem cB_11 (v : ℝ) : centralBasis v 1 1 = -v/24 := rfl

theorem cB_12 (v : ℝ) : centralBasis v 1 2 = -5*v/48+5*v^2/192 := rfl

theorem cB_13 (v : ℝ) : centralBasis v 1 3 = -5*v/32+5*v^2/64-7*v^3/384 := rfl

theorem cB_20 (v : ℝ) : centralBasis v 2 0 = 0 := rfl

theorem cB_21 (v : ℝ) : centralBasis v 2 1 = 0 := rfl

theorem cB_22 (v : ℝ) : centralBasis v 2 2 = v^2/768 := rfl

theorem cB_23 (v : ℝ) : centralBasis v 2 3 = v^2/256-v^3/768 := rfl

theorem cB_30 (v : ℝ) : centralBasis v 3 0 = 0 := rfl

theorem cB_31 (v : ℝ) : centralBasis v 3 1 = 0 := rfl

theorem cB_32 (v : ℝ) : centralBasis v 3 2 = 0 := rfl

theorem cB_33 (v : ℝ) : centralBasis v 3 3 = -v^3/43008 := rfl

/-- Moving-frame numerator, pair `(11)`, entry `(0,0)`. -/
def centralNum11_00 (q : ℝ) : ℝ :=
  (120:ℝ)*q^7 + (-96:ℝ)*q^8 + (32:ℝ)*q^9

/-- Moving-frame numerator, pair `(11)`, entry `(0,1)`. -/
def centralNum11_01 (q : ℝ) : ℝ :=
  (-48:ℝ)*q^7

/-- Moving-frame numerator, pair `(11)`, entry `(0,2)`. -/
def centralNum11_02 (_q : ℝ) : ℝ :=
  0

/-- Moving-frame numerator, pair `(11)`, entry `(0,3)`. -/
def centralNum11_03 (_q : ℝ) : ℝ :=
  0

/-- Moving-frame numerator, pair `(11)`, entry `(1,1)`. -/
def centralNum11_11 (q : ℝ) : ℝ :=
  (-84:ℝ)*q^6 + (192:ℝ)*q^7 + (-80:ℝ)*q^8 + ((64:ℝ)/3)*q^9

/-- Moving-frame numerator, pair `(11)`, entry `(1,2)`. -/
def centralNum11_12 (q : ℝ) : ℝ :=
  (150:ℝ)*q^6 + (-120:ℝ)*q^7 + ((40:ℝ)/3)*q^8

/-- Moving-frame numerator, pair `(11)`, entry `(1,3)`. -/
def centralNum11_13 (q : ℝ) : ℝ :=
  (-60:ℝ)*q^6

/-- Moving-frame numerator, pair `(11)`, entry `(2,2)`. -/
def centralNum11_22 (q : ℝ) : ℝ :=
  (225:ℝ)*q^5 + (-750:ℝ)*q^6 + ((1480:ℝ)/3)*q^7 + ((-440:ℝ)/3)*q^8 + ((80:ℝ)/3)*q^9

/-- Moving-frame numerator, pair `(11)`, entry `(2,3)`. -/
def centralNum11_23 (q : ℝ) : ℝ :=
  ((-1125:ℝ)/2)*q^5 + (840:ℝ)*q^6 + (-290:ℝ)*q^7 + (40:ℝ)*q^8

/-- Moving-frame numerator, pair `(11)`, entry `(3,3)`. -/
def centralNum11_33 (q : ℝ) : ℝ :=
  ((-2475:ℝ)/4)*q^4 + ((5445:ℝ)/2)*q^5 + (-2415:ℝ)*q^6 + ((6030:ℝ)/7)*q^7 + ((-1320:ℝ)/7)*q^8 + ((160:ℝ)/7)*q^9

/-- Moving-frame numerator, pair `(12)`, entry `(0,0)`. -/
def centralNum12_00 (q : ℝ) : ℝ :=
  (300:ℝ)*q^7 + (-1356:ℝ)*q^8 + (1400:ℝ)*q^9 + (-576:ℝ)*q^10

/-- Moving-frame numerator, pair `(12)`, entry `(0,1)`. -/
def centralNum12_01 (q : ℝ) : ℝ :=
  (-1128:ℝ)*q^7 + (5544:ℝ)*q^8 + (-6870:ℝ)*q^9 + (3924:ℝ)*q^10 + (-864:ℝ)*q^11

/-- Moving-frame numerator, pair `(12)`, entry `(0,2)`. -/
def centralNum12_02 (q : ℝ) : ℝ :=
  (5580:ℝ)*q^7 + (-25380:ℝ)*q^8 + ((137475:ℝ)/4)*q^9 + ((-90045:ℝ)/4)*q^10 + ((15525:ℝ)/2)*q^11 + (-972:ℝ)*q^12

/-- Moving-frame numerator, pair `(12)`, entry `(0,3)`. -/
def centralNum12_03 (q : ℝ) : ℝ :=
  (-21060:ℝ)*q^7 + (89100:ℝ)*q^8 + ((-507195:ℝ)/4)*q^9 + ((362475:ℝ)/4)*q^10 + ((-2091015:ℝ)/56)*q^11 + ((223317:ℝ)/28)*q^12 + ((-4374:ℝ)/7)*q^13

/-- Moving-frame numerator, pair `(12)`, entry `(1,1)`. -/
def centralNum12_11 (q : ℝ) : ℝ :=
  (-714:ℝ)*q^6 + (12594:ℝ)*q^7 + (-46271:ℝ)*q^8 + ((174505:ℝ)/3)*q^9 + (-36063:ℝ)*q^10 + (11502:ℝ)*q^11 + (-1296:ℝ)*q^12

/-- Moving-frame numerator, pair `(12)`, entry `(1,2)`. -/
def centralNum12_12 (q : ℝ) : ℝ :=
  (9915:ℝ)*q^6 + (-111855:ℝ)*q^7 + ((2073245:ℝ)/6)*q^8 + ((-1749575:ℝ)/4)*q^9 + ((1160655:ℝ)/4)*q^10 + ((-884493:ℝ)/8)*q^11 + ((84807:ℝ)/4)*q^12 + (-1458:ℝ)*q^13

/-- Moving-frame numerator, pair `(12)`, entry `(1,3)`. -/
def centralNum12_13 (q : ℝ) : ℝ :=
  (-73590:ℝ)*q^6 + (642330:ℝ)*q^7 + (-1771575:ℝ)*q^8 + ((8907705:ℝ)/4)*q^9 + ((-24782625:ℝ)/16)*q^10 + ((73317609:ℝ)/112)*q^11 + ((-18122211:ℝ)/112)*q^12 + ((1130679:ℝ)/56)*q^13 + ((-6561:ℝ)/7)*q^14

/-- Moving-frame numerator, pair `(12)`, entry `(2,2)`. -/
def centralNum12_22 (q : ℝ) : ℝ :=
  ((14625:ℝ)/2)*q^5 + ((-454875:ℝ)/2)*q^6 + ((36704675:ℝ)/24)*q^7 + ((-92267125:ℝ)/24)*q^8 + ((110892625:ℝ)/24)*q^9 + ((-49904295:ℝ)/16)*q^10 + ((82019655:ℝ)/64)*q^11 + ((-19610019:ℝ)/64)*q^12 + ((1177335:ℝ)/32)*q^13 + ((-6561:ℝ)/4)*q^14

/-- Moving-frame numerator, pair `(12)`, entry `(2,3)`. -/
def centralNum12_23 (q : ℝ) : ℝ :=
  ((-548325:ℝ)/4)*q^5 + ((9671025:ℝ)/4)*q^6 + ((-49336925:ℝ)/4)*q^7 + ((54300275:ℝ)/2)*q^8 + ((-1001143275:ℝ)/32)*q^9 + ((342044865:ℝ)/16)*q^10 + ((-2078851041:ℝ)/224)*q^11 + ((284517279:ℝ)/112)*q^12 + ((-364343265:ℝ)/896)*q^13 + ((14952519:ℝ)/448)*q^14 + ((-59049:ℝ)/56)*q^15

/-- Moving-frame numerator, pair `(12)`, entry `(3,3)`. -/
def centralNum12_33 (q : ℝ) : ℝ :=
  ((-636075:ℝ)/8)*q^4 + ((28089225:ℝ)/8)*q^5 + ((-551415225:ℝ)/16)*q^6 + ((14817367125:ℝ)/112)*q^7 + ((-112645654125:ℝ)/448)*q^8 + ((121637026375:ℝ)/448)*q^9 + ((-23413184793:ℝ)/128)*q^10 + ((72789402681:ℝ)/896)*q^11 + ((-42884958573:ℝ)/1792)*q^12 + ((1150197975:ℝ)/256)*q^13 + ((-6268582791:ℝ)/12544)*q^14 + ((183229047:ℝ)/6272)*q^15 + ((-531441:ℝ)/784)*q^16

/-- Moving-frame numerator, pair `(13)`, entry `(0,0)`. -/
def centralNum13_00 (q : ℝ) : ℝ :=
  (600:ℝ)*q^7 + (-7776:ℝ)*q^8 + (16800:ℝ)*q^9 + (-9216:ℝ)*q^10

/-- Moving-frame numerator, pair `(13)`, entry `(0,1)`. -/
def centralNum13_01 (q : ℝ) : ℝ :=
  (-6288:ℝ)*q^7 + (81024:ℝ)*q^8 + (-238720:ℝ)*q^9 + (246784:ℝ)*q^10 + (-98304:ℝ)*q^11

/-- Moving-frame numerator, pair `(13)`, entry `(0,2)`. -/
def centralNum13_02 (q : ℝ) : ℝ :=
  (82080:ℝ)*q^7 + (-967680:ℝ)*q^8 + (3257600:ℝ)*q^9 + (-4474880:ℝ)*q^10 + (2908160:ℝ)*q^11 + (-786432:ℝ)*q^12

/-- Moving-frame numerator, pair `(13)`, entry `(0,3)`. -/
def centralNum13_03 (q : ℝ) : ℝ :=
  (-812160:ℝ)*q^7 + (8985600:ℝ)*q^8 + (-32225280:ℝ)*q^9 + (52019200:ℝ)*q^10 + ((-305233920:ℝ)/7)*q^11 + ((135528448:ℝ)/7)*q^12 + ((-25165824:ℝ)/7)*q^13

/-- Moving-frame numerator, pair `(13)`, entry `(1,1)`. -/
def centralNum13_11 (q : ℝ) : ℝ :=
  (-3444:ℝ)*q^6 + (162624:ℝ)*q^7 + (-1531216:ℝ)*q^8 + (4800960:ℝ)*q^9 + (-6350848:ℝ)*q^10 + ((12025856:ℝ)/3)*q^11 + (-1048576:ℝ)*q^12

/-- Moving-frame numerator, pair `(13)`, entry `(1,2)`. -/
def centralNum13_12 (q : ℝ) : ℝ :=
  (122790:ℝ)*q^6 + (-3586680:ℝ)*q^7 + (28529720:ℝ)*q^8 + (-90761600:ℝ)*q^9 + (137804800:ℝ)*q^10 + ((-332136448:ℝ)/3)*q^11 + ((141819904:ℝ)/3)*q^12 + (-8388608:ℝ)*q^13

/-- Moving-frame numerator, pair `(13)`, entry `(1,3)`. -/
def centralNum13_13 (q : ℝ) : ℝ :=
  (-2325540:ℝ)*q^6 + (52589280:ℝ)*q^7 + (-375655200:ℝ)*q^8 + (1192958720:ℝ)*q^9 + (-1965096960:ℝ)*q^10 + ((12857851904:ℝ)/7)*q^11 + ((-21171273728:ℝ)/21)*q^12 + ((914358272:ℝ)/3)*q^13 + ((-268435456:ℝ)/7)*q^14

/-- Moving-frame numerator, pair `(13)`, entry `(2,2)`. -/
def centralNum13_22 (q : ℝ) : ℝ :=
  (82125:ℝ)*q^5 + (-6663750:ℝ)*q^6 + (115666200:ℝ)*q^7 + (-750437000:ℝ)*q^8 + (2277262000:ℝ)*q^9 + (-3656824320:ℝ)*q^10 + (3359621120:ℝ)*q^11 + (-1817706496:ℝ)*q^12 + ((1625292800:ℝ)/3)*q^13 + (-67108864:ℝ)*q^14

/-- Moving-frame numerator, pair `(13)`, entry `(2,3)`. -/
def centralNum13_23 (q : ℝ) : ℝ :=
  ((-7627725:ℝ)/2)*q^5 + (173988600:ℝ)*q^6 + (-2299614450:ℝ)*q^7 + (13088188200:ℝ)*q^8 + (-38221499200:ℝ)*q^9 + (63366115840:ℝ)*q^10 + ((-445610508288:ℝ)/7)*q^11 + ((841540698112:ℝ)/21)*q^12 + ((-326820167680:ℝ)/21)*q^13 + ((10133438464:ℝ)/3)*q^14 + ((-2147483648:ℝ)/7)*q^15

/-- Moving-frame numerator, pair `(13)`, entry `(3,3)`. -/
def centralNum13_33 (q : ℝ) : ℝ :=
  ((-8120475:ℝ)/4)*q^4 + ((464861025:ℝ)/2)*q^5 + (-5906535975:ℝ)*q^6 + ((411904731750:ℝ)/7)*q^7 + ((-2024051769000:ℝ)/7)*q^8 + ((5554394637600:ℝ)/7)*q^9 + (-1314913862656:ℝ)*q^10 + ((9709155336192:ℝ)/7)*q^11 + ((-6724555112448:ℝ)/7)*q^12 + ((1313173667840:ℝ)/3)*q^13 + ((-6168244125696:ℝ)/49)*q^14 + ((3004329623552:ℝ)/147)*q^15 + ((-68719476736:ℝ)/49)*q^16

/-- Moving-frame numerator, pair `(23)`, entry `(0,0)`. -/
def centralNum23_00 (q : ℝ) : ℝ :=
  (780:ℝ)*q^7 + (-6156:ℝ)*q^8 + (15288:ℝ)*q^9 + (-14400:ℝ)*q^10

/-- Moving-frame numerator, pair `(23)`, entry `(0,1)`. -/
def centralNum23_01 (q : ℝ) : ℝ :=
  (-7368:ℝ)*q^7 + (59208:ℝ)*q^8 + (-155734:ℝ)*q^9 + (205300:ℝ)*q^10 + (-60000:ℝ)*q^11

/-- Moving-frame numerator, pair `(23)`, entry `(0,2)`. -/
def centralNum23_02 (q : ℝ) : ℝ :=
  (87660:ℝ)*q^7 + (-702180:ℝ)*q^8 + ((7421435:ℝ)/4)*q^9 + ((-10854125:ℝ)/4)*q^10 + ((2828125:ℝ)/2)*q^11 + (-187500:ℝ)*q^12

/-- Moving-frame numerator, pair `(23)`, entry `(0,3)`. -/
def centralNum23_03 (q : ℝ) : ℝ :=
  (-833220:ℝ)*q^7 + (6469740:ℝ)*q^8 + ((-68603955:ℝ)/4)*q^9 + ((104396875:ℝ)/4)*q^10 + ((-1001334375:ℝ)/56)*q^11 + ((125828125:ℝ)/28)*q^12 + ((-2343750:ℝ)/7)*q^13

/-- Moving-frame numerator, pair `(23)`, entry `(1,1)`. -/
def centralNum23_11 (q : ℝ) : ℝ :=
  (-4074:ℝ)*q^6 + (159906:ℝ)*q^7 + (-1104799:ℝ)*q^8 + (2801499:ℝ)*q^9 + (-3931375:ℝ)*q^10 + ((5896250:ℝ)/3)*q^11 + (-250000:ℝ)*q^12

/-- Moving-frame numerator, pair `(23)`, entry `(1,2)`. -/
def centralNum23_12 (q : ℝ) : ℝ :=
  (132555:ℝ)*q^6 + (-3252375:ℝ)*q^7 + ((39743695:ℝ)/2)*q^8 + ((-197111615:ℝ)/4)*q^9 + ((281947375:ℝ)/4)*q^10 + ((-1100234375:ℝ)/24)*q^11 + ((131828125:ℝ)/12)*q^12 + (-781250:ℝ)*q^13

/-- Moving-frame numerator, pair `(23)`, entry `(1,3)`. -/
def centralNum23_13 (q : ℝ) : ℝ :=
  (-2399070:ℝ)*q^6 + (45666930:ℝ)*q^7 + (-251781675:ℝ)*q^8 + ((2452738385:ℝ)/4)*q^9 + ((-14104310625:ℝ)/16)*q^10 + ((74345740625:ℝ)/112)*q^11 + ((-74899765625:ℝ)/336)*q^12 + ((5161328125:ℝ)/168)*q^13 + ((-9765625:ℝ)/7)*q^14

/-- Moving-frame numerator, pair `(23)`, entry `(2,2)`. -/
def centralNum23_22 (q : ℝ) : ℝ :=
  ((178425:ℝ)/2)*q^5 + ((-13176075:ℝ)/2)*q^6 + ((777815145:ℝ)/8)*q^7 + ((-3968389015:ℝ)/8)*q^8 + ((9393350195:ℝ)/8)*q^9 + ((-26366634375:ℝ)/16)*q^10 + ((77851609375:ℝ)/64)*q^11 + ((-25714921875:ℝ)/64)*q^12 + ((5236328125:ℝ)/96)*q^13 + ((-9765625:ℝ)/4)*q^14

/-- Moving-frame numerator, pair `(23)`, entry `(2,3)`. -/
def centralNum23_23 (q : ℝ) : ℝ :=
  ((-15801525:ℝ)/4)*q^5 + ((655493865:ℝ)/4)*q^6 + ((-7334421225:ℝ)/4)*q^7 + ((16442962485:ℝ)/2)*q^8 + ((-598626108395:ℝ)/32)*q^9 + ((414013307125:ℝ)/16)*q^10 + ((-4611984703125:ℝ)/224)*q^11 + ((399923828125:ℝ)/48)*q^12 + ((-4353201171875:ℝ)/2688)*q^13 + ((189736328125:ℝ)/1344)*q^14 + ((-244140625:ℝ)/56)*q^15

/-- Moving-frame numerator, pair `(23)`, entry `(3,3)`. -/
def centralNum23_33 (q : ℝ) : ℝ :=
  ((-16872075:ℝ)/8)*q^4 + ((1833754545:ℝ)/8)*q^5 + ((-83998007145:ℝ)/16)*q^6 + ((4929124002765:ℝ)/112)*q^7 + ((-76723155584685:ℝ)/448)*q^8 + ((164888745653055:ℝ)/448)*q^9 + ((-63358359907625:ℝ)/128)*q^10 + ((364713160040625:ℝ)/896)*q^11 + ((-334937462578125:ℝ)/1792)*q^12 + ((245466998046875:ℝ)/5376)*q^13 + ((-72144521484375:ℝ)/12544)*q^14 + ((6518798828125:ℝ)/18816)*q^15 + ((-6103515625:ℝ)/784)*q^16



theorem centralEntry11_00 {q : ℝ} (hq : q ≠ 0) :
    (∑ r : Fin 4, ∑ s : Fin 4, centralBasis (1/q) r 0 * centralBasis (1/q) s 0 *
      (thetaPairRadialEvenPolynomial (1*q^2) (r.val+s.val+1)).eval (2*q)) =
      centralNum11_00 q / q^6 := by
  simp only [Fin.sum_univ_four, Fin.isValue, fin4_v0, fin4_v1, fin4_v2, fin4_v3,
    Nat.reduceAdd, cB_00, cB_10, cB_20, cB_30, cB_00, cB_10, cB_20, cB_30, pairRadial_11_1, pairRadial_11_2, pairRadial_11_3, pairRadial_11_4,
    pairRadial_11_5, pairRadial_11_6, pairRadial_11_7]
  rw [eq_div_iff (pow_ne_zero 6 hq), centralNum11_00]
  field_simp
  ring

theorem centralEntry11_01 {q : ℝ} (hq : q ≠ 0) :
    (∑ r : Fin 4, ∑ s : Fin 4, centralBasis (1/q) r 0 * centralBasis (1/q) s 1 *
      (thetaPairRadialEvenPolynomial (1*q^2) (r.val+s.val+1)).eval (2*q)) =
      centralNum11_01 q / q^6 := by
  simp only [Fin.sum_univ_four, Fin.isValue, fin4_v0, fin4_v1, fin4_v2, fin4_v3,
    Nat.reduceAdd, cB_00, cB_10, cB_20, cB_30, cB_01, cB_11, cB_21, cB_31, pairRadial_11_1, pairRadial_11_2, pairRadial_11_3, pairRadial_11_4,
    pairRadial_11_5, pairRadial_11_6, pairRadial_11_7]
  rw [eq_div_iff (pow_ne_zero 6 hq), centralNum11_01]
  field_simp
  ring

theorem centralEntry11_02 {q : ℝ} (hq : q ≠ 0) :
    (∑ r : Fin 4, ∑ s : Fin 4, centralBasis (1/q) r 0 * centralBasis (1/q) s 2 *
      (thetaPairRadialEvenPolynomial (1*q^2) (r.val+s.val+1)).eval (2*q)) =
      centralNum11_02 q / q^6 := by
  simp only [Fin.sum_univ_four, Fin.isValue, fin4_v0, fin4_v1, fin4_v2, fin4_v3,
    Nat.reduceAdd, cB_00, cB_10, cB_20, cB_30, cB_02, cB_12, cB_22, cB_32, pairRadial_11_1, pairRadial_11_2, pairRadial_11_3, pairRadial_11_4,
    pairRadial_11_5, pairRadial_11_6, pairRadial_11_7]
  rw [eq_div_iff (pow_ne_zero 6 hq), centralNum11_02]
  field_simp
  ring

theorem centralEntry11_03 {q : ℝ} (hq : q ≠ 0) :
    (∑ r : Fin 4, ∑ s : Fin 4, centralBasis (1/q) r 0 * centralBasis (1/q) s 3 *
      (thetaPairRadialEvenPolynomial (1*q^2) (r.val+s.val+1)).eval (2*q)) =
      centralNum11_03 q / q^6 := by
  simp only [Fin.sum_univ_four, Fin.isValue, fin4_v0, fin4_v1, fin4_v2, fin4_v3,
    Nat.reduceAdd, cB_00, cB_10, cB_20, cB_30, cB_03, cB_13, cB_23, cB_33, pairRadial_11_1, pairRadial_11_2, pairRadial_11_3, pairRadial_11_4,
    pairRadial_11_5, pairRadial_11_6, pairRadial_11_7]
  rw [eq_div_iff (pow_ne_zero 6 hq), centralNum11_03]
  field_simp
  ring

theorem centralEntry11_10 {q : ℝ} (hq : q ≠ 0) :
    (∑ r : Fin 4, ∑ s : Fin 4, centralBasis (1/q) r 1 * centralBasis (1/q) s 0 *
      (thetaPairRadialEvenPolynomial (1*q^2) (r.val+s.val+1)).eval (2*q)) =
      centralNum11_01 q / q^6 := by
  simp only [Fin.sum_univ_four, Fin.isValue, fin4_v0, fin4_v1, fin4_v2, fin4_v3,
    Nat.reduceAdd, cB_01, cB_11, cB_21, cB_31, cB_00, cB_10, cB_20, cB_30, pairRadial_11_1, pairRadial_11_2, pairRadial_11_3, pairRadial_11_4,
    pairRadial_11_5, pairRadial_11_6, pairRadial_11_7]
  rw [eq_div_iff (pow_ne_zero 6 hq), centralNum11_01]
  field_simp
  ring

theorem centralEntry11_11 {q : ℝ} (hq : q ≠ 0) :
    (∑ r : Fin 4, ∑ s : Fin 4, centralBasis (1/q) r 1 * centralBasis (1/q) s 1 *
      (thetaPairRadialEvenPolynomial (1*q^2) (r.val+s.val+1)).eval (2*q)) =
      centralNum11_11 q / q^6 := by
  simp only [Fin.sum_univ_four, Fin.isValue, fin4_v0, fin4_v1, fin4_v2, fin4_v3,
    Nat.reduceAdd, cB_01, cB_11, cB_21, cB_31, cB_01, cB_11, cB_21, cB_31, pairRadial_11_1, pairRadial_11_2, pairRadial_11_3, pairRadial_11_4,
    pairRadial_11_5, pairRadial_11_6, pairRadial_11_7]
  rw [eq_div_iff (pow_ne_zero 6 hq), centralNum11_11]
  field_simp
  ring

theorem centralEntry11_12 {q : ℝ} (hq : q ≠ 0) :
    (∑ r : Fin 4, ∑ s : Fin 4, centralBasis (1/q) r 1 * centralBasis (1/q) s 2 *
      (thetaPairRadialEvenPolynomial (1*q^2) (r.val+s.val+1)).eval (2*q)) =
      centralNum11_12 q / q^6 := by
  simp only [Fin.sum_univ_four, Fin.isValue, fin4_v0, fin4_v1, fin4_v2, fin4_v3,
    Nat.reduceAdd, cB_01, cB_11, cB_21, cB_31, cB_02, cB_12, cB_22, cB_32, pairRadial_11_1, pairRadial_11_2, pairRadial_11_3, pairRadial_11_4,
    pairRadial_11_5, pairRadial_11_6, pairRadial_11_7]
  rw [eq_div_iff (pow_ne_zero 6 hq), centralNum11_12]
  field_simp
  ring

theorem centralEntry11_13 {q : ℝ} (hq : q ≠ 0) :
    (∑ r : Fin 4, ∑ s : Fin 4, centralBasis (1/q) r 1 * centralBasis (1/q) s 3 *
      (thetaPairRadialEvenPolynomial (1*q^2) (r.val+s.val+1)).eval (2*q)) =
      centralNum11_13 q / q^6 := by
  simp only [Fin.sum_univ_four, Fin.isValue, fin4_v0, fin4_v1, fin4_v2, fin4_v3,
    Nat.reduceAdd, cB_01, cB_11, cB_21, cB_31, cB_03, cB_13, cB_23, cB_33, pairRadial_11_1, pairRadial_11_2, pairRadial_11_3, pairRadial_11_4,
    pairRadial_11_5, pairRadial_11_6, pairRadial_11_7]
  rw [eq_div_iff (pow_ne_zero 6 hq), centralNum11_13]
  field_simp
  ring

theorem centralEntry11_20 {q : ℝ} (hq : q ≠ 0) :
    (∑ r : Fin 4, ∑ s : Fin 4, centralBasis (1/q) r 2 * centralBasis (1/q) s 0 *
      (thetaPairRadialEvenPolynomial (1*q^2) (r.val+s.val+1)).eval (2*q)) =
      centralNum11_02 q / q^6 := by
  simp only [Fin.sum_univ_four, Fin.isValue, fin4_v0, fin4_v1, fin4_v2, fin4_v3,
    Nat.reduceAdd, cB_02, cB_12, cB_22, cB_32, cB_00, cB_10, cB_20, cB_30, pairRadial_11_1, pairRadial_11_2, pairRadial_11_3, pairRadial_11_4,
    pairRadial_11_5, pairRadial_11_6, pairRadial_11_7]
  rw [eq_div_iff (pow_ne_zero 6 hq), centralNum11_02]
  field_simp
  ring

theorem centralEntry11_21 {q : ℝ} (hq : q ≠ 0) :
    (∑ r : Fin 4, ∑ s : Fin 4, centralBasis (1/q) r 2 * centralBasis (1/q) s 1 *
      (thetaPairRadialEvenPolynomial (1*q^2) (r.val+s.val+1)).eval (2*q)) =
      centralNum11_12 q / q^6 := by
  simp only [Fin.sum_univ_four, Fin.isValue, fin4_v0, fin4_v1, fin4_v2, fin4_v3,
    Nat.reduceAdd, cB_02, cB_12, cB_22, cB_32, cB_01, cB_11, cB_21, cB_31, pairRadial_11_1, pairRadial_11_2, pairRadial_11_3, pairRadial_11_4,
    pairRadial_11_5, pairRadial_11_6, pairRadial_11_7]
  rw [eq_div_iff (pow_ne_zero 6 hq), centralNum11_12]
  field_simp
  ring

theorem centralEntry11_22 {q : ℝ} (hq : q ≠ 0) :
    (∑ r : Fin 4, ∑ s : Fin 4, centralBasis (1/q) r 2 * centralBasis (1/q) s 2 *
      (thetaPairRadialEvenPolynomial (1*q^2) (r.val+s.val+1)).eval (2*q)) =
      centralNum11_22 q / q^6 := by
  simp only [Fin.sum_univ_four, Fin.isValue, fin4_v0, fin4_v1, fin4_v2, fin4_v3,
    Nat.reduceAdd, cB_02, cB_12, cB_22, cB_32, cB_02, cB_12, cB_22, cB_32, pairRadial_11_1, pairRadial_11_2, pairRadial_11_3, pairRadial_11_4,
    pairRadial_11_5, pairRadial_11_6, pairRadial_11_7]
  rw [eq_div_iff (pow_ne_zero 6 hq), centralNum11_22]
  field_simp
  ring

theorem centralEntry11_23 {q : ℝ} (hq : q ≠ 0) :
    (∑ r : Fin 4, ∑ s : Fin 4, centralBasis (1/q) r 2 * centralBasis (1/q) s 3 *
      (thetaPairRadialEvenPolynomial (1*q^2) (r.val+s.val+1)).eval (2*q)) =
      centralNum11_23 q / q^6 := by
  simp only [Fin.sum_univ_four, Fin.isValue, fin4_v0, fin4_v1, fin4_v2, fin4_v3,
    Nat.reduceAdd, cB_02, cB_12, cB_22, cB_32, cB_03, cB_13, cB_23, cB_33, pairRadial_11_1, pairRadial_11_2, pairRadial_11_3, pairRadial_11_4,
    pairRadial_11_5, pairRadial_11_6, pairRadial_11_7]
  rw [eq_div_iff (pow_ne_zero 6 hq), centralNum11_23]
  field_simp
  ring

theorem centralEntry11_30 {q : ℝ} (hq : q ≠ 0) :
    (∑ r : Fin 4, ∑ s : Fin 4, centralBasis (1/q) r 3 * centralBasis (1/q) s 0 *
      (thetaPairRadialEvenPolynomial (1*q^2) (r.val+s.val+1)).eval (2*q)) =
      centralNum11_03 q / q^6 := by
  simp only [Fin.sum_univ_four, Fin.isValue, fin4_v0, fin4_v1, fin4_v2, fin4_v3,
    Nat.reduceAdd, cB_03, cB_13, cB_23, cB_33, cB_00, cB_10, cB_20, cB_30, pairRadial_11_1, pairRadial_11_2, pairRadial_11_3, pairRadial_11_4,
    pairRadial_11_5, pairRadial_11_6, pairRadial_11_7]
  rw [eq_div_iff (pow_ne_zero 6 hq), centralNum11_03]
  field_simp
  ring

theorem centralEntry11_31 {q : ℝ} (hq : q ≠ 0) :
    (∑ r : Fin 4, ∑ s : Fin 4, centralBasis (1/q) r 3 * centralBasis (1/q) s 1 *
      (thetaPairRadialEvenPolynomial (1*q^2) (r.val+s.val+1)).eval (2*q)) =
      centralNum11_13 q / q^6 := by
  simp only [Fin.sum_univ_four, Fin.isValue, fin4_v0, fin4_v1, fin4_v2, fin4_v3,
    Nat.reduceAdd, cB_03, cB_13, cB_23, cB_33, cB_01, cB_11, cB_21, cB_31, pairRadial_11_1, pairRadial_11_2, pairRadial_11_3, pairRadial_11_4,
    pairRadial_11_5, pairRadial_11_6, pairRadial_11_7]
  rw [eq_div_iff (pow_ne_zero 6 hq), centralNum11_13]
  field_simp
  ring

theorem centralEntry11_32 {q : ℝ} (hq : q ≠ 0) :
    (∑ r : Fin 4, ∑ s : Fin 4, centralBasis (1/q) r 3 * centralBasis (1/q) s 2 *
      (thetaPairRadialEvenPolynomial (1*q^2) (r.val+s.val+1)).eval (2*q)) =
      centralNum11_23 q / q^6 := by
  simp only [Fin.sum_univ_four, Fin.isValue, fin4_v0, fin4_v1, fin4_v2, fin4_v3,
    Nat.reduceAdd, cB_03, cB_13, cB_23, cB_33, cB_02, cB_12, cB_22, cB_32, pairRadial_11_1, pairRadial_11_2, pairRadial_11_3, pairRadial_11_4,
    pairRadial_11_5, pairRadial_11_6, pairRadial_11_7]
  rw [eq_div_iff (pow_ne_zero 6 hq), centralNum11_23]
  field_simp
  ring

theorem centralEntry11_33 {q : ℝ} (hq : q ≠ 0) :
    (∑ r : Fin 4, ∑ s : Fin 4, centralBasis (1/q) r 3 * centralBasis (1/q) s 3 *
      (thetaPairRadialEvenPolynomial (1*q^2) (r.val+s.val+1)).eval (2*q)) =
      centralNum11_33 q / q^6 := by
  simp only [Fin.sum_univ_four, Fin.isValue, fin4_v0, fin4_v1, fin4_v2, fin4_v3,
    Nat.reduceAdd, cB_03, cB_13, cB_23, cB_33, cB_03, cB_13, cB_23, cB_33, pairRadial_11_1, pairRadial_11_2, pairRadial_11_3, pairRadial_11_4,
    pairRadial_11_5, pairRadial_11_6, pairRadial_11_7]
  rw [eq_div_iff (pow_ne_zero 6 hq), centralNum11_33]
  field_simp
  ring

theorem centralEntry12_00 {q : ℝ} (hq : q ≠ 0) :
    (∑ r : Fin 4, ∑ s : Fin 4, centralBasis (1/q) r 0 * centralBasis (1/q) s 0 *
      (thetaPairRadialEvenPolynomial (4*q^2) (r.val+s.val+1)).eval (5*q)) =
      centralNum12_00 q / q^6 := by
  simp only [Fin.sum_univ_four, Fin.isValue, fin4_v0, fin4_v1, fin4_v2, fin4_v3,
    Nat.reduceAdd, cB_00, cB_10, cB_20, cB_30, cB_00, cB_10, cB_20, cB_30, pairRadial_12_1, pairRadial_12_2, pairRadial_12_3, pairRadial_12_4,
    pairRadial_12_5, pairRadial_12_6, pairRadial_12_7]
  rw [eq_div_iff (pow_ne_zero 6 hq), centralNum12_00]
  field_simp
  ring

theorem centralEntry12_01 {q : ℝ} (hq : q ≠ 0) :
    (∑ r : Fin 4, ∑ s : Fin 4, centralBasis (1/q) r 0 * centralBasis (1/q) s 1 *
      (thetaPairRadialEvenPolynomial (4*q^2) (r.val+s.val+1)).eval (5*q)) =
      centralNum12_01 q / q^6 := by
  simp only [Fin.sum_univ_four, Fin.isValue, fin4_v0, fin4_v1, fin4_v2, fin4_v3,
    Nat.reduceAdd, cB_00, cB_10, cB_20, cB_30, cB_01, cB_11, cB_21, cB_31, pairRadial_12_1, pairRadial_12_2, pairRadial_12_3, pairRadial_12_4,
    pairRadial_12_5, pairRadial_12_6, pairRadial_12_7]
  rw [eq_div_iff (pow_ne_zero 6 hq), centralNum12_01]
  field_simp
  ring

theorem centralEntry12_02 {q : ℝ} (hq : q ≠ 0) :
    (∑ r : Fin 4, ∑ s : Fin 4, centralBasis (1/q) r 0 * centralBasis (1/q) s 2 *
      (thetaPairRadialEvenPolynomial (4*q^2) (r.val+s.val+1)).eval (5*q)) =
      centralNum12_02 q / q^6 := by
  simp only [Fin.sum_univ_four, Fin.isValue, fin4_v0, fin4_v1, fin4_v2, fin4_v3,
    Nat.reduceAdd, cB_00, cB_10, cB_20, cB_30, cB_02, cB_12, cB_22, cB_32, pairRadial_12_1, pairRadial_12_2, pairRadial_12_3, pairRadial_12_4,
    pairRadial_12_5, pairRadial_12_6, pairRadial_12_7]
  rw [eq_div_iff (pow_ne_zero 6 hq), centralNum12_02]
  field_simp
  ring

theorem centralEntry12_03 {q : ℝ} (hq : q ≠ 0) :
    (∑ r : Fin 4, ∑ s : Fin 4, centralBasis (1/q) r 0 * centralBasis (1/q) s 3 *
      (thetaPairRadialEvenPolynomial (4*q^2) (r.val+s.val+1)).eval (5*q)) =
      centralNum12_03 q / q^6 := by
  simp only [Fin.sum_univ_four, Fin.isValue, fin4_v0, fin4_v1, fin4_v2, fin4_v3,
    Nat.reduceAdd, cB_00, cB_10, cB_20, cB_30, cB_03, cB_13, cB_23, cB_33, pairRadial_12_1, pairRadial_12_2, pairRadial_12_3, pairRadial_12_4,
    pairRadial_12_5, pairRadial_12_6, pairRadial_12_7]
  rw [eq_div_iff (pow_ne_zero 6 hq), centralNum12_03]
  field_simp
  ring

theorem centralEntry12_10 {q : ℝ} (hq : q ≠ 0) :
    (∑ r : Fin 4, ∑ s : Fin 4, centralBasis (1/q) r 1 * centralBasis (1/q) s 0 *
      (thetaPairRadialEvenPolynomial (4*q^2) (r.val+s.val+1)).eval (5*q)) =
      centralNum12_01 q / q^6 := by
  simp only [Fin.sum_univ_four, Fin.isValue, fin4_v0, fin4_v1, fin4_v2, fin4_v3,
    Nat.reduceAdd, cB_01, cB_11, cB_21, cB_31, cB_00, cB_10, cB_20, cB_30, pairRadial_12_1, pairRadial_12_2, pairRadial_12_3, pairRadial_12_4,
    pairRadial_12_5, pairRadial_12_6, pairRadial_12_7]
  rw [eq_div_iff (pow_ne_zero 6 hq), centralNum12_01]
  field_simp
  ring

theorem centralEntry12_11 {q : ℝ} (hq : q ≠ 0) :
    (∑ r : Fin 4, ∑ s : Fin 4, centralBasis (1/q) r 1 * centralBasis (1/q) s 1 *
      (thetaPairRadialEvenPolynomial (4*q^2) (r.val+s.val+1)).eval (5*q)) =
      centralNum12_11 q / q^6 := by
  simp only [Fin.sum_univ_four, Fin.isValue, fin4_v0, fin4_v1, fin4_v2, fin4_v3,
    Nat.reduceAdd, cB_01, cB_11, cB_21, cB_31, cB_01, cB_11, cB_21, cB_31, pairRadial_12_1, pairRadial_12_2, pairRadial_12_3, pairRadial_12_4,
    pairRadial_12_5, pairRadial_12_6, pairRadial_12_7]
  rw [eq_div_iff (pow_ne_zero 6 hq), centralNum12_11]
  field_simp
  ring

theorem centralEntry12_12 {q : ℝ} (hq : q ≠ 0) :
    (∑ r : Fin 4, ∑ s : Fin 4, centralBasis (1/q) r 1 * centralBasis (1/q) s 2 *
      (thetaPairRadialEvenPolynomial (4*q^2) (r.val+s.val+1)).eval (5*q)) =
      centralNum12_12 q / q^6 := by
  simp only [Fin.sum_univ_four, Fin.isValue, fin4_v0, fin4_v1, fin4_v2, fin4_v3,
    Nat.reduceAdd, cB_01, cB_11, cB_21, cB_31, cB_02, cB_12, cB_22, cB_32, pairRadial_12_1, pairRadial_12_2, pairRadial_12_3, pairRadial_12_4,
    pairRadial_12_5, pairRadial_12_6, pairRadial_12_7]
  rw [eq_div_iff (pow_ne_zero 6 hq), centralNum12_12]
  field_simp
  ring

theorem centralEntry12_13 {q : ℝ} (hq : q ≠ 0) :
    (∑ r : Fin 4, ∑ s : Fin 4, centralBasis (1/q) r 1 * centralBasis (1/q) s 3 *
      (thetaPairRadialEvenPolynomial (4*q^2) (r.val+s.val+1)).eval (5*q)) =
      centralNum12_13 q / q^6 := by
  simp only [Fin.sum_univ_four, Fin.isValue, fin4_v0, fin4_v1, fin4_v2, fin4_v3,
    Nat.reduceAdd, cB_01, cB_11, cB_21, cB_31, cB_03, cB_13, cB_23, cB_33, pairRadial_12_1, pairRadial_12_2, pairRadial_12_3, pairRadial_12_4,
    pairRadial_12_5, pairRadial_12_6, pairRadial_12_7]
  rw [eq_div_iff (pow_ne_zero 6 hq), centralNum12_13]
  field_simp
  ring

theorem centralEntry12_20 {q : ℝ} (hq : q ≠ 0) :
    (∑ r : Fin 4, ∑ s : Fin 4, centralBasis (1/q) r 2 * centralBasis (1/q) s 0 *
      (thetaPairRadialEvenPolynomial (4*q^2) (r.val+s.val+1)).eval (5*q)) =
      centralNum12_02 q / q^6 := by
  simp only [Fin.sum_univ_four, Fin.isValue, fin4_v0, fin4_v1, fin4_v2, fin4_v3,
    Nat.reduceAdd, cB_02, cB_12, cB_22, cB_32, cB_00, cB_10, cB_20, cB_30, pairRadial_12_1, pairRadial_12_2, pairRadial_12_3, pairRadial_12_4,
    pairRadial_12_5, pairRadial_12_6, pairRadial_12_7]
  rw [eq_div_iff (pow_ne_zero 6 hq), centralNum12_02]
  field_simp
  ring

theorem centralEntry12_21 {q : ℝ} (hq : q ≠ 0) :
    (∑ r : Fin 4, ∑ s : Fin 4, centralBasis (1/q) r 2 * centralBasis (1/q) s 1 *
      (thetaPairRadialEvenPolynomial (4*q^2) (r.val+s.val+1)).eval (5*q)) =
      centralNum12_12 q / q^6 := by
  simp only [Fin.sum_univ_four, Fin.isValue, fin4_v0, fin4_v1, fin4_v2, fin4_v3,
    Nat.reduceAdd, cB_02, cB_12, cB_22, cB_32, cB_01, cB_11, cB_21, cB_31, pairRadial_12_1, pairRadial_12_2, pairRadial_12_3, pairRadial_12_4,
    pairRadial_12_5, pairRadial_12_6, pairRadial_12_7]
  rw [eq_div_iff (pow_ne_zero 6 hq), centralNum12_12]
  field_simp
  ring

theorem centralEntry12_22 {q : ℝ} (hq : q ≠ 0) :
    (∑ r : Fin 4, ∑ s : Fin 4, centralBasis (1/q) r 2 * centralBasis (1/q) s 2 *
      (thetaPairRadialEvenPolynomial (4*q^2) (r.val+s.val+1)).eval (5*q)) =
      centralNum12_22 q / q^6 := by
  simp only [Fin.sum_univ_four, Fin.isValue, fin4_v0, fin4_v1, fin4_v2, fin4_v3,
    Nat.reduceAdd, cB_02, cB_12, cB_22, cB_32, cB_02, cB_12, cB_22, cB_32, pairRadial_12_1, pairRadial_12_2, pairRadial_12_3, pairRadial_12_4,
    pairRadial_12_5, pairRadial_12_6, pairRadial_12_7]
  rw [eq_div_iff (pow_ne_zero 6 hq), centralNum12_22]
  field_simp
  ring

theorem centralEntry12_23 {q : ℝ} (hq : q ≠ 0) :
    (∑ r : Fin 4, ∑ s : Fin 4, centralBasis (1/q) r 2 * centralBasis (1/q) s 3 *
      (thetaPairRadialEvenPolynomial (4*q^2) (r.val+s.val+1)).eval (5*q)) =
      centralNum12_23 q / q^6 := by
  simp only [Fin.sum_univ_four, Fin.isValue, fin4_v0, fin4_v1, fin4_v2, fin4_v3,
    Nat.reduceAdd, cB_02, cB_12, cB_22, cB_32, cB_03, cB_13, cB_23, cB_33, pairRadial_12_1, pairRadial_12_2, pairRadial_12_3, pairRadial_12_4,
    pairRadial_12_5, pairRadial_12_6, pairRadial_12_7]
  rw [eq_div_iff (pow_ne_zero 6 hq), centralNum12_23]
  field_simp
  ring

theorem centralEntry12_30 {q : ℝ} (hq : q ≠ 0) :
    (∑ r : Fin 4, ∑ s : Fin 4, centralBasis (1/q) r 3 * centralBasis (1/q) s 0 *
      (thetaPairRadialEvenPolynomial (4*q^2) (r.val+s.val+1)).eval (5*q)) =
      centralNum12_03 q / q^6 := by
  simp only [Fin.sum_univ_four, Fin.isValue, fin4_v0, fin4_v1, fin4_v2, fin4_v3,
    Nat.reduceAdd, cB_03, cB_13, cB_23, cB_33, cB_00, cB_10, cB_20, cB_30, pairRadial_12_1, pairRadial_12_2, pairRadial_12_3, pairRadial_12_4,
    pairRadial_12_5, pairRadial_12_6, pairRadial_12_7]
  rw [eq_div_iff (pow_ne_zero 6 hq), centralNum12_03]
  field_simp
  ring

theorem centralEntry12_31 {q : ℝ} (hq : q ≠ 0) :
    (∑ r : Fin 4, ∑ s : Fin 4, centralBasis (1/q) r 3 * centralBasis (1/q) s 1 *
      (thetaPairRadialEvenPolynomial (4*q^2) (r.val+s.val+1)).eval (5*q)) =
      centralNum12_13 q / q^6 := by
  simp only [Fin.sum_univ_four, Fin.isValue, fin4_v0, fin4_v1, fin4_v2, fin4_v3,
    Nat.reduceAdd, cB_03, cB_13, cB_23, cB_33, cB_01, cB_11, cB_21, cB_31, pairRadial_12_1, pairRadial_12_2, pairRadial_12_3, pairRadial_12_4,
    pairRadial_12_5, pairRadial_12_6, pairRadial_12_7]
  rw [eq_div_iff (pow_ne_zero 6 hq), centralNum12_13]
  field_simp
  ring

theorem centralEntry12_32 {q : ℝ} (hq : q ≠ 0) :
    (∑ r : Fin 4, ∑ s : Fin 4, centralBasis (1/q) r 3 * centralBasis (1/q) s 2 *
      (thetaPairRadialEvenPolynomial (4*q^2) (r.val+s.val+1)).eval (5*q)) =
      centralNum12_23 q / q^6 := by
  simp only [Fin.sum_univ_four, Fin.isValue, fin4_v0, fin4_v1, fin4_v2, fin4_v3,
    Nat.reduceAdd, cB_03, cB_13, cB_23, cB_33, cB_02, cB_12, cB_22, cB_32, pairRadial_12_1, pairRadial_12_2, pairRadial_12_3, pairRadial_12_4,
    pairRadial_12_5, pairRadial_12_6, pairRadial_12_7]
  rw [eq_div_iff (pow_ne_zero 6 hq), centralNum12_23]
  field_simp
  ring

theorem centralEntry12_33 {q : ℝ} (hq : q ≠ 0) :
    (∑ r : Fin 4, ∑ s : Fin 4, centralBasis (1/q) r 3 * centralBasis (1/q) s 3 *
      (thetaPairRadialEvenPolynomial (4*q^2) (r.val+s.val+1)).eval (5*q)) =
      centralNum12_33 q / q^6 := by
  simp only [Fin.sum_univ_four, Fin.isValue, fin4_v0, fin4_v1, fin4_v2, fin4_v3,
    Nat.reduceAdd, cB_03, cB_13, cB_23, cB_33, cB_03, cB_13, cB_23, cB_33, pairRadial_12_1, pairRadial_12_2, pairRadial_12_3, pairRadial_12_4,
    pairRadial_12_5, pairRadial_12_6, pairRadial_12_7]
  rw [eq_div_iff (pow_ne_zero 6 hq), centralNum12_33]
  field_simp
  ring

theorem centralEntry13_00 {q : ℝ} (hq : q ≠ 0) :
    (∑ r : Fin 4, ∑ s : Fin 4, centralBasis (1/q) r 0 * centralBasis (1/q) s 0 *
      (thetaPairRadialEvenPolynomial (9*q^2) (r.val+s.val+1)).eval (10*q)) =
      centralNum13_00 q / q^6 := by
  simp only [Fin.sum_univ_four, Fin.isValue, fin4_v0, fin4_v1, fin4_v2, fin4_v3,
    Nat.reduceAdd, cB_00, cB_10, cB_20, cB_30, cB_00, cB_10, cB_20, cB_30, pairRadial_13_1, pairRadial_13_2, pairRadial_13_3, pairRadial_13_4,
    pairRadial_13_5, pairRadial_13_6, pairRadial_13_7]
  rw [eq_div_iff (pow_ne_zero 6 hq), centralNum13_00]
  field_simp
  ring

theorem centralEntry13_01 {q : ℝ} (hq : q ≠ 0) :
    (∑ r : Fin 4, ∑ s : Fin 4, centralBasis (1/q) r 0 * centralBasis (1/q) s 1 *
      (thetaPairRadialEvenPolynomial (9*q^2) (r.val+s.val+1)).eval (10*q)) =
      centralNum13_01 q / q^6 := by
  simp only [Fin.sum_univ_four, Fin.isValue, fin4_v0, fin4_v1, fin4_v2, fin4_v3,
    Nat.reduceAdd, cB_00, cB_10, cB_20, cB_30, cB_01, cB_11, cB_21, cB_31, pairRadial_13_1, pairRadial_13_2, pairRadial_13_3, pairRadial_13_4,
    pairRadial_13_5, pairRadial_13_6, pairRadial_13_7]
  rw [eq_div_iff (pow_ne_zero 6 hq), centralNum13_01]
  field_simp
  ring

theorem centralEntry13_02 {q : ℝ} (hq : q ≠ 0) :
    (∑ r : Fin 4, ∑ s : Fin 4, centralBasis (1/q) r 0 * centralBasis (1/q) s 2 *
      (thetaPairRadialEvenPolynomial (9*q^2) (r.val+s.val+1)).eval (10*q)) =
      centralNum13_02 q / q^6 := by
  simp only [Fin.sum_univ_four, Fin.isValue, fin4_v0, fin4_v1, fin4_v2, fin4_v3,
    Nat.reduceAdd, cB_00, cB_10, cB_20, cB_30, cB_02, cB_12, cB_22, cB_32, pairRadial_13_1, pairRadial_13_2, pairRadial_13_3, pairRadial_13_4,
    pairRadial_13_5, pairRadial_13_6, pairRadial_13_7]
  rw [eq_div_iff (pow_ne_zero 6 hq), centralNum13_02]
  field_simp
  ring

theorem centralEntry13_03 {q : ℝ} (hq : q ≠ 0) :
    (∑ r : Fin 4, ∑ s : Fin 4, centralBasis (1/q) r 0 * centralBasis (1/q) s 3 *
      (thetaPairRadialEvenPolynomial (9*q^2) (r.val+s.val+1)).eval (10*q)) =
      centralNum13_03 q / q^6 := by
  simp only [Fin.sum_univ_four, Fin.isValue, fin4_v0, fin4_v1, fin4_v2, fin4_v3,
    Nat.reduceAdd, cB_00, cB_10, cB_20, cB_30, cB_03, cB_13, cB_23, cB_33, pairRadial_13_1, pairRadial_13_2, pairRadial_13_3, pairRadial_13_4,
    pairRadial_13_5, pairRadial_13_6, pairRadial_13_7]
  rw [eq_div_iff (pow_ne_zero 6 hq), centralNum13_03]
  field_simp
  ring

theorem centralEntry13_10 {q : ℝ} (hq : q ≠ 0) :
    (∑ r : Fin 4, ∑ s : Fin 4, centralBasis (1/q) r 1 * centralBasis (1/q) s 0 *
      (thetaPairRadialEvenPolynomial (9*q^2) (r.val+s.val+1)).eval (10*q)) =
      centralNum13_01 q / q^6 := by
  simp only [Fin.sum_univ_four, Fin.isValue, fin4_v0, fin4_v1, fin4_v2, fin4_v3,
    Nat.reduceAdd, cB_01, cB_11, cB_21, cB_31, cB_00, cB_10, cB_20, cB_30, pairRadial_13_1, pairRadial_13_2, pairRadial_13_3, pairRadial_13_4,
    pairRadial_13_5, pairRadial_13_6, pairRadial_13_7]
  rw [eq_div_iff (pow_ne_zero 6 hq), centralNum13_01]
  field_simp
  ring

theorem centralEntry13_11 {q : ℝ} (hq : q ≠ 0) :
    (∑ r : Fin 4, ∑ s : Fin 4, centralBasis (1/q) r 1 * centralBasis (1/q) s 1 *
      (thetaPairRadialEvenPolynomial (9*q^2) (r.val+s.val+1)).eval (10*q)) =
      centralNum13_11 q / q^6 := by
  simp only [Fin.sum_univ_four, Fin.isValue, fin4_v0, fin4_v1, fin4_v2, fin4_v3,
    Nat.reduceAdd, cB_01, cB_11, cB_21, cB_31, cB_01, cB_11, cB_21, cB_31, pairRadial_13_1, pairRadial_13_2, pairRadial_13_3, pairRadial_13_4,
    pairRadial_13_5, pairRadial_13_6, pairRadial_13_7]
  rw [eq_div_iff (pow_ne_zero 6 hq), centralNum13_11]
  field_simp
  ring

theorem centralEntry13_12 {q : ℝ} (hq : q ≠ 0) :
    (∑ r : Fin 4, ∑ s : Fin 4, centralBasis (1/q) r 1 * centralBasis (1/q) s 2 *
      (thetaPairRadialEvenPolynomial (9*q^2) (r.val+s.val+1)).eval (10*q)) =
      centralNum13_12 q / q^6 := by
  simp only [Fin.sum_univ_four, Fin.isValue, fin4_v0, fin4_v1, fin4_v2, fin4_v3,
    Nat.reduceAdd, cB_01, cB_11, cB_21, cB_31, cB_02, cB_12, cB_22, cB_32, pairRadial_13_1, pairRadial_13_2, pairRadial_13_3, pairRadial_13_4,
    pairRadial_13_5, pairRadial_13_6, pairRadial_13_7]
  rw [eq_div_iff (pow_ne_zero 6 hq), centralNum13_12]
  field_simp
  ring

theorem centralEntry13_13 {q : ℝ} (hq : q ≠ 0) :
    (∑ r : Fin 4, ∑ s : Fin 4, centralBasis (1/q) r 1 * centralBasis (1/q) s 3 *
      (thetaPairRadialEvenPolynomial (9*q^2) (r.val+s.val+1)).eval (10*q)) =
      centralNum13_13 q / q^6 := by
  simp only [Fin.sum_univ_four, Fin.isValue, fin4_v0, fin4_v1, fin4_v2, fin4_v3,
    Nat.reduceAdd, cB_01, cB_11, cB_21, cB_31, cB_03, cB_13, cB_23, cB_33, pairRadial_13_1, pairRadial_13_2, pairRadial_13_3, pairRadial_13_4,
    pairRadial_13_5, pairRadial_13_6, pairRadial_13_7]
  rw [eq_div_iff (pow_ne_zero 6 hq), centralNum13_13]
  field_simp
  ring

theorem centralEntry13_20 {q : ℝ} (hq : q ≠ 0) :
    (∑ r : Fin 4, ∑ s : Fin 4, centralBasis (1/q) r 2 * centralBasis (1/q) s 0 *
      (thetaPairRadialEvenPolynomial (9*q^2) (r.val+s.val+1)).eval (10*q)) =
      centralNum13_02 q / q^6 := by
  simp only [Fin.sum_univ_four, Fin.isValue, fin4_v0, fin4_v1, fin4_v2, fin4_v3,
    Nat.reduceAdd, cB_02, cB_12, cB_22, cB_32, cB_00, cB_10, cB_20, cB_30, pairRadial_13_1, pairRadial_13_2, pairRadial_13_3, pairRadial_13_4,
    pairRadial_13_5, pairRadial_13_6, pairRadial_13_7]
  rw [eq_div_iff (pow_ne_zero 6 hq), centralNum13_02]
  field_simp
  ring

theorem centralEntry13_21 {q : ℝ} (hq : q ≠ 0) :
    (∑ r : Fin 4, ∑ s : Fin 4, centralBasis (1/q) r 2 * centralBasis (1/q) s 1 *
      (thetaPairRadialEvenPolynomial (9*q^2) (r.val+s.val+1)).eval (10*q)) =
      centralNum13_12 q / q^6 := by
  simp only [Fin.sum_univ_four, Fin.isValue, fin4_v0, fin4_v1, fin4_v2, fin4_v3,
    Nat.reduceAdd, cB_02, cB_12, cB_22, cB_32, cB_01, cB_11, cB_21, cB_31, pairRadial_13_1, pairRadial_13_2, pairRadial_13_3, pairRadial_13_4,
    pairRadial_13_5, pairRadial_13_6, pairRadial_13_7]
  rw [eq_div_iff (pow_ne_zero 6 hq), centralNum13_12]
  field_simp
  ring

theorem centralEntry13_22 {q : ℝ} (hq : q ≠ 0) :
    (∑ r : Fin 4, ∑ s : Fin 4, centralBasis (1/q) r 2 * centralBasis (1/q) s 2 *
      (thetaPairRadialEvenPolynomial (9*q^2) (r.val+s.val+1)).eval (10*q)) =
      centralNum13_22 q / q^6 := by
  simp only [Fin.sum_univ_four, Fin.isValue, fin4_v0, fin4_v1, fin4_v2, fin4_v3,
    Nat.reduceAdd, cB_02, cB_12, cB_22, cB_32, cB_02, cB_12, cB_22, cB_32, pairRadial_13_1, pairRadial_13_2, pairRadial_13_3, pairRadial_13_4,
    pairRadial_13_5, pairRadial_13_6, pairRadial_13_7]
  rw [eq_div_iff (pow_ne_zero 6 hq), centralNum13_22]
  field_simp
  ring

theorem centralEntry13_23 {q : ℝ} (hq : q ≠ 0) :
    (∑ r : Fin 4, ∑ s : Fin 4, centralBasis (1/q) r 2 * centralBasis (1/q) s 3 *
      (thetaPairRadialEvenPolynomial (9*q^2) (r.val+s.val+1)).eval (10*q)) =
      centralNum13_23 q / q^6 := by
  simp only [Fin.sum_univ_four, Fin.isValue, fin4_v0, fin4_v1, fin4_v2, fin4_v3,
    Nat.reduceAdd, cB_02, cB_12, cB_22, cB_32, cB_03, cB_13, cB_23, cB_33, pairRadial_13_1, pairRadial_13_2, pairRadial_13_3, pairRadial_13_4,
    pairRadial_13_5, pairRadial_13_6, pairRadial_13_7]
  rw [eq_div_iff (pow_ne_zero 6 hq), centralNum13_23]
  field_simp
  ring

theorem centralEntry13_30 {q : ℝ} (hq : q ≠ 0) :
    (∑ r : Fin 4, ∑ s : Fin 4, centralBasis (1/q) r 3 * centralBasis (1/q) s 0 *
      (thetaPairRadialEvenPolynomial (9*q^2) (r.val+s.val+1)).eval (10*q)) =
      centralNum13_03 q / q^6 := by
  simp only [Fin.sum_univ_four, Fin.isValue, fin4_v0, fin4_v1, fin4_v2, fin4_v3,
    Nat.reduceAdd, cB_03, cB_13, cB_23, cB_33, cB_00, cB_10, cB_20, cB_30, pairRadial_13_1, pairRadial_13_2, pairRadial_13_3, pairRadial_13_4,
    pairRadial_13_5, pairRadial_13_6, pairRadial_13_7]
  rw [eq_div_iff (pow_ne_zero 6 hq), centralNum13_03]
  field_simp
  ring

theorem centralEntry13_31 {q : ℝ} (hq : q ≠ 0) :
    (∑ r : Fin 4, ∑ s : Fin 4, centralBasis (1/q) r 3 * centralBasis (1/q) s 1 *
      (thetaPairRadialEvenPolynomial (9*q^2) (r.val+s.val+1)).eval (10*q)) =
      centralNum13_13 q / q^6 := by
  simp only [Fin.sum_univ_four, Fin.isValue, fin4_v0, fin4_v1, fin4_v2, fin4_v3,
    Nat.reduceAdd, cB_03, cB_13, cB_23, cB_33, cB_01, cB_11, cB_21, cB_31, pairRadial_13_1, pairRadial_13_2, pairRadial_13_3, pairRadial_13_4,
    pairRadial_13_5, pairRadial_13_6, pairRadial_13_7]
  rw [eq_div_iff (pow_ne_zero 6 hq), centralNum13_13]
  field_simp
  ring

theorem centralEntry13_32 {q : ℝ} (hq : q ≠ 0) :
    (∑ r : Fin 4, ∑ s : Fin 4, centralBasis (1/q) r 3 * centralBasis (1/q) s 2 *
      (thetaPairRadialEvenPolynomial (9*q^2) (r.val+s.val+1)).eval (10*q)) =
      centralNum13_23 q / q^6 := by
  simp only [Fin.sum_univ_four, Fin.isValue, fin4_v0, fin4_v1, fin4_v2, fin4_v3,
    Nat.reduceAdd, cB_03, cB_13, cB_23, cB_33, cB_02, cB_12, cB_22, cB_32, pairRadial_13_1, pairRadial_13_2, pairRadial_13_3, pairRadial_13_4,
    pairRadial_13_5, pairRadial_13_6, pairRadial_13_7]
  rw [eq_div_iff (pow_ne_zero 6 hq), centralNum13_23]
  field_simp
  ring

theorem centralEntry13_33 {q : ℝ} (hq : q ≠ 0) :
    (∑ r : Fin 4, ∑ s : Fin 4, centralBasis (1/q) r 3 * centralBasis (1/q) s 3 *
      (thetaPairRadialEvenPolynomial (9*q^2) (r.val+s.val+1)).eval (10*q)) =
      centralNum13_33 q / q^6 := by
  simp only [Fin.sum_univ_four, Fin.isValue, fin4_v0, fin4_v1, fin4_v2, fin4_v3,
    Nat.reduceAdd, cB_03, cB_13, cB_23, cB_33, cB_03, cB_13, cB_23, cB_33, pairRadial_13_1, pairRadial_13_2, pairRadial_13_3, pairRadial_13_4,
    pairRadial_13_5, pairRadial_13_6, pairRadial_13_7]
  rw [eq_div_iff (pow_ne_zero 6 hq), centralNum13_33]
  field_simp
  ring

theorem centralEntry23_00 {q : ℝ} (hq : q ≠ 0) :
    (∑ r : Fin 4, ∑ s : Fin 4, centralBasis (1/q) r 0 * centralBasis (1/q) s 0 *
      (thetaPairRadialEvenPolynomial (36*q^2) (r.val+s.val+1)).eval (13*q)) =
      centralNum23_00 q / q^6 := by
  simp only [Fin.sum_univ_four, Fin.isValue, fin4_v0, fin4_v1, fin4_v2, fin4_v3,
    Nat.reduceAdd, cB_00, cB_10, cB_20, cB_30, cB_00, cB_10, cB_20, cB_30, pairRadial_23_1, pairRadial_23_2, pairRadial_23_3, pairRadial_23_4,
    pairRadial_23_5, pairRadial_23_6, pairRadial_23_7]
  rw [eq_div_iff (pow_ne_zero 6 hq), centralNum23_00]
  field_simp
  ring

theorem centralEntry23_01 {q : ℝ} (hq : q ≠ 0) :
    (∑ r : Fin 4, ∑ s : Fin 4, centralBasis (1/q) r 0 * centralBasis (1/q) s 1 *
      (thetaPairRadialEvenPolynomial (36*q^2) (r.val+s.val+1)).eval (13*q)) =
      centralNum23_01 q / q^6 := by
  simp only [Fin.sum_univ_four, Fin.isValue, fin4_v0, fin4_v1, fin4_v2, fin4_v3,
    Nat.reduceAdd, cB_00, cB_10, cB_20, cB_30, cB_01, cB_11, cB_21, cB_31, pairRadial_23_1, pairRadial_23_2, pairRadial_23_3, pairRadial_23_4,
    pairRadial_23_5, pairRadial_23_6, pairRadial_23_7]
  rw [eq_div_iff (pow_ne_zero 6 hq), centralNum23_01]
  field_simp
  ring

theorem centralEntry23_02 {q : ℝ} (hq : q ≠ 0) :
    (∑ r : Fin 4, ∑ s : Fin 4, centralBasis (1/q) r 0 * centralBasis (1/q) s 2 *
      (thetaPairRadialEvenPolynomial (36*q^2) (r.val+s.val+1)).eval (13*q)) =
      centralNum23_02 q / q^6 := by
  simp only [Fin.sum_univ_four, Fin.isValue, fin4_v0, fin4_v1, fin4_v2, fin4_v3,
    Nat.reduceAdd, cB_00, cB_10, cB_20, cB_30, cB_02, cB_12, cB_22, cB_32, pairRadial_23_1, pairRadial_23_2, pairRadial_23_3, pairRadial_23_4,
    pairRadial_23_5, pairRadial_23_6, pairRadial_23_7]
  rw [eq_div_iff (pow_ne_zero 6 hq), centralNum23_02]
  field_simp
  ring

theorem centralEntry23_03 {q : ℝ} (hq : q ≠ 0) :
    (∑ r : Fin 4, ∑ s : Fin 4, centralBasis (1/q) r 0 * centralBasis (1/q) s 3 *
      (thetaPairRadialEvenPolynomial (36*q^2) (r.val+s.val+1)).eval (13*q)) =
      centralNum23_03 q / q^6 := by
  simp only [Fin.sum_univ_four, Fin.isValue, fin4_v0, fin4_v1, fin4_v2, fin4_v3,
    Nat.reduceAdd, cB_00, cB_10, cB_20, cB_30, cB_03, cB_13, cB_23, cB_33, pairRadial_23_1, pairRadial_23_2, pairRadial_23_3, pairRadial_23_4,
    pairRadial_23_5, pairRadial_23_6, pairRadial_23_7]
  rw [eq_div_iff (pow_ne_zero 6 hq), centralNum23_03]
  field_simp
  ring

theorem centralEntry23_10 {q : ℝ} (hq : q ≠ 0) :
    (∑ r : Fin 4, ∑ s : Fin 4, centralBasis (1/q) r 1 * centralBasis (1/q) s 0 *
      (thetaPairRadialEvenPolynomial (36*q^2) (r.val+s.val+1)).eval (13*q)) =
      centralNum23_01 q / q^6 := by
  simp only [Fin.sum_univ_four, Fin.isValue, fin4_v0, fin4_v1, fin4_v2, fin4_v3,
    Nat.reduceAdd, cB_01, cB_11, cB_21, cB_31, cB_00, cB_10, cB_20, cB_30, pairRadial_23_1, pairRadial_23_2, pairRadial_23_3, pairRadial_23_4,
    pairRadial_23_5, pairRadial_23_6, pairRadial_23_7]
  rw [eq_div_iff (pow_ne_zero 6 hq), centralNum23_01]
  field_simp
  ring

theorem centralEntry23_11 {q : ℝ} (hq : q ≠ 0) :
    (∑ r : Fin 4, ∑ s : Fin 4, centralBasis (1/q) r 1 * centralBasis (1/q) s 1 *
      (thetaPairRadialEvenPolynomial (36*q^2) (r.val+s.val+1)).eval (13*q)) =
      centralNum23_11 q / q^6 := by
  simp only [Fin.sum_univ_four, Fin.isValue, fin4_v0, fin4_v1, fin4_v2, fin4_v3,
    Nat.reduceAdd, cB_01, cB_11, cB_21, cB_31, cB_01, cB_11, cB_21, cB_31, pairRadial_23_1, pairRadial_23_2, pairRadial_23_3, pairRadial_23_4,
    pairRadial_23_5, pairRadial_23_6, pairRadial_23_7]
  rw [eq_div_iff (pow_ne_zero 6 hq), centralNum23_11]
  field_simp
  ring

theorem centralEntry23_12 {q : ℝ} (hq : q ≠ 0) :
    (∑ r : Fin 4, ∑ s : Fin 4, centralBasis (1/q) r 1 * centralBasis (1/q) s 2 *
      (thetaPairRadialEvenPolynomial (36*q^2) (r.val+s.val+1)).eval (13*q)) =
      centralNum23_12 q / q^6 := by
  simp only [Fin.sum_univ_four, Fin.isValue, fin4_v0, fin4_v1, fin4_v2, fin4_v3,
    Nat.reduceAdd, cB_01, cB_11, cB_21, cB_31, cB_02, cB_12, cB_22, cB_32, pairRadial_23_1, pairRadial_23_2, pairRadial_23_3, pairRadial_23_4,
    pairRadial_23_5, pairRadial_23_6, pairRadial_23_7]
  rw [eq_div_iff (pow_ne_zero 6 hq), centralNum23_12]
  field_simp
  ring

theorem centralEntry23_13 {q : ℝ} (hq : q ≠ 0) :
    (∑ r : Fin 4, ∑ s : Fin 4, centralBasis (1/q) r 1 * centralBasis (1/q) s 3 *
      (thetaPairRadialEvenPolynomial (36*q^2) (r.val+s.val+1)).eval (13*q)) =
      centralNum23_13 q / q^6 := by
  simp only [Fin.sum_univ_four, Fin.isValue, fin4_v0, fin4_v1, fin4_v2, fin4_v3,
    Nat.reduceAdd, cB_01, cB_11, cB_21, cB_31, cB_03, cB_13, cB_23, cB_33, pairRadial_23_1, pairRadial_23_2, pairRadial_23_3, pairRadial_23_4,
    pairRadial_23_5, pairRadial_23_6, pairRadial_23_7]
  rw [eq_div_iff (pow_ne_zero 6 hq), centralNum23_13]
  field_simp
  ring

theorem centralEntry23_20 {q : ℝ} (hq : q ≠ 0) :
    (∑ r : Fin 4, ∑ s : Fin 4, centralBasis (1/q) r 2 * centralBasis (1/q) s 0 *
      (thetaPairRadialEvenPolynomial (36*q^2) (r.val+s.val+1)).eval (13*q)) =
      centralNum23_02 q / q^6 := by
  simp only [Fin.sum_univ_four, Fin.isValue, fin4_v0, fin4_v1, fin4_v2, fin4_v3,
    Nat.reduceAdd, cB_02, cB_12, cB_22, cB_32, cB_00, cB_10, cB_20, cB_30, pairRadial_23_1, pairRadial_23_2, pairRadial_23_3, pairRadial_23_4,
    pairRadial_23_5, pairRadial_23_6, pairRadial_23_7]
  rw [eq_div_iff (pow_ne_zero 6 hq), centralNum23_02]
  field_simp
  ring

theorem centralEntry23_21 {q : ℝ} (hq : q ≠ 0) :
    (∑ r : Fin 4, ∑ s : Fin 4, centralBasis (1/q) r 2 * centralBasis (1/q) s 1 *
      (thetaPairRadialEvenPolynomial (36*q^2) (r.val+s.val+1)).eval (13*q)) =
      centralNum23_12 q / q^6 := by
  simp only [Fin.sum_univ_four, Fin.isValue, fin4_v0, fin4_v1, fin4_v2, fin4_v3,
    Nat.reduceAdd, cB_02, cB_12, cB_22, cB_32, cB_01, cB_11, cB_21, cB_31, pairRadial_23_1, pairRadial_23_2, pairRadial_23_3, pairRadial_23_4,
    pairRadial_23_5, pairRadial_23_6, pairRadial_23_7]
  rw [eq_div_iff (pow_ne_zero 6 hq), centralNum23_12]
  field_simp
  ring

theorem centralEntry23_22 {q : ℝ} (hq : q ≠ 0) :
    (∑ r : Fin 4, ∑ s : Fin 4, centralBasis (1/q) r 2 * centralBasis (1/q) s 2 *
      (thetaPairRadialEvenPolynomial (36*q^2) (r.val+s.val+1)).eval (13*q)) =
      centralNum23_22 q / q^6 := by
  simp only [Fin.sum_univ_four, Fin.isValue, fin4_v0, fin4_v1, fin4_v2, fin4_v3,
    Nat.reduceAdd, cB_02, cB_12, cB_22, cB_32, cB_02, cB_12, cB_22, cB_32, pairRadial_23_1, pairRadial_23_2, pairRadial_23_3, pairRadial_23_4,
    pairRadial_23_5, pairRadial_23_6, pairRadial_23_7]
  rw [eq_div_iff (pow_ne_zero 6 hq), centralNum23_22]
  field_simp
  ring

theorem centralEntry23_23 {q : ℝ} (hq : q ≠ 0) :
    (∑ r : Fin 4, ∑ s : Fin 4, centralBasis (1/q) r 2 * centralBasis (1/q) s 3 *
      (thetaPairRadialEvenPolynomial (36*q^2) (r.val+s.val+1)).eval (13*q)) =
      centralNum23_23 q / q^6 := by
  simp only [Fin.sum_univ_four, Fin.isValue, fin4_v0, fin4_v1, fin4_v2, fin4_v3,
    Nat.reduceAdd, cB_02, cB_12, cB_22, cB_32, cB_03, cB_13, cB_23, cB_33, pairRadial_23_1, pairRadial_23_2, pairRadial_23_3, pairRadial_23_4,
    pairRadial_23_5, pairRadial_23_6, pairRadial_23_7]
  rw [eq_div_iff (pow_ne_zero 6 hq), centralNum23_23]
  field_simp
  ring

theorem centralEntry23_30 {q : ℝ} (hq : q ≠ 0) :
    (∑ r : Fin 4, ∑ s : Fin 4, centralBasis (1/q) r 3 * centralBasis (1/q) s 0 *
      (thetaPairRadialEvenPolynomial (36*q^2) (r.val+s.val+1)).eval (13*q)) =
      centralNum23_03 q / q^6 := by
  simp only [Fin.sum_univ_four, Fin.isValue, fin4_v0, fin4_v1, fin4_v2, fin4_v3,
    Nat.reduceAdd, cB_03, cB_13, cB_23, cB_33, cB_00, cB_10, cB_20, cB_30, pairRadial_23_1, pairRadial_23_2, pairRadial_23_3, pairRadial_23_4,
    pairRadial_23_5, pairRadial_23_6, pairRadial_23_7]
  rw [eq_div_iff (pow_ne_zero 6 hq), centralNum23_03]
  field_simp
  ring

theorem centralEntry23_31 {q : ℝ} (hq : q ≠ 0) :
    (∑ r : Fin 4, ∑ s : Fin 4, centralBasis (1/q) r 3 * centralBasis (1/q) s 1 *
      (thetaPairRadialEvenPolynomial (36*q^2) (r.val+s.val+1)).eval (13*q)) =
      centralNum23_13 q / q^6 := by
  simp only [Fin.sum_univ_four, Fin.isValue, fin4_v0, fin4_v1, fin4_v2, fin4_v3,
    Nat.reduceAdd, cB_03, cB_13, cB_23, cB_33, cB_01, cB_11, cB_21, cB_31, pairRadial_23_1, pairRadial_23_2, pairRadial_23_3, pairRadial_23_4,
    pairRadial_23_5, pairRadial_23_6, pairRadial_23_7]
  rw [eq_div_iff (pow_ne_zero 6 hq), centralNum23_13]
  field_simp
  ring

theorem centralEntry23_32 {q : ℝ} (hq : q ≠ 0) :
    (∑ r : Fin 4, ∑ s : Fin 4, centralBasis (1/q) r 3 * centralBasis (1/q) s 2 *
      (thetaPairRadialEvenPolynomial (36*q^2) (r.val+s.val+1)).eval (13*q)) =
      centralNum23_23 q / q^6 := by
  simp only [Fin.sum_univ_four, Fin.isValue, fin4_v0, fin4_v1, fin4_v2, fin4_v3,
    Nat.reduceAdd, cB_03, cB_13, cB_23, cB_33, cB_02, cB_12, cB_22, cB_32, pairRadial_23_1, pairRadial_23_2, pairRadial_23_3, pairRadial_23_4,
    pairRadial_23_5, pairRadial_23_6, pairRadial_23_7]
  rw [eq_div_iff (pow_ne_zero 6 hq), centralNum23_23]
  field_simp
  ring

theorem centralEntry23_33 {q : ℝ} (hq : q ≠ 0) :
    (∑ r : Fin 4, ∑ s : Fin 4, centralBasis (1/q) r 3 * centralBasis (1/q) s 3 *
      (thetaPairRadialEvenPolynomial (36*q^2) (r.val+s.val+1)).eval (13*q)) =
      centralNum23_33 q / q^6 := by
  simp only [Fin.sum_univ_four, Fin.isValue, fin4_v0, fin4_v1, fin4_v2, fin4_v3,
    Nat.reduceAdd, cB_03, cB_13, cB_23, cB_33, cB_03, cB_13, cB_23, cB_33, pairRadial_23_1, pairRadial_23_2, pairRadial_23_3, pairRadial_23_4,
    pairRadial_23_5, pairRadial_23_6, pairRadial_23_7]
  rw [eq_div_iff (pow_ne_zero 6 hq), centralNum23_33]
  field_simp
  ring

/-- Moving-frame numerator matrix of the pair `(11)`. -/
def centralNumMat11 (q : ℝ) (i j : Fin 4) : ℝ :=
  (![![centralNum11_00 q, centralNum11_01 q, centralNum11_02 q, centralNum11_03 q],
    ![centralNum11_01 q, centralNum11_11 q, centralNum11_12 q, centralNum11_13 q],
    ![centralNum11_02 q, centralNum11_12 q, centralNum11_22 q, centralNum11_23 q],
    ![centralNum11_03 q, centralNum11_13 q, centralNum11_23 q, centralNum11_33 q]] : Fin 4 → Fin 4 → ℝ) i j

/-- Moving-frame numerator matrix of the pair `(12)`. -/
def centralNumMat12 (q : ℝ) (i j : Fin 4) : ℝ :=
  (![![centralNum12_00 q, centralNum12_01 q, centralNum12_02 q, centralNum12_03 q],
    ![centralNum12_01 q, centralNum12_11 q, centralNum12_12 q, centralNum12_13 q],
    ![centralNum12_02 q, centralNum12_12 q, centralNum12_22 q, centralNum12_23 q],
    ![centralNum12_03 q, centralNum12_13 q, centralNum12_23 q, centralNum12_33 q]] : Fin 4 → Fin 4 → ℝ) i j

/-- Moving-frame numerator matrix of the pair `(13)`. -/
def centralNumMat13 (q : ℝ) (i j : Fin 4) : ℝ :=
  (![![centralNum13_00 q, centralNum13_01 q, centralNum13_02 q, centralNum13_03 q],
    ![centralNum13_01 q, centralNum13_11 q, centralNum13_12 q, centralNum13_13 q],
    ![centralNum13_02 q, centralNum13_12 q, centralNum13_22 q, centralNum13_23 q],
    ![centralNum13_03 q, centralNum13_13 q, centralNum13_23 q, centralNum13_33 q]] : Fin 4 → Fin 4 → ℝ) i j

/-- Moving-frame numerator matrix of the pair `(23)`. -/
def centralNumMat23 (q : ℝ) (i j : Fin 4) : ℝ :=
  (![![centralNum23_00 q, centralNum23_01 q, centralNum23_02 q, centralNum23_03 q],
    ![centralNum23_01 q, centralNum23_11 q, centralNum23_12 q, centralNum23_13 q],
    ![centralNum23_02 q, centralNum23_12 q, centralNum23_22 q, centralNum23_23 q],
    ![centralNum23_03 q, centralNum23_13 q, centralNum23_23 q, centralNum23_33 q]] : Fin 4 → Fin 4 → ℝ) i j

theorem basisQuadratic (B M : Matrix (Fin 4) (Fin 4) ℝ) (y : Fin 4 → ℝ) :
    (∑ r : Fin 4, ∑ s : Fin 4, (B.mulVec y r)*(B.mulVec y s)*M r s) =
      ∑ i : Fin 4, ∑ j : Fin 4, y i*y j*(∑ r : Fin 4, ∑ s : Fin 4, B r i*B s j*M r s) := by
  simp only [Matrix.mulVec,dotProduct,Finset.sum_mul,Finset.mul_sum]
  conv_lhs =>
    arg 2
    ext r
    arg 2
    ext s
    rw [Finset.sum_comm]
  conv_lhs =>
    arg 2
    ext r
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  conv_lhs =>
    arg 2
    ext r
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro s _
  ring

/-- The radial energy of the pair `(11)` in moving central coordinates. -/
theorem centralEnergy11 {q : ℝ} (hq : q ≠ 0) (y : Fin 4 → ℝ) :
    (∑ r : Fin 4, ∑ s : Fin 4, (centralBasis (1/q)).mulVec y r * (centralBasis (1/q)).mulVec y s *
      (thetaPairRadialEvenPolynomial (1*q^2) (r.val+s.val+1)).eval (2*q)) =
      (∑ i : Fin 4, ∑ j : Fin 4, y i * y j * centralNumMat11 q i j) / q^6 := by
  have hb := basisQuadratic (centralBasis (1/q)) (Matrix.of fun r s : Fin 4 =>
    (thetaPairRadialEvenPolynomial (1*q^2) (r.val+s.val+1)).eval (2*q)) y
  simp only [Matrix.of_apply] at hb
  rw [hb, Finset.sum_div]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mul_div_assoc]
  congr 1
  fin_cases i <;> fin_cases j
  · exact centralEntry11_00 hq
  · exact centralEntry11_01 hq
  · exact centralEntry11_02 hq
  · exact centralEntry11_03 hq
  · exact centralEntry11_10 hq
  · exact centralEntry11_11 hq
  · exact centralEntry11_12 hq
  · exact centralEntry11_13 hq
  · exact centralEntry11_20 hq
  · exact centralEntry11_21 hq
  · exact centralEntry11_22 hq
  · exact centralEntry11_23 hq
  · exact centralEntry11_30 hq
  · exact centralEntry11_31 hq
  · exact centralEntry11_32 hq
  · exact centralEntry11_33 hq

/-- The radial energy of the pair `(12)` in moving central coordinates. -/
theorem centralEnergy12 {q : ℝ} (hq : q ≠ 0) (y : Fin 4 → ℝ) :
    (∑ r : Fin 4, ∑ s : Fin 4, (centralBasis (1/q)).mulVec y r * (centralBasis (1/q)).mulVec y s *
      (thetaPairRadialEvenPolynomial (4*q^2) (r.val+s.val+1)).eval (5*q)) =
      (∑ i : Fin 4, ∑ j : Fin 4, y i * y j * centralNumMat12 q i j) / q^6 := by
  have hb := basisQuadratic (centralBasis (1/q)) (Matrix.of fun r s : Fin 4 =>
    (thetaPairRadialEvenPolynomial (4*q^2) (r.val+s.val+1)).eval (5*q)) y
  simp only [Matrix.of_apply] at hb
  rw [hb, Finset.sum_div]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mul_div_assoc]
  congr 1
  fin_cases i <;> fin_cases j
  · exact centralEntry12_00 hq
  · exact centralEntry12_01 hq
  · exact centralEntry12_02 hq
  · exact centralEntry12_03 hq
  · exact centralEntry12_10 hq
  · exact centralEntry12_11 hq
  · exact centralEntry12_12 hq
  · exact centralEntry12_13 hq
  · exact centralEntry12_20 hq
  · exact centralEntry12_21 hq
  · exact centralEntry12_22 hq
  · exact centralEntry12_23 hq
  · exact centralEntry12_30 hq
  · exact centralEntry12_31 hq
  · exact centralEntry12_32 hq
  · exact centralEntry12_33 hq

/-- The radial energy of the pair `(13)` in moving central coordinates. -/
theorem centralEnergy13 {q : ℝ} (hq : q ≠ 0) (y : Fin 4 → ℝ) :
    (∑ r : Fin 4, ∑ s : Fin 4, (centralBasis (1/q)).mulVec y r * (centralBasis (1/q)).mulVec y s *
      (thetaPairRadialEvenPolynomial (9*q^2) (r.val+s.val+1)).eval (10*q)) =
      (∑ i : Fin 4, ∑ j : Fin 4, y i * y j * centralNumMat13 q i j) / q^6 := by
  have hb := basisQuadratic (centralBasis (1/q)) (Matrix.of fun r s : Fin 4 =>
    (thetaPairRadialEvenPolynomial (9*q^2) (r.val+s.val+1)).eval (10*q)) y
  simp only [Matrix.of_apply] at hb
  rw [hb, Finset.sum_div]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mul_div_assoc]
  congr 1
  fin_cases i <;> fin_cases j
  · exact centralEntry13_00 hq
  · exact centralEntry13_01 hq
  · exact centralEntry13_02 hq
  · exact centralEntry13_03 hq
  · exact centralEntry13_10 hq
  · exact centralEntry13_11 hq
  · exact centralEntry13_12 hq
  · exact centralEntry13_13 hq
  · exact centralEntry13_20 hq
  · exact centralEntry13_21 hq
  · exact centralEntry13_22 hq
  · exact centralEntry13_23 hq
  · exact centralEntry13_30 hq
  · exact centralEntry13_31 hq
  · exact centralEntry13_32 hq
  · exact centralEntry13_33 hq

/-- The radial energy of the pair `(23)` in moving central coordinates. -/
theorem centralEnergy23 {q : ℝ} (hq : q ≠ 0) (y : Fin 4 → ℝ) :
    (∑ r : Fin 4, ∑ s : Fin 4, (centralBasis (1/q)).mulVec y r * (centralBasis (1/q)).mulVec y s *
      (thetaPairRadialEvenPolynomial (36*q^2) (r.val+s.val+1)).eval (13*q)) =
      (∑ i : Fin 4, ∑ j : Fin 4, y i * y j * centralNumMat23 q i j) / q^6 := by
  have hb := basisQuadratic (centralBasis (1/q)) (Matrix.of fun r s : Fin 4 =>
    (thetaPairRadialEvenPolynomial (36*q^2) (r.val+s.val+1)).eval (13*q)) y
  simp only [Matrix.of_apply] at hb
  rw [hb, Finset.sum_div]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mul_div_assoc]
  congr 1
  fin_cases i <;> fin_cases j
  · exact centralEntry23_00 hq
  · exact centralEntry23_01 hq
  · exact centralEntry23_02 hq
  · exact centralEntry23_03 hq
  · exact centralEntry23_10 hq
  · exact centralEntry23_11 hq
  · exact centralEntry23_12 hq
  · exact centralEntry23_13 hq
  · exact centralEntry23_20 hq
  · exact centralEntry23_21 hq
  · exact centralEntry23_22 hq
  · exact centralEntry23_23 hq
  · exact centralEntry23_30 hq
  · exact centralEntry23_31 hq
  · exact centralEntry23_32 hq
  · exact centralEntry23_33 hq

end
end RHTower.ThetaCuspOddFourCentralEntries
