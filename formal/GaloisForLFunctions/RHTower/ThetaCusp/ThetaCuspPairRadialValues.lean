import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRadialCoefficients

/-!
# Radial values of the first theta-atom pairs

For the ordered atom pairs `(1,1)`, `(1,2)`, `(1,3)`, `(2,3)` the radial polynomial enters the
reflected pair jet at `a = n²m²q²` and `X = (n²+m²)q`. Through order seven these values are
explicit polynomials in the first-atom scale `q`, read off the coefficient tables.
-/

open Polynomial
namespace RHTower
noncomputable section

theorem pairRadial_11_1 (q : ℝ) :
    (thetaPairRadialEvenPolynomial (1*q^2) 1).eval (2*q) = (120:ℝ)*q^1 + (-96:ℝ)*q^2 + (32:ℝ)*q^3 := by
  rw [eval_thetaPairRadialEvenPolynomial]
  simp only [Nat.reduceMul, Nat.reduceAdd, Finset.sum_range_succ, Finset.sum_range_zero, radialCoeffs_1_0, radialCoeffs_1_1, radialCoeffs_1_2, radialCoeffs_1_3]
  ring

theorem pairRadial_11_2 (q : ℝ) :
    (thetaPairRadialEvenPolynomial (1*q^2) 2).eval (2*q) = (-480:ℝ)*q^1 + (4416:ℝ)*q^2 + (-2432:ℝ)*q^3 + (768:ℝ)*q^4 := by
  rw [eval_thetaPairRadialEvenPolynomial]
  simp only [Nat.reduceMul, Nat.reduceAdd, Finset.sum_range_succ, Finset.sum_range_zero, radialCoeffs_2_0, radialCoeffs_2_1, radialCoeffs_2_2, radialCoeffs_2_3, radialCoeffs_2_4, radialCoeffs_2_5]
  ring

theorem pairRadial_11_3 (q : ℝ) :
    (thetaPairRadialEvenPolynomial (1*q^2) 3).eval (2*q) = (1920:ℝ)*q^1 + (-82176:ℝ)*q^2 + (253952:ℝ)*q^3 + (-107520:ℝ)*q^4 + (30720:ℝ)*q^5 := by
  rw [eval_thetaPairRadialEvenPolynomial]
  simp only [Nat.reduceMul, Nat.reduceAdd, Finset.sum_range_succ, Finset.sum_range_zero, radialCoeffs_3_0, radialCoeffs_3_1, radialCoeffs_3_2, radialCoeffs_3_3, radialCoeffs_3_4, radialCoeffs_3_5, radialCoeffs_3_6, radialCoeffs_3_7]
  ring

theorem pairRadial_11_4 (q : ℝ) :
    (thetaPairRadialEvenPolynomial (1*q^2) 4).eval (2*q) = (-7680:ℝ)*q^1 + (1360896:ℝ)*q^2 + (-12388352:ℝ)*q^3 + (19611648:ℝ)*q^4 + (-6881280:ℝ)*q^5 + (1720320:ℝ)*q^6 := by
  rw [eval_thetaPairRadialEvenPolynomial]
  simp only [Nat.reduceMul, Nat.reduceAdd, Finset.sum_range_succ, Finset.sum_range_zero, radialCoeffs_4_0, radialCoeffs_4_1, radialCoeffs_4_2, radialCoeffs_4_3, radialCoeffs_4_4, radialCoeffs_4_5, radialCoeffs_4_6, radialCoeffs_4_7, radialCoeffs_4_8, radialCoeffs_4_9]
  ring

theorem pairRadial_11_5 (q : ℝ) :
    (thetaPairRadialEvenPolynomial (1*q^2) 5).eval (2*q) = (30720:ℝ)*q^1 + (-21958656:ℝ)*q^2 + (500252672:ℝ)*q^3 + (-1924055040:ℝ)*q^4 + (1899233280:ℝ)*q^5 + (-578027520:ℝ)*q^6 + (123863040:ℝ)*q^7 := by
  rw [eval_thetaPairRadialEvenPolynomial]
  simp only [Nat.reduceMul, Nat.reduceAdd, Finset.sum_range_succ, Finset.sum_range_zero, radialCoeffs_5_0, radialCoeffs_5_1, radialCoeffs_5_2, radialCoeffs_5_3, radialCoeffs_5_4, radialCoeffs_5_5, radialCoeffs_5_6, radialCoeffs_5_7, radialCoeffs_5_8, radialCoeffs_5_9, radialCoeffs_5_10, radialCoeffs_5_11]
  ring

theorem pairRadial_11_6 (q : ℝ) :
    (thetaPairRadialEvenPolynomial (1*q^2) 6).eval (2*q) = (-122880:ℝ)*q^1 + (352075776:ℝ)*q^2 + (-18886787072:ℝ)*q^3 + (150752329728:ℝ)*q^4 + (-320229212160:ℝ)*q^5 + (221632266240:ℝ)*q^6 + (-59949711360:ℝ)*q^7 + (10899947520:ℝ)*q^8 := by
  rw [eval_thetaPairRadialEvenPolynomial]
  simp only [Nat.reduceMul, Nat.reduceAdd, Finset.sum_range_succ, Finset.sum_range_zero, radialCoeffs_6_0, radialCoeffs_6_1, radialCoeffs_6_2, radialCoeffs_6_3, radialCoeffs_6_4, radialCoeffs_6_5, radialCoeffs_6_6, radialCoeffs_6_7, radialCoeffs_6_8, radialCoeffs_6_9, radialCoeffs_6_10, radialCoeffs_6_11, radialCoeffs_6_12, radialCoeffs_6_13]
  ring

theorem pairRadial_11_7 (q : ℝ) :
    (thetaPairRadialEvenPolynomial (1*q^2) 7).eval (2*q) = (491520:ℝ)*q^1 + (-5636161536:ℝ)*q^2 + (694004744192:ℝ)*q^3 + (-10699371970560:ℝ)*q^4 + (42564900618240:ℝ)*q^5 + (-57797577277440:ℝ)*q^6 + (30323654000640:ℝ)*q^7 + (-7368364523520:ℝ)*q^8 + (1133594542080:ℝ)*q^9 := by
  rw [eval_thetaPairRadialEvenPolynomial]
  simp only [Nat.reduceMul, Nat.reduceAdd, Finset.sum_range_succ, Finset.sum_range_zero, radialCoeffs_7_0, radialCoeffs_7_1, radialCoeffs_7_2, radialCoeffs_7_3, radialCoeffs_7_4, radialCoeffs_7_5, radialCoeffs_7_6, radialCoeffs_7_7, radialCoeffs_7_8, radialCoeffs_7_9, radialCoeffs_7_10, radialCoeffs_7_11, radialCoeffs_7_12, radialCoeffs_7_13, radialCoeffs_7_14, radialCoeffs_7_15]
  ring

theorem pairRadial_12_1 (q : ℝ) :
    (thetaPairRadialEvenPolynomial (4*q^2) 1).eval (5*q) = (300:ℝ)*q^1 + (-1356:ℝ)*q^2 + (1400:ℝ)*q^3 + (-576:ℝ)*q^4 := by
  rw [eval_thetaPairRadialEvenPolynomial]
  simp only [Nat.reduceMul, Nat.reduceAdd, Finset.sum_range_succ, Finset.sum_range_zero, radialCoeffs_1_0, radialCoeffs_1_1, radialCoeffs_1_2, radialCoeffs_1_3]
  ring

theorem pairRadial_12_2 (q : ℝ) :
    (thetaPairRadialEvenPolynomial (4*q^2) 2).eval (5*q) = (-1200:ℝ)*q^1 + (39696:ℝ)*q^2 + (-171200:ℝ)*q^3 + (200784:ℝ)*q^4 + (-108000:ℝ)*q^5 + (20736:ℝ)*q^6 := by
  rw [eval_thetaPairRadialEvenPolynomial]
  simp only [Nat.reduceMul, Nat.reduceAdd, Finset.sum_range_succ, Finset.sum_range_zero, radialCoeffs_2_0, radialCoeffs_2_1, radialCoeffs_2_2, radialCoeffs_2_3, radialCoeffs_2_4, radialCoeffs_2_5]
  ring

theorem pairRadial_12_3 (q : ℝ) :
    (thetaPairRadialEvenPolynomial (4*q^2) 3).eval (5*q) = (4800:ℝ)*q^1 + (-707136:ℝ)*q^2 + (10073600:ℝ)*q^3 + (-35416896:ℝ)*q^4 + (43089600:ℝ)*q^5 + (-25790400:ℝ)*q^6 + (7620480:ℝ)*q^7 + (-746496:ℝ)*q^8 := by
  rw [eval_thetaPairRadialEvenPolynomial]
  simp only [Nat.reduceMul, Nat.reduceAdd, Finset.sum_range_succ, Finset.sum_range_zero, radialCoeffs_3_0, radialCoeffs_3_1, radialCoeffs_3_2, radialCoeffs_3_3, radialCoeffs_3_4, radialCoeffs_3_5, radialCoeffs_3_6, radialCoeffs_3_7]
  ring

theorem pairRadial_12_4 (q : ℝ) :
    (thetaPairRadialEvenPolynomial (4*q^2) 4).eval (5*q) = (-19200:ℝ)*q^1 + (11602176:ℝ)*q^2 + (-433126400:ℝ)*q^3 + (3651012864:ℝ)*q^4 + (-10402022400:ℝ)*q^5 + (12499017216:ℝ)*q^6 + (-7892398080:ℝ)*q^7 + (2788598016:ℝ)*q^8 + (-468426240:ℝ)*q^9 + (26873856:ℝ)*q^10 := by
  rw [eval_thetaPairRadialEvenPolynomial]
  simp only [Nat.reduceMul, Nat.reduceAdd, Finset.sum_range_succ, Finset.sum_range_zero, radialCoeffs_4_0, radialCoeffs_4_1, radialCoeffs_4_2, radialCoeffs_4_3, radialCoeffs_4_4, radialCoeffs_4_5, radialCoeffs_4_6, radialCoeffs_4_7, radialCoeffs_4_8, radialCoeffs_4_9]
  ring

theorem pairRadial_12_5 (q : ℝ) :
    (thetaPairRadialEvenPolynomial (4*q^2) 5).eval (5*q) = (76800:ℝ)*q^1 + (-186786816:ℝ)*q^2 + (16751820800:ℝ)*q^3 + (-293872751616:ℝ)*q^4 + (1684623283200:ℝ)*q^5 + (-4002679526400:ℝ)*q^6 + (4618622453760:ℝ)*q^7 + (-2987682527232:ℝ)*q^8 + (1157721984000:ℝ)*q^9 + (-250538241024:ℝ)*q^10 + (26000455680:ℝ)*q^11 + (-967458816:ℝ)*q^12 := by
  rw [eval_thetaPairRadialEvenPolynomial]
  simp only [Nat.reduceMul, Nat.reduceAdd, Finset.sum_range_succ, Finset.sum_range_zero, radialCoeffs_5_0, radialCoeffs_5_1, radialCoeffs_5_2, radialCoeffs_5_3, radialCoeffs_5_4, radialCoeffs_5_5, radialCoeffs_5_6, radialCoeffs_5_7, radialCoeffs_5_8, radialCoeffs_5_9, radialCoeffs_5_10, radialCoeffs_5_11]
  ring

theorem pairRadial_12_6 (q : ℝ) :
    (thetaPairRadialEvenPolynomial (4*q^2) 6).eval (5*q) = (-307200:ℝ)*q^1 + (2993197056:ℝ)*q^2 + (-621740441600:ℝ)*q^3 + (21146177900544:ℝ)*q^4 + (-220856989900800:ℝ)*q^5 + (939708531818496:ℝ)*q^6 + (-1911756612648960:ℝ)*q^7 + (2090002567606272:ℝ)*q^8 + (-1357634344366080:ℝ)*q^9 + (554264510164992:ℝ)*q^10 + (-138376171929600:ℝ)*q^11 + (19385214160896:ℝ)*q^12 + (-1342349107200:ℝ)*q^13 + (34828517376:ℝ)*q^14 := by
  rw [eval_thetaPairRadialEvenPolynomial]
  simp only [Nat.reduceMul, Nat.reduceAdd, Finset.sum_range_succ, Finset.sum_range_zero, radialCoeffs_6_0, radialCoeffs_6_1, radialCoeffs_6_2, radialCoeffs_6_3, radialCoeffs_6_4, radialCoeffs_6_5, radialCoeffs_6_6, radialCoeffs_6_7, radialCoeffs_6_8, radialCoeffs_6_9, radialCoeffs_6_10, radialCoeffs_6_11, radialCoeffs_6_12, radialCoeffs_6_13]
  ring

theorem pairRadial_12_7 (q : ℝ) :
    (thetaPairRadialEvenPolynomial (4*q^2) 7).eval (5*q) = (1228800:ℝ)*q^1 + (-47909584896:ℝ)*q^2 + (22681960448000:ℝ)*q^3 + (-1440287890292736:ℝ)*q^4 + (25873229882572800:ℝ)*q^5 + (-183368931293184000:ℝ)*q^6 + (614258629468323840:ℝ)*q^7 + (-1091711196399403008:ℝ)*q^8 + (1124791456149504000:ℝ)*q^9 + (-723717393839751168:ℝ)*q^10 + (304249765406146560:ℝ)*q^11 + (-82936975037349888:ℝ)*q^12 + (13929931575705600:ℝ)*q^13 + (-1338962033885184:ℝ)*q^14 + (65738826547200:ℝ)*q^15 + (-1253826625536:ℝ)*q^16 := by
  rw [eval_thetaPairRadialEvenPolynomial]
  simp only [Nat.reduceMul, Nat.reduceAdd, Finset.sum_range_succ, Finset.sum_range_zero, radialCoeffs_7_0, radialCoeffs_7_1, radialCoeffs_7_2, radialCoeffs_7_3, radialCoeffs_7_4, radialCoeffs_7_5, radialCoeffs_7_6, radialCoeffs_7_7, radialCoeffs_7_8, radialCoeffs_7_9, radialCoeffs_7_10, radialCoeffs_7_11, radialCoeffs_7_12, radialCoeffs_7_13, radialCoeffs_7_14, radialCoeffs_7_15]
  ring

theorem pairRadial_13_1 (q : ℝ) :
    (thetaPairRadialEvenPolynomial (9*q^2) 1).eval (10*q) = (600:ℝ)*q^1 + (-7776:ℝ)*q^2 + (16800:ℝ)*q^3 + (-9216:ℝ)*q^4 := by
  rw [eval_thetaPairRadialEvenPolynomial]
  simp only [Nat.reduceMul, Nat.reduceAdd, Finset.sum_range_succ, Finset.sum_range_zero, radialCoeffs_1_0, radialCoeffs_1_1, radialCoeffs_1_2, radialCoeffs_1_3]
  ring

theorem pairRadial_13_2 (q : ℝ) :
    (thetaPairRadialEvenPolynomial (9*q^2) 2).eval (10*q) = (-2400:ℝ)*q^1 + (196416:ℝ)*q^2 + (-2198400:ℝ)*q^3 + (6169344:ℝ)*q^4 + (-6144000:ℝ)*q^5 + (2359296:ℝ)*q^6 := by
  rw [eval_thetaPairRadialEvenPolynomial]
  simp only [Nat.reduceMul, Nat.reduceAdd, Finset.sum_range_succ, Finset.sum_range_zero, radialCoeffs_2_0, radialCoeffs_2_1, radialCoeffs_2_2, radialCoeffs_2_3, radialCoeffs_2_4, radialCoeffs_2_5]
  ring

theorem pairRadial_13_3 (q : ℝ) :
    (thetaPairRadialEvenPolynomial (9*q^2) 3).eval (10*q) = (9600:ℝ)*q^1 + (-3430656:ℝ)*q^2 + (118579200:ℝ)*q^3 + (-1029006336:ℝ)*q^4 + (3099187200:ℝ)*q^5 + (-3966566400:ℝ)*q^6 + (2422210560:ℝ)*q^7 + (-603979776:ℝ)*q^8 := by
  rw [eval_thetaPairRadialEvenPolynomial]
  simp only [Nat.reduceMul, Nat.reduceAdd, Finset.sum_range_succ, Finset.sum_range_zero, radialCoeffs_3_0, radialCoeffs_3_1, radialCoeffs_3_2, radialCoeffs_3_3, radialCoeffs_3_4, radialCoeffs_3_5, radialCoeffs_3_6, radialCoeffs_3_7]
  ring

theorem pairRadial_13_4 (q : ℝ) :
    (thetaPairRadialEvenPolynomial (9*q^2) 4).eval (10*q) = (-38400:ℝ)*q^1 + (56042496:ℝ)*q^2 + (-4955596800:ℝ)*q^3 + (99374874624:ℝ)*q^4 + (-693529804800:ℝ)*q^5 + (2065935384576:ℝ)*q^6 + (-2990549237760:ℝ)*q^7 + (2300256976896:ℝ)*q^8 + (-934155386880:ℝ)*q^9 + (154618822656:ℝ)*q^10 := by
  rw [eval_thetaPairRadialEvenPolynomial]
  simp only [Nat.reduceMul, Nat.reduceAdd, Finset.sum_range_succ, Finset.sum_range_zero, radialCoeffs_4_0, radialCoeffs_4_1, radialCoeffs_4_2, radialCoeffs_4_3, radialCoeffs_4_4, radialCoeffs_4_5, radialCoeffs_4_6, radialCoeffs_4_7, radialCoeffs_4_8, radialCoeffs_4_9]
  ring

theorem pairRadial_13_5 (q : ℝ) :
    (thetaPairRadialEvenPolynomial (9*q^2) 5).eval (10*q) = (153600:ℝ)*q^1 + (-901287936:ℝ)*q^2 + (189612441600:ℝ)*q^3 + (-7752693497856:ℝ)*q^4 + (105665062502400:ℝ)*q^5 + (-614689859174400:ℝ)*q^6 + (1752590959902720:ℝ)*q^7 + (-2685905500372992:ℝ)*q^8 + (2364882812928000:ℝ)*q^9 + (-1222751419367424:ℝ)*q^10 + (344284578447360:ℝ)*q^11 + (-39582418599936:ℝ)*q^12 := by
  rw [eval_thetaPairRadialEvenPolynomial]
  simp only [Nat.reduceMul, Nat.reduceAdd, Finset.sum_range_succ, Finset.sum_range_zero, radialCoeffs_5_0, radialCoeffs_5_1, radialCoeffs_5_2, radialCoeffs_5_3, radialCoeffs_5_4, radialCoeffs_5_5, radialCoeffs_5_6, radialCoeffs_5_7, radialCoeffs_5_8, radialCoeffs_5_9, radialCoeffs_5_10, radialCoeffs_5_11]
  ring

theorem pairRadial_13_6 (q : ℝ) :
    (thetaPairRadialEvenPolynomial (9*q^2) 6).eval (10*q) = (-614400:ℝ)*q^1 + (14439038976:ℝ)*q^2 + (-7006315315200:ℝ)*q^3 + (549346313109504:ℝ)*q^4 + (-13377838537113600:ℝ)*q^5 + (135928451517382656:ℝ)*q^6 + (-676677088373637120:ℝ)*q^7 + (1823384079650783232:ℝ)*q^8 + (-2851633789623336960:ℝ)*q^9 + (2724549422682734592:ℝ)*q^10 + (-1631981057291059200:ℝ)*q^11 + (599168965951881216:ℝ)*q^12 + (-121386083706470400:ℝ)*q^13 + (10133099161583616:ℝ)*q^14 := by
  rw [eval_thetaPairRadialEvenPolynomial]
  simp only [Nat.reduceMul, Nat.reduceAdd, Finset.sum_range_succ, Finset.sum_range_zero, radialCoeffs_6_0, radialCoeffs_6_1, radialCoeffs_6_2, radialCoeffs_6_3, radialCoeffs_6_4, radialCoeffs_6_5, radialCoeffs_6_6, radialCoeffs_6_7, radialCoeffs_6_8, radialCoeffs_6_9, radialCoeffs_6_10, radialCoeffs_6_11, radialCoeffs_6_12, radialCoeffs_6_13]
  ring

theorem pairRadial_13_7 (q : ℝ) :
    (thetaPairRadialEvenPolynomial (9*q^2) 7).eval (10*q) = (2457600:ℝ)*q^1 + (-231098351616:ℝ)*q^2 + (255115198464000:ℝ)*q^3 + (-37121252636491776:ℝ)*q^4 + (1536298066811289600:ℝ)*q^5 + (-25524548765614080000:ℝ)*q^6 + (204995080193027604480:ℝ)*q^7 + (-890876322675790184448:ℝ)*q^8 + (2258791769815646208000:ℝ)*q^9 + (-3529182033083753299968:ℝ)*q^10 + (3539578193131465605120:ℝ)*q^11 + (-2334904934146819227648:ℝ)*q^12 + (1009580592619270963200:ℝ)*q^13 + (-273114888427372806144:ℝ)*q^14 + (41207936590440038400:ℝ)*q^15 + (-2594073385365405696:ℝ)*q^16 := by
  rw [eval_thetaPairRadialEvenPolynomial]
  simp only [Nat.reduceMul, Nat.reduceAdd, Finset.sum_range_succ, Finset.sum_range_zero, radialCoeffs_7_0, radialCoeffs_7_1, radialCoeffs_7_2, radialCoeffs_7_3, radialCoeffs_7_4, radialCoeffs_7_5, radialCoeffs_7_6, radialCoeffs_7_7, radialCoeffs_7_8, radialCoeffs_7_9, radialCoeffs_7_10, radialCoeffs_7_11, radialCoeffs_7_12, radialCoeffs_7_13, radialCoeffs_7_14, radialCoeffs_7_15]
  ring

theorem pairRadial_23_1 (q : ℝ) :
    (thetaPairRadialEvenPolynomial (36*q^2) 1).eval (13*q) = (780:ℝ)*q^1 + (-6156:ℝ)*q^2 + (15288:ℝ)*q^3 + (-14400:ℝ)*q^4 := by
  rw [eval_thetaPairRadialEvenPolynomial]
  simp only [Nat.reduceMul, Nat.reduceAdd, Finset.sum_range_succ, Finset.sum_range_zero, radialCoeffs_1_0, radialCoeffs_1_1, radialCoeffs_1_2, radialCoeffs_1_3]
  ring

theorem pairRadial_23_2 (q : ℝ) :
    (thetaPairRadialEvenPolynomial (36*q^2) 2).eval (13*q) = (-3120:ℝ)*q^1 + (220176:ℝ)*q^2 + (-1629888:ℝ)*q^3 + (4162128:ℝ)*q^4 + (-5272800:ℝ)*q^5 + (1440000:ℝ)*q^6 := by
  rw [eval_thetaPairRadialEvenPolynomial]
  simp only [Nat.reduceMul, Nat.reduceAdd, Finset.sum_range_succ, Finset.sum_range_zero, radialCoeffs_2_0, radialCoeffs_2_1, radialCoeffs_2_2, radialCoeffs_2_3, radialCoeffs_2_4, radialCoeffs_2_5]
  ring

theorem pairRadial_23_3 (q : ℝ) :
    (thetaPairRadialEvenPolynomial (36*q^2) 3).eval (13*q) = (12480:ℝ)*q^1 + (-4009536:ℝ)*q^2 + (113837568:ℝ)*q^3 + (-741184320:ℝ)*q^4 + (1844057280:ℝ)*q^5 + (-2520792000:ℝ)*q^6 + (1201200000:ℝ)*q^7 + (-144000000:ℝ)*q^8 := by
  rw [eval_thetaPairRadialEvenPolynomial]
  simp only [Nat.reduceMul, Nat.reduceAdd, Finset.sum_range_succ, Finset.sum_range_zero, radialCoeffs_3_0, radialCoeffs_3_1, radialCoeffs_3_2, radialCoeffs_3_3, radialCoeffs_3_4, radialCoeffs_3_5, radialCoeffs_3_6, radialCoeffs_3_7]
  ring

theorem pairRadial_23_4 (q : ℝ) :
    (thetaPairRadialEvenPolynomial (36*q^2) 4).eval (13*q) = (-49920:ℝ)*q^1 + (66099456:ℝ)*q^2 + (-5132295168:ℝ)*q^3 + (86652004608:ℝ)*q^4 + (-477861995520:ℝ)*q^5 + (1142989585920:ℝ)*q^6 + (-1573737984000:ℝ)*q^7 + (969213600000:ℝ)*q^8 + (-217464000000:ℝ)*q^9 + (14400000000:ℝ)*q^10 := by
  rw [eval_thetaPairRadialEvenPolynomial]
  simp only [Nat.reduceMul, Nat.reduceAdd, Finset.sum_range_succ, Finset.sum_range_zero, radialCoeffs_4_0, radialCoeffs_4_1, radialCoeffs_4_2, radialCoeffs_4_3, radialCoeffs_4_4, radialCoeffs_4_5, radialCoeffs_4_6, radialCoeffs_4_7, radialCoeffs_4_8, radialCoeffs_4_9]
  ring

theorem pairRadial_23_5 (q : ℝ) :
    (thetaPairRadialEvenPolynomial (36*q^2) 5).eval (13*q) = (199680:ℝ)*q^1 + (-1065378816:ℝ)*q^2 + (201915138048:ℝ)*q^3 + (-7377052554240:ℝ)*q^4 + (85839332766720:ℝ)*q^5 + (-400910215173120:ℝ)*q^6 + (913846131394560:ℝ)*q^7 + (-1237810256640000:ℝ)*q^8 + (870927408000000:ℝ)*q^9 + (-271160880000000:ℝ)*q^10 + (34476000000000:ℝ)*q^11 + (-1440000000000:ℝ)*q^12 := by
  rw [eval_thetaPairRadialEvenPolynomial]
  simp only [Nat.reduceMul, Nat.reduceAdd, Finset.sum_range_succ, Finset.sum_range_zero, radialCoeffs_5_0, radialCoeffs_5_1, radialCoeffs_5_2, radialCoeffs_5_3, radialCoeffs_5_4, radialCoeffs_5_5, radialCoeffs_5_6, radialCoeffs_5_7, radialCoeffs_5_8, radialCoeffs_5_9, radialCoeffs_5_10, radialCoeffs_5_11]
  ring

theorem pairRadial_23_6 (q : ℝ) :
    (thetaPairRadialEvenPolynomial (36*q^2) 6).eval (13*q) = (-798720:ℝ)*q^1 + (17077211136:ℝ)*q^2 + (-7545810075648:ℝ)*q^3 + (545033972748288:ℝ)*q^4 + (-11936819251568640:ℝ)*q^5 + (103552351670845440:ℝ)*q^6 + (-416007395666903040:ℝ)*q^7 + (897283335453880320:ℝ)*q^8 + (-1185518280900096000:ℝ)*q^9 + (894625727424000000:ℝ)*q^10 + (-340416510720000000:ℝ)*q^11 + (61847496000000000:ℝ)*q^12 + (-5020080000000000:ℝ)*q^13 + (144000000000000:ℝ)*q^14 := by
  rw [eval_thetaPairRadialEvenPolynomial]
  simp only [Nat.reduceMul, Nat.reduceAdd, Finset.sum_range_succ, Finset.sum_range_zero, radialCoeffs_6_0, radialCoeffs_6_1, radialCoeffs_6_2, radialCoeffs_6_3, radialCoeffs_6_4, radialCoeffs_6_5, radialCoeffs_6_6, radialCoeffs_6_7, radialCoeffs_6_8, radialCoeffs_6_9, radialCoeffs_6_10, radialCoeffs_6_11, radialCoeffs_6_12, radialCoeffs_6_13]
  ring

theorem pairRadial_23_7 (q : ℝ) :
    (thetaPairRadialEvenPolynomial (36*q^2) 7).eval (13*q) = (3194880:ℝ)*q^1 + (-273359978496:ℝ)*q^2 + (276088704073728:ℝ)*q^3 + (-37619316299612160:ℝ)*q^4 + (1445018574471413760:ℝ)*q^5 + (-21493314729538928640:ℝ)*q^6 + (146589703642631208960:ℝ)*q^7 + (-515424848467041976320:ℝ)*q^8 + (1047386723816394424320:ℝ)*q^9 + (-1344528951143718912000:ℝ)*q^10 + (1050895484704665600000:ℝ)*q^11 + (-455375000021760000000:ℝ)*q^12 + (104360247264000000000:ℝ)*q^13 + (-12281021280000000000:ℝ)*q^14 + (689208000000000000:ℝ)*q^15 + (-14400000000000000:ℝ)*q^16 := by
  rw [eval_thetaPairRadialEvenPolynomial]
  simp only [Nat.reduceMul, Nat.reduceAdd, Finset.sum_range_succ, Finset.sum_range_zero, radialCoeffs_7_0, radialCoeffs_7_1, radialCoeffs_7_2, radialCoeffs_7_3, radialCoeffs_7_4, radialCoeffs_7_5, radialCoeffs_7_6, radialCoeffs_7_7, radialCoeffs_7_8, radialCoeffs_7_9, radialCoeffs_7_10, radialCoeffs_7_11, radialCoeffs_7_12, radialCoeffs_7_13, radialCoeffs_7_14, radialCoeffs_7_15]
  ring

end
end RHTower
