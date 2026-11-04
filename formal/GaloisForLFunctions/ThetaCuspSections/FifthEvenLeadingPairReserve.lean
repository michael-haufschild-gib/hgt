import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRadialCoefficients
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspDeepTailPeakTwelve
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic
/-!
# Quadratic reserve for the leading fifth even theta pairs

Normalize the radial moment of order `k` by `q^k`. In the displayed Gaussian
basis, the first atom and its two ordered cross pairs with atom two retain
one thousandth of their zeroth moment. Their Gram matrix is therefore at
least `49/1000` times the identity whenever `q ≥ 5`.

The weight `exp(-3q)` lies between zero and `9765625/(1024q^15)`. Both affine
endpoints have positive coefficient matrices in `q-5`, after clearing powers
of `q`. Two exact Schur square completions certify those matrices; convexity
then preserves their reserve throughout the weight interval.
-/

noncomputable section
open Matrix
namespace GaloisForLFunctions.ThetaCuspSections.FifthLeadingPair
open _root_.RHTower Polynomial
-- Two Schur eliminations certify a real symmetric matrix from five scalar signs.
/-- The leading two-coordinate determinant. -/
def delta (A : Matrix (Fin 5) (Fin 5) ℝ) : ℝ := A 0 0*A 1 1-(A 0 1)^2
/-- Embedding of the three tail coordinates after the leading two. -/
def tailIndex (i : Fin 3) : Fin 5 := ⟨i.val+2,by omega⟩
/-- The tail Schur complement multiplied by the leading two-coordinate determinant. -/
def schur (A : Matrix (Fin 5) (Fin 5) ℝ) (i j : Fin 3) : ℝ :=
  delta A*A (tailIndex i) (tailIndex j)-
    (A 1 1*A 0 (tailIndex i)*A 0 (tailIndex j)-
      A 0 1*(A 0 (tailIndex i)*A 1 (tailIndex j)+A 1 (tailIndex i)*A 0 (tailIndex j))+
      A 0 0*A 1 (tailIndex i)*A 1 (tailIndex j))
/-- The leading two-coordinate minor of the cleared tail Schur form. -/
def minor (A : Matrix (Fin 5) (Fin 5) ℝ) : ℝ := schur A 0 0*schur A 1 1-(schur A 0 1)^2
/-- The determinant polynomial of the symmetric cleared tail Schur form. -/
def determinant (A : Matrix (Fin 5) (Fin 5) ℝ) : ℝ := minor A*schur A 2 2-
  (schur A 1 1*(schur A 0 2)^2-2*schur A 0 1*schur A 0 2*schur A 1 2+schur A 0 0*(schur A 1 2)^2)
/-- The quadratic form of the symmetric cleared tail Schur matrix. -/
def tailQuadratic (A : Matrix (Fin 5) (Fin 5) ℝ) (u v w : ℝ) : ℝ :=
  schur A 0 0*u^2+2*schur A 0 1*u*v+2*schur A 0 2*u*w+
    schur A 1 1*v^2+2*schur A 1 2*v*w+schur A 2 2*w^2
private theorem tail_square_completion (A : Matrix (Fin 5) (Fin 5) ℝ) (u v w : ℝ) :
    (schur A 0 0*minor A)*tailQuadratic A u v w =
      minor A*(schur A 0 0*u+schur A 0 1*v+schur A 0 2*w)^2+
      (minor A*v+(schur A 0 0*schur A 1 2-schur A 0 1*schur A 0 2)*w)^2+
      schur A 0 0*determinant A*w^2 := by
  unfold tailQuadratic determinant minor
  ring
private theorem tailQuadratic_pos {A : Matrix (Fin 5) (Fin 5) ℝ}
    (hs : 0 < schur A 0 0) (hm : 0 < minor A) (hd : 0 < determinant A)
    (u v w : ℝ) (h : u ≠ 0 ∨ v ≠ 0 ∨ w ≠ 0) : 0 < tailQuadratic A u v w := by
  apply pos_of_mul_pos_right ?_ (mul_pos hs hm).le
  rw [tail_square_completion]
  by_cases hw : w = 0
  · subst w
    simp only [mul_zero, add_zero, zero_pow (by decide : (2 : ℕ) ≠ 0)]
    by_cases hv : v = 0
    · subst v
      simp only [mul_zero, add_zero, zero_pow (by decide : (2 : ℕ) ≠ 0)]
      have hu : u ≠ 0 := h.resolve_right (by simp)
      exact mul_pos hm (sq_pos_of_ne_zero (mul_ne_zero hs.ne' hu))
    · exact add_pos_of_nonneg_of_pos (mul_nonneg hm.le (sq_nonneg _))
        (sq_pos_of_ne_zero (mul_ne_zero hm.ne' hv))
  · exact add_pos_of_nonneg_of_pos
      (add_nonneg (mul_nonneg hm.le (sq_nonneg _)) (sq_nonneg _))
      (mul_pos (mul_pos hs hd) (sq_pos_of_ne_zero hw))
/-- The quadratic form represented by the upper triangle of a five-coordinate matrix. -/
def quadratic (A : Matrix (Fin 5) (Fin 5) ℝ) (x0 x1 x2 x3 x4 : ℝ) : ℝ :=
  A 0 0*x0^2+2*A 0 1*x0*x1+2*A 0 2*x0*x2+2*A 0 3*x0*x3+2*A 0 4*x0*x4+
  A 1 1*x1^2+2*A 1 2*x1*x2+2*A 1 3*x1*x3+2*A 1 4*x1*x4+
  A 2 2*x2^2+2*A 2 3*x2*x3+2*A 2 4*x2*x4+A 3 3*x3^2+2*A 3 4*x3*x4+A 4 4*x4^2
/-- The first head coordinate in the Schur square completion. -/
def firstCoordinate (A : Matrix (Fin 5) (Fin 5) ℝ) (x0 x1 x2 x3 x4 : ℝ) : ℝ :=
  A 0 0*x0+A 0 1*x1+A 0 2*x2+A 0 3*x3+A 0 4*x4
/-- The second head coordinate after eliminating the first. -/
def secondCoordinate (A : Matrix (Fin 5) (Fin 5) ℝ) (x1 x2 x3 x4 : ℝ) : ℝ :=
  delta A*x1+A 0 0*(A 1 2*x2+A 1 3*x3+A 1 4*x4)-A 0 1*(A 0 2*x2+A 0 3*x3+A 0 4*x4)
/-- Two head squares separate the five-coordinate form from its cleared Schur tail. -/
theorem quadratic_square_completion (A : Matrix (Fin 5) (Fin 5) ℝ) (x0 x1 x2 x3 x4 : ℝ) :
    (A 0 0*delta A)*quadratic A x0 x1 x2 x3 x4 =
      delta A*(firstCoordinate A x0 x1 x2 x3 x4)^2+
      (secondCoordinate A x1 x2 x3 x4)^2+A 0 0*tailQuadratic A x2 x3 x4 := by
  simp only [quadratic, firstCoordinate, secondCoordinate, tailQuadratic, schur, delta,
    show tailIndex 0 = 2 by rfl, show tailIndex 1 = 3 by rfl, show tailIndex 2 = 4 by rfl]
  ring
private theorem quadratic_pos {A : Matrix (Fin 5) (Fin 5) ℝ}
    (hr : 0 < A 0 0) (hd : 0 < delta A) (hs : 0 < schur A 0 0)
    (hm : 0 < minor A) (htd : 0 < determinant A) (x0 x1 x2 x3 x4 : ℝ)
    (h : x0 ≠ 0 ∨ x1 ≠ 0 ∨ x2 ≠ 0 ∨ x3 ≠ 0 ∨ x4 ≠ 0) :
    0 < quadratic A x0 x1 x2 x3 x4 := by
  apply pos_of_mul_pos_right ?_ (mul_pos hr hd).le
  rw [quadratic_square_completion]
  by_cases ht : x2 ≠ 0 ∨ x3 ≠ 0 ∨ x4 ≠ 0
  · exact add_pos_of_nonneg_of_pos
      (add_nonneg (mul_nonneg hd.le (sq_nonneg _)) (sq_nonneg _))
      (mul_pos hr (tailQuadratic_pos hs hm htd x2 x3 x4 ht))
  · push Not at ht
    rcases ht with ⟨h2,h3,h4⟩
    subst x2; subst x3; subst x4
    simp only [firstCoordinate, secondCoordinate, tailQuadratic, mul_zero,
      add_zero, sub_zero, zero_pow (by decide : (2 : ℕ) ≠ 0)]
    by_cases h1 : x1 = 0
    · subst x1
      simp only [mul_zero, add_zero, zero_pow (by decide : (2 : ℕ) ≠ 0)]
      have h0 : x0 ≠ 0 := h.resolve_right (by simp)
      exact mul_pos hd (sq_pos_of_ne_zero (mul_ne_zero hr.ne' h0))
    · exact add_pos_of_nonneg_of_pos (mul_nonneg hd.le (sq_nonneg _))
        (sq_pos_of_ne_zero (mul_ne_zero hd.ne' h1))
/-- A symmetric matrix evaluates to its upper-triangle quadratic expression. -/
theorem matrix_energy {A : Matrix (Fin 5) (Fin 5) ℝ}
    (hA : ∀ i j, A i j = A j i) (v : Fin 5 → ℝ) :
    v ⬝ᵥ (A *ᵥ v) = quadratic A (v 0) (v 1) (v 2) (v 3) (v 4) := by
  norm_num [dotProduct, Matrix.mulVec, Fin.sum_univ_succ]
  simp only [show (Fin.succ (2 : Fin 4) : Fin 5) = 3 by rfl,
    show (Fin.succ (Fin.succ (2 : Fin 3)) : Fin 5) = 4 by rfl]
  simp only [hA 1 0,hA 2 0,hA 3 0,hA 4 0,hA 2 1,hA 3 1,hA 4 1,hA 3 2,hA 4 2,hA 4 3,quadratic]
  ring
/-- Five strictly positive Schur signs certify a real symmetric five-coordinate matrix. -/
theorem posDef_of_schur_signs {A : Matrix (Fin 5) (Fin 5) ℝ}
    (hA : ∀ i j, A i j = A j i) (hr : 0 < A 0 0) (hd : 0 < delta A)
    (hs : 0 < schur A 0 0) (hm : 0 < minor A) (htd : 0 < determinant A) : A.PosDef := by
  refine Matrix.posDef_iff_dotProduct_mulVec.mpr ⟨?_, ?_⟩
  · ext i j
    simp only [Matrix.conjTranspose_apply, star_trivial, hA]
  · intro v hv
    simp only [star_trivial, matrix_energy hA]
    apply quadratic_pos hr hd hs hm htd
    by_contra h
    push Not at h
    rcases h with ⟨h0,h1,h2,h3,h4⟩
    apply hv
    funext i
    fin_cases i
    · exact h0
    · exact h1
    · exact h2
    · exact h3
    · exact h4
-- Coefficients in q−5 of the upper-weight endpoint after scaling by 128 q²².
private def m0 : ℕ → ℝ
  | 0 => 14953810882568359375
  | 1 => 134244171142578125000
  | 2 => 3469591564941406250000
  | 3 => 142909033115234375000000
  | 4 => 7852483344968750000000000
  | 5 => 527355244013318750000000000
  | 6 => 41189141390287355000000000000
  | 7 => 3650251375899962984000000000000
  | 8 => 366856006145403944835200000000000
  | _ => 0
private def m1 : ℕ → ℝ
  | 0 => 74341196136474609375
  | 1 => 659109933471679687500
  | 2 => 16868372319335937500000
  | 3 => 690418040734375000000000
  | 4 => 37866688569914062500000000
  | 5 => 2551378181933198750000000000
  | 6 => 200774116687165753000000000000
  | 7 => 17899584206181306021600000000000
  | 8 => 1776198643295149070704640000000000
  | _ => 0
private def m2 : ℕ → ℝ
  | 0 => 176990063140869140625
  | 1 => 1551203505249023437500
  | 2 => 39347084583007812500000
  | 3 => 1601241293355468750000000
  | 4 => 87638901655068750000000000
  | 5 => 5914679958638991500000000000
  | 6 => 467399247522762303600000000000
  | 7 => 41777838478098219636960000000000
  | 8 => 4108748248679686962454400000000000
  | _ => 0
private def m3 : ℕ → ℝ
  | 0 => 268554843231201171875
  | 1 => 2328869206665039062500
  | 2 => 58595297210449218750000
  | 3 => 2372006821157812500000000
  | 4 => 129540622648696875000000000
  | 5 => 8749527651950981450000000000
  | 6 => 693411014445697065440000000000
  | 7 => 62144738983495645947200000000000
  | 8 => 6101974313082265949445760000000000
  | _ => 0
private def m4 : ℕ → ℝ
  | 0 => 291569873309326171875
  | 1 => 2503990265991210937500
  | 2 => 62537069989453125000000
  | 3 => 2519358152321718750000000
  | 4 => 137293383798493312500000000
  | 5 => 9277428052756567160000000000
  | 6 => 737159618144554330000000000000
  | 7 => 66325935640924148871360000000000
  | 8 => 6545182226230707562528000000000000
  | _ => 0
private def m5 : ℕ → ℝ
  | 0 => 241061143112548828125
  | 1 => 2051926243315429687500
  | 2 => 50903352267035156250000
  | 3 => 2041685405460534375000000
  | 4 => 111043441995145740000000000
  | 5 => 7506977923075465550000000000
  | 6 => 598140819422798554560000000000
  | 7 => 54099864831779699184000000000000
  | 8 => 5387841202252179392938240000000000
  | _ => 0
private def m6 : ℕ → ℝ
  | 0 => 157701114719873046875
  | 1 => 1331557989856445312500
  | 2 => 32832387113087500000000
  | 3 => 1311689691848063125000000
  | 4 => 71218805051254412500000000
  | 5 => 4817623642007720160000000000
  | 6 => 385042513655592878400000000000
  | 7 => 35038800053687435241600000000000
  | 8 => 3527796875565895631695360000000000
  | _ => 0
private def m7 : ℕ → ℝ
  | 0 => 83733890753994140625
  | 1 => 701848052402929687500
  | 2 => 17211149143528281250000
  | 3 => 685213921207400000000000
  | 4 => 37152754603578547500000000
  | 5 => 2515383876213210750000000000
  | 6 => 201717859049635202640000000000
  | 7 => 18476086579976974640640000000000
  | 8 => 1880858696681557501841920000000000
  | _ => 0
private def m8 : ℕ → ℝ
  | 0 => 36723585944238281250
  | 1 => 305780056773867187500
  | 2 => 7462029826602343750000
  | 3 => 296186849391163125000000
  | 4 => 16043156036672362500000000
  | 5 => 1087434982353891750000000000
  | 6 => 87520926543373707360000000000
  | 7 => 8069479438180401490080000000000
  | 8 => 830095484035457917833088000000000
  | _ => 0
private def m9 : ℕ → ℝ
  | 0 => 13468090625156250000
  | 1 => 111475374732421875000
  | 2 => 2708662077663906250000
  | 3 => 107241238558609375000000
  | 4 => 5805129516383852500000000
  | 5 => 394055543103023290000000000
  | 6 => 31836292756182567400000000000
  | 7 => 2954674776055779531040000000000
  | 8 => 306926607478897491157529600000000
  | _ => 0
private def m10 : ℕ → ℝ
  | 0 => 4165670437500000000
  | 1 => 34295332494375000000
  | 2 => 830187530082812500000
  | 3 => 32800898145471875000000
  | 4 => 1775141912483947500000000
  | 5 => 120710767829329906000000000
  | 6 => 9791542574649420464000000000
  | 7 => 914695171929501736899840000000
  | 8 => 95904983775741749617648640000000
  | _ => 0
private def m11 : ℕ → ℝ
  | 0 => 1092741300000000000
  | 1 => 8953560000000000000
  | 2 => 216037645802500000000
  | 3 => 8522020060698750000000
  | 4 => 461274846596014500000000
  | 5 => 31432471570105073200000000
  | 6 => 2560427496106728233280000000
  | 7 => 240761161500671740810752000000
  | 8 => 25474305689883318398721843200000
  | _ => 0
private def m12 : ℕ → ℝ
  | 0 => 243888417500000000
  | 1 => 1989906100000000000
  | 2 => 47882372720000000000
  | 3 => 1886638238150000000000
  | 4 => 102175751243702600000000
  | 5 => 6979328851665368880000000
  | 6 => 571050681607929427392000000
  | 7 => 54055318352562148639180800000
  | 8 => 5771610046899352811169996800000
  | _ => 0
private def m13 : ℕ → ℝ
  | 0 => 46361805000000000
  | 1 => 376863480000000000
  | 2 => 9047798480000000000
  | 3 => 356242767232000000000
  | 4 => 19311558194287680000000
  | 5 => 1322736913369528800000000
  | 6 => 108734870566088293747200000
  | 7 => 10363029393504336042547200000
  | 8 => 1116648032633101211907399680000
  | _ => 0
private def m14 : ℕ → ℝ
  | 0 => 7498606500000000
  | 1 => 60756300000000000
  | 2 => 1456001312000000000
  | 3 => 57311069337600000000
  | 4 => 3110917720879104000000
  | 5 => 213736603815080908800000
  | 6 => 17657224106768690304000000
  | 7 => 1694619014973888273561600000
  | 8 => 184293436171398559748120576000
  | _ => 0
private def m15 : ℕ → ℝ
  | 0 => 1028664560000000
  | 1 => 8311177600000000
  | 2 => 198897715200000000
  | 3 => 7829896065024000000
  | 4 => 425742367474483200000
  | 5 => 29350415909069783040000
  | 6 => 2437378196910206853120000
  | 7 => 235607076713331622922649600
  | 8 => 25862602078578743759170764800
  | _ => 0
private def m16 : ℕ → ℝ
  | 0 => 119018394000000
  | 1 => 959310000000000
  | 2 => 22934943168000000
  | 3 => 903318755174400000
  | 4 => 49218592845127680000
  | 5 => 3405756271927001088000
  | 6 => 284383749066524275507200
  | 7 => 27693182957611471259566080
  | 8 => 3068632245974382396032811008
  | _ => 0
private def m17 : ℕ → ℝ
  | 0 => 11516234400000
  | 1 => 92635488000000
  | 2 => 2213359065600000
  | 3 => 87251223859200000
  | 4 => 4765481719455744000
  | 5 => 331088286557090611200
  | 6 => 27805666623888666132480
  | 7 => 2728301765674867183583232
  | 8 => 305212566363627505014800384
  | _ => 0
private def m18 : ℕ → ℝ
  | 0 => 920519600000
  | 1 => 7392246400000
  | 2 => 176579737600000
  | 3 => 6969267220480000
  | 4 => 381691044762419200
  | 5 => 26633711566304051200
  | 6 => 2250255690149876727808
  | 7 => 222520562151585507966976
  | 8 => 25134762955975398600474624
  | _ => 0
private def m19 : ℕ → ℝ
  | 0 => 59727360000
  | 1 => 479001600000
  | 2 => 11442887680000
  | 3 => 452324163584000
  | 4 => 24848417212661760
  | 5 => 1741905709151813632
  | 6 => 148095924450501853184
  | 7 => 14762049862019391160320
  | 8 => 1683853911878583535534080
  | _ => 0
private def m20 : ℕ → ℝ
  | 0 => 3066940800
  | 1 => 24571008000
  | 2 => 587206144000
  | 3 => 23254387998720
  | 4 => 1281752280465408
  | 5 => 90292623209660416
  | 6 => 7726638353596022784
  | 7 => 776499965098847109120
  | 8 => 89455869717058242478080
  | _ => 0
private def m21 : ℕ → ℝ
  | 0 => 119947520
  | 1 => 960256000
  | 2 => 22964080640
  | 3 => 911353413632
  | 4 => 50414304886784
  | 5 => 3569704532705280
  | 6 => 307528207140126720
  | 7 => 31164456690914426880
  | 8 => 3626517885367992975360
  | _ => 0
private def m22 : ℕ → ℝ
  | 0 => 3357312
  | 1 => 26864640
  | 2 => 643063808
  | 3 => 25581715456
  | 4 => 1420604473344
  | 5 => 101130373693440
  | 6 => 8772742828523520
  | 7 => 896609801490923520
  | 8 => 105401003847167508480
  | _ => 0
private def m23 : ℕ → ℝ
  | 0 => 59904
  | 1 => 479232
  | 2 => 11485184
  | 3 => 458096640
  | 4 => 25543311360
  | 5 => 1828548771840
  | 6 => 159749630853120
  | 7 => 16468861507338240
  | 8 => 1955949366686515200
  | _ => 0
private def m24 : ℕ → ℝ
  | 0 => 512
  | 1 => 4096
  | 2 => 98304
  | 3 => 3932160
  | 4 => 220200960
  | 5 => 15854469120
  | 6 => 1395193282560
  | 7 => 145100101386240
  | 8 => 17412012166348800
  | _ => 0
-- Exact entries after the Gaussian change of basis and zeroth-moment subtraction.
private def e00 (m : ℕ → ℝ) : ℝ := m 0 * (999 / 1000)
private def e01 (m : ℕ → ℝ) : ℝ := -m 0 + m 1 * (1 / 8)
private def e02 (m : ℕ → ℝ) : ℝ := (m 0 * (3 / 4) + m 1 * (-3 / 16) + m 2 * (1 / 256) - 0)
private def e03 (m : ℕ → ℝ) : ℝ := (m 0 * (-5 / 8) + m 1 * (15 / 64) + m 2 * (-5 / 512) + m 3 * (1 / 12288) - 0)
private def e04 (m : ℕ → ℝ) : ℝ := (m 0 * (35 / 64) + m 1 * (-35 / 128) + m 2 * (35 / 2048) + m 3 * (-7 / 24576) + m 4 * (1 / 786432) -
      0)
private def e11 (m : ℕ → ℝ) : ℝ := m 0 * (999 / 1000) + m 1 * (-1 / 4) + m 2 * (1 / 64)
private def e12 (m : ℕ → ℝ) : ℝ := (m 0 * (-3 / 4) + m 1 * (9 / 32) + m 2 * (-7 / 256) + m 3 * (1 / 2048) - 0)
private def e13 (m : ℕ → ℝ) : ℝ := (m 0 * (5 / 8) + m 1 * (-5 / 16) + m 2 * (5 / 128) + m 3 * (-1 / 768) + m 4 * (1 / 98304) -
      0)
private def e14 (m : ℕ → ℝ) : ℝ := (m 0 * (-35 / 64) + m 1 * (175 / 512) + m 2 * (-105 / 2048) + m 3 * (119 / 49152) + m 4 * (-29 / 786432) +
        m 5 * (1 / 6291456) -
      0)
private def e22 (m : ℕ → ℝ) : ℝ := m 0 * (1123 / 2000) + m 1 * (-9 / 32) + m 2 * (21 / 512) + m 3 * (-3 / 2048) + m 4 * (1 / 65536)
private def e23 (m : ℕ → ℝ) : ℝ := (m 0 * (-15 / 32) + m 1 * (75 / 256) + m 2 * (-55 / 1024) + m 3 * (23 / 8192) + m 4 * (-7 / 131072) +
        m 5 * (1 / 3145728) -
      0)
private def e24 (m : ℕ → ℝ) : ℝ := (m 0 * (105 / 256) + m 1 * (-315 / 1024) + m 2 * (1085 / 16384) + m 3 * (-147 / 32768) + m 4 * (127 / 1048576) +
          m 5 * (-17 / 12582912) +
        m 6 * (1 / 201326592) -
      0)
private def e33 (m : ℕ → ℝ) : ℝ := m 0 * (3117 / 8000) + m 1 * (-75 / 256) + m 2 * (275 / 4096) + m 3 * (-115 / 24576) + m 4 * (35 / 262144) +
        m 5 * (-5 / 3145728) +
      m 6 * (1 / 150994944)
private def e34 (m : ℕ → ℝ) : ℝ := (m 0 * (-175 / 512) + m 1 * (1225 / 4096) + m 2 * (-2625 / 32768) + m 3 * (5425 / 786432) + m 4 * (-1615 / 6291456) +
            m 5 * (75 / 16777216) +
          m 6 * (-43 / 1207959552) +
        m 7 * (1 / 9663676416) -
      0)
private def e44 (m : ℕ → ℝ) : ℝ := m 0 * (152613 / 512000) + m 1 * (-1225 / 4096) + m 2 * (6125 / 65536) + m 3 * (-7595 / 786432) +
              m 4 * (11305 / 25165824) +
            m 5 * (-175 / 16777216) +
          m 6 * (301 / 2415919104) +
        m 7 * (-7 / 9663676416) +
      m 8 * (1 / 618475290624)
private def entryPoly (m : ℕ → ℝ) (i j : Fin 5) : ℝ :=
  match i.val,j.val with
  | 0,0 => e00 m
  | 0,1 | 1,0 => e01 m
  | 0,2 | 2,0 => e02 m
  | 0,3 | 3,0 => e03 m
  | 0,4 | 4,0 => e04 m
  | 1,1 => e11 m
  | 1,2 | 2,1 => e12 m
  | 1,3 | 3,1 => e13 m
  | 1,4 | 4,1 => e14 m
  | 2,2 => e22 m
  | 2,3 | 3,2 => e23 m
  | 2,4 | 4,2 => e24 m
  | 3,3 => e33 m
  | 3,4 | 4,3 => e34 m
  | 4,4 => e44 m
  | _,_ => 0
private theorem reserve_signs_0 : 0 < entryPoly m0 0 0 ∧ 0 < delta (entryPoly m0) ∧
    0 < schur (entryPoly m0) 0 0 ∧ 0 < minor (entryPoly m0) ∧ 0 < determinant (entryPoly m0) := by
  norm_num [delta,schur,minor,determinant,tailIndex,entryPoly,m0, e00, e01, e02, e03, e04, e11, e12, e13, e14, e22, e23, e24, e33, e34, e44]
private theorem reserve_signs_1 : 0 < entryPoly m1 0 0 ∧ 0 < delta (entryPoly m1) ∧
    0 < schur (entryPoly m1) 0 0 ∧ 0 < minor (entryPoly m1) ∧ 0 < determinant (entryPoly m1) := by
  norm_num [delta,schur,minor,determinant,tailIndex,entryPoly,m1, e00, e01, e02, e03, e04, e11, e12, e13, e14, e22, e23, e24, e33, e34, e44]
private theorem reserve_signs_2 : 0 < entryPoly m2 0 0 ∧ 0 < delta (entryPoly m2) ∧
    0 < schur (entryPoly m2) 0 0 ∧ 0 < minor (entryPoly m2) ∧ 0 < determinant (entryPoly m2) := by
  norm_num [delta,schur,minor,determinant,tailIndex,entryPoly,m2, e00, e01, e02, e03, e04, e11, e12, e13, e14, e22, e23, e24, e33, e34, e44]
private theorem reserve_signs_3 : 0 < entryPoly m3 0 0 ∧ 0 < delta (entryPoly m3) ∧
    0 < schur (entryPoly m3) 0 0 ∧ 0 < minor (entryPoly m3) ∧ 0 < determinant (entryPoly m3) := by
  norm_num [delta,schur,minor,determinant,tailIndex,entryPoly,m3, e00, e01, e02, e03, e04, e11, e12, e13, e14, e22, e23, e24, e33, e34, e44]
private theorem reserve_signs_4 : 0 < entryPoly m4 0 0 ∧ 0 < delta (entryPoly m4) ∧
    0 < schur (entryPoly m4) 0 0 ∧ 0 < minor (entryPoly m4) ∧ 0 < determinant (entryPoly m4) := by
  norm_num [delta,schur,minor,determinant,tailIndex,entryPoly,m4, e00, e01, e02, e03, e04, e11, e12, e13, e14, e22, e23, e24, e33, e34, e44]
private theorem reserve_signs_5 : 0 < entryPoly m5 0 0 ∧ 0 < delta (entryPoly m5) ∧
    0 < schur (entryPoly m5) 0 0 ∧ 0 < minor (entryPoly m5) ∧ 0 < determinant (entryPoly m5) := by
  norm_num [delta,schur,minor,determinant,tailIndex,entryPoly,m5, e00, e01, e02, e03, e04, e11, e12, e13, e14, e22, e23, e24, e33, e34, e44]
private theorem reserve_signs_6 : 0 < entryPoly m6 0 0 ∧ 0 < delta (entryPoly m6) ∧
    0 < schur (entryPoly m6) 0 0 ∧ 0 < minor (entryPoly m6) ∧ 0 < determinant (entryPoly m6) := by
  norm_num [delta,schur,minor,determinant,tailIndex,entryPoly,m6, e00, e01, e02, e03, e04, e11, e12, e13, e14, e22, e23, e24, e33, e34, e44]
private theorem reserve_signs_7 : 0 < entryPoly m7 0 0 ∧ 0 < delta (entryPoly m7) ∧
    0 < schur (entryPoly m7) 0 0 ∧ 0 < minor (entryPoly m7) ∧ 0 < determinant (entryPoly m7) := by
  norm_num [delta,schur,minor,determinant,tailIndex,entryPoly,m7, e00, e01, e02, e03, e04, e11, e12, e13, e14, e22, e23, e24, e33, e34, e44]
private theorem reserve_signs_8 : 0 < entryPoly m8 0 0 ∧ 0 < delta (entryPoly m8) ∧
    0 < schur (entryPoly m8) 0 0 ∧ 0 < minor (entryPoly m8) ∧ 0 < determinant (entryPoly m8) := by
  norm_num [delta,schur,minor,determinant,tailIndex,entryPoly,m8, e00, e01, e02, e03, e04, e11, e12, e13, e14, e22, e23, e24, e33, e34, e44]
private theorem reserve_signs_9 : 0 < entryPoly m9 0 0 ∧ 0 < delta (entryPoly m9) ∧
    0 < schur (entryPoly m9) 0 0 ∧ 0 < minor (entryPoly m9) ∧ 0 < determinant (entryPoly m9) := by
  norm_num [delta,schur,minor,determinant,tailIndex,entryPoly,m9, e00, e01, e02, e03, e04, e11, e12, e13, e14, e22, e23, e24, e33, e34, e44]
private theorem reserve_signs_10 : 0 < entryPoly m10 0 0 ∧ 0 < delta (entryPoly m10) ∧
    0 < schur (entryPoly m10) 0 0 ∧ 0 < minor (entryPoly m10) ∧ 0 < determinant (entryPoly m10) := by
  norm_num [delta,schur,minor,determinant,tailIndex,entryPoly,m10, e00, e01, e02, e03, e04, e11, e12, e13, e14, e22, e23, e24, e33, e34, e44]
private theorem reserve_signs_11 : 0 < entryPoly m11 0 0 ∧ 0 < delta (entryPoly m11) ∧
    0 < schur (entryPoly m11) 0 0 ∧ 0 < minor (entryPoly m11) ∧ 0 < determinant (entryPoly m11) := by
  norm_num [delta,schur,minor,determinant,tailIndex,entryPoly,m11, e00, e01, e02, e03, e04, e11, e12, e13, e14, e22, e23, e24, e33, e34, e44]
private theorem reserve_signs_12 : 0 < entryPoly m12 0 0 ∧ 0 < delta (entryPoly m12) ∧
    0 < schur (entryPoly m12) 0 0 ∧ 0 < minor (entryPoly m12) ∧ 0 < determinant (entryPoly m12) := by
  norm_num [delta,schur,minor,determinant,tailIndex,entryPoly,m12, e00, e01, e02, e03, e04, e11, e12, e13, e14, e22, e23, e24, e33, e34, e44]
private theorem reserve_signs_13 : 0 < entryPoly m13 0 0 ∧ 0 < delta (entryPoly m13) ∧
    0 < schur (entryPoly m13) 0 0 ∧ 0 < minor (entryPoly m13) ∧ 0 < determinant (entryPoly m13) := by
  norm_num [delta,schur,minor,determinant,tailIndex,entryPoly,m13, e00, e01, e02, e03, e04, e11, e12, e13, e14, e22, e23, e24, e33, e34, e44]
private theorem reserve_signs_14 : 0 < entryPoly m14 0 0 ∧ 0 < delta (entryPoly m14) ∧
    0 < schur (entryPoly m14) 0 0 ∧ 0 < minor (entryPoly m14) ∧ 0 < determinant (entryPoly m14) := by
  norm_num [delta,schur,minor,determinant,tailIndex,entryPoly,m14, e00, e01, e02, e03, e04, e11, e12, e13, e14, e22, e23, e24, e33, e34, e44]
private theorem reserve_signs_15 : 0 < entryPoly m15 0 0 ∧ 0 < delta (entryPoly m15) ∧
    0 < schur (entryPoly m15) 0 0 ∧ 0 < minor (entryPoly m15) ∧ 0 < determinant (entryPoly m15) := by
  norm_num [delta,schur,minor,determinant,tailIndex,entryPoly,m15, e00, e01, e02, e03, e04, e11, e12, e13, e14, e22, e23, e24, e33, e34, e44]
private theorem reserve_signs_16 : 0 < entryPoly m16 0 0 ∧ 0 < delta (entryPoly m16) ∧
    0 < schur (entryPoly m16) 0 0 ∧ 0 < minor (entryPoly m16) ∧ 0 < determinant (entryPoly m16) := by
  norm_num [delta,schur,minor,determinant,tailIndex,entryPoly,m16, e00, e01, e02, e03, e04, e11, e12, e13, e14, e22, e23, e24, e33, e34, e44]
private theorem reserve_signs_17 : 0 < entryPoly m17 0 0 ∧ 0 < delta (entryPoly m17) ∧
    0 < schur (entryPoly m17) 0 0 ∧ 0 < minor (entryPoly m17) ∧ 0 < determinant (entryPoly m17) := by
  norm_num [delta,schur,minor,determinant,tailIndex,entryPoly,m17, e00, e01, e02, e03, e04, e11, e12, e13, e14, e22, e23, e24, e33, e34, e44]
private theorem reserve_signs_18 : 0 < entryPoly m18 0 0 ∧ 0 < delta (entryPoly m18) ∧
    0 < schur (entryPoly m18) 0 0 ∧ 0 < minor (entryPoly m18) ∧ 0 < determinant (entryPoly m18) := by
  norm_num [delta,schur,minor,determinant,tailIndex,entryPoly,m18, e00, e01, e02, e03, e04, e11, e12, e13, e14, e22, e23, e24, e33, e34, e44]
private theorem reserve_signs_19 : 0 < entryPoly m19 0 0 ∧ 0 < delta (entryPoly m19) ∧
    0 < schur (entryPoly m19) 0 0 ∧ 0 < minor (entryPoly m19) ∧ 0 < determinant (entryPoly m19) := by
  norm_num [delta,schur,minor,determinant,tailIndex,entryPoly,m19, e00, e01, e02, e03, e04, e11, e12, e13, e14, e22, e23, e24, e33, e34, e44]
private theorem reserve_signs_20 : 0 < entryPoly m20 0 0 ∧ 0 < delta (entryPoly m20) ∧
    0 < schur (entryPoly m20) 0 0 ∧ 0 < minor (entryPoly m20) ∧ 0 < determinant (entryPoly m20) := by
  norm_num [delta,schur,minor,determinant,tailIndex,entryPoly,m20, e00, e01, e02, e03, e04, e11, e12, e13, e14, e22, e23, e24, e33, e34, e44]
private theorem reserve_signs_21 : 0 < entryPoly m21 0 0 ∧ 0 < delta (entryPoly m21) ∧
    0 < schur (entryPoly m21) 0 0 ∧ 0 < minor (entryPoly m21) ∧ 0 < determinant (entryPoly m21) := by
  norm_num [delta,schur,minor,determinant,tailIndex,entryPoly,m21, e00, e01, e02, e03, e04, e11, e12, e13, e14, e22, e23, e24, e33, e34, e44]
private theorem reserve_signs_22 : 0 < entryPoly m22 0 0 ∧ 0 < delta (entryPoly m22) ∧
    0 < schur (entryPoly m22) 0 0 ∧ 0 < minor (entryPoly m22) ∧ 0 < determinant (entryPoly m22) := by
  norm_num [delta,schur,minor,determinant,tailIndex,entryPoly,m22, e00, e01, e02, e03, e04, e11, e12, e13, e14, e22, e23, e24, e33, e34, e44]
private theorem reserve_signs_23 : 0 < entryPoly m23 0 0 ∧ 0 < delta (entryPoly m23) ∧
    0 < schur (entryPoly m23) 0 0 ∧ 0 < minor (entryPoly m23) ∧ 0 < determinant (entryPoly m23) := by
  norm_num [delta,schur,minor,determinant,tailIndex,entryPoly,m23, e00, e01, e02, e03, e04, e11, e12, e13, e14, e22, e23, e24, e33, e34, e44]
private theorem reserve_signs_24 : 0 < entryPoly m24 0 0 ∧ 0 < delta (entryPoly m24) ∧
    0 < schur (entryPoly m24) 0 0 ∧ 0 < minor (entryPoly m24) ∧ 0 < determinant (entryPoly m24) := by
  norm_num [delta,schur,minor,determinant,tailIndex,entryPoly,m24, e00, e01, e02, e03, e04, e11, e12, e13, e14, e22, e23, e24, e33, e34, e44]
/-- Fixed Gaussian polynomial coordinates for five normalized even moments. -/
def gaussianBasis : Matrix (Fin 5) (Fin 5) ℝ := fun i j =>
  match i.val,j.val with
  | 0,0 => 1
  | 1,0 => -1 | 1,1 => 1/8
  | 2,0 => 3/4 | 2,1 => -3/16 | 2,2 => 1/256
  | 3,0 => -5/8 | 3,1 => 15/64 | 3,2 => -5/512 | 3,3 => 1/12288
  | 4,0 => 35/64 | 4,1 => -35/128 | 4,2 => 35/2048 | 4,3 => -7/24576 | 4,4 => 1/786432
  | _,_ => 0
private def entry (m : ℕ → ℝ) (i j : Fin 5) : ℝ :=
  (∑ u : Fin 5, ∑ v : Fin 5, gaussianBasis i u*gaussianBasis j v*m (u.val+v.val))-
    if i.val=j.val then m 0/1000 else 0
private theorem entry_row_0 (m : ℕ → ℝ) (j : Fin 5) :
    entry m 0 j = entryPoly m 0 j := by
  fin_cases j
  all_goals norm_num [entry,entryPoly,gaussianBasis,Fin.sum_univ_succ, e00, e01, e02, e03, e04, e11, e12, e13, e14, e22, e23, e24, e33, e34, e44]
  all_goals ring
private theorem entry_row_1 (m : ℕ → ℝ) (j : Fin 5) :
    entry m 1 j = entryPoly m 1 j := by
  fin_cases j
  all_goals norm_num [entry,entryPoly,gaussianBasis,Fin.sum_univ_succ, e00, e01, e02, e03, e04, e11, e12, e13, e14, e22, e23, e24, e33, e34, e44]
  all_goals ring
private theorem entry_row_2 (m : ℕ → ℝ) (j : Fin 5) :
    entry m 2 j = entryPoly m 2 j := by
  fin_cases j
  all_goals norm_num [entry,entryPoly,gaussianBasis,Fin.sum_univ_succ, e00, e01, e02, e03, e04, e11, e12, e13, e14, e22, e23, e24, e33, e34, e44]
  all_goals ring
private theorem entry_row_3 (m : ℕ → ℝ) (j : Fin 5) :
    entry m 3 j = entryPoly m 3 j := by
  fin_cases j
  all_goals norm_num [entry,entryPoly,gaussianBasis,Fin.sum_univ_succ, e00, e01, e02, e03, e04, e11, e12, e13, e14, e22, e23, e24, e33, e34, e44]
  all_goals ring
private theorem entry_row_4 (m : ℕ → ℝ) (j : Fin 5) :
    entry m 4 j = entryPoly m 4 j := by
  fin_cases j
  all_goals norm_num [entry,entryPoly,gaussianBasis,Fin.sum_univ_succ, e00, e01, e02, e03, e04, e11, e12, e13, e14, e22, e23, e24, e33, e34, e44]
  all_goals ring
/-- The Gaussian Hankel form minus its diagonal reserve equals the displayed moment polynomial. -/
theorem entry_eq_entryPoly (m : ℕ → ℝ) (i j : Fin 5) : entry m i j = entryPoly m i j := by
  fin_cases i
  · exact entry_row_0 m j
  · exact entry_row_1 m j
  · exact entry_row_2 m j
  · exact entry_row_3 m j
  · exact entry_row_4 m j
/-- The displayed Gaussian Hankel entry polynomial is symmetric. -/
theorem entryPoly_symmetric (m : ℕ → ℝ) (i j : Fin 5) :
    entryPoly m i j = entryPoly m j i := by
  fin_cases i <;> fin_cases j <;> rfl
private def coefficients (j : Fin 25) : ℕ → ℝ :=
  match j.val with
  | 0 => m0
  | 1 => m1
  | 2 => m2
  | 3 => m3
  | 4 => m4
  | 5 => m5
  | 6 => m6
  | 7 => m7
  | 8 => m8
  | 9 => m9
  | 10 => m10
  | 11 => m11
  | 12 => m12
  | 13 => m13
  | 14 => m14
  | 15 => m15
  | 16 => m16
  | 17 => m17
  | 18 => m18
  | 19 => m19
  | 20 => m20
  | 21 => m21
  | 22 => m22
  | 23 => m23
  | 24 => m24
  | _ => m0
private theorem coefficient_signs (j : Fin 25) :
    0 < entryPoly (coefficients j) 0 0 ∧ 0 < delta (entryPoly (coefficients j)) ∧
    0 < schur (entryPoly (coefficients j)) 0 0 ∧ 0 < minor (entryPoly (coefficients j)) ∧
    0 < determinant (entryPoly (coefficients j)) := by
  fin_cases j
  · exact reserve_signs_0
  · exact reserve_signs_1
  · exact reserve_signs_2
  · exact reserve_signs_3
  · exact reserve_signs_4
  · exact reserve_signs_5
  · exact reserve_signs_6
  · exact reserve_signs_7
  · exact reserve_signs_8
  · exact reserve_signs_9
  · exact reserve_signs_10
  · exact reserve_signs_11
  · exact reserve_signs_12
  · exact reserve_signs_13
  · exact reserve_signs_14
  · exact reserve_signs_15
  · exact reserve_signs_16
  · exact reserve_signs_17
  · exact reserve_signs_18
  · exact reserve_signs_19
  · exact reserve_signs_20
  · exact reserve_signs_21
  · exact reserve_signs_22
  · exact reserve_signs_23
  · exact reserve_signs_24
private theorem coefficient_reserve_posDef (j : Fin 25) :
    Matrix.PosDef (entry (coefficients j)) := by
  have he : entry (coefficients j) = entryPoly (coefficients j) :=
    funext fun i => funext fun k => entry_eq_entryPoly _ i k
  rw [he]
  obtain ⟨h0,hd,hs,hm,ht⟩ := coefficient_signs j
  exact posDef_of_schur_signs (entryPoly_symmetric _) h0 hd hs hm ht
private def polynomialMatrix (y : ℝ) : Matrix (Fin 5) (Fin 5) ℝ :=
  fun i j => ∑ k : Fin 25, y^k.val*coefficients k (i.val+j.val)
/-- The congruence associated with the fixed Gaussian polynomial coordinates. -/
def gaussianGram (A : Matrix (Fin 5) (Fin 5) ℝ) : Matrix (Fin 5) (Fin 5) ℝ :=
  fun i j => ∑ u : Fin 5, ∑ v : Fin 5, gaussianBasis i u*gaussianBasis j v*A u v
/-- The explicit double sum is the usual matrix congruence. -/
theorem gaussianGram_eq_congruence (A : Matrix (Fin 5) (Fin 5) ℝ) :
    gaussianGram A = gaussianBasis*A*gaussianBasisᴴ := by
  ext i j
  simp only [gaussianGram,Matrix.mul_apply,Matrix.conjTranspose_apply,star_trivial,
    Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v _
  apply Finset.sum_congr rfl
  intro u _
  ring
/-- Positive semidefiniteness is preserved in Gaussian coordinates. -/
theorem gaussianGram_posSemidef {A : Matrix (Fin 5) (Fin 5) ℝ} (hA : A.PosSemidef) :
    (gaussianGram A).PosSemidef := by
  rw [gaussianGram_eq_congruence]
  exact hA.mul_mul_conjTranspose_same gaussianBasis
private def reserve (A : Matrix (Fin 5) (Fin 5) ℝ) : Matrix (Fin 5) (Fin 5) ℝ :=
  gaussianGram A-(A 0 0/1000) • 1
theorem gaussianGram_add (A C : Matrix (Fin 5) (Fin 5) ℝ) :
    gaussianGram (A+C)=gaussianGram A+gaussianGram C := by
  ext i j
  simp only [gaussianGram, Matrix.add_apply, mul_add, Finset.sum_add_distrib]
theorem gaussianGram_smul (c : ℝ) (A : Matrix (Fin 5) (Fin 5) ℝ) :
    gaussianGram (c • A)=c • gaussianGram A := by
  ext i j
  simp only [gaussianGram, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u _
  apply Finset.sum_congr rfl
  intro v _
  ring
private theorem reserve_add (A C : Matrix (Fin 5) (Fin 5) ℝ) :
    reserve (A+C)=reserve A+reserve C := by
  simp only [reserve, gaussianGram_add, Matrix.add_apply, add_div, add_smul]
  abel
private theorem reserve_smul (c : ℝ) (A : Matrix (Fin 5) (Fin 5) ℝ) :
    reserve (c • A)=c • reserve A := by
  simp only [reserve, gaussianGram_smul, Matrix.smul_apply, smul_eq_mul, smul_sub, smul_smul]
  congr 1
  congr 1
  ring
private theorem finite_reserve_eq {ι : Type*} [Fintype ι]
    (c : ι → ℕ → ℝ) (w : ι → ℝ) :
    reserve (fun i j => ∑ k, w k*c k (i.val+j.val)) =
      ∑ k, w k • entry (c k) := by
  ext i j
  have hsum : (∑ u : Fin 5, ∑ v : Fin 5,
      gaussianBasis i u*gaussianBasis j v*(∑ k : ι, w k*c k (u.val+v.val))) =
      ∑ k : ι, w k*(∑ u : Fin 5, ∑ v : Fin 5,
        gaussianBasis i u*gaussianBasis j v*c k (u.val+v.val)) := by
    simp only [Finset.mul_sum]
    calc
      _ = ∑ u : Fin 5, ∑ k : ι, ∑ v : Fin 5,
          gaussianBasis i u*gaussianBasis j v*(w k*c k (u.val+v.val)) :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_comm
      _ = ∑ k : ι, ∑ u : Fin 5, ∑ v : Fin 5,
          gaussianBasis i u*gaussianBasis j v*(w k*c k (u.val+v.val)) := Finset.sum_comm
      _ = _ := by
        refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun u _ =>
          Finset.sum_congr rfl fun v _ => ?_
        ring
  simp only [reserve, gaussianGram, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
    Finset.sum_apply]
  change (∑ u : Fin 5, ∑ v : Fin 5,
      gaussianBasis i u*gaussianBasis j v*(∑ k : ι, w k*c k (u.val+v.val))) -
      (∑ k : ι, w k*c k 0)/1000*(1 : Matrix (Fin 5) (Fin 5) ℝ) i j =
      ∑ k : ι, w k*((∑ u : Fin 5, ∑ v : Fin 5,
        gaussianBasis i u*gaussianBasis j v*c k (u.val+v.val))-
        if i.val=j.val then c k 0/1000 else 0)
  rw [hsum]
  simp only [mul_sub, Finset.sum_sub_distrib]
  congr 1
  by_cases h : i=j
  · subst j
    simp only [Matrix.one_apply_eq, if_true, mul_one,Finset.sum_div]
    apply Finset.sum_congr rfl
    intro k _
    ring
  · have hv : i.val ≠ j.val := fun he => h (Fin.ext he)
    simp only [Matrix.one_apply_ne h, if_neg hv, mul_zero, Finset.sum_const_zero]
private theorem finite_reserve_posSemidef {ι : Type*} [Fintype ι]
    (c : ι → ℕ → ℝ) (hc : ∀ k, Matrix.PosDef (entry (c k)))
    (w : ι → ℝ) (hw : ∀ k, 0 ≤ w k) :
    (reserve (fun i j => ∑ k, w k*c k (i.val+j.val))).PosSemidef := by
  rw [finite_reserve_eq]
  exact Matrix.posSemidef_sum _ fun k _ => (hc k).posSemidef.smul (hw k)
private theorem polynomial_reserve_posSemidef {y : ℝ} (hy : 0 ≤ y) :
    (reserve (polynomialMatrix y)).PosSemidef :=
  finite_reserve_posSemidef coefficients coefficient_reserve_posDef
    (fun k => y^k.val) (fun k => pow_nonneg hy k.val)
-- Coefficients in q−5 of the zero-weight endpoint after scaling by q⁷.
private def baseM0 : ℕ → ℝ
  | 0 => 3828125
  | 1 => 34375000
  | 2 => 887500000
  | 3 => 36562000000
  | 4 => 2014840000000
  | 5 => 135991809280000
  | 6 => 10641884154880000
  | 7 => 928147588481843200
  | 8 => 87363515095131750400
  | _ => 0
private def baseM1 : ℕ → ℝ
  | 0 => 7546875
  | 1 => 65625000
  | 2 => 1654000000
  | 3 => 67041200000
  | 4 => 3664191360000
  | 5 => 247393720576000
  | 6 => 19549973833318400
  | 7 => 1740728189609410560
  | 8 => 169481337875010420736
  | _ => 0
private def baseM2 : ℕ → ℝ
  | 0 => 6590625
  | 1 => 55875000
  | 2 => 1381300000
  | 3 => 55257600000
  | 4 => 3000413568000
  | 5 => 202698950502400
  | 6 => 16156184963112960
  | 7 => 1464324301788217344
  | 8 => 146712488536561942528
  | _ => 0
private def baseM3 : ℕ → ℝ
  | 0 => 3346875
  | 1 => 27825000
  | 2 => 677800000
  | 3 => 26854240000
  | 4 => 1452069990400
  | 5 => 98275638425600
  | 6 => 7899925124366336
  | 7 => 727642964654292992
  | 8 => 74750577801280094208
  | _ => 0
private def baseM4 : ℕ → ℝ
  | 0 => 1089375
  | 1 => 8925000
  | 2 => 215140000
  | 3 => 8472272000
  | 4 => 457509342720
  | 5 => 31082477318144
  | 6 => 2522359595696128
  | 7 => 236032220957245440
  | 8 => 24813936618881679360
  | _ => 0
private def baseM5 : ℕ → ℝ
  | 0 => 235725
  | 1 => 1911000
  | 2 => 45760000
  | 3 => 1797421440
  | 4 => 97232065536
  | 5 => 6647897833472
  | 6 => 545623703420928
  | 7 => 51920574456791040
  | 8 => 5584507466793615360
  | _ => 0
private def baseM6 : ℕ → ℝ
  | 0 => 33915
  | 1 => 273000
  | 2 => 6515680
  | 3 => 256102144
  | 4 => 13920483328
  | 5 => 960491765760
  | 6 => 79921551114240
  | 7 => 7748417838120960
  | 8 => 853669240236933120
  | _ => 0
private def baseM7 : ℕ → ℝ
  | 0 => 3129
  | 1 => 25080
  | 2 => 598336
  | 3 => 23601152
  | 4 => 1292648448
  | 5 => 90254868480
  | 6 => 7633596579840
  | 7 => 755824160931840
  | 8 => 85475295661916160
  | _ => 0
private def baseM8 : ℕ → ℝ
  | 0 => 168
  | 1 => 1344
  | 2 => 32128
  | 3 => 1274880
  | 4 => 70533120
  | 5 => 4995809280
  | 6 => 430547927040
  | 7 => 43643389870080
  | 8 => 5078503548518400
  | _ => 0
private def baseM9 : ℕ → ℝ
  | 0 => 4
  | 1 => 32
  | 2 => 768
  | 3 => 30720
  | 4 => 1720320
  | 5 => 123863040
  | 6 => 10899947520
  | 7 => 1133594542080
  | 8 => 136031345049600
  | _ => 0
private theorem base_reserve_signs_0 : 0 < entryPoly baseM0 0 0 ∧ 0 < delta (entryPoly baseM0) ∧
    0 < schur (entryPoly baseM0) 0 0 ∧ 0 < minor (entryPoly baseM0) ∧ 0 < determinant (entryPoly baseM0) := by
  norm_num [delta,schur,minor,determinant,tailIndex,entryPoly,baseM0, e00, e01, e02, e03, e04, e11, e12, e13, e14, e22, e23, e24, e33, e34, e44]
private theorem base_reserve_signs_1 : 0 < entryPoly baseM1 0 0 ∧ 0 < delta (entryPoly baseM1) ∧
    0 < schur (entryPoly baseM1) 0 0 ∧ 0 < minor (entryPoly baseM1) ∧ 0 < determinant (entryPoly baseM1) := by
  norm_num [delta,schur,minor,determinant,tailIndex,entryPoly,baseM1, e00, e01, e02, e03, e04, e11, e12, e13, e14, e22, e23, e24, e33, e34, e44]
private theorem base_reserve_signs_2 : 0 < entryPoly baseM2 0 0 ∧ 0 < delta (entryPoly baseM2) ∧
    0 < schur (entryPoly baseM2) 0 0 ∧ 0 < minor (entryPoly baseM2) ∧ 0 < determinant (entryPoly baseM2) := by
  norm_num [delta,schur,minor,determinant,tailIndex,entryPoly,baseM2, e00, e01, e02, e03, e04, e11, e12, e13, e14, e22, e23, e24, e33, e34, e44]
private theorem base_reserve_signs_3 : 0 < entryPoly baseM3 0 0 ∧ 0 < delta (entryPoly baseM3) ∧
    0 < schur (entryPoly baseM3) 0 0 ∧ 0 < minor (entryPoly baseM3) ∧ 0 < determinant (entryPoly baseM3) := by
  norm_num [delta,schur,minor,determinant,tailIndex,entryPoly,baseM3, e00, e01, e02, e03, e04, e11, e12, e13, e14, e22, e23, e24, e33, e34, e44]
private theorem base_reserve_signs_4 : 0 < entryPoly baseM4 0 0 ∧ 0 < delta (entryPoly baseM4) ∧
    0 < schur (entryPoly baseM4) 0 0 ∧ 0 < minor (entryPoly baseM4) ∧ 0 < determinant (entryPoly baseM4) := by
  norm_num [delta,schur,minor,determinant,tailIndex,entryPoly,baseM4, e00, e01, e02, e03, e04, e11, e12, e13, e14, e22, e23, e24, e33, e34, e44]
private theorem base_reserve_signs_5 : 0 < entryPoly baseM5 0 0 ∧ 0 < delta (entryPoly baseM5) ∧
    0 < schur (entryPoly baseM5) 0 0 ∧ 0 < minor (entryPoly baseM5) ∧ 0 < determinant (entryPoly baseM5) := by
  norm_num [delta,schur,minor,determinant,tailIndex,entryPoly,baseM5, e00, e01, e02, e03, e04, e11, e12, e13, e14, e22, e23, e24, e33, e34, e44]
private theorem base_reserve_signs_6 : 0 < entryPoly baseM6 0 0 ∧ 0 < delta (entryPoly baseM6) ∧
    0 < schur (entryPoly baseM6) 0 0 ∧ 0 < minor (entryPoly baseM6) ∧ 0 < determinant (entryPoly baseM6) := by
  norm_num [delta,schur,minor,determinant,tailIndex,entryPoly,baseM6, e00, e01, e02, e03, e04, e11, e12, e13, e14, e22, e23, e24, e33, e34, e44]
private theorem base_reserve_signs_7 : 0 < entryPoly baseM7 0 0 ∧ 0 < delta (entryPoly baseM7) ∧
    0 < schur (entryPoly baseM7) 0 0 ∧ 0 < minor (entryPoly baseM7) ∧ 0 < determinant (entryPoly baseM7) := by
  norm_num [delta,schur,minor,determinant,tailIndex,entryPoly,baseM7, e00, e01, e02, e03, e04, e11, e12, e13, e14, e22, e23, e24, e33, e34, e44]
private theorem base_reserve_signs_8 : 0 < entryPoly baseM8 0 0 ∧ 0 < delta (entryPoly baseM8) ∧
    0 < schur (entryPoly baseM8) 0 0 ∧ 0 < minor (entryPoly baseM8) ∧ 0 < determinant (entryPoly baseM8) := by
  norm_num [delta,schur,minor,determinant,tailIndex,entryPoly,baseM8, e00, e01, e02, e03, e04, e11, e12, e13, e14, e22, e23, e24, e33, e34, e44]
private theorem base_reserve_signs_9 : 0 < entryPoly baseM9 0 0 ∧ 0 < delta (entryPoly baseM9) ∧
    0 < schur (entryPoly baseM9) 0 0 ∧ 0 < minor (entryPoly baseM9) ∧ 0 < determinant (entryPoly baseM9) := by
  norm_num [delta,schur,minor,determinant,tailIndex,entryPoly,baseM9, e00, e01, e02, e03, e04, e11, e12, e13, e14, e22, e23, e24, e33, e34, e44]
private def baseCoefficients (j : Fin 10) : ℕ → ℝ :=
  match j.val with
  | 0 => baseM0
  | 1 => baseM1
  | 2 => baseM2
  | 3 => baseM3
  | 4 => baseM4
  | 5 => baseM5
  | 6 => baseM6
  | 7 => baseM7
  | 8 => baseM8
  | 9 => baseM9
  | _ => baseM0
private theorem base_coefficient_signs (j : Fin 10) :
    0 < entryPoly (baseCoefficients j) 0 0 ∧ 0 < delta (entryPoly (baseCoefficients j)) ∧
    0 < schur (entryPoly (baseCoefficients j)) 0 0 ∧ 0 < minor (entryPoly (baseCoefficients j)) ∧
    0 < determinant (entryPoly (baseCoefficients j)) := by
  fin_cases j
  · exact base_reserve_signs_0
  · exact base_reserve_signs_1
  · exact base_reserve_signs_2
  · exact base_reserve_signs_3
  · exact base_reserve_signs_4
  · exact base_reserve_signs_5
  · exact base_reserve_signs_6
  · exact base_reserve_signs_7
  · exact base_reserve_signs_8
  · exact base_reserve_signs_9
private theorem base_coefficient_reserve_posDef (j : Fin 10) :
    Matrix.PosDef (entry (baseCoefficients j)) := by
  have he : entry (baseCoefficients j) = entryPoly (baseCoefficients j) :=
    funext fun i => funext fun k => entry_eq_entryPoly _ i k
  rw [he]
  obtain ⟨h0,hd,hs,hm,ht⟩ := base_coefficient_signs j
  exact posDef_of_schur_signs (entryPoly_symmetric _) h0 hd hs hm ht
private def basePolynomialMatrix (y : ℝ) : Matrix (Fin 5) (Fin 5) ℝ :=
  fun i j => ∑ k : Fin 10, y^k.val*baseCoefficients k (i.val+j.val)
private theorem base_polynomial_reserve_posSemidef {y : ℝ} (hy : 0 ≤ y) :
    (reserve (basePolynomialMatrix y)).PosSemidef :=
  finite_reserve_posSemidef baseCoefficients base_coefficient_reserve_posDef
    (fun k => y^k.val) (fun k => pow_nonneg hy k.val)
-- The nine radial moments and their cleared-denominator polynomials.
private def r0 (q : ℝ) : ℝ := 9 - q * 12 + q ^ 2 * 4
private def b0 (q : ℝ) : ℝ := 9 - q * 30 + q ^ 2 * 16
private def g0 (q : ℝ) : ℝ := 128*q^(22-0)*r0 q+9765625*q^(7-0)*b0 q
private def r1 (q : ℝ) : ℝ := q * 120 - q ^ 2 * 96 + q ^ 3 * 32
private def b1 (q : ℝ) : ℝ := q * 300 - q ^ 2 * 1356 + q ^ 3 * 1400 - q ^ 4 * 576
private def g1 (q : ℝ) : ℝ := 128*q^(22-1)*r1 q+9765625*q^(7-1)*b1 q
private def r2 (q : ℝ) : ℝ := -(q * 480) + q ^ 2 * 4416 - q ^ 3 * 2432 + q ^ 4 * 768
private def b2 (q : ℝ) : ℝ := -(q * 1200) + q ^ 2 * 39696 - q ^ 3 * 171200 + q ^ 4 * 200784 - q ^ 5 * 108000 + q ^ 6 * 20736
private def g2 (q : ℝ) : ℝ := 128*q^(22-2)*r2 q+9765625*q^(7-2)*b2 q
private def r3 (q : ℝ) : ℝ := q * 1920 - q ^ 2 * 82176 + q ^ 3 * 253952 - q ^ 4 * 107520 + q ^ 5 * 30720
private def b3 (q : ℝ) : ℝ := q * 4800 - q ^ 2 * 707136 + q ^ 3 * 10073600 - q ^ 4 * 35416896 + q ^ 5 * 43089600 - q ^ 6 * 25790400 +
        q ^ 7 * 7620480 -
      q ^ 8 * 746496
private def g3 (q : ℝ) : ℝ := 128*q^(22-3)*r3 q+9765625*q^(7-3)*b3 q
private def r4 (q : ℝ) : ℝ := -(q * 7680) + q ^ 2 * 1360896 - q ^ 3 * 12388352 + q ^ 4 * 19611648 - q ^ 5 * 6881280 + q ^ 6 * 1720320
private def b4 (q : ℝ) : ℝ := -(q * 19200) + q ^ 2 * 11602176 - q ^ 3 * 433126400 + q ^ 4 * 3651012864 - q ^ 5 * 10402022400 + q ^ 6 * 12499017216 -
            q ^ 7 * 7892398080 +
          q ^ 8 * 2788598016 -
        q ^ 9 * 468426240 +
      q ^ 10 * 26873856
private def g4 (q : ℝ) : ℝ := 128*q^(22-4)*r4 q+9765625*q^(7-4)*b4 q
private def r5 (q : ℝ) : ℝ := q * 30720 - q ^ 2 * 21958656 + q ^ 3 * 500252672 - q ^ 4 * 1924055040 + q ^ 5 * 1899233280 - q ^ 6 * 578027520 +
      q ^ 7 * 123863040
private def b5 (q : ℝ) : ℝ := q * 76800 - q ^ 2 * 186786816 + q ^ 3 * 16751820800 - q ^ 4 * 293872751616 + q ^ 5 * 1684623283200 -
                  q ^ 6 * 4002679526400 +
                q ^ 7 * 4618622453760 -
              q ^ 8 * 2987682527232 +
            q ^ 9 * 1157721984000 -
          q ^ 10 * 250538241024 +
        q ^ 11 * 26000455680 -
      q ^ 12 * 967458816
private def g5 (q : ℝ) : ℝ := 128*q^(22-5)*r5 q+9765625*q^(7-5)*b5 q
private def r6 (q : ℝ) : ℝ := -(q * 122880) + q ^ 2 * 352075776 - q ^ 3 * 18886787072 + q ^ 4 * 150752329728 - q ^ 5 * 320229212160 +
          q ^ 6 * 221632266240 -
        q ^ 7 * 59949711360 +
      q ^ 8 * 10899947520
private def b6 (q : ℝ) : ℝ := -(q * 307200) + q ^ 2 * 2993197056 - q ^ 3 * 621740441600 + q ^ 4 * 21146177900544 - q ^ 5 * 220856989900800 +
                      q ^ 6 * 939708531818496 -
                    q ^ 7 * 1911756612648960 +
                  q ^ 8 * 2090002567606272 -
                q ^ 9 * 1357634344366080 +
              q ^ 10 * 554264510164992 -
            q ^ 11 * 138376171929600 +
          q ^ 12 * 19385214160896 -
        q ^ 13 * 1342349107200 +
      q ^ 14 * 34828517376
private def g6 (q : ℝ) : ℝ := 128*q^(22-6)*r6 q+9765625*q^(7-6)*b6 q
private def r7 (q : ℝ) : ℝ := q * 491520 - q ^ 2 * 5636161536 + q ^ 3 * 694004744192 - q ^ 4 * 10699371970560 + q ^ 5 * 42564900618240 -
            q ^ 6 * 57797577277440 +
          q ^ 7 * 30323654000640 -
        q ^ 8 * 7368364523520 +
      q ^ 9 * 1133594542080
private def b7 (q : ℝ) : ℝ := q * 1228800 - q ^ 2 * 47909584896 + q ^ 3 * 22681960448000 - q ^ 4 * 1440287890292736 + q ^ 5 * 25873229882572800 -
                          q ^ 6 * 183368931293184000 +
                        q ^ 7 * 614258629468323840 -
                      q ^ 8 * 1091711196399403008 +
                    q ^ 9 * 1124791456149504000 -
                  q ^ 10 * 723717393839751168 +
                q ^ 11 * 304249765406146560 -
              q ^ 12 * 82936975037349888 +
            q ^ 13 * 13929931575705600 -
          q ^ 14 * 1338962033885184 +
        q ^ 15 * 65738826547200 -
      q ^ 16 * 1253826625536
private def g7 (q : ℝ) : ℝ := 128*q^(22-7)*r7 q+9765625*q^(7-7)*b7 q
private def r8 (q : ℝ) : ℝ := -(q * 1966080) + q ^ 2 * 90190381056 - q ^ 3 * 25209606766592 + q ^ 4 * 723521013547008 - q ^ 5 * 5015348591984640 +
              q ^ 6 * 11904065218805760 -
            q ^ 7 * 11342746988052480 +
          q ^ 8 * 4763364265820160 -
        q ^ 9 * 1042906978713600 +
      q ^ 10 * 136031345049600
private def b8 (q : ℝ) : ℝ := -(q * 4915200) + q ^ 2 * 766627086336 - q ^ 3 * 821341473996800 + q ^ 4 * 95352120017485824 -
                                q ^ 5 * 2845887571309363200 +
                              q ^ 6 * 32060191465030680576 -
                            q ^ 7 * 167495442068487536640 +
                          q ^ 8 * 460233151236709613568 -
                        q ^ 9 * 725737675056009707520 +
                      q ^ 10 * 703779563626546987008 -
                    q ^ 11 * 444465339058343116800 +
                  q ^ 12 * 189568590591937609728 -
                q ^ 13 * 54676337965085491200 +
              q ^ 14 * 10342260481727397888 -
            q ^ 15 * 1222973202943180800 +
          q ^ 16 * 84812489945579520 -
        q ^ 17 * 3093817198510080 +
      q ^ 18 * 45137758519296
private def b8div (q : ℝ) : ℝ := -(1 * 4915200) + q ^ (2-1) * 766627086336 - q ^ (3-1) * 821341473996800 + q ^ (4-1) * 95352120017485824 -
                                q ^ (5-1) * 2845887571309363200 +
                              q ^ (6-1) * 32060191465030680576 -
                            q ^ (7-1) * 167495442068487536640 +
                          q ^ (8-1) * 460233151236709613568 -
                        q ^ (9-1) * 725737675056009707520 +
                      q ^ (10-1) * 703779563626546987008 -
                    q ^ (11-1) * 444465339058343116800 +
                  q ^ (12-1) * 189568590591937609728 -
                q ^ (13-1) * 54676337965085491200 +
              q ^ (14-1) * 10342260481727397888 -
            q ^ (15-1) * 1222973202943180800 +
          q ^ (16-1) * 84812489945579520 -
        q ^ (17-1) * 3093817198510080 +
      q ^ (18-1) * 45137758519296
example (q : ℝ) : q*b8div q = b8 q := by
  simp only [b8div,b8]
  norm_num only [Nat.reduceSub]
  ring
private def g8 (q : ℝ) : ℝ := 128*q^(22-8)*r8 q+9765625*b8div q


private theorem polynomial_identity_0 (q : ℝ) :
    (∑ j : Fin 25, (q-5)^j.val*coefficients j 0) = g0 q := by
  norm_num [coefficients, m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15, m16, m17, m18, m19, m20, m21, m22, m23, m24, Fin.sum_univ_succ]
  simp only [g0, r0, b0]
  norm_num only [Nat.reduceSub]
  ring
private theorem polynomial_identity_1 (q : ℝ) :
    (∑ j : Fin 25, (q-5)^j.val*coefficients j 1) = g1 q := by
  norm_num [coefficients, m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15, m16, m17, m18, m19, m20, m21, m22, m23, m24, Fin.sum_univ_succ]
  simp only [g1, r1, b1]
  norm_num only [Nat.reduceSub]
  ring
private theorem polynomial_identity_2 (q : ℝ) :
    (∑ j : Fin 25, (q-5)^j.val*coefficients j 2) = g2 q := by
  norm_num [coefficients, m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15, m16, m17, m18, m19, m20, m21, m22, m23, m24, Fin.sum_univ_succ]
  simp only [g2, r2, b2]
  norm_num only [Nat.reduceSub]
  ring
private theorem polynomial_identity_3 (q : ℝ) :
    (∑ j : Fin 25, (q-5)^j.val*coefficients j 3) = g3 q := by
  norm_num [coefficients, m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15, m16, m17, m18, m19, m20, m21, m22, m23, m24, Fin.sum_univ_succ]
  simp only [g3, r3, b3]
  norm_num only [Nat.reduceSub]
  ring
private theorem polynomial_identity_4 (q : ℝ) :
    (∑ j : Fin 25, (q-5)^j.val*coefficients j 4) = g4 q := by
  norm_num [coefficients, m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15, m16, m17, m18, m19, m20, m21, m22, m23, m24, Fin.sum_univ_succ]
  simp only [g4, r4, b4]
  norm_num only [Nat.reduceSub]
  ring
private theorem polynomial_identity_5 (q : ℝ) :
    (∑ j : Fin 25, (q-5)^j.val*coefficients j 5) = g5 q := by
  norm_num [coefficients, m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15, m16, m17, m18, m19, m20, m21, m22, m23, m24, Fin.sum_univ_succ]
  simp only [g5, r5, b5]
  norm_num only [Nat.reduceSub]
  ring
private theorem polynomial_identity_6 (q : ℝ) :
    (∑ j : Fin 25, (q-5)^j.val*coefficients j 6) = g6 q := by
  norm_num [coefficients, m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15, m16, m17, m18, m19, m20, m21, m22, m23, m24, Fin.sum_univ_succ]
  simp only [g6, r6, b6]
  norm_num only [Nat.reduceSub]
  ring
private theorem polynomial_identity_7 (q : ℝ) :
    (∑ j : Fin 25, (q-5)^j.val*coefficients j 7) = g7 q := by
  norm_num [coefficients, m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15, m16, m17, m18, m19, m20, m21, m22, m23, m24, Fin.sum_univ_succ]
  simp only [g7, r7, b7]
  norm_num only [Nat.reduceSub]
  ring
private theorem polynomial_identity_8 (q : ℝ) :
    (∑ j : Fin 25, (q-5)^j.val*coefficients j 8) = g8 q := by
  norm_num [coefficients, m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15, m16, m17, m18, m19, m20, m21, m22, m23, m24, Fin.sum_univ_succ]
  simp only [g8, r8, b8div]
  norm_num only [Nat.reduceSub]
  ring

-- The radial recurrence identifies all displayed moments with literal reflected jets.
private theorem radial_eight_coeff (a : ℝ) (k : ℕ) :
 radialCoeffs a 8 k = radialStepCoeff a (radialCoeffs a 7) k := rfl
private theorem radial_seven_zero_16 (a : ℝ) : radialCoeffs a 7 16=0 :=
 radialCoeffs_eq_zero a (by norm_num)
private theorem radial_seven_zero_17 (a : ℝ) : radialCoeffs a 7 17=0 :=
 radialCoeffs_eq_zero a (by norm_num)
private theorem radial_seven_zero_18 (a : ℝ) : radialCoeffs a 7 18=0 :=
 radialCoeffs_eq_zero a (by norm_num)
private theorem radial_seven_zero_19 (a : ℝ) : radialCoeffs a 7 19=0 :=
 radialCoeffs_eq_zero a (by norm_num)



local macro "reduce_radial" : tactic =>
  `(tactic| norm_num only [eval_thetaPairRadialEvenPolynomial, Finset.sum_range_succ, radialCoeffs_0_0,
    radialCoeffs_0_1, radialCoeffs_1_0, radialCoeffs_1_1, radialCoeffs_1_2, radialCoeffs_1_3,
    radialCoeffs_2_0, radialCoeffs_2_1, radialCoeffs_2_2, radialCoeffs_2_3, radialCoeffs_2_4,
    radialCoeffs_2_5, radialCoeffs_3_0, radialCoeffs_3_1, radialCoeffs_3_2, radialCoeffs_3_3,
    radialCoeffs_3_4, radialCoeffs_3_5, radialCoeffs_3_6, radialCoeffs_3_7, radialCoeffs_4_0,
    radialCoeffs_4_1, radialCoeffs_4_2, radialCoeffs_4_3, radialCoeffs_4_4, radialCoeffs_4_5,
    radialCoeffs_4_6, radialCoeffs_4_7, radialCoeffs_4_8, radialCoeffs_4_9, radialCoeffs_5_0,
    radialCoeffs_5_1, radialCoeffs_5_2, radialCoeffs_5_3, radialCoeffs_5_4, radialCoeffs_5_5,
    radialCoeffs_5_6, radialCoeffs_5_7, radialCoeffs_5_8, radialCoeffs_5_9, radialCoeffs_5_10,
    radialCoeffs_5_11, radialCoeffs_6_0, radialCoeffs_6_1, radialCoeffs_6_2, radialCoeffs_6_3,
    radialCoeffs_6_4, radialCoeffs_6_5, radialCoeffs_6_6, radialCoeffs_6_7, radialCoeffs_6_8,
    radialCoeffs_6_9, radialCoeffs_6_10, radialCoeffs_6_11, radialCoeffs_6_12,
    radialCoeffs_6_13, radialCoeffs_7_0, radialCoeffs_7_1, radialCoeffs_7_2, radialCoeffs_7_3,
    radialCoeffs_7_4, radialCoeffs_7_5, radialCoeffs_7_6, radialCoeffs_7_7, radialCoeffs_7_8,
    radialCoeffs_7_9, radialCoeffs_7_10, radialCoeffs_7_11, radialCoeffs_7_12,
    radialCoeffs_7_13, radialCoeffs_7_14, radialCoeffs_7_15, radial_eight_coeff,
    radial_seven_zero_16, radial_seven_zero_17, radial_seven_zero_18, radial_seven_zero_19,
    radialStepCoeff, radialInnerCoeff, Nat.reduceAdd, Nat.reduceMul, Nat.reducePow])
/-- The explicit diagonal-pair radial moment of order 0. -/
theorem radial_0 (q : ℝ) :
    (thetaPairRadialEvenPolynomial (q^2) 0).eval (2*q) = r0 q := by
  reduce_radial
  simp only [r0]
  ring
/-- The explicit unequal-pair radial moment of order 0. -/
theorem mixed_0 (q : ℝ) :
    (thetaPairRadialEvenPolynomial (4*q^2) 0).eval (5*q) = b0 q := by
  reduce_radial
  simp only [b0]
  ring
/-- The explicit diagonal-pair radial moment of order 1. -/
theorem radial_1 (q : ℝ) :
    (thetaPairRadialEvenPolynomial (q^2) 1).eval (2*q) = r1 q := by
  reduce_radial
  simp only [r1]
  ring
/-- The explicit unequal-pair radial moment of order 1. -/
theorem mixed_1 (q : ℝ) :
    (thetaPairRadialEvenPolynomial (4*q^2) 1).eval (5*q) = b1 q := by
  reduce_radial
  simp only [b1]
  ring
/-- The explicit diagonal-pair radial moment of order 2. -/
theorem radial_2 (q : ℝ) :
    (thetaPairRadialEvenPolynomial (q^2) 2).eval (2*q) = r2 q := by
  reduce_radial
  simp only [r2]
  ring
/-- The explicit unequal-pair radial moment of order 2. -/
theorem mixed_2 (q : ℝ) :
    (thetaPairRadialEvenPolynomial (4*q^2) 2).eval (5*q) = b2 q := by
  reduce_radial
  simp only [b2]
  ring
/-- The explicit diagonal-pair radial moment of order 3. -/
theorem radial_3 (q : ℝ) :
    (thetaPairRadialEvenPolynomial (q^2) 3).eval (2*q) = r3 q := by
  reduce_radial
  simp only [r3]
  ring
/-- The explicit unequal-pair radial moment of order 3. -/
theorem mixed_3 (q : ℝ) :
    (thetaPairRadialEvenPolynomial (4*q^2) 3).eval (5*q) = b3 q := by
  reduce_radial
  simp only [b3]
  ring
/-- The explicit diagonal-pair radial moment of order 4. -/
theorem radial_4 (q : ℝ) :
    (thetaPairRadialEvenPolynomial (q^2) 4).eval (2*q) = r4 q := by
  reduce_radial
  simp only [r4]
  ring
/-- The explicit unequal-pair radial moment of order 4. -/
theorem mixed_4 (q : ℝ) :
    (thetaPairRadialEvenPolynomial (4*q^2) 4).eval (5*q) = b4 q := by
  reduce_radial
  simp only [b4]
  ring
/-- The explicit diagonal-pair radial moment of order 5. -/
theorem radial_5 (q : ℝ) :
    (thetaPairRadialEvenPolynomial (q^2) 5).eval (2*q) = r5 q := by
  reduce_radial
  simp only [r5]
  ring
/-- The explicit unequal-pair radial moment of order 5. -/
theorem mixed_5 (q : ℝ) :
    (thetaPairRadialEvenPolynomial (4*q^2) 5).eval (5*q) = b5 q := by
  reduce_radial
  simp only [b5]
  ring
/-- The explicit diagonal-pair radial moment of order 6. -/
theorem radial_6 (q : ℝ) :
    (thetaPairRadialEvenPolynomial (q^2) 6).eval (2*q) = r6 q := by
  reduce_radial
  simp only [r6]
  ring
/-- The explicit unequal-pair radial moment of order 6. -/
theorem mixed_6 (q : ℝ) :
    (thetaPairRadialEvenPolynomial (4*q^2) 6).eval (5*q) = b6 q := by
  reduce_radial
  simp only [b6]
  ring
/-- The explicit diagonal-pair radial moment of order 7. -/
theorem radial_7 (q : ℝ) :
    (thetaPairRadialEvenPolynomial (q^2) 7).eval (2*q) = r7 q := by
  reduce_radial
  simp only [r7]
  ring
/-- The explicit unequal-pair radial moment of order 7. -/
theorem mixed_7 (q : ℝ) :
    (thetaPairRadialEvenPolynomial (4*q^2) 7).eval (5*q) = b7 q := by
  reduce_radial
  simp only [b7]
  ring
/-- The explicit diagonal-pair radial moment of order 8. -/
theorem radial_8 (q : ℝ) :
    (thetaPairRadialEvenPolynomial (q^2) 8).eval (2*q) = r8 q := by
  reduce_radial
  simp only [r8]
  ring
/-- The explicit unequal-pair radial moment of order 8. -/
theorem mixed_8 (q : ℝ) :
    (thetaPairRadialEvenPolynomial (4*q^2) 8).eval (5*q) = b8 q := by
  reduce_radial
  simp only [b8]
  ring
private theorem b8_factor (q : ℝ) : b8 q = q*b8div q := by
  simp only [b8,b8div]
  norm_num only [Nat.reduceSub]
  ring
/-- Normalized radial moment of the first atom and its two cross pairs with atom two. -/
def leadingMoment (q z : ℝ) (k : ℕ) : ℝ :=
  ((thetaPairRadialEvenPolynomial (q^2) k).eval (2*q)+
    8*z*(thetaPairRadialEvenPolynomial (4*q^2) k).eval (5*q))/q^k
private theorem normalized_identity_0 (q : ℝ) (hq : q ≠ 0) :
    (∑ j : Fin 25, (q-5)^j.val*coefficients j 0) =
      128*q^22*leadingMoment q (9765625/(1024*q^15)) 0 := by
  rw [polynomial_identity_0]
  unfold leadingMoment
  rw [radial_0,mixed_0]
  simp only [g0]
  norm_num only [Nat.reduceSub]
  field_simp [hq]
  ring
private theorem normalized_identity_1 (q : ℝ) (hq : q ≠ 0) :
    (∑ j : Fin 25, (q-5)^j.val*coefficients j 1) =
      128*q^22*leadingMoment q (9765625/(1024*q^15)) 1 := by
  rw [polynomial_identity_1]
  unfold leadingMoment
  rw [radial_1,mixed_1]
  simp only [g1]
  norm_num only [Nat.reduceSub]
  field_simp [hq]
  ring
private theorem normalized_identity_2 (q : ℝ) (hq : q ≠ 0) :
    (∑ j : Fin 25, (q-5)^j.val*coefficients j 2) =
      128*q^22*leadingMoment q (9765625/(1024*q^15)) 2 := by
  rw [polynomial_identity_2]
  unfold leadingMoment
  rw [radial_2,mixed_2]
  simp only [g2]
  norm_num only [Nat.reduceSub]
  field_simp [hq]
  ring
private theorem normalized_identity_3 (q : ℝ) (hq : q ≠ 0) :
    (∑ j : Fin 25, (q-5)^j.val*coefficients j 3) =
      128*q^22*leadingMoment q (9765625/(1024*q^15)) 3 := by
  rw [polynomial_identity_3]
  unfold leadingMoment
  rw [radial_3,mixed_3]
  simp only [g3]
  norm_num only [Nat.reduceSub]
  field_simp [hq]
  ring
private theorem normalized_identity_4 (q : ℝ) (hq : q ≠ 0) :
    (∑ j : Fin 25, (q-5)^j.val*coefficients j 4) =
      128*q^22*leadingMoment q (9765625/(1024*q^15)) 4 := by
  rw [polynomial_identity_4]
  unfold leadingMoment
  rw [radial_4,mixed_4]
  simp only [g4]
  norm_num only [Nat.reduceSub]
  field_simp [hq]
  ring
private theorem normalized_identity_5 (q : ℝ) (hq : q ≠ 0) :
    (∑ j : Fin 25, (q-5)^j.val*coefficients j 5) =
      128*q^22*leadingMoment q (9765625/(1024*q^15)) 5 := by
  rw [polynomial_identity_5]
  unfold leadingMoment
  rw [radial_5,mixed_5]
  simp only [g5]
  norm_num only [Nat.reduceSub]
  field_simp [hq]
  ring
private theorem normalized_identity_6 (q : ℝ) (hq : q ≠ 0) :
    (∑ j : Fin 25, (q-5)^j.val*coefficients j 6) =
      128*q^22*leadingMoment q (9765625/(1024*q^15)) 6 := by
  rw [polynomial_identity_6]
  unfold leadingMoment
  rw [radial_6,mixed_6]
  simp only [g6]
  norm_num only [Nat.reduceSub]
  field_simp [hq]
  ring
private theorem normalized_identity_7 (q : ℝ) (hq : q ≠ 0) :
    (∑ j : Fin 25, (q-5)^j.val*coefficients j 7) =
      128*q^22*leadingMoment q (9765625/(1024*q^15)) 7 := by
  rw [polynomial_identity_7]
  unfold leadingMoment
  rw [radial_7,mixed_7]
  simp only [g7]
  norm_num only [Nat.reduceSub]
  field_simp [hq]
  ring
private theorem normalized_identity_8 (q : ℝ) (hq : q ≠ 0) :
    (∑ j : Fin 25, (q-5)^j.val*coefficients j 8) =
      128*q^22*leadingMoment q (9765625/(1024*q^15)) 8 := by
  rw [polynomial_identity_8]
  unfold leadingMoment
  rw [radial_8,mixed_8,b8_factor]
  simp only [g8]
  norm_num only [Nat.reduceSub]
  field_simp [hq]
  ring
private theorem normalized_identity (q : ℝ) (hq : q ≠ 0) (k : ℕ) (hk : k ≤ 8) :
    (∑ j : Fin 25, (q-5)^j.val*coefficients j k) =
      128*q^22*leadingMoment q (9765625/(1024*q^15)) k := by
  interval_cases k
  · exact normalized_identity_0 q hq
  · exact normalized_identity_1 q hq
  · exact normalized_identity_2 q hq
  · exact normalized_identity_3 q hq
  · exact normalized_identity_4 q hq
  · exact normalized_identity_5 q hq
  · exact normalized_identity_6 q hq
  · exact normalized_identity_7 q hq
  · exact normalized_identity_8 q hq
/-- Fifth even matrix of the retained leading pairs, at cross weight `z`. -/
def leadingMatrix (q z : ℝ) : Matrix (Fin 5) (Fin 5) ℝ :=
  fun i j => leadingMoment q z (i.val+j.val)
private theorem endpoint_scaled (q : ℝ) (hq : q ≠ 0) :
    polynomialMatrix (q-5) = (128*q^22) • leadingMatrix q (9765625/(1024*q^15)) := by
  ext i j
  exact normalized_identity q hq (i.val+j.val) (by omega)
private theorem endpoint_reserve_posSemidef {q : ℝ} (hq : 5 ≤ q) :
    (reserve (leadingMatrix q (9765625/(1024*q^15)))).PosSemidef := by
  have hq0 : 0 < q := by linarith only [hq]
  have hc : 0 < 128*q^22 := by positivity
  have hp := polynomial_reserve_posSemidef (sub_nonneg.mpr hq)
  change (reserve (polynomialMatrix (q-5))).PosSemidef at hp
  rw [endpoint_scaled q hq0.ne',reserve_smul] at hp
  have hs := hp.smul (inv_nonneg.mpr hc.le)
  simpa only [smul_smul, inv_mul_cancel₀ hc.ne', one_smul] using hs
private def r8div (q : ℝ) : ℝ := -(1 * 1966080) + q ^ (2-1) * 90190381056 - q ^ (3-1) * 25209606766592 + q ^ (4-1) * 723521013547008 - q ^ (5-1) * 5015348591984640 +
              q ^ (6-1) * 11904065218805760 -
            q ^ (7-1) * 11342746988052480 +
          q ^ (8-1) * 4763364265820160 -
        q ^ (9-1) * 1042906978713600 +
      q ^ (10-1) * 136031345049600
private def a0 (q : ℝ) : ℝ := q^(7-0)*r0 q
private theorem base_polynomial_identity_0 (q : ℝ) :
    (∑ j : Fin 10, (q-5)^j.val*baseCoefficients j 0) = a0 q := by
  norm_num [baseCoefficients, baseM0, baseM1, baseM2, baseM3, baseM4, baseM5, baseM6, baseM7, baseM8, baseM9, Fin.sum_univ_succ]
  simp only [a0, r0]
  norm_num only [Nat.reduceSub]
  ring
private def a1 (q : ℝ) : ℝ := q^(7-1)*r1 q
private theorem base_polynomial_identity_1 (q : ℝ) :
    (∑ j : Fin 10, (q-5)^j.val*baseCoefficients j 1) = a1 q := by
  norm_num [baseCoefficients, baseM0, baseM1, baseM2, baseM3, baseM4, baseM5, baseM6, baseM7, baseM8, baseM9, Fin.sum_univ_succ]
  simp only [a1, r1]
  norm_num only [Nat.reduceSub]
  ring
private def a2 (q : ℝ) : ℝ := q^(7-2)*r2 q
private theorem base_polynomial_identity_2 (q : ℝ) :
    (∑ j : Fin 10, (q-5)^j.val*baseCoefficients j 2) = a2 q := by
  norm_num [baseCoefficients, baseM0, baseM1, baseM2, baseM3, baseM4, baseM5, baseM6, baseM7, baseM8, baseM9, Fin.sum_univ_succ]
  simp only [a2, r2]
  norm_num only [Nat.reduceSub]
  ring
private def a3 (q : ℝ) : ℝ := q^(7-3)*r3 q
private theorem base_polynomial_identity_3 (q : ℝ) :
    (∑ j : Fin 10, (q-5)^j.val*baseCoefficients j 3) = a3 q := by
  norm_num [baseCoefficients, baseM0, baseM1, baseM2, baseM3, baseM4, baseM5, baseM6, baseM7, baseM8, baseM9, Fin.sum_univ_succ]
  simp only [a3, r3]
  norm_num only [Nat.reduceSub]
  ring
private def a4 (q : ℝ) : ℝ := q^(7-4)*r4 q
private theorem base_polynomial_identity_4 (q : ℝ) :
    (∑ j : Fin 10, (q-5)^j.val*baseCoefficients j 4) = a4 q := by
  norm_num [baseCoefficients, baseM0, baseM1, baseM2, baseM3, baseM4, baseM5, baseM6, baseM7, baseM8, baseM9, Fin.sum_univ_succ]
  simp only [a4, r4]
  norm_num only [Nat.reduceSub]
  ring
private def a5 (q : ℝ) : ℝ := q^(7-5)*r5 q
private theorem base_polynomial_identity_5 (q : ℝ) :
    (∑ j : Fin 10, (q-5)^j.val*baseCoefficients j 5) = a5 q := by
  norm_num [baseCoefficients, baseM0, baseM1, baseM2, baseM3, baseM4, baseM5, baseM6, baseM7, baseM8, baseM9, Fin.sum_univ_succ]
  simp only [a5, r5]
  norm_num only [Nat.reduceSub]
  ring
private def a6 (q : ℝ) : ℝ := q^(7-6)*r6 q
private theorem base_polynomial_identity_6 (q : ℝ) :
    (∑ j : Fin 10, (q-5)^j.val*baseCoefficients j 6) = a6 q := by
  norm_num [baseCoefficients, baseM0, baseM1, baseM2, baseM3, baseM4, baseM5, baseM6, baseM7, baseM8, baseM9, Fin.sum_univ_succ]
  simp only [a6, r6]
  norm_num only [Nat.reduceSub]
  ring
private def a7 (q : ℝ) : ℝ := q^(7-7)*r7 q
private theorem base_polynomial_identity_7 (q : ℝ) :
    (∑ j : Fin 10, (q-5)^j.val*baseCoefficients j 7) = a7 q := by
  norm_num [baseCoefficients, baseM0, baseM1, baseM2, baseM3, baseM4, baseM5, baseM6, baseM7, baseM8, baseM9, Fin.sum_univ_succ]
  simp only [a7, r7]
  norm_num only [Nat.reduceSub]
  ring
private def a8 (q : ℝ) : ℝ := r8div q
private theorem base_polynomial_identity_8 (q : ℝ) :
    (∑ j : Fin 10, (q-5)^j.val*baseCoefficients j 8) = a8 q := by
  norm_num [baseCoefficients, baseM0, baseM1, baseM2, baseM3, baseM4, baseM5, baseM6, baseM7, baseM8, baseM9, Fin.sum_univ_succ]
  simp only [a8, r8div]
  norm_num only [Nat.reduceSub]
  ring
private theorem r8_factor (q : ℝ) : r8 q = q*r8div q := by
  simp only [r8,r8div]
  norm_num only [Nat.reduceSub]
  ring
private theorem base_normalized_identity_0 (q : ℝ) (hq : q ≠ 0) :
    (∑ j : Fin 10, (q-5)^j.val*baseCoefficients j 0) =
      q^7*leadingMoment q 0 0 := by
  rw [base_polynomial_identity_0]
  simp only [leadingMoment, mul_zero, zero_mul, add_zero]
  rw [radial_0]
  simp only [a0]
  norm_num only [Nat.reduceSub]
  field_simp [hq]
private theorem base_normalized_identity_1 (q : ℝ) (hq : q ≠ 0) :
    (∑ j : Fin 10, (q-5)^j.val*baseCoefficients j 1) =
      q^7*leadingMoment q 0 1 := by
  rw [base_polynomial_identity_1]
  simp only [leadingMoment, mul_zero, zero_mul, add_zero]
  rw [radial_1]
  simp only [a1]
  norm_num only [Nat.reduceSub]
  field_simp [hq]
private theorem base_normalized_identity_2 (q : ℝ) (hq : q ≠ 0) :
    (∑ j : Fin 10, (q-5)^j.val*baseCoefficients j 2) =
      q^7*leadingMoment q 0 2 := by
  rw [base_polynomial_identity_2]
  simp only [leadingMoment, mul_zero, zero_mul, add_zero]
  rw [radial_2]
  simp only [a2]
  norm_num only [Nat.reduceSub]
  field_simp [hq]
private theorem base_normalized_identity_3 (q : ℝ) (hq : q ≠ 0) :
    (∑ j : Fin 10, (q-5)^j.val*baseCoefficients j 3) =
      q^7*leadingMoment q 0 3 := by
  rw [base_polynomial_identity_3]
  simp only [leadingMoment, mul_zero, zero_mul, add_zero]
  rw [radial_3]
  simp only [a3]
  norm_num only [Nat.reduceSub]
  field_simp [hq]
private theorem base_normalized_identity_4 (q : ℝ) (hq : q ≠ 0) :
    (∑ j : Fin 10, (q-5)^j.val*baseCoefficients j 4) =
      q^7*leadingMoment q 0 4 := by
  rw [base_polynomial_identity_4]
  simp only [leadingMoment, mul_zero, zero_mul, add_zero]
  rw [radial_4]
  simp only [a4]
  norm_num only [Nat.reduceSub]
  field_simp [hq]
private theorem base_normalized_identity_5 (q : ℝ) (hq : q ≠ 0) :
    (∑ j : Fin 10, (q-5)^j.val*baseCoefficients j 5) =
      q^7*leadingMoment q 0 5 := by
  rw [base_polynomial_identity_5]
  simp only [leadingMoment, mul_zero, zero_mul, add_zero]
  rw [radial_5]
  simp only [a5]
  norm_num only [Nat.reduceSub]
  field_simp [hq]
private theorem base_normalized_identity_6 (q : ℝ) (hq : q ≠ 0) :
    (∑ j : Fin 10, (q-5)^j.val*baseCoefficients j 6) =
      q^7*leadingMoment q 0 6 := by
  rw [base_polynomial_identity_6]
  simp only [leadingMoment, mul_zero, zero_mul, add_zero]
  rw [radial_6]
  simp only [a6]
  norm_num only [Nat.reduceSub]
  field_simp [hq]
private theorem base_normalized_identity_7 (q : ℝ) (hq : q ≠ 0) :
    (∑ j : Fin 10, (q-5)^j.val*baseCoefficients j 7) =
      q^7*leadingMoment q 0 7 := by
  rw [base_polynomial_identity_7]
  simp only [leadingMoment, mul_zero, zero_mul, add_zero]
  rw [radial_7]
  simp only [a7]
  norm_num only [Nat.reduceSub]
  field_simp [hq]
private theorem base_normalized_identity_8 (q : ℝ) (hq : q ≠ 0) :
    (∑ j : Fin 10, (q-5)^j.val*baseCoefficients j 8) =
      q^7*leadingMoment q 0 8 := by
  rw [base_polynomial_identity_8]
  simp only [leadingMoment, mul_zero, zero_mul, add_zero]
  rw [radial_8,r8_factor]
  simp only [a8]
  field_simp [hq]
private theorem base_normalized_identity (q : ℝ) (hq : q ≠ 0) (k : ℕ) (hk : k ≤ 8) :
    (∑ j : Fin 10, (q-5)^j.val*baseCoefficients j k) = q^7*leadingMoment q 0 k := by
  interval_cases k
  · exact base_normalized_identity_0 q hq
  · exact base_normalized_identity_1 q hq
  · exact base_normalized_identity_2 q hq
  · exact base_normalized_identity_3 q hq
  · exact base_normalized_identity_4 q hq
  · exact base_normalized_identity_5 q hq
  · exact base_normalized_identity_6 q hq
  · exact base_normalized_identity_7 q hq
  · exact base_normalized_identity_8 q hq
private theorem base_scaled (q : ℝ) (hq : q ≠ 0) :
    basePolynomialMatrix (q-5) = q^7 • leadingMatrix q 0 := by
  ext i j
  exact base_normalized_identity q hq (i.val+j.val) (by omega)
private theorem base_reserve_posSemidef {q : ℝ} (hq : 5 ≤ q) :
    (reserve (leadingMatrix q 0)).PosSemidef := by
  have hq0 : 0 < q := by linarith only [hq]
  have hc : 0 < q^7 := pow_pos hq0 _
  have hp := base_polynomial_reserve_posSemidef (sub_nonneg.mpr hq)
  rw [base_scaled q hq0.ne',reserve_smul] at hp
  have hs := hp.smul (inv_nonneg.mpr hc.le)
  simpa only [smul_smul, inv_mul_cancel₀ hc.ne', one_smul] using hs
private theorem normalized_affine (q z : ℝ) (hq : 0 < q) :
    leadingMatrix q z =
      (1-z/(9765625/(1024*q^15))) • leadingMatrix q 0 +
      (z/(9765625/(1024*q^15))) • leadingMatrix q (9765625/(1024*q^15)) := by
  ext i j
  simp only [leadingMatrix,leadingMoment,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,
    mul_zero,zero_mul,add_zero]
  field_simp [hq.ne']
  ring
private theorem leading_reserve_posSemidef {q z : ℝ} (hq : 5 ≤ q)
    (hz : 0 ≤ z) (hzU : z ≤ 9765625/(1024*q^15)) :
    (reserve (leadingMatrix q z)).PosSemidef := by
  have hq0 : 0 < q := by linarith only [hq]
  have hc : 0 < 9765625/(1024*q^15) := by positivity
  have ht0 : 0 ≤ z/(9765625/(1024*q^15)) := div_nonneg hz hc.le
  have ht1 : z/(9765625/(1024*q^15)) ≤ 1 := (div_le_one hc).mpr hzU
  rw [normalized_affine q z hq0,reserve_add,reserve_smul,reserve_smul]
  exact ((base_reserve_posSemidef hq).smul (sub_nonneg.mpr ht1)).add
    ((endpoint_reserve_posSemidef hq).smul ht0)
private theorem exp_three_lower : (20 : ℝ) ≤ Real.exp 3 := by
  have h1 : (2718/1000 : ℝ) ≤ Real.exp 1 := by linarith only [Real.exp_one_gt_d9]
  have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2718/1000) h1 3
  rw [← Real.exp_nat_mul] at hp
  norm_num at hp
  linarith only [hp]
private theorem exponential_envelope {q : ℝ} (hq : 5 ≤ q) :
    Real.exp (-3*q) ≤ 9765625/(1024*q^15) := by
  have hq0 : 0 < q := by linarith only [hq]
  have hp := _root_.RHTower.pow_mul_exp_neg_le_stationary_radius 15
    (a := 5) (t := q) (by norm_num) hq0.le
  norm_num only [Nat.cast_ofNat, div_self, OfNat.ofNat_ne_zero, div_eq_mul_inv] at hp
  have h15 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 20) exp_three_lower 5
  rw [← Real.exp_nat_mul] at h15
  norm_num at h15
  have he : Real.exp (-15 : ℝ) ≤ 1/3200000 := by
    rw [Real.exp_neg, inv_eq_one_div]
    exact one_div_le_one_div_of_le (by norm_num) h15
  have hh := mul_le_mul_of_nonneg_left he (show (0 : ℝ) ≤ 5^15 by positivity)
  have hp' : q^15*Real.exp (-3*q) ≤ (5 : ℝ)^15*Real.exp (-15) := by
    convert hp using 1 <;> norm_num
  apply (le_div_iff₀ (show 0 < (1024 : ℝ)*q^15 by positivity)).mpr
  nlinarith only [hp',hh]
private theorem leading_mass_lower {q z : ℝ} (hq : 5 ≤ q) (hz : 0 ≤ z) :
    49 ≤ leadingMoment q z 0 := by
  have hr : 49 ≤ r0 q := by
    dsimp [r0]
    nlinarith only [sq_nonneg (q-5),hq]
  have hb : 0 ≤ b0 q := by
    dsimp [b0]
    nlinarith only [sq_nonneg (q-5),hq]
  simp only [leadingMoment,radial_0,mixed_0,pow_zero,div_one]
  exact hr.trans (le_add_of_nonneg_right (mul_nonneg (mul_nonneg (by norm_num) hz) hb))
private theorem leading_gaussian_floor {q z : ℝ} (hq : 5 ≤ q)
    (hz : 0 ≤ z) (hzU : z ≤ 9765625/(1024*q^15)) :
    (gaussianGram (leadingMatrix q z)-(49/1000 : ℝ) • (1 : Matrix (Fin 5) (Fin 5) ℝ)).PosSemidef := by
  have hp := leading_reserve_posSemidef hq hz hzU
  have hm := leading_mass_lower hq hz
  have hc : 0 ≤ (leadingMoment q z 0-49)/1000 := by linarith only [hm]
  have hi : (((leadingMoment q z 0-49)/1000) •
      (1 : Matrix (Fin 5) (Fin 5) ℝ)).PosSemidef := Matrix.PosSemidef.one.smul hc
  have he : gaussianGram (leadingMatrix q z)-(49/1000 : ℝ) • (1 : Matrix (Fin 5) (Fin 5) ℝ) =
      reserve (leadingMatrix q z)+((leadingMoment q z 0-49)/1000) •
        (1 : Matrix (Fin 5) (Fin 5) ℝ) := by
    ext i j
    simp only [reserve,Matrix.add_apply,Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul]
    change _ = gaussianGram (leadingMatrix q z) i j-leadingMoment q z 0/1000*
      (1 : Matrix (Fin 5) (Fin 5) ℝ) i j+(leadingMoment q z 0-49)/1000*
      (1 : Matrix (Fin 5) (Fin 5) ℝ) i j
    ring
  rw [he]
  exact hp.add hi
/-- The actual cross weight retains one thousandth of the zeroth moment in Gaussian coordinates. -/
theorem source_reserve_posSemidef {q : ℝ} (hq : 5 ≤ q) :
    (gaussianGram (leadingMatrix q (Real.exp (-3*q)))-
      (leadingMoment q (Real.exp (-3*q)) 0/1000) •
        (1 : Matrix (Fin 5) (Fin 5) ℝ)).PosSemidef :=
  leading_reserve_posSemidef hq (Real.exp_pos _).le (exponential_envelope hq)
/-- The retained leading-pair form has a uniform Gaussian-coordinate floor of `49/1000`. -/
theorem source_floor_posSemidef {q : ℝ} (hq : 5 ≤ q) :
    (gaussianGram (leadingMatrix q (Real.exp (-3*q)))-(49/1000 : ℝ) •
      (1 : Matrix (Fin 5) (Fin 5) ℝ)).PosSemidef :=
  leading_gaussian_floor hq (Real.exp_pos _).le (exponential_envelope hq)
end GaloisForLFunctions.ThetaCuspSections.FifthLeadingPair
