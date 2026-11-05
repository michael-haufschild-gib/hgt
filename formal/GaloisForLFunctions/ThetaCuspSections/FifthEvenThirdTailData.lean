import GaloisForLFunctions.ThetaCuspSections.FifthEvenFirstAtomTailModel
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRadialCoefficients
/-!
# Radial polynomial moments for theta atoms one and three

The signed reflected jets give nine polynomial moments. Their linear
functionals preserve every coefficient when integrated against a radial weight.
-/
noncomputable section
namespace GaloisForLFunctions.ThetaCuspSections.FifthThirdTail
open _root_.RHTower

/-- The `(1,3)` radial polynomials applied to a sequence of power moments. -/
def thirdLinear (m : ℕ → ℝ) : ℕ → ℝ
 | 0 => m 0 * 9 + m 2 * 36 - m 1 * 60
 | 1 => -(m 2 * 7776) - m 4 * 9216 + m 1 * 600 + m 3 * 16800
 | 2 => m 2 * 196416 + m 4 * 6169344 + m 6 * 2359296 - m 1 * 2400 - m 3 * 2198400 - m 5 * 6144000
 | 3 => -(m 2 * 3430656) - m 4 * 1029006336 - m 6 * 3966566400 - m 8 * 603979776 + m 1 * 9600 + m 3 * 118579200 +
        m 5 * 3099187200 +
      m 7 * 2422210560
 | 4 => m 2 * 56042496 + m 4 * 99374874624 + m 6 * 2065935384576 + m 8 * 2300256976896 + m 10 * 154618822656 - m 1 * 38400 -
            m 3 * 4955596800 -
          m 5 * 693529804800 -
        m 7 * 2990549237760 -
      m 9 * 934155386880
 | 5 => -(m 2 * 901287936) - m 4 * 7752693497856 - m 6 * 614689859174400 - m 8 * 2685905500372992 - m 10 * 1222751419367424 -
                  m 12 * 39582418599936 +
                m 1 * 153600 +
              m 3 * 189612441600 +
            m 5 * 105665062502400 +
          m 7 * 1752590959902720 +
        m 9 * 2364882812928000 +
      m 11 * 344284578447360
 | 6 => m 2 * 14439038976 + m 4 * 549346313109504 + m 6 * 135928451517382656 + m 8 * 1823384079650783232 +
                        m 10 * 2724549422682734592 +
                      m 12 * 599168965951881216 +
                    m 14 * 10133099161583616 -
                  m 1 * 614400 -
                m 3 * 7006315315200 -
              m 5 * 13377838537113600 -
            m 7 * 676677088373637120 -
          m 9 * 2851633789623336960 -
        m 11 * 1631981057291059200 -
      m 13 * 121386083706470400
 | 7 => -(m 2 * 231098351616) - m 4 * 37121252636491776 - m 6 * 25524548765614080000 - m 8 * 890876322675790184448 -
                            m 10 * 3529182033083753299968 -
                          m 12 * 2334904934146819227648 -
                        m 14 * 273114888427372806144 -
                      m 16 * 2594073385365405696 +
                    m 1 * 2457600 +
                  m 3 * 255115198464000 +
                m 5 * 1536298066811289600 +
              m 7 * 204995080193027604480 +
            m 9 * 2258791769815646208000 +
          m 11 * 3539578193131465605120 +
        m 13 * 1009580592619270963200 +
      m 15 * 41207936590440038400
 | 8 => m 2 * 3697868537856 + m 4 * 2447213553971625984 + m 6 * 4355850465324130369536 + m 8 * 354405977767163417591808 +
                                m 10 * 3255773473399652543889408 +
                              m 12 * 5170198225072515069247488 +
                            m 14 * 1757119900415860049707008 +
                          m 16 * 117022973869475726622720 +
                        m 18 * 664082786653543858176 -
                      m 3 * 9230366972313600 -
                    m 5 * 167020705132471910400 -
                  m 7 * 53643383081072150446080 -
                m 9 * 1365698380934569776906240 -
              m 11 * 5018032962237537819033600 -
            m 13 * 3639143557348997883494400 -
          m 15 * 569530162836863031705600 -
        m 17 * 13558356894176520437760 -
      m 1 * 9830400
 | _ => 0

private theorem radial_eight_coeff (a : ℝ) (k : ℕ) :
 radialCoeffs a 8 k=radialStepCoeff a (radialCoeffs a 7) k := rfl
private theorem radial_seven_zero_16 (a : ℝ) : radialCoeffs a 7 16=0 :=
 radialCoeffs_eq_zero a (by norm_num)
private theorem radial_seven_zero_17 (a : ℝ) : radialCoeffs a 7 17=0 :=
 radialCoeffs_eq_zero a (by norm_num)
private theorem radial_seven_zero_18 (a : ℝ) : radialCoeffs a 7 18=0 :=
 radialCoeffs_eq_zero a (by norm_num)
private theorem radial_seven_zero_19 (a : ℝ) : radialCoeffs a 7 19=0 :=
 radialCoeffs_eq_zero a (by norm_num)

private theorem thirdLinear_pow_0 (q : ℝ) :
 thirdLinear (fun n => q^n) 0=(thetaPairRadialEvenPolynomial (9*q^2) 0).eval (10*q) := by
 norm_num only [thirdLinear,eval_thetaPairRadialEvenPolynomial,Finset.sum_range_succ,
  Finset.sum_range_zero,radialCoeffs_0_0,radialCoeffs_0_1,Nat.reduceAdd,Nat.reduceMul,Nat.reducePow]
 ring

private theorem thirdLinear_pow_1 (q : ℝ) :
 thirdLinear (fun n => q^n) 1=(thetaPairRadialEvenPolynomial (9*q^2) 1).eval (10*q) := by
 norm_num only [thirdLinear,eval_thetaPairRadialEvenPolynomial,Finset.sum_range_succ,
  Finset.sum_range_zero,radialCoeffs_1_0,radialCoeffs_1_1,radialCoeffs_1_2,radialCoeffs_1_3,Nat.reduceAdd,Nat.reduceMul,Nat.reducePow]
 ring

private theorem thirdLinear_pow_2 (q : ℝ) :
 thirdLinear (fun n => q^n) 2=(thetaPairRadialEvenPolynomial (9*q^2) 2).eval (10*q) := by
 norm_num only [thirdLinear,eval_thetaPairRadialEvenPolynomial,Finset.sum_range_succ,
  Finset.sum_range_zero,radialCoeffs_2_0,radialCoeffs_2_1,radialCoeffs_2_2,radialCoeffs_2_3,radialCoeffs_2_4,radialCoeffs_2_5,Nat.reduceAdd,Nat.reduceMul,Nat.reducePow]
 ring

private theorem thirdLinear_pow_3 (q : ℝ) :
 thirdLinear (fun n => q^n) 3=(thetaPairRadialEvenPolynomial (9*q^2) 3).eval (10*q) := by
 norm_num only [thirdLinear,eval_thetaPairRadialEvenPolynomial,Finset.sum_range_succ,
  Finset.sum_range_zero,radialCoeffs_3_0,radialCoeffs_3_1,radialCoeffs_3_2,radialCoeffs_3_3,radialCoeffs_3_4,radialCoeffs_3_5,radialCoeffs_3_6,radialCoeffs_3_7,Nat.reduceAdd,Nat.reduceMul,Nat.reducePow]
 ring

private theorem thirdLinear_pow_4 (q : ℝ) :
 thirdLinear (fun n => q^n) 4=(thetaPairRadialEvenPolynomial (9*q^2) 4).eval (10*q) := by
 norm_num only [thirdLinear,eval_thetaPairRadialEvenPolynomial,Finset.sum_range_succ,
  Finset.sum_range_zero,radialCoeffs_4_0,radialCoeffs_4_1,radialCoeffs_4_2,radialCoeffs_4_3,radialCoeffs_4_4,radialCoeffs_4_5,radialCoeffs_4_6,radialCoeffs_4_7,radialCoeffs_4_8,radialCoeffs_4_9,Nat.reduceAdd,Nat.reduceMul,Nat.reducePow]
 ring

private theorem thirdLinear_pow_5 (q : ℝ) :
 thirdLinear (fun n => q^n) 5=(thetaPairRadialEvenPolynomial (9*q^2) 5).eval (10*q) := by
 norm_num only [thirdLinear,eval_thetaPairRadialEvenPolynomial,Finset.sum_range_succ,
  Finset.sum_range_zero,radialCoeffs_5_0,radialCoeffs_5_1,radialCoeffs_5_2,radialCoeffs_5_3,radialCoeffs_5_4,radialCoeffs_5_5,radialCoeffs_5_6,radialCoeffs_5_7,radialCoeffs_5_8,radialCoeffs_5_9,radialCoeffs_5_10,radialCoeffs_5_11,Nat.reduceAdd,Nat.reduceMul,Nat.reducePow]
 ring

private theorem thirdLinear_pow_6 (q : ℝ) :
 thirdLinear (fun n => q^n) 6=(thetaPairRadialEvenPolynomial (9*q^2) 6).eval (10*q) := by
 norm_num only [thirdLinear,eval_thetaPairRadialEvenPolynomial,Finset.sum_range_succ,
  Finset.sum_range_zero,radialCoeffs_6_0,radialCoeffs_6_1,radialCoeffs_6_2,radialCoeffs_6_3,radialCoeffs_6_4,radialCoeffs_6_5,radialCoeffs_6_6,radialCoeffs_6_7,radialCoeffs_6_8,radialCoeffs_6_9,radialCoeffs_6_10,radialCoeffs_6_11,radialCoeffs_6_12,radialCoeffs_6_13,Nat.reduceAdd,Nat.reduceMul,Nat.reducePow]
 ring

private theorem thirdLinear_pow_7 (q : ℝ) :
 thirdLinear (fun n => q^n) 7=(thetaPairRadialEvenPolynomial (9*q^2) 7).eval (10*q) := by
 norm_num only [thirdLinear,eval_thetaPairRadialEvenPolynomial,Finset.sum_range_succ,
  Finset.sum_range_zero,radialCoeffs_7_0,radialCoeffs_7_1,radialCoeffs_7_2,radialCoeffs_7_3,radialCoeffs_7_4,radialCoeffs_7_5,radialCoeffs_7_6,radialCoeffs_7_7,radialCoeffs_7_8,radialCoeffs_7_9,radialCoeffs_7_10,radialCoeffs_7_11,radialCoeffs_7_12,radialCoeffs_7_13,radialCoeffs_7_14,radialCoeffs_7_15,Nat.reduceAdd,Nat.reduceMul,Nat.reducePow]
 ring

private theorem thirdLinear_pow_8 (q : ℝ) :
 thirdLinear (fun n => q^n) 8=(thetaPairRadialEvenPolynomial (9*q^2) 8).eval (10*q) := by
 norm_num only [thirdLinear,eval_thetaPairRadialEvenPolynomial,Finset.sum_range_succ,
  Finset.sum_range_zero,radialCoeffs_7_0,radialCoeffs_7_1,radialCoeffs_7_2,radialCoeffs_7_3,radialCoeffs_7_4,radialCoeffs_7_5,radialCoeffs_7_6,radialCoeffs_7_7,radialCoeffs_7_8,radialCoeffs_7_9,radialCoeffs_7_10,radialCoeffs_7_11,radialCoeffs_7_12,radialCoeffs_7_13,radialCoeffs_7_14,radialCoeffs_7_15,radial_eight_coeff,radial_seven_zero_16,radial_seven_zero_17,radial_seven_zero_18,radial_seven_zero_19,radialStepCoeff,radialInnerCoeff,Nat.reduceAdd,Nat.reduceMul,Nat.reducePow]
 ring

/-- Each retained linear functional is the exact reflected pair polynomial. -/
theorem thirdLinear_pow (q : ℝ) (k : ℕ) (hk : k≤8) :
 thirdLinear (fun n => q^n) k=(thetaPairRadialEvenPolynomial (9*q^2) k).eval (10*q) := by
 interval_cases k
 · exact thirdLinear_pow_0 q
 · exact thirdLinear_pow_1 q
 · exact thirdLinear_pow_2 q
 · exact thirdLinear_pow_3 q
 · exact thirdLinear_pow_4 q
 · exact thirdLinear_pow_5 q
 · exact thirdLinear_pow_6 q
 · exact thirdLinear_pow_7 q
 · exact thirdLinear_pow_8 q

/-- Scalar radial weights pass through every pair moment. -/
theorem thirdLinear_smul (c : ℝ) (m : ℕ → ℝ) (k : ℕ) (hk : k≤8) :
 thirdLinear (fun n => c*m n) k=c*thirdLinear m k := by
 interval_cases k <;> simp only [thirdLinear] <;> ring

/-- Convex gamma interpolation is exact for the signed pair moments. -/
theorem thirdLinear_affine (m n : ℕ → ℝ) (t : ℝ) (k : ℕ) (hk : k≤8) :
 thirdLinear (fun j => (1-t)*m j+t*n j) k=
  (1-t)*thirdLinear m k+t*thirdLinear n k := by
 interval_cases k <;> simp only [thirdLinear] <;> ring

/-- The pair moment depends only on the nineteen retained power moments. -/
theorem thirdLinear_sum (k : ℕ) (hk : k≤8) (m : ℕ → ℝ) :
 thirdLinear m k=∑ j ∈ Finset.range 19,
  thirdLinear (fun n => if n=j then 1 else 0) k*m j := by
 interval_cases k <;> norm_num [thirdLinear,Finset.sum_range_succ] <;> ring

end GaloisForLFunctions.ThetaCuspSections.FifthThirdTail
