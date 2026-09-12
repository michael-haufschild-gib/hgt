import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMRealSourceWeights
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMFixedSourcePolynomial
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMFixedSourceDefect

/-! Strict real-axis coercivity of the complete original source family. -/
namespace RHTower.D4BMJointSource
open Complex Set
open scoped Polynomial
noncomputable section
set_option autoImplicit false

def realSourceCoefficientA (u : ℝ) : ℝ := 5*(u+1)^2+(5/2)*(u+1)-3/2
def realSourceCoefficientB (u : ℝ) : ℝ := (15/2)*(u+1)^4+(81/4)*(u+1)^3+15*(u+1)^2+(9/4)*(u+1)

theorem realSourceCoefficient_bounds (u : ℝ) (hu : u ∈ Icc (-(3/2):ℝ) (-1)) :
    realSourceCoefficientA u ≤ -(3/2) ∧ realSourceCoefficientB u ≤ 9/16 := by
  let t := -(u+1)
  have ht0 : 0 ≤ t := by dsimp only [t]; linarith [hu.2]
  have ht1 : t ≤ 1/2 := by dsimp only [t]; linarith [hu.1]
  have hx0 : 0 ≤ t*(1-t) := mul_nonneg ht0 (by linarith)
  have hx1 : t*(1-t) ≤ 1/4 := by nlinarith [sq_nonneg (t-1/2)]
  have hy1 : (5*t-1)*(3-2*t) ≤ 3 := by
    have h := mul_nonneg (show 0 ≤ 1/2-t by linarith) (show 0 ≤ 12-10*t by linarith)
    nlinarith
  constructor
  · have h := mul_nonneg ht0 (show 0 ≤ 1/2-t by linarith)
    dsimp only [realSourceCoefficientA,t] at *
    nlinarith
  · have he : realSourceCoefficientB u=(3/4)*(t*(1-t))*((5*t-1)*(3-2*t)) := by
      dsimp only [realSourceCoefficientB,t]
      ring
    have hxy := mul_le_mul_of_nonneg_left hy1 hx0
    have hx3 := mul_le_mul_of_nonneg_right hx1 (by norm_num : (0:ℝ)≤3)
    rw [he]
    nlinarith

/-- A signed coefficient cannot cancel the positive second moment against the bounded fourth one. -/
theorem realSourceMoment_combination_bound (u : ℝ) (hu : u ∈ Icc (-(3/2):ℝ) (-1)) :
    realSourceCoefficientA u*realSourceSecondMoment u+realSourceCoefficientB u*realSourceFourthMoment u ≤
      -(3/8)*realSourceSecondMoment u := by
  have hu2 : -2 < u := by linarith [hu.1]
  obtain ⟨ha,hb⟩ := realSourceCoefficient_bounds u hu
  have h2 := realSourceSecondMoment_pos u hu2
  have h4 := realSourceFourthMoment_nonneg u
  have h42 := realSourceFourthMoment_le_twice_second u hu2
  have hA := mul_le_mul_of_nonneg_right ha h2.le
  have hB := mul_le_mul_of_nonneg_right hb h4
  have hC := mul_le_mul_of_nonneg_left h42 (by norm_num : (0:ℝ)≤9/16)
  linarith

theorem nonstationarySourceNumerator_real_normalized (u : ℝ) (hu : -2 < u) (hu1 : u+1 ≠ 0) :
    ((u:ℂ)+1)*nonstationaryMoment nonstationarySourceNumerator 8 (u:ℂ)=
      ((realSourceCoefficientA u*realSourceSecondMoment u+
        realSourceCoefficientB u*realSourceFourthMoment u):ℝ) := by
  have huC : (u:ℂ)+1 ≠ 0 := by exact_mod_cast hu1
  have h2 := nonstationaryMoment_recurrence ((1-Polynomial.X)^2) 0 (u:ℂ) hu huC
  have h4 := nonstationaryMoment_recurrence ((1-Polynomial.X)^4) 0 (u:ℂ) hu huC
  have hz (n : ℕ) (hn : 0 < n) : nonstationaryWeight ((1-Polynomial.X)^n) 0 1=0 := by
    norm_num [nonstationaryWeight,zero_pow hn.ne']
  rw [hz 2 (by omega),zero_div] at h2
  rw [hz 4 (by omega),zero_div] at h4
  change ((u:ℂ)+1)*nonstationaryMoment ((1-Polynomial.X)^2) 0 (u:ℂ)+
    nonstationaryMoment (nonstationaryPolynomial 2 1) 2 (u:ℂ)=0 at h2
  change ((u:ℂ)+1)*nonstationaryMoment ((1-Polynomial.X)^4) 0 (u:ℂ)+
    nonstationaryMoment (nonstationaryPolynomial 4 1) 2 (u:ℂ)=0 at h4
  have he2 : ((u:ℂ)+1)*nonstationaryMoment ((1-Polynomial.X)^2) 0 (u:ℂ)=(realSourceSecondMoment u:ℂ) := by
    linear_combination h2-realSourceSecondMoment_eq u
  have he4 : ((u:ℂ)+1)*nonstationaryMoment ((1-Polynomial.X)^4) 0 (u:ℂ)=(realSourceFourthMoment u:ℂ) := by
    linear_combination h4-realSourceFourthMoment_eq u
  rw [nonstationarySourceNumerator_moment _ hu huC]
  calc
    _ = (5*((u:ℂ)+1)^2+(5/2:ℂ)*((u:ℂ)+1)-3/2)*
        (((u:ℂ)+1)*nonstationaryMoment ((1-Polynomial.X)^2) 0 (u:ℂ))+
        ((15/2:ℂ)*((u:ℂ)+1)^4+(81/4:ℂ)*((u:ℂ)+1)^3+15*((u:ℂ)+1)^2+(9/4:ℂ)*((u:ℂ)+1))*
        (((u:ℂ)+1)*nonstationaryMoment ((1-Polynomial.X)^4) 0 (u:ℂ)) := by ring
    _ = _ := by
      rw [he2,he4]
      simp only [realSourceCoefficientA,realSourceCoefficientB,Complex.ofReal_add,Complex.ofReal_sub,
        Complex.ofReal_mul,Complex.ofReal_pow,Complex.ofReal_div,Complex.ofReal_ofNat,Complex.ofReal_one]

/-- Strict sign on the entire real physical interval, derived from admitted positive kernels. -/
theorem nonstationarySourceNumerator_real_re_pos (u : ℝ) (hu : u ∈ Ico (-(3/2):ℝ) (-1)) :
    0 < (nonstationaryMoment nonstationarySourceNumerator 8 (u:ℂ)).re := by
  have hu2 : -2 < u := by linarith [hu.1]
  have hu1 : u+1 ≠ 0 := by linarith [hu.2]
  have he := congrArg Complex.re (nonstationarySourceNumerator_real_normalized u hu2 hu1)
  simp only [Complex.mul_re,Complex.add_re,Complex.ofReal_re,Complex.one_re,
    Complex.add_im,Complex.ofReal_im,Complex.one_im,zero_add,zero_mul,sub_zero] at he
  have hb := realSourceMoment_combination_bound u ⟨hu.1,hu.2.le⟩
  have hp := realSourceSecondMoment_pos u hu2
  nlinarith [hu.2]

/-- The normalized source has a strict gap even at the subtracted-pole endpoint. -/
theorem nonstationarySourceDefect_real_gap (u : ℝ) (hu : u ∈ Icc (-(3/2):ℝ) (-1)) :
    (86/625:ℝ) < (nonstationarySourceDefect (u:ℂ)).re := by
  rcases hu.2.eq_or_lt with he | he
  · subst u
    norm_num [nonstationarySourceDefect_neg_one]
  · have hu2 : -2 < u := by linarith [hu.1]
    have hu1 : u+1 ≠ 0 := by linarith
    have huC : (u:ℂ)+1 ≠ 0 := by exact_mod_cast hu1
    have hn := nonstationarySourceNumerator_normalized (u:ℂ) hu2 huC
    rw [nonstationarySourceNumerator_real_normalized u hu2 hu1] at hn
    have hr := congrArg Complex.re hn
    simp only [Complex.ofReal_re,Complex.sub_re,Complex.div_ofNat_re] at hr
    have hb := realSourceMoment_combination_bound u hu
    have hp := realSourceSecondMoment_pos u hu2
    norm_num at hr
    linarith

end
end RHTower.D4BMJointSource
