import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMNonstationaryMomentAlgebra
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMNonstationaryIntegrationByParts
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMNonstationaryPolynomial

/-! Positive admitted real-axis source weights and their sharp comparison. -/
namespace RHTower.D4BMJointSource
open Complex Set MeasureTheory D4BMLaplaceRadial GaloisForLFunctions.HTGeometry
open scoped Polynomial
noncomputable section
set_option autoImplicit false

def realSourcePhase (u x : ℝ) : ℝ := x^u*(2-x)^(-4*u)
def realSourceSecondWeight (x : ℝ) : ℝ := x*(1-x)*(8-4*x+6*x^(2 : ℕ))/(2-x)^(8 : ℕ)/(2+3*x)^(2 : ℕ)
def realSourceFourthWeight (x : ℝ) : ℝ := 4*x*(1-x)^(3 : ℕ)*(4+x)/(2-x)^(8 : ℕ)/(2+3*x)^(2 : ℕ)
def realSourceSecondDensity (u x : ℝ) : ℝ := realSourcePhase u x*realSourceSecondWeight x
def realSourceFourthDensity (u x : ℝ) : ℝ := realSourcePhase u x*realSourceFourthWeight x
def realSourceSecondMoment (u : ℝ) : ℝ := ∫ x in Ioc (0:ℝ) 1, realSourceSecondDensity u x
def realSourceFourthMoment (u : ℝ) : ℝ := ∫ x in Ioc (0:ℝ) 1, realSourceFourthDensity u x

theorem nonstationaryPolynomial_second_first :
    nonstationaryPolynomial 2 1=-Polynomial.X*(1-Polynomial.X)*(8-4*Polynomial.X+6*Polynomial.X^(2 : ℕ)) := by
  have h := nonstationaryWeightStep_factor 1 0 1
  simp only [mul_one] at h
  change nonstationaryWeightStep ((1-Polynomial.X)^(2 : ℕ)) 0 = _
  rw [h]
  norm_num [nonstationaryWeightFactor]
  ring

theorem nonstationaryPolynomial_fourth_first :
    nonstationaryPolynomial 4 1=-4*Polynomial.X*(1-Polynomial.X)^(3 : ℕ)*(4+Polynomial.X) := by
  have h := nonstationaryWeightStep_factor 1 0 3
  simp only [mul_one] at h
  change nonstationaryWeightStep ((1-Polynomial.X)^(4 : ℕ)) 0 = _
  rw [h]
  norm_num [nonstationaryWeightFactor]
  ring

private theorem realSourcePhase_cast (u : ℝ) {x : ℝ} (hx : x ∈ Ioc (0:ℝ) 1) :
    (x:ℂ)^(u:ℂ)*power (-4*(u:ℂ)) (2-x)=(realSourcePhase u x:ℂ) := by
  rw [power,show -4*(u:ℂ)=((-4*u:ℝ):ℂ) by push_cast; ring,
    ← Complex.ofReal_cpow hx.1.le u,← Complex.ofReal_cpow (by linarith [hx.2] : 0 ≤ 2-x) (-4*u)]
  exact (Complex.ofReal_mul _ _).symm

theorem realSourceSecondDensity_cast (u : ℝ) {x : ℝ} (hx : x ∈ Ioc (0:ℝ) 1) :
    (realSourceSecondDensity u x:ℂ)=-((x:ℂ)^(u:ℂ)*nonstationaryCore (nonstationaryPolynomial 2 1) 2 (u:ℂ) x) := by
  rw [nonstationaryCore,← mul_assoc,realSourcePhase_cast u hx]
  simp only [realSourceSecondDensity,realSourceSecondWeight,nonstationaryWeight,
    nonstationaryPolynomial_second_first,Polynomial.eval_mul,Polynomial.eval_neg,
    Polynomial.eval_pow,Polynomial.eval_sub,Polynomial.eval_add,Polynomial.eval_ofNat,Polynomial.eval_one,
    Polynomial.eval_X,Complex.ofReal_mul,Complex.ofReal_sub,Complex.ofReal_div,Complex.ofReal_add,
    Complex.ofReal_pow,Complex.ofReal_ofNat,Complex.ofReal_one]
  ring

theorem realSourceFourthDensity_cast (u : ℝ) {x : ℝ} (hx : x ∈ Ioc (0:ℝ) 1) :
    (realSourceFourthDensity u x:ℂ)=-((x:ℂ)^(u:ℂ)*nonstationaryCore (nonstationaryPolynomial 4 1) 2 (u:ℂ) x) := by
  rw [nonstationaryCore,← mul_assoc,realSourcePhase_cast u hx]
  simp only [realSourceFourthDensity,realSourceFourthWeight,nonstationaryWeight,
    nonstationaryPolynomial_fourth_first,Polynomial.eval_mul,Polynomial.eval_neg,
    Polynomial.eval_pow,Polynomial.eval_sub,Polynomial.eval_add,Polynomial.eval_ofNat,Polynomial.eval_one,
    Polynomial.eval_X,Complex.ofReal_mul,Complex.ofReal_sub,Complex.ofReal_div,Complex.ofReal_add,
    Complex.ofReal_pow,Complex.ofReal_ofNat,Complex.ofReal_one]
  ring

private theorem realSource_integrable (f : ℝ → ℝ) (P : ℂ[X]) (j : ℕ) (u : ℝ)
    (hu : -2 < u) (hz : P.eval 0=0)
    (he : ∀ x ∈ Ioc (0:ℝ) 1, (f x:ℂ)=-((x:ℂ)^(u:ℂ)*nonstationaryCore P j (u:ℂ) x)) :
    IntegrableOn f (Ioc (0:ℝ) 1) := by
  have hi := nonstationaryMoment_remainder_integrable P j (u:ℂ) hu
  have h0 : nonstationaryCore P j (u:ℂ) 0=0 := by
    simp only [nonstationaryCore,nonstationaryWeight,Complex.ofReal_zero,hz,zero_div,mul_zero]
  simp only [h0,sub_zero] at hi
  apply hi.neg.re.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
  change (-( (x:ℂ)^(u:ℂ)*nonstationaryCore P j (u:ℂ) x)).re=f x
  rw [← he x hx]
  rfl

theorem realSourceSecondDensity_integrable (u : ℝ) (hu : -2 < u) :
    IntegrableOn (realSourceSecondDensity u) (Ioc (0:ℝ) 1) :=
  realSource_integrable _ _ _ u hu (nonstationaryWeightStep_zero _ _) (fun _ hx => realSourceSecondDensity_cast u hx)

theorem realSourceFourthDensity_integrable (u : ℝ) (hu : -2 < u) :
    IntegrableOn (realSourceFourthDensity u) (Ioc (0:ℝ) 1) :=
  realSource_integrable _ _ _ u hu (nonstationaryWeightStep_zero _ _) (fun _ hx => realSourceFourthDensity_cast u hx)

theorem realSourceSecondDensity_nonneg (u : ℝ) {x : ℝ} (hx : x ∈ Ioc (0:ℝ) 1) :
    0 ≤ realSourceSecondDensity u x := by
  have hx0 : 0 < x := hx.1
  have ha : 0 < 2-x := by linarith [hx.2]
  have hq : 0 ≤ 8-4*x+6*x^(2 : ℕ) := by nlinarith [sq_nonneg x]
  have hx1 : 0 ≤ 1-x := by linarith [hx.2]
  unfold realSourceSecondDensity realSourcePhase realSourceSecondWeight
  positivity

theorem realSourceSecondDensity_pos (u : ℝ) {x : ℝ} (hx : x ∈ Ioo (0:ℝ) 1) :
    0 < realSourceSecondDensity u x := by
  have hx0 : 0 < x := hx.1
  have hq : 0 < 8-4*x+6*x^(2 : ℕ) := by nlinarith [sq_nonneg x]
  have hx1 : 0 < 1-x := by linarith [hx.2]
  have ha : 0 < 2-x := by linarith [hx.2]
  have hb : 0 < 2+3*x := by linarith [hx.1]
  unfold realSourceSecondDensity realSourcePhase realSourceSecondWeight
  positivity

theorem realSourceFourthDensity_nonneg (u : ℝ) {x : ℝ} (hx : x ∈ Ioc (0:ℝ) 1) :
    0 ≤ realSourceFourthDensity u x := by
  have hx0 : 0 < x := hx.1
  have ha : 0 < 2-x := by linarith [hx.2]
  have hx1 : 0 ≤ 1-x := by linarith [hx.2]
  have hx4 : 0 ≤ 4+x := by linarith [hx.1]
  unfold realSourceFourthDensity realSourcePhase realSourceFourthWeight
  positivity

/-- The exact difference has a positive factorization, uniformly across the whole interval. -/
theorem realSourceFourthDensity_le_twice_second (u : ℝ) {x : ℝ} (hx : x ∈ Ioc (0:ℝ) 1) :
    realSourceFourthDensity u x ≤ 2*realSourceSecondDensity u x := by
  have hx0 : 0 < x := hx.1
  have ha : 0 < 2-x := by linarith [hx.2]
  have hx1 : 0 ≤ 1-x := by linarith [hx.2]
  have hq : 0 ≤ 5+x-x^(2 : ℕ) := by nlinarith [mul_nonneg hx.1.le hx1]
  have hd : 0 ≤ 4*x^(2 : ℕ)*(1-x)*(5+x-x^(2 : ℕ)) := by positivity
  have hn : 4*x*(1-x)^(3 : ℕ)*(4+x) ≤ 2*(x*(1-x)*(8-4*x+6*x^(2 : ℕ))) := by nlinarith
  have h := div_le_div_of_nonneg_right
    (div_le_div_of_nonneg_right hn (pow_nonneg (by linarith [hx.2] : 0 ≤ 2-x) 8)) (sq_nonneg (2+3*x))
  have hp : 0 ≤ realSourcePhase u x := by unfold realSourcePhase; positivity
  have hh := mul_le_mul_of_nonneg_left h hp
  calc
    _ ≤ realSourcePhase u x*(2*(x*(1-x)*(8-4*x+6*x^(2 : ℕ)))/(2-x)^(8 : ℕ)/(2+3*x)^(2 : ℕ)) := hh
    _ = _ := by unfold realSourceSecondDensity realSourceSecondWeight; ring

theorem realSourceSecondMoment_pos (u : ℝ) (hu : -2 < u) : 0 < realSourceSecondMoment u := by
  have hn : 0 ≤ᵐ[volume.restrict (Ioc (0:ℝ) 1)] realSourceSecondDensity u := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    exact realSourceSecondDensity_nonneg u hx
  apply (integral_pos_iff_support_of_nonneg_ae hn (realSourceSecondDensity_integrable u hu)).mpr
  have hs : Ioo (0:ℝ) 1 ⊆ Function.support (realSourceSecondDensity u) := by
    intro x hx
    exact (realSourceSecondDensity_pos u hx).ne'
  have hm : 0 < (volume.restrict (Ioc (0:ℝ) 1)) (Ioo (0:ℝ) 1) := by
    rw [Measure.restrict_apply measurableSet_Ioo,inter_eq_left.mpr (by intro x hx; exact ⟨hx.1,hx.2.le⟩)]
    norm_num
  exact hm.trans_le (measure_mono hs)

theorem realSourceFourthMoment_nonneg (u : ℝ) : 0 ≤ realSourceFourthMoment u := by
  apply integral_nonneg_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
  exact realSourceFourthDensity_nonneg u hx

theorem realSourceFourthMoment_le_twice_second (u : ℝ) (hu : -2 < u) :
    realSourceFourthMoment u ≤ 2*realSourceSecondMoment u := by
  rw [realSourceFourthMoment,realSourceSecondMoment,← integral_const_mul]
  apply integral_mono_ae (realSourceFourthDensity_integrable u hu) ((realSourceSecondDensity_integrable u hu).const_mul 2)
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
  exact realSourceFourthDensity_le_twice_second u hx

private theorem realSourceIntegral_eq_neg_moment (f : ℝ → ℝ) (P : ℂ[X]) (j : ℕ) (u : ℝ)
    (hz : P.eval 0=0)
    (he : ∀ x ∈ Ioc (0:ℝ) 1, (f x:ℂ)=-((x:ℂ)^(u:ℂ)*nonstationaryCore P j (u:ℂ) x)) :
    (((∫ x in Ioc (0:ℝ) 1, f x):ℝ):ℂ)=-nonstationaryMoment P j (u:ℂ) := by
  have h0 : nonstationaryCore P j (u:ℂ) 0=0 := by
    simp only [nonstationaryCore,nonstationaryWeight,Complex.ofReal_zero,hz,zero_div,mul_zero]
  simp only [nonstationaryMoment,firstEndpointMellin,h0,zero_mul,zero_div,zero_add,
    firstEndpointMellinRemainder,sub_zero]
  rw [← integral_complex_ofReal,← integral_neg]
  apply setIntegral_congr_fun measurableSet_Ioc
  intro x hx
  exact he x hx

theorem realSourceSecondMoment_eq (u : ℝ) :
    (realSourceSecondMoment u:ℂ)=-nonstationaryMoment (nonstationaryPolynomial 2 1) 2 (u:ℂ) :=
  realSourceIntegral_eq_neg_moment _ _ _ u (nonstationaryWeightStep_zero _ _) (fun _ hx => realSourceSecondDensity_cast u hx)

theorem realSourceFourthMoment_eq (u : ℝ) :
    (realSourceFourthMoment u:ℂ)=-nonstationaryMoment (nonstationaryPolynomial 4 1) 2 (u:ℂ) :=
  realSourceIntegral_eq_neg_moment _ _ _ u (nonstationaryWeightStep_zero _ _) (fun _ hx => realSourceFourthDensity_cast u hx)

end
end RHTower.D4BMJointSource
