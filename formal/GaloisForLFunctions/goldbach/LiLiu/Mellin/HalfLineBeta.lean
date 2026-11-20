import GaloisForLFunctions.MetaplecticMobiusDescent.Eisenstein.SourceCuspMellinReflection
import Mathlib.MeasureTheory.Function.JacobianOneDim

/-! # The Beta integral over a positive half-line

The substitution u = x/(1−x) identifies its integral and its absolute
convergence with Euler's integral on the unit interval.
-/

namespace GaloisForLFunctions.Goldbach.LiLiu
open _root_.Complex Set MeasureTheory MetaplecticMobiusDescent.CubicEisenstein
noncomputable section

private def odds (x : ℝ) := x/(1-x)

private theorem odds_image : odds '' Ioo 0 1 = Ioi 0 := by
  ext y
  constructor
  · rintro ⟨x,hx,rfl⟩
    exact div_pos hx.1 (sub_pos.mpr hx.2)
  · intro hy
    have h : 0 < y := hy
    have h1 : 0 < 1+y := by linarith only [h]
    have hsub : 1 - y/(1+y) = 1/(1+y) := by field_simp; ring
    refine ⟨y/(1+y), ⟨div_pos h h1, (div_lt_one h1).mpr (by linarith only)⟩, ?_⟩
    rw [odds, hsub]
    field_simp

private theorem odds_inj : InjOn odds (Ioo 0 1) := by
  intro x hx y hy he
  have hc := (div_eq_div_iff (sub_ne_zero.mpr hx.2.ne') (sub_ne_zero.mpr hy.2.ne')).mp he
  linarith only [hc]

private theorem odds_deriv (x : ℝ) (hx : x ∈ Ioo (0:ℝ) 1) :
    HasDerivWithinAt odds ((1-x)^2)⁻¹ (Ioo 0 1) x := by
  have h := ((hasDerivAt_id x).div ((hasDerivAt_const x (1:ℝ)).sub (hasDerivAt_id x))
    (sub_ne_zero.mpr hx.2.ne')).hasDerivWithinAt (s := Ioo 0 1)
  convert h using 1 <;> simp [odds,div_eq_mul_inv] <;> ring

private def halfBetaIntegrand (a b : ℂ) (x : ℝ) := (x:ℂ)^(a-1)*(1+(x:ℂ))^(-(a+b))

private theorem odds_jacobian (a b : ℂ) {x : ℝ} (hx : x ∈ Ioo 0 1) :
    |((1-x)^2)⁻¹| • halfBetaIntegrand a b (odds x) = (x:ℂ)^(a-1)*(1-(x:ℂ))^(b-1) := by
  let d := 1-x
  have hd : 0 < d := sub_pos.mpr hx.2
  have hdc : (d:ℂ) ≠ 0 := ofReal_ne_zero.mpr hd.ne'
  have hbase : 1+(odds x:ℂ) = (((1/d:ℝ):ℂ)) := by
    dsimp [odds,d]
    push_cast
    field_simp [sub_ne_zero.mpr (by exact_mod_cast hx.2.ne' : (1:ℂ) ≠ x)]
    ring
  have hd2 : ((1-x)^2)⁻¹ = (d^2)⁻¹ := rfl
  rw [hd2, abs_of_nonneg (inv_nonneg.mpr (sq_nonneg d)), Complex.real_smul, halfBetaIntegrand, hbase]
  change (((d^2)⁻¹ : ℝ):ℂ) * ((((x/d:ℝ):ℂ))^(a-1)*(((1/d:ℝ):ℂ))^(-(a+b))) = _
  rw [positive_div_cpow x d hx.1.le hd, positive_div_cpow 1 d zero_le_one hd,
    Complex.ofReal_one, one_cpow, Complex.cpow_neg, div_inv_eq_mul, one_mul]
  have hpow : (d:ℂ)^(a+b) = (d:ℂ)^(a-1) * (d:ℂ)^(b-1) * (d:ℂ)^2 := by
    rw [show (d:ℂ)^2 = (d:ℂ)^((2:ℕ):ℂ) from (cpow_natCast _ _).symm,
      ← cpow_add _ _ hdc, ← cpow_add _ _ hdc]
    congr 1
    push_cast
    ring
  rw [hpow, show 1-(x:ℂ) = (d:ℂ) by simp [d]]
  have hdA : (d:ℂ)^(a-1) ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl hdc)
  push_cast
  field_simp [hdc,hdA]
  ring

/-- The change of variables also transfers absolute convergence. -/
theorem halfLineBeta_integrable {a b : ℂ} (ha : 0 < a.re) (hb : 0 < b.re) :
    IntegrableOn (halfBetaIntegrand a b) (Ioi 0) := by
  rw [← odds_image, integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioo odds_deriv odds_inj]
  have h := (betaIntegral_convergent ha hb).1.mono_set Ioo_subset_Ioc_self
  exact h.congr_fun (fun x hx => (odds_jacobian a b hx).symm) measurableSet_Ioo

theorem halfLineBeta (a b : ℂ) :
    (∫ x in Ioi (0:ℝ), (x:ℂ)^(a-1)*(1+(x:ℂ))^(-(a+b))) = betaIntegral a b := by
  change (∫ x in Ioi (0:ℝ), halfBetaIntegrand a b x) = _
  rw [← odds_image, integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo odds_deriv odds_inj,
    betaIntegral, intervalIntegral.integral_of_le zero_le_one]
  calc
    _ = ∫ x in Ioo (0:ℝ) 1, (x:ℂ)^(a-1)*(1-(x:ℂ))^(b-1) :=
      setIntegral_congr_fun measurableSet_Ioo (fun x hx => odds_jacobian a b hx)
    _ = _ := setIntegral_congr_set Ioo_ae_eq_Ioc

#print axioms halfLineBeta
#print axioms halfLineBeta_integrable
end
end GaloisForLFunctions.Goldbach.LiLiu
