import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspCenterMixedAllOrderIntegration
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# A zero-integral correction for the physical center mixture

The derivative of the literal theta flux has vanishing half-line integral and an
aperture-independent lower bound. These exact identities permit center compensation;
they do not supply a global positive Hankel hierarchy.
-/

open MeasureTheory Set Filter
open scoped Topology SchwartzMap
namespace RHTower
noncomputable section

/-- Literal center flux whose derivative changes no integrated source moment. -/
def thetaCuspCenterCompensationFlux (a r : ℝ) : ℝ :=
  r^(2 : ℕ) * Real.sinh (a*r) * thetaCuspFullSource (r/2)^(2 : ℕ)

private theorem exists_schwartz_thetaCuspCenterCompensationFlux
    {a : ℝ} (ha : |a| < 1) :
    ∃ F : 𝓢(ℝ, ℝ), (F : ℝ → ℝ) = thetaCuspCenterCompensationFlux a := by
  have hg : (fun r : ℝ => r/2).HasTemperateGrowth := by simp only [div_eq_mul_inv]; fun_prop
  have hbound : ∃ (k : ℕ) (C : ℝ), ∀ r : ℝ, ‖r‖ ≤ C*(1+‖r/2‖)^k := by
    refine ⟨1, 2, fun r => ?_⟩
    simp only [pow_one, Real.norm_eq_abs, abs_div, abs_of_pos (by norm_num : (0:ℝ)<2)]
    linarith
  let f := SchwartzMap.compCLM ℝ hg hbound (thetaCuspTiltedSchwartzReal a ha)
  let g := SchwartzMap.compCLM ℝ hg hbound
    (thetaCuspTiltedSchwartzReal (-a) (by simpa using ha))
  let h := SchwartzMap.pairing (ContinuousLinearMap.mul ℝ ℝ) f f -
    SchwartzMap.pairing (ContinuousLinearMap.mul ℝ ℝ) g g
  have hp : (fun r : ℝ => r^(2 : ℕ)/2).HasTemperateGrowth := by fun_prop
  refine ⟨SchwartzMap.smulLeftCLM ℝ (fun r : ℝ => r^(2 : ℕ)/2) h, ?_⟩
  funext r
  rw [SchwartzMap.smulLeftCLM_apply_apply hp]
  change r^(2 : ℕ)/2 * ((Real.exp (a*(r/2))*thetaCuspFullSource (r/2)) *
    (Real.exp (a*(r/2))*thetaCuspFullSource (r/2)) -
    (Real.exp (-a*(r/2))*thetaCuspFullSource (r/2)) *
    (Real.exp (-a*(r/2))*thetaCuspFullSource (r/2))) = _
  have he : Real.exp (a*(r/2))*Real.exp (a*(r/2)) = Real.exp (a*r) := by
    rw [← Real.exp_add]; congr 1; ring
  have hn : Real.exp (-a*(r/2))*Real.exp (-a*(r/2)) = Real.exp (-(a*r)) := by
    rw [← Real.exp_add]; congr 1; ring
  unfold thetaCuspCenterCompensationFlux
  rw [Real.sinh_eq]
  calc
    _ = r^(2 : ℕ)/2 * ((Real.exp (a*(r/2))*Real.exp (a*(r/2))) -
      (Real.exp (-a*(r/2))*Real.exp (-a*(r/2)))) * thetaCuspFullSource (r/2)^(2 : ℕ) := by ring
    _ = _ := by rw [he, hn]; ring

/-- The center correction derivative is absolutely integrable. -/
theorem integrableOn_deriv_thetaCuspCenterCompensationFlux
    {a : ℝ} (ha : |a| < 1) :
    IntegrableOn (deriv (thetaCuspCenterCompensationFlux a)) (Ioi 0) := by
  obtain ⟨F, hF⟩ := exists_schwartz_thetaCuspCenterCompensationFlux ha
  rw [← hF]
  exact (SchwartzMap.derivCLM ℝ ℝ F).integrable.integrableOn

/-- The literal compensation has exactly zero integral, including both boundaries. -/
theorem integral_deriv_thetaCuspCenterCompensationFlux
    {a : ℝ} (ha : |a| < 1) :
    ∫ r : ℝ in Ioi 0, deriv (thetaCuspCenterCompensationFlux a) r = 0 := by
  obtain ⟨F, hF⟩ := exists_schwartz_thetaCuspCenterCompensationFlux ha
  have hz : F 0 = 0 := by rw [hF]; simp [thetaCuspCenterCompensationFlux]
  rw [← hF]
  have ht : Tendsto (F : ℝ → ℝ) atTop (𝓝 0) :=
    F.tendsto_cocompact.mono_left atTop_le_cocompact
  simpa only [hz, sub_self] using integral_Ioi_of_hasDerivAt_of_tendsto' (a := 0)
    (fun r _ => F.hasDerivAt r) (SchwartzMap.derivCLM ℝ ℝ F).integrable.integrableOn ht

/-- Exact derivative of the literal center flux. -/
theorem hasDerivAt_thetaCuspCenterCompensationFlux (a r : ℝ) :
    HasDerivAt (thetaCuspCenterCompensationFlux a)
      ((2*r*Real.sinh (a*r) + a*r^(2 : ℕ)*Real.cosh (a*r))*thetaCuspFullSource (r/2)^(2 : ℕ) +
        r^(2 : ℕ)*Real.sinh (a*r)*thetaCuspFullSource (r/2)*deriv thetaCuspFullSource (r/2)) r := by
  have hp : HasDerivAt thetaCuspFullSource (deriv thetaCuspFullSource (r/2)) (r/2) :=
    thetaCuspSchwartzReal.hasDerivAt (r/2)
  have h := (((hasDerivAt_id r).pow 2).mul ((hasDerivAt_id r).const_mul a).sinh).mul
    ((hp.comp r ((hasDerivAt_id r).div_const 2)).pow 2)
  exact h.congr_deriv (by dsimp; ring)

/-- Aperture-independent lower bound for the zero-integral correction. -/
theorem deriv_thetaCuspCenterCompensationFlux_lower
    {a r : ℝ} (ha : 0 ≤ a) (hr : 0 ≤ r) :
    r*Real.sinh (a*r)*(3*thetaCuspFullSource (r/2)^(2 : ℕ) +
      r*thetaCuspFullSource (r/2)*deriv thetaCuspFullSource (r/2)) ≤
      deriv (thetaCuspCenterCompensationFlux a) r := by
  rw [(hasDerivAt_thetaCuspCenterCompensationFlux a r).deriv]
  have hs := HTGeometry.sinh_le_self_mul_cosh (mul_nonneg ha hr)
  have hn := mul_nonneg (mul_nonneg hr (sub_nonneg.mpr hs))
    (sq_nonneg (thetaCuspFullSource (r/2)))
  nlinarith only [hn]

/-- Every integrated source quadratic form is unchanged by this exact boundary correction. -/
theorem integral_thetaCuspNativeSignedHankelForm_add_compensation
    {a : ℝ} (ha0 : 0 ≤ a) (ha : a < 1/2) {N : ℕ} (v : Fin N → ℝ) (C : ℝ) :
    (∫ r : ℝ in Ioi 0,
      (r*Real.sinh (a*r)*thetaCuspNativeSignedHankelForm (r/2) v +
        C*deriv (thetaCuspCenterCompensationFlux a) r)) =
      ∑ i : Fin N, ∑ j : Fin N, v i*v j*thetaCuspCenterMixedSignedJet a (i.val+j.val) := by
  have habs : |a| < 1 := by rw [abs_of_nonneg ha0]; linarith
  rw [integral_add (integrableOn_thetaCuspWeightedNativeSignedHankelForm ha0 ha v)
    ((integrableOn_deriv_thetaCuspCenterCompensationFlux habs).const_mul C),
    integral_const_mul, integral_deriv_thetaCuspCenterCompensationFlux habs,
    mul_zero, add_zero, thetaCuspCenterMixedSignedHankelForm_eq_integral_native ha0 ha]

/-- Polynomial multiples of the center flux remain lawful source corrections. -/
def thetaCuspPolynomialFlux (n : ℕ) (a r : ℝ) : ℝ :=
  r^n * thetaCuspCenterCompensationFlux a r

private theorem exists_schwartz_thetaCuspPolynomialFlux
    (n : ℕ) {a : ℝ} (ha : |a| < 1) :
    ∃ F : 𝓢(ℝ, ℝ), (F : ℝ → ℝ) = thetaCuspPolynomialFlux n a := by
  obtain ⟨F, hF⟩ := exists_schwartz_thetaCuspCenterCompensationFlux ha
  have hp : (fun r : ℝ => r^n).HasTemperateGrowth := by fun_prop
  refine ⟨SchwartzMap.smulLeftCLM ℝ (fun r : ℝ => r^n) F, ?_⟩
  funext r
  rw [SchwartzMap.smulLeftCLM_apply_apply hp, hF]
  rfl

/-- Every polynomial center flux has integrable derivative in the critical aperture. -/
theorem integrableOn_deriv_thetaCuspPolynomialFlux
    (n : ℕ) {a : ℝ} (ha : |a| < 1) :
    IntegrableOn (deriv (thetaCuspPolynomialFlux n a)) (Ioi 0) := by
  obtain ⟨F, hF⟩ := exists_schwartz_thetaCuspPolynomialFlux n ha
  rw [← hF]
  exact (SchwartzMap.derivCLM ℝ ℝ F).integrable.integrableOn

/-- The polynomial correction does not change the integrated signed source. -/
theorem integral_deriv_thetaCuspPolynomialFlux
    (n : ℕ) {a : ℝ} (ha : |a| < 1) :
    ∫ r : ℝ in Ioi 0, deriv (thetaCuspPolynomialFlux n a) r = 0 := by
  obtain ⟨F, hF⟩ := exists_schwartz_thetaCuspPolynomialFlux n ha
  have hz : F 0 = 0 := by
    rw [hF]
    simp [thetaCuspPolynomialFlux, thetaCuspCenterCompensationFlux]
  rw [← hF]
  have ht : Tendsto (F : ℝ → ℝ) atTop (𝓝 0) :=
    F.tendsto_cocompact.mono_left atTop_le_cocompact
  simpa only [hz, sub_self] using integral_Ioi_of_hasDerivAt_of_tendsto' (a := 0)
    (fun r _ => F.hasDerivAt r) (SchwartzMap.derivCLM ℝ ℝ F).integrable.integrableOn ht

/-- The exact signed tail debt beyond any cutoff is the negative boundary flux. -/
theorem integral_Ioi_deriv_thetaCuspPolynomialFlux_eq_neg
    (n : ℕ) {a : ℝ} (ha : |a| < 1) (R : ℝ) :
    (∫ r : ℝ in Ioi R, deriv (thetaCuspPolynomialFlux n a) r) =
      -thetaCuspPolynomialFlux n a R := by
  obtain ⟨F, hF⟩ := exists_schwartz_thetaCuspPolynomialFlux n ha
  rw [← hF]
  have ht : Tendsto (F : ℝ → ℝ) atTop (𝓝 0) :=
    F.tendsto_cocompact.mono_left atTop_le_cocompact
  simpa only [hF, zero_sub] using integral_Ioi_of_hasDerivAt_of_tendsto' (a := R)
    (fun r _ => F.hasDerivAt r) (SchwartzMap.derivCLM ℝ ℝ F).integrable.integrableOn ht

end
end RHTower
