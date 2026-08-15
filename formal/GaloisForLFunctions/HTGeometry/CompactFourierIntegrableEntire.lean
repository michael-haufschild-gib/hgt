import GaloisForLFunctions.HTGeometry.CompactFourierEntire
import GaloisForLFunctions.HTGeometry.FourierUniquenessL1

/-!
# The compact Fourier transform of an integrable amplitude

Entirety of `z ↦ ∫_a^b f(x) e^{i z x} dx` needs only integrability of the amplitude: on the
integration interval the frequency factor is bounded, so the amplitude itself dominates the
differentiated integrand.  Combining this with the identity theorem along the real axis and Fourier
uniqueness on `L¹` gives the uniqueness statement the Slepian band operator needs: an integrable
amplitude whose compact Fourier transform vanishes on a nondegenerate interval of real frequencies
vanishes almost everywhere.
-/

noncomputable section

open MeasureTheory intervalIntegral
open scoped FourierTransform

namespace GaloisForLFunctions.HTGeometry

/-- **Differentiation under a compact Fourier integral, for an integrable amplitude.** -/
theorem hasDerivAt_compactFourier_of_integrable {f : ℝ → ℂ} {a b : ℝ}
    (hf : IntervalIntegrable f volume a b) (z₀ : ℂ) :
    HasDerivAt (compactFourier f a b)
      (∫ x in a..b, f x * (Complex.I * (x : ℂ)) * Complex.exp (Complex.I * (z₀ * (x : ℂ)))) z₀ := by
  set R : ℝ := max |a| |b| with hR
  have hRnonneg : 0 ≤ R := le_trans (abs_nonneg a) (le_max_left _ _)
  have hball : Metric.ball z₀ 1 ∈ nhds z₀ := Metric.ball_mem_nhds z₀ one_pos
  have hfres : IntegrableOn f (Set.uIoc a b) volume := intervalIntegrable_iff.mp hf
  have hmeasf : AEStronglyMeasurable f (volume.restrict (Set.uIoc a b)) :=
    hfres.aestronglyMeasurable
  set C : ℝ := R * Real.exp ((‖z₀‖ + 1) * R) with hC
  have hCnonneg : 0 ≤ C := by
    rw [hC]
    positivity
  have hintF : ∀ w : ℂ, IntervalIntegrable
      (fun x : ℝ => f x * Complex.exp (Complex.I * (w * (x : ℂ)))) volume a b := by
    intro w
    rw [intervalIntegrable_iff]
    have hcw : Continuous fun x : ℝ => Complex.exp (Complex.I * (w * (x : ℂ))) := by fun_prop
    refine Integrable.mono' (hfres.norm.mul_const (Real.exp (‖w‖ * R)))
      (hmeasf.mul hcw.aestronglyMeasurable) ?_
    refine (ae_restrict_iff' measurableSet_uIoc).mpr (Filter.Eventually.of_forall fun x hx => ?_)
    have hxR : |x| ≤ R := abs_le_max_abs_of_mem_uIoc hx
    have hre : (Complex.I * (w * (x : ℂ))).re ≤ ‖w‖ * R := by
      have h1 : (Complex.I * (w * (x : ℂ))).re ≤ ‖Complex.I * (w * (x : ℂ))‖ :=
        Complex.re_le_norm _
      have h2 : ‖Complex.I * (w * (x : ℂ))‖ = ‖w‖ * |x| := by
        rw [norm_mul, Complex.norm_I, one_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      have h3 : ‖w‖ * |x| ≤ ‖w‖ * R := by
        have := norm_nonneg w
        gcongr
      rw [h2] at h1
      linarith
    rw [norm_mul, Complex.norm_exp]
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hre) (norm_nonneg _)
  refine (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun w x => f x * Complex.exp (Complex.I * (w * (x : ℂ))))
    (F' := fun w x => f x * (Complex.I * (x : ℂ)) * Complex.exp (Complex.I * (w * (x : ℂ))))
    (bound := fun x : ℝ => ‖f x‖ * C) hball ?_ (hintF z₀) ?_ ?_ ?_ ?_).2
  · refine Filter.Eventually.of_forall fun w => ?_
    have hcw : Continuous fun x : ℝ => Complex.exp (Complex.I * (w * (x : ℂ))) := by fun_prop
    exact hmeasf.mul hcw.aestronglyMeasurable
  · have h1 : Continuous fun x : ℝ => Complex.I * (x : ℂ) := by fun_prop
    have h2 : Continuous fun x : ℝ => Complex.exp (Complex.I * (z₀ * (x : ℂ))) := by fun_prop
    exact ((hmeasf.mul h1.aestronglyMeasurable).mul h2.aestronglyMeasurable).congr
      (Filter.Eventually.of_forall fun x => rfl)
  · filter_upwards with x
    intro hx w hw
    have hxR : |x| ≤ R := abs_le_max_abs_of_mem_uIoc hx
    have hwnorm : ‖w‖ ≤ ‖z₀‖ + 1 := by
      have hd : dist w z₀ < 1 := Metric.mem_ball.mp hw
      have := norm_sub_norm_le w z₀
      rw [dist_eq_norm] at hd
      linarith
    have hIx : ‖Complex.I * (x : ℂ)‖ = |x| := by
      rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
    have hnorm : ‖f x * (Complex.I * (x : ℂ)) * Complex.exp (Complex.I * (w * (x : ℂ)))‖
        = ‖f x‖ * |x| * Real.exp ((Complex.I * (w * (x : ℂ))).re) := by
      rw [norm_mul, norm_mul, Complex.norm_exp, hIx]
    rw [hnorm]
    have hre : (Complex.I * (w * (x : ℂ))).re ≤ (‖z₀‖ + 1) * R := by
      have h1 : (Complex.I * (w * (x : ℂ))).re ≤ ‖Complex.I * (w * (x : ℂ))‖ :=
        Complex.re_le_norm _
      have h2 : ‖Complex.I * (w * (x : ℂ))‖ = ‖w‖ * |x| := by
        rw [norm_mul, Complex.norm_I, one_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      have h3 : ‖w‖ * |x| ≤ (‖z₀‖ + 1) * R := by
        have hw0 : (0 : ℝ) ≤ ‖w‖ := norm_nonneg w
        have := abs_nonneg x
        gcongr
      rw [h2] at h1
      linarith
    have hexp : Real.exp ((Complex.I * (w * (x : ℂ))).re) ≤ Real.exp ((‖z₀‖ + 1) * R) :=
      Real.exp_le_exp.mpr hre
    calc ‖f x‖ * |x| * Real.exp ((Complex.I * (w * (x : ℂ))).re)
        ≤ ‖f x‖ * R * Real.exp ((‖z₀‖ + 1) * R) := by
          have h0 : (0 : ℝ) ≤ ‖f x‖ := norm_nonneg _
          have h1 : (0 : ℝ) ≤ Real.exp ((Complex.I * (w * (x : ℂ))).re) := (Real.exp_pos _).le
          have h2 : (0 : ℝ) ≤ |x| := abs_nonneg x
          gcongr
      _ = ‖f x‖ * C := by rw [hC]; ring
  · exact hf.norm.mul_const C
  · filter_upwards with x
    intro _ w _
    exact hasDerivAt_compactFourier_integrand f x w

/-- **The compact Fourier transform of an integrable amplitude is entire.** -/
theorem differentiable_compactFourier_of_integrable {f : ℝ → ℂ} {a b : ℝ}
    (hf : IntervalIntegrable f volume a b) :
    Differentiable ℂ (compactFourier f a b) := fun z =>
  (hasDerivAt_compactFourier_of_integrable hf z).differentiableAt

/-- The compact Fourier transform of an integrable amplitude is continuous. -/
theorem continuous_compactFourier_of_integrable {f : ℝ → ℂ} {a b : ℝ}
    (hf : IntervalIntegrable f volume a b) :
    Continuous (compactFourier f a b) :=
  (differentiable_compactFourier_of_integrable hf).continuous

/-- The compact Fourier transform at a real frequency is the Fourier integral of the
zero-extension. -/
theorem compactFourier_eq_fourierIntegral {g : ℝ → ℂ} {a b : ℝ} (hab : a ≤ b)
    (hsupp : ∀ x : ℝ, x ∉ Set.Icc a b → g x = 0) (ξ : ℝ) :
    compactFourier g a b ((-(2 * Real.pi * ξ) : ℝ) : ℂ) = 𝓕 g ξ := by
  rw [Real.fourier_real_eq_integral_exp_smul, compactFourier,
    intervalIntegral.integral_of_le hab, ← MeasureTheory.integral_Icc_eq_integral_Ioc]
  rw [← MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
    (s := Set.Icc a b) (f := fun x : ℝ => Complex.exp ((↑(-2 * Real.pi * x * ξ) : ℂ) * Complex.I) • g x)
    (fun x hx => by rw [hsupp x hx, smul_zero])]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc fun x _ => ?_
  show g x * Complex.exp (Complex.I * (((-(2 * Real.pi * ξ) : ℝ) : ℂ) * (x : ℂ)))
    = Complex.exp ((↑(-2 * Real.pi * x * ξ) : ℂ) * Complex.I) • g x
  rw [smul_eq_mul]
  rw [show Complex.I * (((-(2 * Real.pi * ξ) : ℝ) : ℂ) * (x : ℂ))
      = ((↑(-2 * Real.pi * x * ξ) : ℂ)) * Complex.I by push_cast; ring]
  ring

/-- **Uniqueness from a window of real frequencies.**  An integrable amplitude supported on `[a,b]`
whose compact Fourier transform vanishes on a nondegenerate interval of real frequencies vanishes
almost everywhere.  Entirety spreads the vanishing to all frequencies; `L¹` Fourier uniqueness then
kills the amplitude. -/
theorem ae_eq_zero_of_compactFourier_vanishing {g : ℝ → ℂ} {a b : ℝ} (hab : a ≤ b)
    (hg : Integrable g) (hsupp : ∀ x : ℝ, x ∉ Set.Icc a b → g x = 0)
    {t₀ r : ℝ} (hr : 0 < r)
    (h : ∀ᵐ t ∂(volume.restrict (Set.Ioo (t₀ - r) (t₀ + r))),
      compactFourier g a b ((t : ℝ) : ℂ) = 0) :
    g =ᵐ[volume] 0 := by
  have hgi : IntervalIntegrable g volume a b := hg.intervalIntegrable
  have hzero : ∀ z : ℂ, compactFourier g a b z = 0 :=
    entire_eq_zero_of_ae_vanishing_on_real_interval
      (differentiable_compactFourier_of_integrable hgi) hr h
  refine _root_.HTGeometry.ae_eq_zero_of_fourierIntegral_eq_zero hg fun ξ => ?_
  rw [← compactFourier_eq_fourierIntegral hab hsupp ξ]
  exact hzero _

end GaloisForLFunctions.HTGeometry
