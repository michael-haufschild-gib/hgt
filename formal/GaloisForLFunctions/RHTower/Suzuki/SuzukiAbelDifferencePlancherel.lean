import GaloisForLFunctions.RHTower.Suzuki.SuzukiAbelLogFourierKernel
import GaloisForLFunctions.RHTower.FourierPlancherelIntegral
import GaloisForLFunctions.HTGeometry.FourierDecayFromDerivative
import GaloisForLFunctions.HTGeometry.GagliardoFourierConstant

/-!
# Plancherel identity for the Abel-weighted difference energy

For a Schwartz function `f` on `ℝ` and `δ > 0`, the physical Abel difference energy
`∫_0^∞ (e^(-δh) / h) ∫ |f(x) - f(x + h)|^2 dx dh` is rewritten by Plancherel and Tonelli as a
spectral energy. Plancherel gives `∫ |f(x) - f(x + h)|^2 dx = ∫ |m_h(ξ)|^2 |𝓕f(ξ)|^2 dξ` with
`|m_h(ξ)|^2 = 4 sin^2(π h ξ)`, and the Frullani-type Abel kernel integral
`∫_0^∞ (e^(-δh) / h) |m_h(ξ)|^2 dh = log(1 + (2πξ/δ)^2)` identifies the weight.

## Main results

- `integral_norm_sq_schwartzTranslationDifference_eq`: Plancherel for the translation difference
  `f(x) - f(x + h)`.
- `abelSchwartzPhysicalEnergyL_eq_spectralJoint`: the physical energy equals the joint
  `(h, ξ)` spectral integral.
- `integral_abelDifferenceSymbolWeight_eq_log_one_add_sq_of_pos`:
  `∫_0^∞ (e^(-δh) / h) |m_h(ξ)|^2 dh = log(1 + (2πξ/δ)^2)` for `δ > 0`.
- `abelSchwartzPhysicalEnergyL_eq_spectralEnergy`: for `δ > 0` the physical energy equals
  `∫ log(1 + (2πξ/δ)^2) |𝓕f(ξ)|^2 dξ` (as extended nonnegative reals).

## Hypotheses

Unconditional for Schwartz `f`; the kernel and energy identities assume `δ > 0`.
-/

open Complex Filter MeasureTheory Set
open FourierTransform
open scoped Topology

namespace RHTower

noncomputable section

/-- The translation difference `x ↦ f(x) - f(x + h)` of a Schwartz function. -/
def schwartzTranslationDifference (f : SchwartzMap ℝ ℂ) (h x : ℝ) : ℂ :=
  f x - f (x + h)

/-- Plancherel for the translation difference: `∫ |f(x) - f(x + h)|^2 dx` equals
`∫ |m_h(ξ)|^2 |𝓕f(ξ)|^2 dξ`, where `m_h` is the Fourier symbol of the difference operator. -/
theorem integral_norm_sq_schwartzTranslationDifference_eq
    (f : SchwartzMap ℝ ℂ) (h : ℝ) :
    (∫ x : ℝ, ‖schwartzTranslationDifference f h x‖ ^ 2) =
      ∫ xi : ℝ,
        ‖GaloisForLFunctions.HTGeometry.differenceSymbol h xi‖ ^ 2 *
          ‖𝓕 (f : ℝ → ℂ) xi‖ ^ 2 := by
  let g : ℝ → ℂ := fun x => f x - f (x + h)
  have hg1 : Integrable g := f.integrable.sub (f.integrable.comp_add_right h)
  have htrans2 : MemLp (fun x : ℝ => f (x + h)) 2 (volume : Measure ℝ) := by
    exact (SchwartzMap.memLp f 2 (volume : Measure ℝ)).comp_measurePreserving
      (measurePreserving_add_right (volume : Measure ℝ) h)
  have hg2 : MemLp g 2 (volume : Measure ℝ) :=
    (SchwartzMap.memLp f 2 (volume : Measure ℝ)).sub htrans2
  change (∫ x : ℝ, ‖g x‖ ^ 2) = _
  rw [← GaloisForLFunctions.RHTower.integral_norm_sq_fourier_eq hg1 hg2]
  refine integral_congr_ae (Filter.Eventually.of_forall fun xi => ?_)
  change ‖𝓕 (fun x : ℝ => f x - f (x + h)) xi‖ ^ 2 = _
  rw [GaloisForLFunctions.HTGeometry.fourier_sub_translate f f.integrable h xi]
  rw [norm_mul]
  simp only [GaloisForLFunctions.HTGeometry.differenceSymbol]
  ring

theorem integrable_norm_sq_schwartzTranslationDifference
    (f : SchwartzMap ℝ ℂ) (h : ℝ) :
    Integrable (fun x : ℝ => ‖schwartzTranslationDifference f h x‖ ^ 2) := by
  let g : ℝ → ℂ := fun x => f x - f (x + h)
  have htrans2 : MemLp (fun x : ℝ => f (x + h)) 2 (volume : Measure ℝ) := by
    exact (SchwartzMap.memLp f 2 (volume : Measure ℝ)).comp_measurePreserving
      (measurePreserving_add_right (volume : Measure ℝ) h)
  have hg2 : MemLp g 2 (volume : Measure ℝ) :=
    (SchwartzMap.memLp f 2 (volume : Measure ℝ)).sub htrans2
  have hsquare := (memLp_two_iff_integrable_sq_norm hg2.aestronglyMeasurable).mp hg2
  exact hsquare.congr (Filter.Eventually.of_forall fun x => rfl)

theorem integrable_schwartzDifferenceSpectralDensity
    (f : SchwartzMap ℝ ℂ) (h : ℝ) :
    Integrable (fun xi : ℝ =>
      ‖GaloisForLFunctions.HTGeometry.differenceSymbol h xi‖ ^ 2 *
        ‖𝓕 (f : ℝ → ℂ) xi‖ ^ 2) := by
  let g : ℝ → ℂ := fun x => f x - f (x + h)
  have hg1 : Integrable g := f.integrable.sub (f.integrable.comp_add_right h)
  have htrans2 : MemLp (fun x : ℝ => f (x + h)) 2 (volume : Measure ℝ) := by
    exact (SchwartzMap.memLp f 2 (volume : Measure ℝ)).comp_measurePreserving
      (measurePreserving_add_right (volume : Measure ℝ) h)
  have hg2 : MemLp g 2 (volume : Measure ℝ) :=
    (SchwartzMap.memLp f 2 (volume : Measure ℝ)).sub htrans2
  have hbase := GaloisForLFunctions.RHTower.integrable_norm_sq_fourier hg1 hg2
  refine hbase.congr (Filter.Eventually.of_forall fun xi => ?_)
  change ‖𝓕 (fun x : ℝ => f x - f (x + h)) xi‖ ^ 2 = _
  rw [GaloisForLFunctions.HTGeometry.fourier_sub_translate f f.integrable h xi]
  rw [norm_mul]
  simp only [GaloisForLFunctions.HTGeometry.differenceSymbol]
  ring

/-- The Plancherel identity for the translation difference, as lower Lebesgue integrals. -/
theorem lintegral_norm_sq_schwartzTranslationDifference_eq
    (f : SchwartzMap ℝ ℂ) (h : ℝ) :
    (∫⁻ x : ℝ, ENNReal.ofReal (‖schwartzTranslationDifference f h x‖ ^ 2)) =
      ∫⁻ xi : ℝ, ENNReal.ofReal
        (‖GaloisForLFunctions.HTGeometry.differenceSymbol h xi‖ ^ 2 *
          ‖𝓕 (f : ℝ → ℂ) xi‖ ^ 2) := by
  rw [← ofReal_integral_eq_lintegral_ofReal
      (integrable_norm_sq_schwartzTranslationDifference f h)
      (Filter.Eventually.of_forall fun x => sq_nonneg _),
    ← ofReal_integral_eq_lintegral_ofReal
      (integrable_schwartzDifferenceSpectralDensity f h)
      (Filter.Eventually.of_forall fun xi => mul_nonneg (sq_nonneg _) (sq_nonneg _)),
    integral_norm_sq_schwartzTranslationDifference_eq]

/-- Physical Abel difference energy `∫_0^∞ (e^(-δh) / h) ∫ |f(x) - f(x + h)|^2 dx dh`, valued in
`[0, ∞]`. -/
def abelSchwartzPhysicalEnergyL (delta : ℝ) (f : SchwartzMap ℝ ℂ) : ENNReal :=
  ∫⁻ h in Ioi (0 : ℝ),
    ENNReal.ofReal (Real.exp (-(delta * h)) / h) *
      ∫⁻ x : ℝ, ENNReal.ofReal (‖schwartzTranslationDifference f h x‖ ^ 2)

/-- Joint spectral form `∫_0^∞ ∫ (e^(-δh) / h) |m_h(ξ)|^2 |𝓕f(ξ)|^2 dξ dh` of the Abel
difference energy. -/
def abelSchwartzSpectralJointL (delta : ℝ) (f : SchwartzMap ℝ ℂ) : ENNReal :=
  ∫⁻ h in Ioi (0 : ℝ), ∫⁻ xi : ℝ, ENNReal.ofReal
    ((Real.exp (-(delta * h)) / h) *
      (‖GaloisForLFunctions.HTGeometry.differenceSymbol h xi‖ ^ 2 *
        ‖𝓕 (f : ℝ → ℂ) xi‖ ^ 2))

/-- The physical Abel difference energy equals its joint spectral form, by Plancherel at each
fixed shift `h > 0`. -/
theorem abelSchwartzPhysicalEnergyL_eq_spectralJoint
    (delta : ℝ) (f : SchwartzMap ℝ ℂ) :
    abelSchwartzPhysicalEnergyL delta f = abelSchwartzSpectralJointL delta f := by
  unfold abelSchwartzPhysicalEnergyL abelSchwartzSpectralJointL
  refine setLIntegral_congr_fun measurableSet_Ioi ?_
  intro h hh
  change ENNReal.ofReal (Real.exp (-(delta * h)) / h) *
      (∫⁻ x : ℝ, ENNReal.ofReal (‖schwartzTranslationDifference f h x‖ ^ 2)) =
    ∫⁻ xi : ℝ, ENNReal.ofReal
      ((Real.exp (-(delta * h)) / h) *
        (‖GaloisForLFunctions.HTGeometry.differenceSymbol h xi‖ ^ 2 *
          ‖𝓕 (f : ℝ → ℂ) xi‖ ^ 2))
  rw [lintegral_norm_sq_schwartzTranslationDifference_eq]
  have hw : 0 ≤ Real.exp (-(delta * h)) / h :=
    div_nonneg (Real.exp_pos _).le hh.le
  have hmeas : Measurable fun xi : ℝ => ENNReal.ofReal
      (‖GaloisForLFunctions.HTGeometry.differenceSymbol h xi‖ ^ 2 *
        ‖𝓕 (f : ℝ → ℂ) xi‖ ^ 2) := by
    apply Measurable.ennreal_ofReal
    have hfcont := GaloisForLFunctions.RHTower.continuous_fourier_of_integrable f.integrable
    unfold GaloisForLFunctions.HTGeometry.differenceSymbol
    fun_prop
  rw [← lintegral_const_mul _ hmeas]
  refine lintegral_congr fun xi => ?_
  rw [← ENNReal.ofReal_mul hw]

theorem measurable_abelSchwartzSpectralJointKernel
    (delta : ℝ) (f : SchwartzMap ℝ ℂ) :
    Measurable fun p : ℝ × ℝ => ENNReal.ofReal
      ((Real.exp (-(delta * p.1)) / p.1) *
        (‖GaloisForLFunctions.HTGeometry.differenceSymbol p.1 p.2‖ ^ 2 *
          ‖𝓕 (f : ℝ → ℂ) p.2‖ ^ 2)) := by
  have hfcont := GaloisForLFunctions.RHTower.continuous_fourier_of_integrable f.integrable
  apply Measurable.ennreal_ofReal
  unfold GaloisForLFunctions.HTGeometry.differenceSymbol
  fun_prop

/-- Tonelli: the joint spectral integral may be computed with the `h`-integral inside. -/
theorem abelSchwartzSpectralJointL_swap (delta : ℝ) (f : SchwartzMap ℝ ℂ) :
    abelSchwartzSpectralJointL delta f =
      ∫⁻ xi : ℝ, ∫⁻ h in Ioi (0 : ℝ), ENNReal.ofReal
        ((Real.exp (-(delta * h)) / h) *
          (‖GaloisForLFunctions.HTGeometry.differenceSymbol h xi‖ ^ 2 *
            ‖𝓕 (f : ℝ → ℂ) xi‖ ^ 2)) := by
  unfold abelSchwartzSpectralJointL
  exact lintegral_lintegral_swap
    (μ := volume.restrict (Ioi (0 : ℝ))) (ν := volume)
    (measurable_abelSchwartzSpectralJointKernel delta f).aemeasurable

/-- For `δ > 0`, the weight `h ↦ (e^(-δh) / h) |m_h(ξ)|^2` is integrable on `(0, ∞)`. -/
theorem integrableOn_abelDifferenceSymbolWeight {delta xi : ℝ} (hdelta : 0 < delta) :
    IntegrableOn (fun h : ℝ => Real.exp (-(delta * h)) / h *
      ‖GaloisForLFunctions.HTGeometry.differenceSymbol h xi‖ ^ 2) (Ioi 0) := by
  have hint := (integrableOn_abelLogKernelIntegrand
    (delta := delta) (b := 2 * Real.pi * xi) hdelta).const_mul 2
  apply hint.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with h hh
  rw [GaloisForLFunctions.HTGeometry.normSq_differenceSymbol]
  unfold abelLogKernelIntegrand
  have hcos : 4 * Real.sin (Real.pi * (h * xi)) ^ 2 =
      2 * (1 - Real.cos ((2 * Real.pi * xi) * h)) := by
    have hs := GaloisForLFunctions.HTGeometry.sin_sq_half
      (2 * Real.pi * (h * xi))
    have harg : (2 * Real.pi * (h * xi)) / 2 = Real.pi * (h * xi) := by ring
    rw [harg] at hs
    have hcosarg : (2 * Real.pi * xi) * h = 2 * Real.pi * (h * xi) := by ring
    rw [hcosarg]
    linarith
  rw [hcos]
  ring

/-- For `δ > 0`, `∫_0^∞ (e^(-δh) / h) |m_h(ξ)|^2 dh = log(1 + (2πξ/δ)^2)`, using
`|m_h(ξ)|^2 = 2 (1 - cos(2πξh))` and the Abel log-kernel integral. -/
theorem integral_abelDifferenceSymbolWeight_eq_log_one_add_sq_of_pos
    {delta : ℝ} (hdelta : 0 < delta) (xi : ℝ) :
    (∫ h in Ioi (0 : ℝ), Real.exp (-(delta * h)) / h *
      ‖GaloisForLFunctions.HTGeometry.differenceSymbol h xi‖ ^ 2) =
        Real.log (1 + ((2 * Real.pi * xi) / delta) ^ 2) := by
  have hcongr :
      (∫ h in Ioi (0 : ℝ), Real.exp (-(delta * h)) / h *
        ‖GaloisForLFunctions.HTGeometry.differenceSymbol h xi‖ ^ 2) =
      2 * abelLogKernelIntegral delta (2 * Real.pi * xi) := by
    rw [abelLogKernelIntegral, ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi ?_
    intro h hh
    change Real.exp (-(delta * h)) / h *
      ‖GaloisForLFunctions.HTGeometry.differenceSymbol h xi‖ ^ 2 =
        2 * abelLogKernelIntegrand delta (2 * Real.pi * xi) h
    rw [GaloisForLFunctions.HTGeometry.normSq_differenceSymbol]
    unfold abelLogKernelIntegrand
    have hcos : 4 * Real.sin (Real.pi * (h * xi)) ^ 2 =
        2 * (1 - Real.cos ((2 * Real.pi * xi) * h)) := by
      have hs := GaloisForLFunctions.HTGeometry.sin_sq_half
        (2 * Real.pi * (h * xi))
      have harg : (2 * Real.pi * (h * xi)) / 2 = Real.pi * (h * xi) := by ring
      rw [harg] at hs
      have hcosarg : (2 * Real.pi * xi) * h = 2 * Real.pi * (h * xi) := by ring
      rw [hcosarg]
      linarith
    rw [hcos]
    ring
  rw [hcongr, integral_abelLogKernel_eq_half_log_one_add_div_sq_of_pos hdelta]
  ring

theorem lintegral_abelDifferenceSymbolWeight_eq_ofReal_log
    {delta : ℝ} (hdelta : 0 < delta) (xi : ℝ) :
    (∫⁻ h in Ioi (0 : ℝ), ENNReal.ofReal
      (Real.exp (-(delta * h)) / h *
        ‖GaloisForLFunctions.HTGeometry.differenceSymbol h xi‖ ^ 2)) =
      ENNReal.ofReal (Real.log (1 + ((2 * Real.pi * xi) / delta) ^ 2)) := by
  rw [← ofReal_integral_eq_lintegral_ofReal
    (integrableOn_abelDifferenceSymbolWeight hdelta)
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with h hh
      exact mul_nonneg (div_nonneg (Real.exp_pos _).le hh.le) (sq_nonneg _)),
    integral_abelDifferenceSymbolWeight_eq_log_one_add_sq_of_pos hdelta]

/-- For `δ > 0`, the inner `h`-integral of the joint spectral kernel at frequency `ξ` equals
`log(1 + (2πξ/δ)^2) |𝓕f(ξ)|^2`. -/
theorem lintegral_abelSpectralJoint_inner
    {delta : ℝ} (hdelta : 0 < delta) (f : SchwartzMap ℝ ℂ) (xi : ℝ) :
    (∫⁻ h in Ioi (0 : ℝ), ENNReal.ofReal
      ((Real.exp (-(delta * h)) / h) *
        (‖GaloisForLFunctions.HTGeometry.differenceSymbol h xi‖ ^ 2 *
          ‖𝓕 (f : ℝ → ℂ) xi‖ ^ 2))) =
      ENNReal.ofReal
        (Real.log (1 + ((2 * Real.pi * xi) / delta) ^ 2) *
          ‖𝓕 (f : ℝ → ℂ) xi‖ ^ 2) := by
  let G : ℝ := ‖𝓕 (f : ℝ → ℂ) xi‖ ^ 2
  have hG : 0 ≤ G := sq_nonneg _
  have hbaseMeas : Measurable fun h : ℝ => ENNReal.ofReal
      (Real.exp (-(delta * h)) / h *
        ‖GaloisForLFunctions.HTGeometry.differenceSymbol h xi‖ ^ 2) := by
    apply Measurable.ennreal_ofReal
    unfold GaloisForLFunctions.HTGeometry.differenceSymbol
    fun_prop
  have hrewrite : (fun h : ℝ => ENNReal.ofReal
      ((Real.exp (-(delta * h)) / h) *
        (‖GaloisForLFunctions.HTGeometry.differenceSymbol h xi‖ ^ 2 * G))) =
      fun h : ℝ => ENNReal.ofReal
        (Real.exp (-(delta * h)) / h *
          ‖GaloisForLFunctions.HTGeometry.differenceSymbol h xi‖ ^ 2) *
            ENNReal.ofReal G := by
    funext h
    have halg :
        Real.exp (-(delta * h)) / h *
          (‖GaloisForLFunctions.HTGeometry.differenceSymbol h xi‖ ^ 2 * G) =
        G * (Real.exp (-(delta * h)) / h *
          ‖GaloisForLFunctions.HTGeometry.differenceSymbol h xi‖ ^ 2) := by ring
    rw [halg, ENNReal.ofReal_mul hG, mul_comm]
  change (∫⁻ h in Ioi (0 : ℝ), ENNReal.ofReal
      ((Real.exp (-(delta * h)) / h) *
        (‖GaloisForLFunctions.HTGeometry.differenceSymbol h xi‖ ^ 2 * G))) =
    ENNReal.ofReal (Real.log (1 + ((2 * Real.pi * xi) / delta) ^ 2) * G)
  rw [hrewrite, lintegral_mul_const _ hbaseMeas,
    lintegral_abelDifferenceSymbolWeight_eq_ofReal_log hdelta]
  have hlog : 0 ≤ Real.log (1 + ((2 * Real.pi * xi) / delta) ^ 2) :=
    Real.log_nonneg (by nlinarith [sq_nonneg ((2 * Real.pi * xi) / delta)])
  rw [← ENNReal.ofReal_mul hlog]

/-- Spectral Abel energy `∫ log(1 + (2πξ/δ)^2) |𝓕f(ξ)|^2 dξ`, valued in `[0, ∞]`. -/
def abelSchwartzSpectralEnergyL (delta : ℝ) (f : SchwartzMap ℝ ℂ) : ENNReal :=
  ∫⁻ xi : ℝ, ENNReal.ofReal
    (Real.log (1 + ((2 * Real.pi * xi) / delta) ^ 2) *
      ‖𝓕 (f : ℝ → ℂ) xi‖ ^ 2)

/-- Abel difference Plancherel identity: for `δ > 0` and Schwartz `f`, the physical Abel difference
energy equals the spectral energy `∫ log(1 + (2πξ/δ)^2) |𝓕f(ξ)|^2 dξ`. -/
theorem abelSchwartzPhysicalEnergyL_eq_spectralEnergy
    {delta : ℝ} (hdelta : 0 < delta) (f : SchwartzMap ℝ ℂ) :
    abelSchwartzPhysicalEnergyL delta f = abelSchwartzSpectralEnergyL delta f := by
  rw [abelSchwartzPhysicalEnergyL_eq_spectralJoint delta,
    abelSchwartzSpectralJointL_swap]
  unfold abelSchwartzSpectralEnergyL
  refine lintegral_congr fun xi => ?_
  exact lintegral_abelSpectralJoint_inner hdelta f xi

end
end RHTower
