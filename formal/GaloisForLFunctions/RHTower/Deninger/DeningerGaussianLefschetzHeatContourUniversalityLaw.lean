import GaloisForLFunctions.RHTower.Deninger.DeningerLefschetzTrace
import GaloisForLFunctions.RHTower.XiComplexHeatSourceContourVerticalBoundUniversalityLaw

/-!
# Deninger Gaussian Lefschetz heat-contour universality

The Deninger centered resolvent Lefschetz trace agrees pointwise with the continued
prime--archimedean source trace on every admissible contour edge. Consequently Gaussian contour
functional calculus of that cohomological resolvent trace produces the same finite,
multiplicity-exact spectral packets as the Guinand--Weil source contour.

Under RH these cofinal packets converge throughout the open complex heat half-plane, and the
resulting Deninger contour approximants inherit the vertical heat-trace norm bound.
-/

open Complex Filter
open scoped BigOperators

namespace RHTower

noncomputable section

/--
On every admissible rectangle, Gaussian or general entire functional calculus of the Deninger
resolvent Lefschetz trace equals the enclosed multiplicity-exact Xi spectral packet.
-/
theorem rectIntegral_deningerResolventLefschetzTrace_eq_xiZeroCopyClosedRectangleSum
    {g : ℂ → ℂ} (hg : AnalyticOnNhd ℂ g Set.univ)
    {z₁ z₂ : ℂ} (hre : z₁.re < z₂.re) (him : z₁.im < z₂.im)
    (hbot : ∀ x ∈ Set.uIcc z₁.re z₂.re,
      XiExplicitAdmissible ((x : ℂ) + z₁.im * I))
    (htop : ∀ x ∈ Set.uIcc z₁.re z₂.re,
      XiExplicitAdmissible ((x : ℂ) + z₂.im * I))
    (hright : ∀ y ∈ Set.uIcc z₁.im z₂.im,
      XiExplicitAdmissible ((z₂.re : ℂ) + y * I))
    (hleft : ∀ y ∈ Set.uIcc z₁.im z₂.im,
      XiExplicitAdmissible ((z₁.re : ℂ) + y * I)) :
    rectIntegral
        (fun z => g z * deningerDivisorRelativeResolventTrace z) z₁ z₂ =
      2 * Real.pi * I * ∑ q ∈ xiZeroCopyClosedRectangle z₁ z₂,
        g (xiSpectralPoint q) := by
  calc
    rectIntegral
        (fun z => g z * deningerDivisorRelativeResolventTrace z) z₁ z₂ =
        rectIntegral
          (fun z => g z * continuedPrimeArchSourceRelativeTrace z) z₁ z₂ := by
      apply rectIntegral_congr
        (S := {z : ℂ | XiExplicitAdmissible z})
      · intro z hz
        rw [deningerResolventLefschetzTrace hz]
      · intro x hx
        exact hbot x hx
      · intro x hx
        exact htop x hx
      · intro y hy
        exact hright y hy
      · intro y hy
        exact hleft y hy
    _ = 2 * Real.pi * I * ∑ q ∈ xiZeroCopyClosedRectangle z₁ z₂,
          g (xiSpectralPoint q) :=
      rectIntegral_continuedPrimeArchSourceRelativeTrace_eq_xiZeroCopyClosedRectangleSum
        hg hre him hbot htop hright hleft

/--
Under RH, cofinal Gaussian functional calculus of the Deninger resolvent trace converges to the
complete complex-time Xi heat trace.
-/
theorem exists_admissible_deningerGaussianContour_approximates_heatTraceC_of_rh
    (hRH : RiemannHypothesis) {τ : ℂ} (hτ : 0 < τ.re)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ z₁ z₂ : ℂ,
      z₁.re < z₂.re ∧ z₁.im < z₂.im ∧
      dist ((2 * Real.pi * I)⁻¹ *
          rectIntegral (fun z => xiGaussianComplexTestC τ z *
            deningerDivisorRelativeResolventTrace z) z₁ z₂)
        (xiGaussianHeatTraceC τ) < epsilon := by
  classical
  set f : XiZeroCopy → ℂ := fun q => xiGaussianHeatTermC τ q with hf
  have hsum : Summable f :=
    summable_norm_iff.mp (summable_norm_xiGaussianHeatTermC_of_rh hRH hτ)
  have hball : Metric.ball (∑' q, f q) epsilon ∈ nhds (∑' q, f q) :=
    Metric.ball_mem_nhds _ hepsilon
  have hevent : ∀ᶠ s : Finset XiZeroCopy in atTop,
      ∑ q ∈ s, f q ∈ Metric.ball (∑' q, f q) epsilon :=
    hsum.hasSum.eventually hball
  rw [eventually_atTop] at hevent
  obtain ⟨F, hF⟩ := hevent
  obtain ⟨z₁, z₂, hre, him, hpacket, hbot, htop, hright, hleft⟩ :=
    exists_admissible_rectangle_containing_xiZeroCopy_finset F
  refine ⟨z₁, z₂, hre, him, ?_⟩
  have hpi : (2 * Real.pi * I : ℂ) ≠ 0 := by
    have hpi0 : (Real.pi : ℂ) ≠ 0 := by
      exact_mod_cast Real.pi_ne_zero
    simp [hpi0, Complex.I_ne_zero]
  have hcontour :=
    rectIntegral_deningerResolventLefschetzTrace_eq_xiZeroCopyClosedRectangleSum
      (analyticOnNhd_xiGaussianComplexTestC τ) hre him
      hbot htop hright hleft
  have hnorm : (2 * Real.pi * I : ℂ)⁻¹ *
      rectIntegral (fun z => xiGaussianComplexTestC τ z *
        deningerDivisorRelativeResolventTrace z) z₁ z₂ =
      ∑ q ∈ xiZeroCopyClosedRectangle z₁ z₂, f q := by
    rw [hcontour, ← mul_assoc, inv_mul_cancel₀ hpi, one_mul]
    exact Finset.sum_congr rfl fun q _ =>
      xiGaussianComplexTestC_spectralPoint τ q
  rw [hnorm, xiGaussianHeatTraceC]
  have hsubset : F ⊆ xiZeroCopyClosedRectangle z₁ z₂ := by
    intro q hq
    rw [mem_xiZeroCopyClosedRectangle]
    apply Complex.mem_reProdIm.mpr
    rw [Set.uIcc_of_le hre.le, Set.uIcc_of_le him.le]
    exact ⟨⟨(hpacket q hq).1.le, (hpacket q hq).2.1.le⟩,
      ⟨(hpacket q hq).2.2.1.le, (hpacket q hq).2.2.2.le⟩⟩
  exact hF _ hsubset

/--
**Deninger Gaussian Lefschetz heat-contour universality.**

Under RH, every complex heat trace in the open right heat half-plane is approximated by Gaussian
contour functional calculus of the centered Deninger resolvent trace, and each chosen approximant
obeys the RH vertical norm bound up to the same error.
-/
theorem deninger_gaussianLefschetz_heatContourUniversality
    (hRH : RiemannHypothesis) {τ : ℂ} (hτ : 0 < τ.re)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ z₁ z₂ : ℂ,
      z₁.re < z₂.re ∧ z₁.im < z₂.im ∧
      let C := (2 * Real.pi * I)⁻¹ *
        rectIntegral (fun z => xiGaussianComplexTestC τ z *
          deningerDivisorRelativeResolventTrace z) z₁ z₂
      dist C (xiGaussianHeatTraceC τ) < epsilon ∧
        ‖C‖ < xiGaussianHeatTraceReal τ.re + epsilon := by
  obtain ⟨z₁, z₂, hre, him, hdist⟩ :=
    exists_admissible_deningerGaussianContour_approximates_heatTraceC_of_rh
      hRH hτ hepsilon
  refine ⟨z₁, z₂, hre, him, hdist, ?_⟩
  let C := (2 * Real.pi * I)⁻¹ *
    rectIntegral (fun z => xiGaussianComplexTestC τ z *
      deningerDivisorRelativeResolventTrace z) z₁ z₂
  have htriangle : ‖C‖ ≤ ‖xiGaussianHeatTraceC τ‖ +
      dist C (xiGaussianHeatTraceC τ) := by
    rw [dist_eq]
    calc
      ‖C‖ = ‖xiGaussianHeatTraceC τ + (C - xiGaussianHeatTraceC τ)‖ := by
        congr 1
        ring
      _ ≤ ‖xiGaussianHeatTraceC τ‖ + ‖C - xiGaussianHeatTraceC τ‖ :=
        norm_add_le _ _
  have hvertical := norm_xiGaussianHeatTraceC_le_of_rh hRH hτ
  dsimp only [C] at htriangle
  linarith

end

end RHTower
