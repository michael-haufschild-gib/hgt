import GaloisForLFunctions.RHTower.HedenmalmCenterMixedLocalThreePoint
import GaloisForLFunctions.RHTower.ThetaCuspFullReflectionSixthBellTransfer

/-!
# Strict sign of the center-mixed first jet

Strict log-concavity of the completed theta source gives a pointwise negative Wronskian between
the two reflected source factors.  Positive center mixing preserves strictness because the
Wronskian is negative on the full positive radial support.  Hence the first displacement jet of
the actual center-mixed density is strictly negative at every positive displacement.
-/

open MeasureTheory Set

namespace RHTower

noncomputable section

private theorem thetaCuspFullSource_firstJet_factor (x : ℝ) :
    iteratedDeriv 1 thetaCuspFullSource x =
      thetaCuspFullSource x * iteratedDeriv 1 thetaCuspLogSource x := by
  rw [iteratedDeriv_one_thetaCuspFullSource_eq_logExponentialJet]
  unfold thetaCuspLogExponentialJetOne
  rw [← congrFun thetaCuspFullSource_eq_logExponentialJetZero x]

private theorem thetaCuspCenterMixedDerivativeProduct_firstGap_neg
    {a r t : ℝ} (ha0 : 0 < a) (hr : 0 < r) (ht : 0 < t) :
    thetaCuspCenterMixedDerivativeProduct 1 0 a r t -
        thetaCuspCenterMixedDerivativeProduct 0 1 a r t < 0 := by
  have hderivAnti : StrictAnti (deriv thetaCuspLogSource) :=
    strictAntiOn_univ.mp <|
      strictConcaveOn_thetaCuspLogSource.strictAntiOn_deriv fun x _ =>
        (hasDerivAt_thetaCuspLogSource x).differentiableAt
  have hlog : iteratedDeriv 1 thetaCuspLogSource (r / 2 + t) <
      iteratedDeriv 1 thetaCuspLogSource (r / 2 - t) := by
    simpa only [iteratedDeriv_one] using
      hderivAnti (by linarith : r / 2 - t < r / 2 + t)
  have hplus : 0 < thetaCuspFullSource (r / 2 + t) :=
    thetaCuspFullSource_pos_all _
  have hminus : 0 < thetaCuspFullSource (r / 2 - t) :=
    thetaCuspFullSource_pos_all _
  have hweight : 0 < r * Real.sinh (a * r) :=
    mul_pos hr (Real.sinh_pos_iff.mpr (mul_pos ha0 hr))
  rw [thetaCuspCenterMixedDerivativeProduct,
    thetaCuspCenterMixedDerivativeProduct, thetaCuspFullSource_firstJet_factor,
    thetaCuspFullSource_firstJet_factor]
  simp only [iteratedDeriv_zero]
  have hcore :
      thetaCuspFullSource (r / 2 + t) *
            iteratedDeriv 1 thetaCuspLogSource (r / 2 + t) *
            thetaCuspFullSource (r / 2 - t) -
          thetaCuspFullSource (r / 2 + t) *
            (thetaCuspFullSource (r / 2 - t) *
              iteratedDeriv 1 thetaCuspLogSource (r / 2 - t)) < 0 := by
    calc
      _ = (thetaCuspFullSource (r / 2 + t) *
            thetaCuspFullSource (r / 2 - t)) *
          (iteratedDeriv 1 thetaCuspLogSource (r / 2 + t) -
            iteratedDeriv 1 thetaCuspLogSource (r / 2 - t)) := by ring
      _ < 0 := mul_neg_of_pos_of_neg (mul_pos hplus hminus) (sub_neg.mpr hlog)
  nlinarith

/-- At positive aperture, the first displacement jet of the actual center-mixed density is
strictly negative at every positive displacement. -/
theorem thetaCuspCenterMixedDensityFirstJet_lt_zero
    {a t : ℝ} (ha0 : 0 < a) (ha : a < 1 / 2) (ht : 0 < t) :
    thetaCuspCenterMixedDensityFirstJet a t < 0 := by
  let mu : Measure ℝ := volume.restrict (Ioi 0)
  let h : ℝ → ℝ := fun r =>
    thetaCuspCenterMixedDerivativeProduct 1 0 a r t -
      thetaCuspCenterMixedDerivativeProduct 0 1 a r t
  have h10 : Integrable
      (thetaCuspCenterMixedDerivativeProduct 1 0 a · t) mu := by
    simpa [mu, IntegrableOn] using
      integrable_thetaCuspCenterMixedDerivativeProduct (t := t) ha0.le ha 1 0
  have h01 : Integrable
      (thetaCuspCenterMixedDerivativeProduct 0 1 a · t) mu := by
    simpa [mu, IntegrableOn] using
      integrable_thetaCuspCenterMixedDerivativeProduct (t := t) ha0.le ha 0 1
  have hh : Integrable h mu := by
    change Integrable
      ((fun r => thetaCuspCenterMixedDerivativeProduct 1 0 a r t) -
        (fun r => thetaCuspCenterMixedDerivativeProduct 0 1 a r t)) mu
    exact h10.sub h01
  have hneg : ∀ r ∈ Ioi (0 : ℝ), h r < 0 := by
    intro r hr
    exact thetaCuspCenterMixedDerivativeProduct_firstGap_neg ha0 hr ht
  have hnonneg : 0 ≤ᵐ[mu] fun r => -h r := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    exact (neg_pos.mpr (hneg r hr)).le
  have hpos : 0 < ∫ r : ℝ in Ioi 0, -h r := by
    apply (setIntegral_pos_iff_support_of_nonneg_ae hnonneg hh.neg).2
    have hk (j : ℕ) : Continuous (iteratedDeriv j thetaCuspFullSource) := by
      rw [iteratedDeriv_thetaCuspFullSource]
      exact continuous_iff_continuousAt.mpr fun x =>
        (hasDerivAt_thetaCuspFullDerivative j x).continuousAt
    have hcontinuous : Continuous h := by
      dsimp [h]
      unfold thetaCuspCenterMixedDerivativeProduct
      fun_prop
    have hopen : IsOpen (Function.support (fun r => -h r) ∩ Ioi (0 : ℝ)) :=
      hcontinuous.neg.isOpen_support.inter isOpen_Ioi
    apply hopen.measure_pos (volume : Measure ℝ)
    refine ⟨1, ?_, by norm_num⟩
    change -h 1 ≠ 0
    exact (neg_pos.mpr (hneg 1 (by norm_num))).ne'
  have hintegral : (∫ r : ℝ in Ioi 0, h r) < 0 := by
    rw [integral_neg] at hpos
    linarith
  unfold thetaCuspCenterMixedDensityFirstJet
  unfold thetaCuspCenterMixedDerivativeProductIntegral
  rw [← integral_sub h10 h01]
  simpa only [h] using hintegral

/-- Positive aperture makes the actual center-mixed density strictly decreasing on the full
nonnegative displacement ray, not merely smaller than its central value. -/
theorem strictAntiOn_thetaCuspCenterMixedDensity
    {a : ℝ} (ha0 : 0 < a) (ha : a < 1 / 2) :
    StrictAntiOn (thetaCuspCenterMixedDensity a) (Ici 0) := by
  apply strictAntiOn_of_deriv_neg (convex_Ici (0 : ℝ))
  · exact (continuous_iff_continuousAt.mpr fun t =>
      (hasDerivAt_thetaCuspCenterMixedDensity ha0.le ha t).continuousAt).continuousOn
  · intro t ht
    rw [interior_Ici] at ht
    rw [(hasDerivAt_thetaCuspCenterMixedDensity ha0.le ha t).deriv]
    exact thetaCuspCenterMixedDensityFirstJet_lt_zero ha0 ha ht

end

end RHTower
