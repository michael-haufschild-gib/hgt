import GaloisForLFunctions.RHTower.CCM.CCMActualHeadExteriorCosineDualMassWall
import GaloisForLFunctions.RHTower.CCM.CCMActualHeadExteriorGaugeCoerciveCompactReduction

/-!
# Source-sensitive Jordan-mass wall for exterior CCM gauges

The phase-coherent corrected CCM symbol is the literal finite prime--polar--Gamma source on an
actual head.  An exterior cosine gauge leaves every such head average unchanged, but it cannot
repair a negative source region for free.  Pairing a pointwise nonnegative representative with a
compact Sonin profile gives an explicit lower bound for the combined Jordan mass of the exterior
measures in terms of the negative *actual corrected-symbol* average.

This differs from the existing constant-mode mass wall: the test retains the completed arithmetic
symbol, so it applies to a genuinely source-adapted gauge.  It is a necessary condition, not a
positivity claim or an RH proof.
-/

open Complex MeasureTheory Set Filter Topology
open scoped ENNReal InnerProduct InnerProductSpace BigOperators ComplexConjugate FourierTransform

noncomputable section

namespace RHTower

/-- **Source-sensitive exterior mass wall.**  If a positive-minus-positive exterior cosine gauge
makes the literal corrected CCM representative nonnegative, then its combined Jordan mass must
cover every negative compact Sonin average of the untouched prime--polar--Gamma symbol.  The
right-hand side is the exact Fourier-tail attenuation forced by exterior support. -/
theorem exteriorCosineGauge_sourceMass_lower_bound_of_correctedRepresentative_nonneg
    (a : SuzukiPositiveAperture) (m delta H0 : ℝ)
    (hdelta : 0 < delta) (hH0 : 0 ≤ H0)
    (mu nu : Measure ℝ) [IsFiniteMeasure mu] [IsFiniteMeasure nu]
    (hmu : ∀ᵐ h : ℝ ∂mu, H0 ≤ h) (hnu : ∀ᵐ h : ℝ ∂nu, H0 ≤ h)
    (hrep : ∀ x : ℝ,
      0 ≤ ccmCorrectedExteriorMeasureGaugeRepresentative a mu nu x) :
    -(∫ x : ℝ, soninScaledAnnulusBump m delta x *
        correctedCCMSymbol a.1 (2 * Real.pi * x)) ≤
      (4 * delta * soninRefTailSup (delta * H0)) *
        (mu.real Set.univ + nu.real Set.univ) := by
  let phi : ℝ → ℝ := soninScaledAnnulusBump m delta
  let F : ℝ → ℝ := fun x => correctedCCMSymbol a.1 (2 * Real.pi * x)
  let G : ℝ → ℝ := fun x =>
    ccmActualHeadExteriorCosineMeasureGauge mu x -
      ccmActualHeadExteriorCosineMeasureGauge nu x
  have hphiCont : Continuous phi := by
    exact (contDiff_soninScaledAnnulusBump m delta hdelta).continuous
  have hFcont : Continuous F := by
    exact (continuous_correctedCCMSymbol a.1).comp
      (continuous_const.mul continuous_id)
  have hphiSupp : HasCompactSupport phi :=
    hasCompactSupport_soninScaledAnnulusBump m delta hdelta
  have hphiF : Integrable (fun x => phi x * F x) := by
    apply (hphiCont.mul hFcont).integrable_of_hasCompactSupport
    exact hphiSupp.mul_right
  have hphiMu : Integrable (fun x => phi x *
      ccmActualHeadExteriorCosineMeasureGauge mu x) := by
    simpa only [phi] using
      integrable_soninScaledAnnulusBump_mul_exteriorCosineMeasureGauge m delta hdelta mu
  have hphiNu : Integrable (fun x => phi x *
      ccmActualHeadExteriorCosineMeasureGauge nu x) := by
    simpa only [phi] using
      integrable_soninScaledAnnulusBump_mul_exteriorCosineMeasureGauge m delta hdelta nu
  have hphiG : Integrable (fun x => phi x * G x) := by
    apply (hphiMu.sub hphiNu).congr
    filter_upwards with x
    simp only [Pi.sub_apply]
    dsimp only [G]
    ring
  have hnonneg : 0 ≤ ∫ x : ℝ, phi x * (F x + G x) := by
    apply integral_nonneg
    intro x
    have hphi0 : 0 ≤ phi x := soninScaledAnnulusBump_nonneg m delta x
    have hsum : 0 ≤ F x + G x := by
      have hraw := hrep x
      unfold ccmCorrectedExteriorMeasureGaugeRepresentative at hraw
      dsimp only [F, G]
      linarith
    exact mul_nonneg hphi0 hsum
  have hsplit : (∫ x : ℝ, phi x * (F x + G x)) =
      (∫ x : ℝ, phi x * F x) + ∫ x : ℝ, phi x * G x := by
    rw [← integral_add hphiF hphiG]
    apply integral_congr_ae
    filter_upwards with x
    ring
  have hGabs :=
    abs_integral_soninScaledAnnulusBump_mul_exteriorCosineGauge_sub_le
      m delta H0 hdelta hH0 mu nu hmu hnu
  have hGbound : (∫ x : ℝ, phi x * G x) ≤
      (4 * delta * soninRefTailSup (delta * H0)) *
        (mu.real Set.univ + nu.real Set.univ) := by
    apply le_trans (le_abs_self _)
    simpa only [phi, G] using hGabs
  rw [hsplit] at hnonneg
  change -(∫ x : ℝ, phi x * F x) ≤ _
  linarith

end RHTower
