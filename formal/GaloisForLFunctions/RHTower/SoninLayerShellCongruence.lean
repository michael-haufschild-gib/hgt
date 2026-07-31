import GaloisForLFunctions.RHTower.SoninLayerWindowNormalForm

/-!
# The aperture layer is the two-polarization shell modulo the relative ideal

Substituting the formal complement for the inner projection in the window normal form leaves a
product of elementary cutoffs.  The like-polarization products collapse by the minimum law, and the
two mixed products are finite time-band blocks, hence in the ideal.

What survives is exactly the two-polarization shell between the two apertures.  The aperture layer,
defined by an orthogonality condition, is therefore an ordinary shell up to trace class.
-/

noncomputable section

set_option maxHeartbeats 1000000

namespace RHTower

open ContinuousLinearMap

/-- The Sonin projection is its formal complement modulo the relative ideal. -/
theorem evenCentralSoninProjection_principalRelativeEq_formalComplement
    {a : ℝ} (ha : 0 < a) :
    evenCentralSoninProjection a =ᵣ
      1 - evenIndicatorCutoff a - evenFourierCutoff a := by
  unfold SoninPrincipalRelativeEq
  exact IsSoninPrincipalRelativeIdeal.projectionCorrection a ha

/-- **Layer–shell congruence.**  The aperture layer between two apertures is the two-polarization
shell between them, modulo the concrete relative ideal. -/
theorem evenSoninApertureLayer_principalRelativeEq_twoPolarizationShell
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : a ≤ b) :
    evenSoninApertureLayer a b =ᵣ evenTwoPolarizationShell a b := by
  have hwindow := evenSoninApertureLayer_principalRelativeEq_window hab hb
  have hcompl := evenCentralSoninProjection_principalRelativeEq_formalComplement ha
  have hstep : (evenIndicatorCutoff b + evenFourierCutoff b) *
      evenCentralSoninProjection a =ᵣ
        (evenIndicatorCutoff b + evenFourierCutoff b) *
          (1 - evenIndicatorCutoff a - evenFourierCutoff a) :=
    hcompl.left_mul _
  have hmixed : IsSoninPrincipalRelativeIdeal
      (evenIndicatorCutoff b * evenFourierCutoff a +
        evenFourierCutoff b * evenIndicatorCutoff a) :=
    (IsSoninPrincipalRelativeIdeal.indicatorFourier b a hb).add
      (IsSoninPrincipalRelativeIdeal.fourierIndicator b a hb)
  have hexpand : (evenIndicatorCutoff b + evenFourierCutoff b) *
      (1 - evenIndicatorCutoff a - evenFourierCutoff a) =
      evenTwoPolarizationShell a b -
        (evenIndicatorCutoff b * evenFourierCutoff a +
          evenFourierCutoff b * evenIndicatorCutoff a) := by
    have hA : evenIndicatorCutoff b * evenIndicatorCutoff a =
        evenIndicatorCutoff a := by
      rw [evenIndicatorCutoff_mul_min, min_eq_right hab]
    have hR : evenFourierCutoff b * evenFourierCutoff a =
        evenFourierCutoff a := by
      rw [evenFourierCutoff_mul_min, min_eq_right hab]
    unfold evenTwoPolarizationShell
    rw [add_mul, mul_sub, mul_sub, mul_sub, mul_sub, mul_one, mul_one, hA, hR]
    abel
  have hfinal : (evenIndicatorCutoff b + evenFourierCutoff b) *
      (1 - evenIndicatorCutoff a - evenFourierCutoff a) =ᵣ
        evenTwoPolarizationShell a b := by
    unfold SoninPrincipalRelativeEq
    rw [hexpand]
    have hsub : evenTwoPolarizationShell a b -
        (evenIndicatorCutoff b * evenFourierCutoff a +
          evenFourierCutoff b * evenIndicatorCutoff a) -
        evenTwoPolarizationShell a b =
        -(evenIndicatorCutoff b * evenFourierCutoff a +
          evenFourierCutoff b * evenIndicatorCutoff a) := by
      abel
    rw [hsub]
    exact hmixed.neg
  exact (hwindow.trans hstep).trans hfinal

end RHTower
