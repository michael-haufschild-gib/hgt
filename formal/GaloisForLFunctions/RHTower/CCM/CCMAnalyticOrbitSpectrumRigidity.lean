import GaloisForLFunctions.RHTower.CCM.CCMAnalyticShiftSpectrumRigidity

/-!
# Dimension-free holomorphic orbit spectrum rigidity

The fixed-shift aperture law does not depend on a scalar, finite-dimensional, or finitely generated
shift coordinate.  Let an arbitrary complex normed space carry a norm-holomorphic orbit germ
through its augmentation point, and let an arbitrary norm-holomorphic vector/operator-valued
filter act on that orbit.  Their composition is a one-variable analytic germ.  Its finite
vanishing order is the complete aperture exponent, while a locally zero composition annihilates
the physical orbit eventually.

This closes every regular norm-holomorphic fixed Banach-orbit implementation at once, including
infinite shift-coordinate and operator-ideal realizations.  A surviving CCM boundary transport
must therefore fail norm-holomorphy, vary cofinally with aperture, or retain singular graph data.
-/

open Filter
open scoped Topology

noncomputable section

namespace RHTower

variable {A E : Type*}
  [NormedAddCommGroup A] [NormedSpace ℂ A]
  [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Restriction of a filter to an arbitrary analytic orbit germ. -/
def analyticOrbitGerm (gamma : ℂ → A) (F : A → E) (z : ℂ) : E :=
  F (gamma z)

/-- Norm of a filter evaluated on its physical analytic orbit. -/
def normedAnalyticOrbitMultiplier
    (q : ℝ) (gamma : ℂ → A) (F : A → E) (h : ℝ) : ℝ :=
  ‖F (gamma (Real.exp (-q * h) : ℂ))‖

/-- Analyticity survives restriction to an arbitrary normed-space orbit through augmentation. -/
theorem analyticAt_analyticOrbitGerm
    {gamma : ℂ → A} (hgamma : AnalyticAt ℂ gamma 0) (hgamma0 : gamma 0 = 0)
    {F : A → E} (hF : AnalyticAt ℂ F 0) :
    AnalyticAt ℂ (analyticOrbitGerm gamma F) 0 := by
  exact hF.fun_comp_of_eq hgamma hgamma0

omit [NormedAddCommGroup A] [NormedSpace ℂ A] [NormedSpace ℂ E] in
/-- Physical orbit evaluation is fixed-shift evaluation of the composite germ. -/
theorem normedAnalyticOrbitMultiplier_eq
    (q : ℝ) (gamma : ℂ → A) (F : A → E) :
    normedAnalyticOrbitMultiplier q gamma F =
      normedAnalyticShiftMultiplier q (analyticOrbitGerm gamma F) := by
  rfl

/-- **Universal norm-holomorphic orbit spectrum law.**  In arbitrary complex normed source and
target spaces, a nonzero composite orbit germ translates every aperture upper-rate budget by
exactly base shift times its vanishing order.  Dimension, coordinate cardinality, operator rank,
and compactness do not occur. -/
theorem apertureExponentialUpperBound_normedAnalyticOrbit_complete_iff
    {q : ℝ} (hq : 0 < q)
    {gamma : ℂ → A} (hgamma : AnalyticAt ℂ gamma 0) (hgamma0 : gamma 0 = 0)
    {F : A → E} (hF : AnalyticAt ℂ F 0)
    (hfinite : analyticOrderAt (analyticOrbitGerm gamma F) 0 ≠ ⊤)
    {eta : ℝ → ℝ} (heta : ∀ᶠ h : ℝ in atTop, 0 ≤ eta h) (epsilon : ℝ) :
    ApertureExponentialUpperBound
        (fun h => normedAnalyticOrbitMultiplier q gamma F h * eta h) epsilon ↔
      ApertureExponentialUpperBound eta
        (epsilon + q * (analyticOrderNatAt (analyticOrbitGerm gamma F) 0 : ℝ)) := by
  rw [normedAnalyticOrbitMultiplier_eq]
  exact apertureExponentialUpperBound_normedAnalyticShift_complete_iff
    hq (analyticAt_analyticOrbitGerm hgamma hgamma0 hF) hfinite heta epsilon

/-- Zero-type form of the universal norm-holomorphic orbit law. -/
theorem subexponentialAtApertureInfinity_normedAnalyticOrbit_complete_iff
    {q : ℝ} (hq : 0 < q)
    {gamma : ℂ → A} (hgamma : AnalyticAt ℂ gamma 0) (hgamma0 : gamma 0 = 0)
    {F : A → E} (hF : AnalyticAt ℂ F 0)
    (hfinite : analyticOrderAt (analyticOrbitGerm gamma F) 0 ≠ ⊤)
    {eta : ℝ → ℝ} (heta : ∀ᶠ h : ℝ in atTop, 0 ≤ eta h) :
    SubexponentialAtApertureInfinity
        (fun h => normedAnalyticOrbitMultiplier q gamma F h * eta h) ↔
      SubexponentialAboveApertureRate eta
        (q * (analyticOrderNatAt (analyticOrbitGerm gamma F) 0 : ℝ)) := by
  rw [normedAnalyticOrbitMultiplier_eq]
  exact subexponentialAtApertureInfinity_normedAnalyticShift_complete_iff
    hq (analyticAt_analyticOrbitGerm hgamma hgamma0 hF) hfinite heta

omit [NormedAddCommGroup A] [NormedSpace ℂ A] in
/-- The locally zero composite branch annihilates the physical orbit eventually, even when the
ambient filter is not locally zero away from that orbit. -/
theorem normedAnalyticOrbitMultiplier_eventually_eq_zero_of_order_eq_top
    {q : ℝ} (hq : 0 < q) {gamma : ℂ → A} {F : A → E}
    (htop : analyticOrderAt (analyticOrbitGerm gamma F) 0 = ⊤) :
    normedAnalyticOrbitMultiplier q gamma F =ᶠ[atTop] 0 := by
  rw [normedAnalyticOrbitMultiplier_eq]
  exact normedAnalyticShiftMultiplier_eventually_eq_zero_of_order_eq_top hq htop

/-- Direct arbitrary-orbit connector for the published completed critical-Mellin error. -/
theorem criticalMellinCompletedError_analyticOrbit_upperBound_iff
    {q : ℝ} (hq : 0 < q)
    {gamma : ℂ → A} (hgamma : AnalyticAt ℂ gamma 0) (hgamma0 : gamma 0 = 0)
    {F : A → ℂ} (hF : AnalyticAt ℂ F 0)
    (hfinite : analyticOrderAt (analyticOrbitGerm gamma F) 0 ≠ ⊤)
    (epsilon : ℝ) :
    ApertureExponentialUpperBound
        (fun h => normedAnalyticOrbitMultiplier q gamma F h *
          |criticalMellinCompletedError h|) epsilon ↔
      ApertureExponentialUpperBound
        (fun h => |criticalMellinCompletedError h|)
        (epsilon + q * (analyticOrderNatAt (analyticOrbitGerm gamma F) 0 : ℝ)) := by
  exact apertureExponentialUpperBound_normedAnalyticOrbit_complete_iff
    hq hgamma hgamma0 hF hfinite
      (Eventually.of_forall fun h => abs_nonneg (criticalMellinCompletedError h)) epsilon

end RHTower
