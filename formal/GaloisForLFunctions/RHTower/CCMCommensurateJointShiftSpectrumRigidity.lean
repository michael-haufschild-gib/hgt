import GaloisForLFunctions.RHTower.CCMAnalyticOrbitSpectrumRigidity

/-!
# Joint holomorphic calculus of finitely many commensurate CCM shifts

A finite family of positive commensurate shifts `k_i q` is the monomial image
`z ↦ (z ^ k_i)_i` of one augmentation coordinate.  Consequently every joint
norm-holomorphic filter restricts to one norm-holomorphic germ on the physical arc.

This file proves the complete aperture-spectrum law after all cross-shift cancellations.  Either
the restricted germ vanishes locally and the physical multiplier is eventually zero, or its one
finite vanishing order translates every exponential rate by exactly `q` times that order.  Thus
finite joint holomorphic shift calculus has no exponent behavior beyond the one-coordinate law.
-/

open Filter
open scoped Topology

noncomputable section

namespace RHTower

variable {ι E : Type*} [Fintype ι]
  [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Monomial curve containing a finite family of commensurate shift coordinates. -/
def commensurateJointShiftCurve (k : ι → ℕ) (z : ℂ) : ι → ℂ :=
  fun i => z ^ k i

/-- Restriction of a joint filter to its commensurate monomial curve. -/
def commensurateJointShiftGerm (k : ι → ℕ) (F : (ι → ℂ) → E) (z : ℂ) : E :=
  F (commensurateJointShiftCurve k z)

/-- Norm of a joint filter evaluated at the physical shifts `k_i q`. -/
def normedCommensurateJointShiftMultiplier
    (q : ℝ) (k : ι → ℕ) (F : (ι → ℂ) → E) (h : ℝ) : ℝ :=
  ‖F (fun i => (Real.exp (-q * h) : ℂ) ^ k i)‖

omit [Fintype ι] in
/-- Positive shift lengths send the augmentation point to the joint origin. -/
theorem commensurateJointShiftCurve_zero
    {k : ι → ℕ} (hk : ∀ i, 0 < k i) :
    commensurateJointShiftCurve k 0 = 0 := by
  funext i
  simp [commensurateJointShiftCurve, Nat.ne_of_gt (hk i)]

/-- The complete commensurate monomial curve is analytic. -/
theorem analyticAt_commensurateJointShiftCurve (k : ι → ℕ) :
    AnalyticAt ℂ (commensurateJointShiftCurve k) 0 := by
  exact AnalyticAt.pi fun i => analyticAt_id.pow (k i)

/-- Every joint holomorphic filter restricts to a one-variable holomorphic germ. -/
theorem analyticAt_commensurateJointShiftGerm
    {k : ι → ℕ} (hk : ∀ i, 0 < k i) {F : (ι → ℂ) → E}
    (hF : AnalyticAt ℂ F 0) :
    AnalyticAt ℂ (commensurateJointShiftGerm k F) 0 := by
  exact hF.comp_of_eq' (analyticAt_commensurateJointShiftCurve k)
    (commensurateJointShiftCurve_zero hk)

omit [Fintype ι] [NormedSpace ℂ E] in
/-- Physical joint evaluation is literally fixed-shift evaluation of the restricted germ. -/
theorem normedCommensurateJointShiftMultiplier_eq
    (q : ℝ) (k : ι → ℕ) (F : (ι → ℂ) → E) :
    normedCommensurateJointShiftMultiplier q k F =
      normedAnalyticShiftMultiplier q (commensurateJointShiftGerm k F) := by
  rfl

/-- **Complete finite joint-shift spectrum law.**  After every possible cross-shift
cancellation, a nonzero joint holomorphic filter translates each aperture upper-rate budget by
exactly the base shift times the vanishing order of its monomial restriction. -/
theorem apertureExponentialUpperBound_normedCommensurateJointShift_complete_iff
    {q : ℝ} (hq : 0 < q) {k : ι → ℕ} (hk : ∀ i, 0 < k i)
    {F : (ι → ℂ) → E} (hF : AnalyticAt ℂ F 0)
    (hfinite : analyticOrderAt (commensurateJointShiftGerm k F) 0 ≠ ⊤)
    {eta : ℝ → ℝ} (heta : ∀ᶠ h : ℝ in atTop, 0 ≤ eta h) (epsilon : ℝ) :
    ApertureExponentialUpperBound
        (fun h => normedCommensurateJointShiftMultiplier q k F h * eta h) epsilon ↔
      ApertureExponentialUpperBound eta
        (epsilon + q *
          (analyticOrderNatAt (commensurateJointShiftGerm k F) 0 : ℝ)) := by
  rw [normedCommensurateJointShiftMultiplier_eq]
  exact apertureExponentialUpperBound_normedAnalyticShift_complete_iff
    hq (analyticAt_commensurateJointShiftGerm hk hF) hfinite heta epsilon

/-- Zero-type version of the complete finite joint-shift law. -/
theorem subexponentialAtApertureInfinity_normedCommensurateJointShift_complete_iff
    {q : ℝ} (hq : 0 < q) {k : ι → ℕ} (hk : ∀ i, 0 < k i)
    {F : (ι → ℂ) → E} (hF : AnalyticAt ℂ F 0)
    (hfinite : analyticOrderAt (commensurateJointShiftGerm k F) 0 ≠ ⊤)
    {eta : ℝ → ℝ} (heta : ∀ᶠ h : ℝ in atTop, 0 ≤ eta h) :
    SubexponentialAtApertureInfinity
        (fun h => normedCommensurateJointShiftMultiplier q k F h * eta h) ↔
      SubexponentialAboveApertureRate eta
        (q * (analyticOrderNatAt (commensurateJointShiftGerm k F) 0 : ℝ)) := by
  rw [normedCommensurateJointShiftMultiplier_eq]
  exact subexponentialAtApertureInfinity_normedAnalyticShift_complete_iff
    hq (analyticAt_commensurateJointShiftGerm hk hF) hfinite heta

omit [Fintype ι] in
/-- If all weighted Taylor contributions cancel on the monomial curve, the physical joint
multiplier is eventually zero.  The ambient filter itself need not be locally zero. -/
theorem normedCommensurateJointShiftMultiplier_eventually_eq_zero_of_order_eq_top
    {q : ℝ} (hq : 0 < q) {k : ι → ℕ} {F : (ι → ℂ) → E}
    (htop : analyticOrderAt (commensurateJointShiftGerm k F) 0 = ⊤) :
    normedCommensurateJointShiftMultiplier q k F =ᶠ[atTop] 0 := by
  rw [normedCommensurateJointShiftMultiplier_eq]
  exact normedAnalyticShiftMultiplier_eventually_eq_zero_of_order_eq_top hq htop

/-- Direct CCM connector for the published completed critical-Mellin error. -/
theorem criticalMellinCompletedError_commensurateJointShift_upperBound_iff
    {q : ℝ} (hq : 0 < q) {k : ι → ℕ} (hk : ∀ i, 0 < k i)
    {F : (ι → ℂ) → ℂ} (hF : AnalyticAt ℂ F 0)
    (hfinite : analyticOrderAt (commensurateJointShiftGerm k F) 0 ≠ ⊤)
    (epsilon : ℝ) :
    ApertureExponentialUpperBound
        (fun h => normedCommensurateJointShiftMultiplier q k F h *
          |criticalMellinCompletedError h|) epsilon ↔
      ApertureExponentialUpperBound
        (fun h => |criticalMellinCompletedError h|)
        (epsilon + q *
          (analyticOrderNatAt (commensurateJointShiftGerm k F) 0 : ℝ)) := by
  exact apertureExponentialUpperBound_normedCommensurateJointShift_complete_iff
    hq hk hF hfinite
      (Eventually.of_forall fun h => abs_nonneg (criticalMellinCompletedError h)) epsilon

end RHTower
