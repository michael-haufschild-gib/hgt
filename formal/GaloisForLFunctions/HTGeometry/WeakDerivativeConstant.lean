import GaloisForLFunctions.HTGeometry.CompactPrimitive
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-!
# A vanishing weak derivative forces a constant

A locally integrable function whose weak derivative vanishes on an open interval agrees almost
everywhere with a constant there.  The mechanism is the classical one: a test function with
vanishing integral is the derivative of a test function, so the pairing of the function with a test
function depends only on the integral of the test function.
-/

open Set MeasureTheory intervalIntegral

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

/-- A normalised test function supported in a bounded open interval. -/
theorem exists_test_integral_one {a b : ℝ} (hab : a < b) :
    ∃ χ : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) χ ∧ HasCompactSupport χ ∧ tsupport χ ⊆ Ioo a b ∧
      (∫ x, χ x) = 1 := by
  set c : ℝ := (a + b) / 2 with hc
  set r : ℝ := (b - a) / 4 with hr
  have hrpos : 0 < r := by rw [hr]; linarith
  set f : ContDiffBump c := ⟨r / 2, r, by linarith, by linarith⟩ with hf
  refine ⟨f.normed volume, f.contDiff_normed, f.hasCompactSupport_normed, ?_,
    f.integral_normed⟩
  intro x hx
  rw [f.tsupport_normed_eq] at hx
  rw [Metric.mem_closedBall, Real.dist_eq] at hx
  have hrout : f.rOut = r := rfl
  rw [hrout] at hx
  have h2 := abs_le.mp hx
  have hcv : c = (a + b) / 2 := hc
  have hrv : r = (b - a) / 4 := hr
  constructor
  · have := h2.1
    linarith
  · have := h2.2
    linarith

end

end GaloisForLFunctions.HTGeometry
