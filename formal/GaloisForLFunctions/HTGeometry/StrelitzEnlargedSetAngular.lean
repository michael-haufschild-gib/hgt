import GaloisForLFunctions.HTGeometry.StrelitzEnlargedSet
import GaloisForLFunctions.HTGeometry.NevanlinnaCoeffFun

/-!
# Angular persistence inside Strelitz's enlarged set

All radial quantities in the definition of the enlarged set are constant along a centered circle.
The remaining value and logarithmic-derivative norms vary continuously away from zeros.  Hence
every point of the enlarged set lies on a local angular arc that remains in the set.  This is the
source's precise local non-isolation mechanism and does not assert radial openness across jumps of
the one-sided maximum slopes.
-/

namespace GaloisForLFunctions.HTGeometry

open Complex Filter Set

noncomputable section

@[simp]
theorem norm_circlePath (z : ℂ) (t : ℝ) : ‖circlePath z t‖ = ‖z‖ := by
  simp [circlePath, Complex.norm_exp]

/-- Every point of Strelitz's enlarged set lies on a local angular arc contained in the same
enlarged set. -/
theorem eventually_circlePath_mem_strelitzEnlargedSet
    {a : ℕ → ℂ} (ha : EntireCoeffs a) {s : ℕ} {z : ℂ}
    (hzH : z ∈ strelitzEnlargedSet a s) :
    ∀ᶠ t : ℝ in nhds 0, circlePath z t ∈ strelitzEnlargedSet a s := by
  rcases hzH with ⟨hz, hlarge, hlower, hupper⟩
  have hfz : coeffFun a z ≠ 0 := by
    rw [← norm_ne_zero_iff]
    have hM0 : 0 ≤ coeffCircleMaximumNorm a ‖z‖ :=
      (norm_nonneg _).trans (norm_coeffFun_circleMap_le_coeffCircleMaximumNorm ha ‖z‖ 0)
    exact ne_of_gt ((Real.rpow_nonneg hM0 _).trans_lt hlarge)
  have hpath : ContinuousAt (circlePath z) 0 :=
    (hasDerivAt_circlePath z 0).continuousAt
  have hfcont : ContinuousAt (fun t : ℝ => ‖coeffFun a (circlePath z t)‖) 0 := by
    simpa [Function.comp_def] using
      (((differentiable_coeffFun ha).continuous.continuousAt.comp hpath).norm)
  have hfa : AnalyticAt ℂ (coeffFun a) z :=
    GaloisForLFunctions.Nevanlinna.analyticOnNhd_coeffFun ha z (by simp)
  have hu : DifferentiableAt ℂ (eulerLogDeriv (coeffFun a)) z := by
    exact (differentiableAt_id.mul hfa.deriv.differentiableAt).div
      hfa.differentiableAt hfz
  have hucont : ContinuousAt
      (fun t : ℝ => ‖eulerLogDeriv (coeffFun a) (circlePath z t)‖) 0 := by
    simpa [Function.comp_def] using
      ((hu.continuousAt.comp_of_eq hpath (circlePath_zero z)).norm)
  have hlarge' : ∀ᶠ t : ℝ in nhds 0,
      coeffCircleMaximumNorm a ‖z‖ ^ (1 - 1 / (4 * (s : ℝ))) <
        ‖coeffFun a (circlePath z t)‖ := by
    simpa using hfcont.eventually_const_lt (by simpa using hlarge)
  have hlower' : ∀ᶠ t : ℝ in nhds 0,
      strelitzMaximumLeftSlope a (Real.log ‖z‖) ^ (-(1 : ℝ) / 3) <
        ‖eulerLogDeriv (coeffFun a) (circlePath z t)‖ := by
    simpa using hucont.eventually_const_lt (by simpa using hlower)
  have hupper' : ∀ᶠ t : ℝ in nhds 0,
      ‖eulerLogDeriv (coeffFun a) (circlePath z t)‖ <
        strelitzMaximumSlope a (Real.log ‖z‖) ^ ((5 : ℝ) / 3) := by
    simpa using hucont.eventually_lt_const (by simpa using hupper)
  filter_upwards [hlarge', hlower', hupper'] with t htlarge htlower htupper
  exact ⟨by simpa using hz, by simpa using htlarge,
    by simpa using htlower, by simpa using htupper⟩

end

end GaloisForLFunctions.HTGeometry
