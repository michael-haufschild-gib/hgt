import GaloisForLFunctions.HTGeometry.StrelitzCauchyJetBound
import GaloisForLFunctions.HTGeometry.NevanlinnaCoeffFun

/-!
# Second Euler-jet bound throughout Strelitz's enlarged set

The exact identity

`v = u + z² f″/f - u²`

combines with the unit-distance Cauchy estimate, the enlarged set's value floor, and its upper
first-jet bound.  The result is the source's uniform second-jet estimate at every point of the
enlarged set, before maximum-growth asymptotics are applied.
-/

namespace GaloisForLFunctions.HTGeometry

open Complex

noncomputable section

/-- Exact logarithmic-jet identity `v = u + z²f″/f - u²`. -/
theorem eulerLogDerivSecond_eq_add_deriv2_sub_sq
    {f : ℂ → ℂ} {z : ℂ} (hf : AnalyticAt ℂ f z) (hfz : f z ≠ 0) :
    eulerLogDerivSecond f z = eulerLogDeriv f z +
      z ^ 2 * deriv (deriv f) z / f z - (eulerLogDeriv f z) ^ 2 := by
  have hf' : HasDerivAt f (deriv f z) z := hf.differentiableAt.hasDerivAt
  have hdf : HasDerivAt (deriv f) (deriv (deriv f) z) z :=
    hf.deriv.differentiableAt.hasDerivAt
  have hnum := (hasDerivAt_id z).mul hdf
  have hquot := hnum.div hf' hfz
  have hderiv : deriv (eulerLogDeriv f) z =
      ((deriv f z + z * deriv (deriv f) z) * f z -
        z * deriv f z * deriv f z) / f z ^ 2 := by
    change deriv (fun w : ℂ => w * deriv f w / f w) z = _
    rw [show (fun w : ℂ => w * deriv f w / f w) = id * deriv f / f by
      funext w
      rfl]
    simpa using hquot.deriv
  rw [eulerLogDerivSecond, hderiv]
  simp only [eulerLogDeriv]
  field_simp [hfz]

/-- Raw Cauchy bound for the second Euler logarithmic jet. -/
theorem norm_eulerLogDerivSecond_le_cauchy
    {a : ℕ → ℂ} (ha : EntireCoeffs a) {z : ℂ} (hfz : coeffFun a z ≠ 0) :
    ‖eulerLogDerivSecond (coeffFun a) z‖ ≤
      ‖eulerLogDeriv (coeffFun a) z‖ +
        ‖z‖ ^ 2 * (2 * coeffCircleMaximumNorm a (‖z‖ + 1)) / ‖coeffFun a z‖ +
          ‖eulerLogDeriv (coeffFun a) z‖ ^ 2 := by
  have hfa : AnalyticAt ℂ (coeffFun a) z :=
    GaloisForLFunctions.Nevanlinna.analyticOnNhd_coeffFun ha z (by simp)
  rw [eulerLogDerivSecond_eq_add_deriv2_sub_sq hfa hfz]
  calc
    ‖eulerLogDeriv (coeffFun a) z +
        z ^ 2 * deriv (deriv (coeffFun a)) z / coeffFun a z -
          eulerLogDeriv (coeffFun a) z ^ 2‖
        ≤ ‖eulerLogDeriv (coeffFun a) z‖ +
            ‖z ^ 2 * deriv (deriv (coeffFun a)) z / coeffFun a z‖ +
              ‖eulerLogDeriv (coeffFun a) z ^ 2‖ := by
          exact (norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ = ‖eulerLogDeriv (coeffFun a) z‖ +
          ‖z‖ ^ 2 * ‖deriv (deriv (coeffFun a)) z‖ / ‖coeffFun a z‖ +
            ‖eulerLogDeriv (coeffFun a) z‖ ^ 2 := by
          rw [norm_div, norm_mul, norm_pow, norm_pow]
    _ ≤ ‖eulerLogDeriv (coeffFun a) z‖ +
          ‖z‖ ^ 2 * (2 * coeffCircleMaximumNorm a (‖z‖ + 1)) / ‖coeffFun a z‖ +
            ‖eulerLogDeriv (coeffFun a) z‖ ^ 2 := by
          gcongr
          exact norm_deriv_deriv_coeffFun_le_circleMaximumNorm_add_one ha z

/-- The exact circle maximum is nonnegative at every real radius. -/
theorem coeffCircleMaximumNorm_nonneg
    {a : ℕ → ℂ} (ha : EntireCoeffs a) (r : ℝ) :
    0 ≤ coeffCircleMaximumNorm a r :=
  (norm_nonneg _).trans (norm_coeffFun_circleMap_le_coeffCircleMaximumNorm ha r 0)

/-- The source's uniform second-jet estimate on the enlarged set, before applying maximum-growth
asymptotics. -/
theorem norm_eulerLogDerivSecond_le_of_mem_strelitzEnlargedSet
    {a : ℕ → ℂ} (ha : EntireCoeffs a) {s : ℕ} {z : ℂ}
    (hzH : z ∈ strelitzEnlargedSet a s) :
    ‖eulerLogDerivSecond (coeffFun a) z‖ ≤
      strelitzMaximumSlope a (Real.log ‖z‖) ^ ((5 : ℝ) / 3) +
        ‖z‖ ^ 2 * (2 * coeffCircleMaximumNorm a (‖z‖ + 1)) /
          coeffCircleMaximumNorm a ‖z‖ ^ (1 - 1 / (4 * (s : ℝ))) +
        (strelitzMaximumSlope a (Real.log ‖z‖) ^ ((5 : ℝ) / 3)) ^ 2 := by
  rcases hzH with ⟨hz, hlarge, _hlower, hupper⟩
  have hM0 := coeffCircleMaximumNorm_nonneg ha ‖z‖
  have hfz : coeffFun a z ≠ 0 := by
    rw [← norm_ne_zero_iff]
    exact ne_of_gt ((Real.rpow_nonneg hM0 _).trans_lt hlarge)
  have hMpos : 0 < coeffCircleMaximumNorm a ‖z‖ := by
    have hpoint := norm_coeffFun_le_coeffCircleMaximumNorm_of_norm_eq ha hz rfl
    exact (norm_pos_iff.mpr hfz).trans_le hpoint
  have hMpowpos : 0 <
      coeffCircleMaximumNorm a ‖z‖ ^ (1 - 1 / (4 * (s : ℝ))) :=
    Real.rpow_pos_of_pos hMpos _
  have hnum0 : 0 ≤ ‖z‖ ^ 2 * (2 * coeffCircleMaximumNorm a (‖z‖ + 1)) := by
    exact mul_nonneg (sq_nonneg _) <|
      mul_nonneg (by norm_num) (coeffCircleMaximumNorm_nonneg ha _)
  have hfrac :
      ‖z‖ ^ 2 * (2 * coeffCircleMaximumNorm a (‖z‖ + 1)) / ‖coeffFun a z‖ ≤
        ‖z‖ ^ 2 * (2 * coeffCircleMaximumNorm a (‖z‖ + 1)) /
          coeffCircleMaximumNorm a ‖z‖ ^ (1 - 1 / (4 * (s : ℝ))) :=
    div_le_div_of_nonneg_left hnum0 hMpowpos hlarge.le
  have hu := hupper.le
  calc
    ‖eulerLogDerivSecond (coeffFun a) z‖ ≤
        ‖eulerLogDeriv (coeffFun a) z‖ +
          ‖z‖ ^ 2 * (2 * coeffCircleMaximumNorm a (‖z‖ + 1)) / ‖coeffFun a z‖ +
            ‖eulerLogDeriv (coeffFun a) z‖ ^ 2 :=
      norm_eulerLogDerivSecond_le_cauchy ha hfz
    _ ≤ strelitzMaximumSlope a (Real.log ‖z‖) ^ ((5 : ℝ) / 3) +
          ‖z‖ ^ 2 * (2 * coeffCircleMaximumNorm a (‖z‖ + 1)) /
            coeffCircleMaximumNorm a ‖z‖ ^ (1 - 1 / (4 * (s : ℝ))) +
          (strelitzMaximumSlope a (Real.log ‖z‖) ^ ((5 : ℝ) / 3)) ^ 2 := by
      gcongr

end

end GaloisForLFunctions.HTGeometry
