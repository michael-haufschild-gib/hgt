import GaloisForLFunctions.MultiscaleMollifiedZetaField.TheShiftedSelbergAmplitudeHasTheSameMajorant
import GaloisForLFunctions.RHTower.Sieve.SelbergEulerCorrectionWeight

/-!
# A common summable envelope for shifted Selberg correction fibres

The squarefree-support fibres keep the original absolute majorant under
reciprocal-logarithmic shifts. Each fixed fibre is continuous at zero shift.
Cancellation is retained inside the arithmetic convolution; domination is
applied to the absolutely summable fibres before pushing them forward.
-/

open ArithmeticFunction Filter Topology
open RHTower.Sieve
open scoped ArithmeticFunction.Moebius

noncomputable section

namespace GaloisForLFunctions.MultiscaleMollifiedZetaField

/-- The shifted amplitude restricted to the primes of its correction support. -/
def localizedShiftedSelbergAmplitude (c : ℝ) (r n : ℕ) : ℝ := by
  classical
  exact if primeSupportedOn r n then powerShiftedReciprocalAmplitude c n else 0

theorem localizedShiftedSelbergAmplitude_zero (r n : ℕ) :
    localizedShiftedSelbergAmplitude 0 r n = localizedReciprocalMoebiusAmplitude r n := by
  classical
  simp only [localizedShiftedSelbergAmplitude, powerShiftedReciprocalAmplitude_zero,
    localizedReciprocalMoebiusAmplitude]

theorem continuous_localizedShiftedSelbergAmplitude (r n : ℕ) :
    Continuous (fun c : ℝ => localizedShiftedSelbergAmplitude c r n) := by
  classical
  by_cases h : primeSupportedOn r n
  · simpa only [localizedShiftedSelbergAmplitude, if_pos h] using
      continuous_powerShiftedReciprocalAmplitude n
  · simpa only [localizedShiftedSelbergAmplitude, if_neg h] using
      (continuous_const : Continuous (fun _ : ℝ => (0 : ℝ)))

theorem abs_localizedShiftedSelbergAmplitude_le {N : ℕ} (hN : 1 < N)
    (c : ℝ) (r : ℕ) {n : ℕ} (hn : n ≤ N) :
    |localizedShiftedSelbergAmplitude (c / Real.log N) r n| ≤
      Real.exp (2 * |c|) * |localizedReciprocalMoebiusAmplitude r n| := by
  classical
  by_cases h : primeSupportedOn r n
  · simpa only [localizedShiftedSelbergAmplitude, localizedReciprocalMoebiusAmplitude, if_pos h]
      using abs_powerShiftedReciprocalAmplitude_log_shift_le hN c hn
  · simp only [localizedShiftedSelbergAmplitude, localizedReciprocalMoebiusAmplitude,
      if_neg h, abs_zero, mul_zero, le_refl]

/-- The parameterized squarefree-support Euler correction fibre. -/
def shiftedSelbergCorrectionWeight (c : ℝ) (r u v : ℕ) : ℝ :=
  (((moebius r : ℤ) : ℝ) / (r : ℝ) ^ 2) *
    localizedShiftedSelbergAmplitude c r u * localizedShiftedSelbergAmplitude c r v

theorem shiftedSelbergCorrectionWeight_zero (r u v : ℕ) :
    shiftedSelbergCorrectionWeight 0 r u v = selbergCorrectionWeight r u v := by
  simp only [shiftedSelbergCorrectionWeight, localizedShiftedSelbergAmplitude_zero,
    selbergCorrectionWeight]

theorem continuous_shiftedSelbergCorrectionWeight (r u v : ℕ) :
    Continuous (fun c : ℝ => shiftedSelbergCorrectionWeight c r u v) :=
  ((continuous_localizedShiftedSelbergAmplitude r u).const_mul _).mul
    (continuous_localizedShiftedSelbergAmplitude r v)

/-- The original absolute fibre majorant changes only by the constant `exp(4|c|)`. -/
theorem abs_shiftedSelbergCorrectionWeight_le {N : ℕ} (hN : 1 < N)
    (c : ℝ) (r : ℕ) {u v : ℕ} (hu : u ≤ N) (hv : v ≤ N) :
    |shiftedSelbergCorrectionWeight (c / Real.log N) r u v| ≤
      Real.exp (4 * |c|) * |selbergCorrectionWeight r u v| := by
  have hu' := abs_localizedShiftedSelbergAmplitude_le hN c r hu
  have hv' := abs_localizedShiftedSelbergAmplitude_le hN c r hv
  unfold shiftedSelbergCorrectionWeight
  rw [abs_mul, abs_mul]
  calc
    _ ≤ |(((moebius r : ℤ) : ℝ) / (r : ℝ) ^ 2)| *
        (Real.exp (2 * |c|) * |localizedReciprocalMoebiusAmplitude r u|) *
        (Real.exp (2 * |c|) * |localizedReciprocalMoebiusAmplitude r v|) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hu' (abs_nonneg _)) hv' (abs_nonneg _)
        (by positivity)
    _ = _ := by
      have he : Real.exp (2 * |c|) * Real.exp (2 * |c|) = Real.exp (4 * |c|) := by
        rw [← Real.exp_add]
        congr 1
        ring
      unfold selbergCorrectionWeight
      rw [abs_mul, abs_mul, ← he]
      ring

/-- The majorant is summable over all support fibres, independently of the finite cutoff. -/
theorem summable_shiftedSelbergCorrectionMajorant (c : ℝ) :
    Summable (fun x : ℕ × (ℕ × ℕ) =>
      Real.exp (4 * |c|) * |selbergCorrectionWeight x.1 x.2.1 x.2.2|) := by
  simpa only [Real.norm_eq_abs] using
    summable_selbergCorrectionWeight.norm.mul_left (Real.exp (4 * |c|))

/-- The correction fibre retained by the finite bivariate convolution. -/
def cutoffShiftedSelbergCorrection (c : ℝ) (N : ℕ) (x : ℕ × (ℕ × ℕ)) : ℝ :=
  if x.1 * x.2.1 ≤ N ∧ x.1 * x.2.2 ≤ N then
    shiftedSelbergCorrectionWeight (c / Real.log N) x.1 x.2.1 x.2.2 else 0

/-- Reciprocal-logarithmic shifts preserve the limiting unit mass of the actual cutoff correction. -/
theorem tendsto_tsum_cutoffShiftedSelbergCorrection (c : ℝ) :
    Tendsto (fun N : ℕ => ∑' x : ℕ × (ℕ × ℕ), cutoffShiftedSelbergCorrection c N x)
      atTop (𝓝 1) := by
  have hlog : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hc : Tendsto (fun N : ℕ => c / Real.log N) atTop (𝓝 0) :=
    Filter.Tendsto.div_atTop tendsto_const_nhds hlog
  have hpoint (x : ℕ × (ℕ × ℕ)) :
      Tendsto (fun N : ℕ => cutoffShiftedSelbergCorrection c N x) atTop
        (𝓝 (selbergCorrectionWeight x.1 x.2.1 x.2.2)) := by
    have hh := (continuous_shiftedSelbergCorrectionWeight x.1 x.2.1 x.2.2).continuousAt.tendsto.comp hc
    rw [shiftedSelbergCorrectionWeight_zero] at hh
    refine hh.congr' ?_
    filter_upwards [eventually_ge_atTop (max (x.1 * x.2.1) (x.1 * x.2.2))] with N hN
    simp only [Function.comp_def, cutoffShiftedSelbergCorrection,
      if_pos ⟨(le_max_left _ _).trans hN, (le_max_right _ _).trans hN⟩]
  have hbound : ∀ᶠ N : ℕ in atTop, ∀ x : ℕ × (ℕ × ℕ),
      ‖cutoffShiftedSelbergCorrection c N x‖ ≤
        Real.exp (4 * |c|) * |selbergCorrectionWeight x.1 x.2.1 x.2.2| := by
    filter_upwards [eventually_ge_atTop 2] with N hN
    rintro ⟨r, u, v⟩
    by_cases hr : r = 0
    · simp [cutoffShiftedSelbergCorrection, hr, shiftedSelbergCorrectionWeight, selbergCorrectionWeight]
    by_cases hx : r * u ≤ N ∧ r * v ≤ N
    · have hr1 : 1 ≤ r := Nat.pos_of_ne_zero hr
      have hu : u ≤ N := calc
        u = 1 * u := by rw [one_mul]
        _ ≤ r * u := Nat.mul_le_mul_right u hr1
        _ ≤ N := hx.1
      have hv : v ≤ N := calc
        v = 1 * v := by rw [one_mul]
        _ ≤ r * v := Nat.mul_le_mul_right v hr1
        _ ≤ N := hx.2
      simp only [cutoffShiftedSelbergCorrection, if_pos hx, Real.norm_eq_abs]
      exact abs_shiftedSelbergCorrectionWeight_le (by omega) c r hu hv
    · simp only [cutoffShiftedSelbergCorrection, if_neg hx, norm_zero]
      positivity
  have hh := tendsto_tsum_of_dominated_convergence
    (summable_shiftedSelbergCorrectionMajorant c) hpoint hbound
  rw [tsum_selbergCorrectionWeight] at hh
  exact hh

end GaloisForLFunctions.MultiscaleMollifiedZetaField
