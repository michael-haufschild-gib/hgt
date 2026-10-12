import GaloisForLFunctions.RHTower.PaperThetaDirichletConvolution
import GaloisForLFunctions.HTGeometry.PaperFourierRiemannLebesgue

/-! # Pointwise interior Fourier recovery on the exact theta L¹ domain -/

noncomputable section

open MeasureTheory Set Filter Topology

namespace RHTower.PaperThetaEndpoint

open GaloisForLFunctions.HTGeometry FourierLLogL

private theorem integrable_mul_phase {f : ℝ → ℂ} (hf : Integrable f) (u : ℝ) :
    Integrable (fun x => f x * Period.phase u x) := by
  apply hf.norm.mono' (hf.aestronglyMeasurable.mul (Period.phase_cont u).aestronglyMeasurable)
  exact Eventually.of_forall fun x => by
    change ‖f x * Period.phase u x‖ ≤ _
    rw [norm_mul, Period.phase_unimod, mul_one]

/-- Integrable local cancellation makes the exact Dirichlet error vanish. -/
theorem tendsto_dini_oscillation (z : L1Point) (t : Ioo (0 : ℝ) 1) :
    Tendsto (fun N : ℕ => ∫ y in Period.centerWin,
      diniDifference z.val t.val y * (Real.sin (Period.ang N y + Real.pi*y) : ℂ))
      atTop (𝓝 0) := by
  let f := Period.centerWin.indicator (diniDifference z.val t.val)
  have hf : Integrable f :=
    (integrable_indicator_iff measurableSet_Ico).mpr (integrable_diniDifference z t)
  have he (N : ℕ) : (∫ y in Period.centerWin,
      diniDifference z.val t.val y * (Real.sin (Period.ang N y + Real.pi*y) : ℂ)) =
      ((∫ y, f y * Period.phase ((N : ℝ)+1/2) y) -
        ∫ y, f y * Period.phase (-((N : ℝ)+1/2)) y) / (2*Complex.I) := by
    rw [← integral_sub (integrable_mul_phase hf _) (integrable_mul_phase hf _), ← integral_div,
      ← integral_indicator (show MeasurableSet Period.centerWin from measurableSet_Ico)]
    apply integral_congr_ae
    filter_upwards [] with y
    by_cases hy : y ∈ Period.centerWin
    · simp only [f, indicator_of_mem hy, Period.dirichlet_sine_eq_phase_pair]
      ring
    · simp only [f, indicator_of_notMem hy, zero_mul, sub_self, zero_div]
  simp_rw [he]
  simpa only [sub_self, zero_div] using
    ((Period.tendsto_integral_phase_half_pos f).sub
      (Period.tendsto_integral_phase_half_neg f)).div_const (2*Complex.I)

/-- Every interior point is recovered; no exceptional set or logarithmic admission is needed. -/
theorem circle_interior_recovery_L1 (z : L1Point) (t : Ioo (0 : ℝ) 1) :
    Tendsto (fun N : ℕ => symmetricPartialSum (circleMode z.val) N (Period.circle t.val))
      atTop (𝓝 (flatModePullback z.val t.val)) := by
  have h : Tendsto (fun N : ℕ =>
      symmetricPartialSum (circleMode z.val) N (Period.circle t.val) - flatModePullback z.val t.val)
      atTop (𝓝 0) := by
    simpa only [symmetric_error_eq_dini_integral] using tendsto_dini_oscillation z t
  simpa only [sub_add_cancel, zero_add] using h.add_const (flatModePullback z.val t.val)

end RHTower.PaperThetaEndpoint
