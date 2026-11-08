import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.TopWindowConductorRowCancellation

/-!
# Polar sampling and normalized square means

The polar square-root weight turns a scalar row into a horizon vector. In the
critical normalization its squared top-window norm is bounded by the ordinary
normalized square mean of that row.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Finset Filter Topology
open scoped BigOperators
namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
open CriticalArithmeticCorrelationTheory BezoutValuationIncidence
  RenormalizedArithmeticPotentialTheory SpacingScaleHarmonicAnalysis

/-- A scalar row sampled with the polar square-root normalization. -/
def polarSampleVector (c : ℝ) (N : ℕ) (F : ℕ → ℝ) : EuclideanSpace ℝ (PrimeHorizonIndex N) :=
  WithLp.toLp 2 (fun idx => (c / N) * Real.sqrt idx.1 * F idx.1 / Real.sqrt (Real.log N))

/-- Sampled polar squared norms cost at most the normalized scalar square mean. -/
theorem normalized_topWindow_polarSample_le {c δ : ℝ} {N : ℕ} (hc : 0 < c)
    (hN : 1 ≤ N) (hL : 0 < Real.log (N : ℝ)) (F : ℕ → ℝ) :
    (Real.log (N : ℝ) / c ^ 2) * topWindowResidualMass δ N (polarSampleVector c N F) ≤
      (∑ n ∈ Ioc ⌊δ * (N : ℝ)⌋₊ N, F n ^ 2) / N := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  unfold topWindowResidualMass
  rw [mul_sum, sum_div]
  refine sum_le_sum fun n hn => ?_
  have hn1 : 1 ≤ n := by have := (mem_Ioc.mp hn).1; omega
  have hnN := (mem_Ioc.mp hn).2
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  let idx : PrimeHorizonIndex N := ⟨n, mem_Icc.mpr ⟨hn1, hnN⟩⟩
  have hext : primeHorizonExtension (polarSampleVector c N F) n =
      (c / N) * Real.sqrt n * F n / Real.sqrt (Real.log N) := by
    change primeHorizonExtension (polarSampleVector c N F) idx.1 = _
    rw [primeHorizonExtension_coe]
    rfl
  rw [hext]
  have he : (Real.log (N : ℝ) / c ^ 2) *
      ((c / N) * Real.sqrt n * F n / Real.sqrt (Real.log N)) ^ 2 =
      ((n : ℝ) / N) * (F n ^ 2 / N) := by
    rw [div_pow, mul_pow, mul_pow, div_pow, Real.sq_sqrt hn0.le, Real.sq_sqrt hL.le]
    field_simp [hc.ne', hN0.ne', hL.ne']
    ring
  rw [he]
  have hx : (n : ℝ) / N ≤ 1 := (div_le_one hN0).mpr (by exact_mod_cast hnN)
  exact (mul_le_mul_of_nonneg_right hx (by positivity)).trans_eq (one_mul _)

/-- Scalar square-mean convergence transfers to polar top-window convergence. -/
theorem tendsto_normalized_topWindow_polarSample {c : ℕ → ℝ} (hc : ∀ N, 0 < c N)
    {δ : ℝ} {F : ℕ → ℕ → ℝ}
    (hF : Tendsto (fun N : ℕ => (∑ n ∈ Ioc ⌊δ * (N : ℝ)⌋₊ N, F N n ^ 2) / N)
      atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => (Real.log (N : ℝ) / c N ^ 2) *
      topWindowResidualMass δ N (polarSampleVector (c N) N (F N))) atTop (𝓝 0) := by
  refine squeeze_zero' (Eventually.of_forall fun N =>
    mul_nonneg (div_nonneg (Real.log_natCast_nonneg N) (sq_nonneg _))
      (topWindowResidualMass_nonneg δ N _)) ?_ hF
  filter_upwards [eventually_ge_atTop 1,
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_gt_atTop 0]
    with N hN hL
  exact normalized_topWindow_polarSample_le (hc N) hN hL (F N)

#print axioms normalized_topWindow_polarSample_le
#print axioms tendsto_normalized_topWindow_polarSample
end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
