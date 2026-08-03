import GaloisForLFunctions.HTGeometry.HardyTwoMultiplier
import Mathlib.Analysis.Analytic.Polynomial

/-!
# Cyclicity of an invertible bounded analytic function in `H²`

If `O` and `1 / O` are both bounded on the unit disk, multiplication by `O` is a bijection of the
coefficient Hardy space with bounded inverse, so the polynomial multiples of `O` are dense: given
`f`, divide by `O`, truncate the Taylor series of the quotient, and multiply back.

No boundary theory is needed — neither Fatou's theorem nor Beurling's, and in particular no outer
function theory.  The multiplier bound of `HardyTwoMultiplier.lean` carries the truncation error.
-/

open MeasureTheory Complex Filter Topology Set
open scoped Real

namespace GaloisForLFunctions.HTGeometry

noncomputable section

theorem analyticOnNhd_polyEval (p : Polynomial ℂ) (s : Set ℂ) :
    AnalyticOnNhd ℂ (fun z => Polynomial.eval z p) s := by
  have h : AnalyticOnNhd ℂ (fun z : ℂ => Polynomial.aeval z p) Set.univ :=
    _root_.AnalyticOnNhd.aeval_polynomial analyticOnNhd_id p
  have h2 : AnalyticOnNhd ℂ (fun z : ℂ => Polynomial.eval z p) Set.univ := by
    simpa [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map] using h
  exact h2.mono (Set.subset_univ s)

/-- The `N`-th Taylor polynomial of a disk-analytic function. -/
def hardyApproxPoly (g : ℂ → ℂ) (R₀ : NNReal) (N : ℕ) : Polynomial ℂ :=
  ∑ k ∈ Finset.range N, Polynomial.C ((cauchyPowerSeries g 0 R₀).coeff k) * Polynomial.X ^ k

theorem eval_hardyApproxPoly (g : ℂ → ℂ) (R₀ : NNReal) (N : ℕ) (z : ℂ) :
    Polynomial.eval z (hardyApproxPoly g R₀ N) = (cauchyPowerSeries g 0 R₀).partialSum N z := by
  rw [hardyApproxPoly, Polynomial.eval_finsetSum, FormalMultilinearSeries.partialSum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X,
    FormalMultilinearSeries.apply_eq_pow_smul_coeff, smul_eq_mul, mul_comm]

/-- The Taylor coefficients of the truncation error are the discarded tail. -/
theorem coeff_sub_partialSum {g : ℂ → ℂ} (hg : AnalyticOnNhd ℂ g (Metric.ball 0 1))
    {R₀ : NNReal} (hR₀0 : 0 < R₀) (hR₀1 : (R₀ : ℝ) < 1) (N k : ℕ) :
    (cauchyPowerSeries (fun z => g z - (cauchyPowerSeries g 0 R₀).partialSum N z) 0 R₀).coeff k
      = if k < N then 0 else (cauchyPowerSeries g 0 R₀).coeff k := by
  have hpart : AnalyticOnNhd ℂ (fun z => (cauchyPowerSeries g 0 R₀).partialSum N z)
      (Metric.ball 0 1) := fun z _ =>
    (hasFPowerSeriesOnBall_partialSum_truncSeries (cauchyPowerSeries g 0 R₀) N).analyticAt_of_mem (by simp)
  rw [cauchyPowerSeries_sub hg hpart hR₀0 hR₀1, cauchyPowerSeries_partialSum N hR₀0 hR₀1]
  show (cauchyPowerSeries g 0 R₀).coeff k - (truncSeries (cauchyPowerSeries g 0 R₀) N).coeff k = _
  rw [coeff_truncSeries]
  by_cases h : k < N
  · rw [if_pos h, if_pos h, sub_self]
  · rw [if_neg h, if_neg h, sub_zero]

/-- The `H²` norm of the truncation error is the discarded tail of the coefficient sum. -/
theorem tsum_normSq_coeff_sub_partialSum {g : ℂ → ℂ} (hg : AnalyticOnNhd ℂ g (Metric.ball 0 1))
    {R₀ : NNReal} (hR₀0 : 0 < R₀) (hR₀1 : (R₀ : ℝ) < 1)
    (hgsum : Summable fun k => ‖(cauchyPowerSeries g 0 R₀).coeff k‖ ^ 2) (N : ℕ) :
    ∑' k, ‖(cauchyPowerSeries
        (fun z => g z - (cauchyPowerSeries g 0 R₀).partialSum N z) 0 R₀).coeff k‖ ^ 2
      = (∑' k, ‖(cauchyPowerSeries g 0 R₀).coeff k‖ ^ 2)
        - ∑ k ∈ Finset.range N, ‖(cauchyPowerSeries g 0 R₀).coeff k‖ ^ 2 := by
  classical
  set b : ℕ → ℝ := fun k => ‖(cauchyPowerSeries g 0 R₀).coeff k‖ ^ 2 with hb
  have hbnn : ∀ k, 0 ≤ b k := fun k => by rw [hb]; positivity
  have hcoeff : ∀ k, ‖(cauchyPowerSeries
      (fun z => g z - (cauchyPowerSeries g 0 R₀).partialSum N z) 0 R₀).coeff k‖ ^ 2
      = if k < N then 0 else b k := by
    intro k
    rw [coeff_sub_partialSum hg hR₀0 hR₀1 N k]
    by_cases h : k < N
    · rw [if_pos h, if_pos h, norm_zero]
      norm_num
    · rw [if_neg h, if_neg h]
  have hsplit : ∀ k, b k = (if k < N then b k else 0) + (if k < N then 0 else b k) := by
    intro k
    by_cases h : k < N
    · rw [if_pos h, if_pos h, add_zero]
    · rw [if_neg h, if_neg h, zero_add]
  have hfin : Summable fun k => if k < N then b k else 0 :=
    summable_of_ne_finset_zero (s := Finset.range N) fun k hk => by
      rw [if_neg (by simpa [Finset.mem_range] using hk)]
  have htail : Summable fun k => if k < N then 0 else b k := by
    refine Summable.of_nonneg_of_le (fun k => ?_) (fun k => ?_) hgsum
    · by_cases h : k < N
      · rw [if_pos h]
      · rw [if_neg h]
        exact hbnn k
    · by_cases h : k < N
      · rw [if_pos h]
        exact hbnn k
      · rw [if_neg h]
  have hfinsum : ∑' k, (if k < N then b k else 0) = ∑ k ∈ Finset.range N, b k := by
    rw [tsum_eq_sum (f := fun k => if k < N then b k else 0) (s := Finset.range N)
      (fun k hk => by rw [if_neg (by simpa [Finset.mem_range] using hk)])]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [if_pos (Finset.mem_range.mp hk)]
  have htot : ∑' k, b k = (∑ k ∈ Finset.range N, b k) + ∑' k, (if k < N then 0 else b k) := by
    calc ∑' k, b k = ∑' k, ((if k < N then b k else 0) + (if k < N then 0 else b k)) :=
          tsum_congr hsplit
      _ = (∑' k, (if k < N then b k else 0)) + ∑' k, (if k < N then 0 else b k) :=
          hfin.tsum_add htail
      _ = (∑ k ∈ Finset.range N, b k) + ∑' k, (if k < N then 0 else b k) := by rw [hfinsum]
  rw [tsum_congr hcoeff, htot]
  ring

/-- The truncation error tends to zero. -/
theorem tendsto_tsum_normSq_coeff_sub_partialSum {g : ℂ → ℂ}
    (hg : AnalyticOnNhd ℂ g (Metric.ball 0 1)) {R₀ : NNReal} (hR₀0 : 0 < R₀) (hR₀1 : (R₀ : ℝ) < 1)
    (hgsum : Summable fun k => ‖(cauchyPowerSeries g 0 R₀).coeff k‖ ^ 2) :
    Tendsto (fun N => ∑' k, ‖(cauchyPowerSeries
        (fun z => g z - (cauchyPowerSeries g 0 R₀).partialSum N z) 0 R₀).coeff k‖ ^ 2)
      atTop (𝓝 0) := by
  have hpart := hgsum.hasSum.tendsto_sum_nat
  have hlim : Tendsto (fun N => (∑' k, ‖(cauchyPowerSeries g 0 R₀).coeff k‖ ^ 2)
      - ∑ k ∈ Finset.range N, ‖(cauchyPowerSeries g 0 R₀).coeff k‖ ^ 2) atTop (𝓝 0) := by
    have hc : Tendsto (fun N : ℕ => (∑' k, ‖(cauchyPowerSeries g 0 R₀).coeff k‖ ^ 2)
        - ∑ k ∈ Finset.range N, ‖(cauchyPowerSeries g 0 R₀).coeff k‖ ^ 2) atTop
        (𝓝 ((∑' k, ‖(cauchyPowerSeries g 0 R₀).coeff k‖ ^ 2)
          - ∑' k, ‖(cauchyPowerSeries g 0 R₀).coeff k‖ ^ 2)) :=
      tendsto_const_nhds.sub hpart
    simpa using hc
  refine hlim.congr fun N => ?_
  exact (tsum_normSq_coeff_sub_partialSum hg hR₀0 hR₀1 hgsum N).symm

/-- **Cyclicity of an invertible bounded analytic function.**  If `O` is nonvanishing on the disk
and both `O` and `1 / O` are bounded there, the polynomial multiples of `O` approximate every `H²`
function in the coefficient norm. -/
theorem tendsto_tsum_normSq_coeff_sub_polynomial_mul {O f : ℂ → ℂ} {M K : ℝ}
    (hO : AnalyticOnNhd ℂ O (Metric.ball 0 1)) (hf : AnalyticOnNhd ℂ f (Metric.ball 0 1))
    (hOne : ∀ z ∈ Metric.ball (0 : ℂ) 1, O z ≠ 0)
    (hM0 : 0 ≤ M) (hOb : ∀ z ∈ Metric.ball (0 : ℂ) 1, ‖O z‖ ^ 2 ≤ M)
    (hK0 : 0 ≤ K) (hOinv : ∀ z ∈ Metric.ball (0 : ℂ) 1, ‖(O z)⁻¹‖ ^ 2 ≤ K)
    {R₀ : NNReal} (hR₀0 : 0 < R₀) (hR₀1 : (R₀ : ℝ) < 1)
    (hfsum : Summable fun k => ‖(cauchyPowerSeries f 0 R₀).coeff k‖ ^ 2) :
    Tendsto (fun N => ∑' k, ‖(cauchyPowerSeries
        (fun z => f z - Polynomial.eval z
          (hardyApproxPoly (fun z => f z / O z) R₀ N) * O z) 0 R₀).coeff k‖ ^ 2)
      atTop (𝓝 0) := by
  set g : ℂ → ℂ := fun z => f z / O z with hgdef
  have hOinvA : AnalyticOnNhd ℂ (fun z => (O z)⁻¹) (Metric.ball 0 1) := by
    have hone : AnalyticOnNhd ℂ (fun _ : ℂ => (1 : ℂ)) (Metric.ball 0 1) := analyticOnNhd_const
    have hdiv := hone.div hO hOne
    simpa using hdiv
  have hgA : AnalyticOnNhd ℂ g (Metric.ball 0 1) := hf.div hO hOne
  -- the quotient is again `H²`, by the bound on `1 / O`
  have hgsum : Summable fun k => ‖(cauchyPowerSeries g 0 R₀).coeff k‖ ^ 2 := by
    have h1 : HasFPowerSeriesAt g (cauchyPowerSeries g 0 R₀) 0 :=
      (hasFPowerSeriesOnBall_of_analyticOnNhd_ball hgA hR₀0 hR₀1).hasFPowerSeriesAt
    have heq : g =ᶠ[nhds 0] fun z => f z * (O z)⁻¹ :=
      Filter.Eventually.of_forall fun z => div_eq_mul_inv (f z) (O z)
    have hser : cauchyPowerSeries g 0 R₀ = cauchyPowerSeries (fun z => f z * (O z)⁻¹) 0 R₀ :=
      (h1.congr heq).eq_formalMultilinearSeries
        (hasFPowerSeriesOnBall_of_analyticOnNhd_ball (hf.mul hOinvA) hR₀0 hR₀1).hasFPowerSeriesAt
    rw [hser]
    exact summable_normSq_coeff_mul hK0 hf hOinvA hOinv hR₀0 hR₀1 hfsum
  -- the approximation error is the truncation error multiplied by `O`
  have hkey : ∀ N : ℕ, ∑' k, ‖(cauchyPowerSeries
      (fun z => f z - Polynomial.eval z (hardyApproxPoly g R₀ N) * O z) 0 R₀).coeff k‖ ^ 2
      ≤ M * ∑' k, ‖(cauchyPowerSeries
        (fun z => g z - (cauchyPowerSeries g 0 R₀).partialSum N z) 0 R₀).coeff k‖ ^ 2 := by
    intro N
    have hpart : AnalyticOnNhd ℂ (fun z => (cauchyPowerSeries g 0 R₀).partialSum N z)
        (Metric.ball 0 1) := fun z _ =>
      (hasFPowerSeriesOnBall_partialSum_truncSeries (cauchyPowerSeries g 0 R₀) N).analyticAt_of_mem (by simp)
    have hdiffA : AnalyticOnNhd ℂ
        (fun z => g z - (cauchyPowerSeries g 0 R₀).partialSum N z) (Metric.ball 0 1) :=
      hgA.sub hpart
    have hLA : AnalyticOnNhd ℂ
        (fun z => f z - Polynomial.eval z (hardyApproxPoly g R₀ N) * O z) (Metric.ball 0 1) :=
      hf.sub ((analyticOnNhd_polyEval (hardyApproxPoly g R₀ N) _).mul hO)
    have h1 : HasFPowerSeriesAt
        (fun z => f z - Polynomial.eval z (hardyApproxPoly g R₀ N) * O z)
        (cauchyPowerSeries
          (fun z => f z - Polynomial.eval z (hardyApproxPoly g R₀ N) * O z) 0 R₀) 0 :=
      (hasFPowerSeriesOnBall_of_analyticOnNhd_ball hLA hR₀0 hR₀1).hasFPowerSeriesAt
    have heq : (fun z => f z - Polynomial.eval z (hardyApproxPoly g R₀ N) * O z)
        =ᶠ[nhds 0] fun z => (g z - (cauchyPowerSeries g 0 R₀).partialSum N z) * O z := by
      filter_upwards [Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self one_pos)] with z hz
      rw [eval_hardyApproxPoly, sub_mul]
      congr 1
      show f z = f z / O z * O z
      rw [div_mul_cancel₀ _ (hOne z hz)]
    have hser : cauchyPowerSeries
        (fun z => f z - Polynomial.eval z (hardyApproxPoly g R₀ N) * O z) 0 R₀
        = cauchyPowerSeries
          (fun z => (g z - (cauchyPowerSeries g 0 R₀).partialSum N z) * O z) 0 R₀ :=
      (h1.congr heq).eq_formalMultilinearSeries
        (hasFPowerSeriesOnBall_of_analyticOnNhd_ball (hdiffA.mul hO) hR₀0 hR₀1).hasFPowerSeriesAt
    rw [hser]
    refine tsum_normSq_coeff_mul_le hM0 hdiffA hO hOb hR₀0 hR₀1 ?_
    refine Summable.of_nonneg_of_le (fun k => sq_nonneg _) (fun k => ?_) hgsum
    rw [coeff_sub_partialSum hgA hR₀0 hR₀1 N k]
    by_cases h : k < N
    · rw [if_pos h, norm_zero, zero_pow (by norm_num : (2:ℕ) ≠ 0)]
      positivity
    · rw [if_neg h]
  refine squeeze_zero (fun N => tsum_nonneg fun k => sq_nonneg _) hkey ?_
  have hlim := (tendsto_tsum_normSq_coeff_sub_partialSum hgA hR₀0 hR₀1 hgsum).const_mul M
  simpa using hlim

end

end GaloisForLFunctions.HTGeometry
