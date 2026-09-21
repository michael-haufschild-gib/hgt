/-
# Fourth jet of a Hilbert--Carleman determinant

For every Hilbert--Schmidt kernel, the fourth Taylor coefficient of
`det₂(1-zK)` is determined by the two trace-class coordinates
`tr K²` and `tr K⁴`.  The proof represents the resolvent trace by its
actual local power series and takes degree three in `D' = -D R`.
-/

import GaloisForLFunctions.HTGeometry.HermitianDilationSecondJetObstruction
import GaloisForLFunctions.HTGeometry.TaylorFormalBridge

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open HilbertSchmidt Filter Metric
open scoped BigOperators Topology

variable {ι : Type*} [DecidableEq ι]

private theorem hasFPowerSeriesOnBall_of_hasSum_local
    {a : ℕ → ℂ} {f : ℂ → ℂ} {r : ℝ} (hr : 0 < r)
    (ha : ∀ w : ℂ, ‖w‖ < r → HasSum (fun n => a n * w ^ n) (f w)) :
    HasFPowerSeriesOnBall f (FormalMultilinearSeries.ofScalars ℂ a) 0
      (ENNReal.ofReal (r / 2)) where
  r_le := by
    have hsum := (ha ((r / 2 : ℝ) : ℂ) (by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
      linarith)).summable
    have htend := hsum.tendsto_atTop_zero
    have hnorm : Tendsto (fun n => ‖FormalMultilinearSeries.ofScalars ℂ a n‖ *
        ((⟨r / 2, by linarith⟩ : NNReal) : ℝ) ^ n) atTop (𝓝 0) := by
      have h := htend.norm
      rw [norm_zero] at h
      refine h.congr fun n => ?_
      rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (by linarith), FormalMultilinearSeries.ofScalars_norm]
    have hradius := FormalMultilinearSeries.le_radius_of_tendsto _ hnorm
    rwa [ENNReal.ofReal_eq_coe_nnreal (by linarith : (0 : ℝ) ≤ r / 2)]
  r_pos := by simpa using (by linarith : (0 : ℝ) < r / 2)
  hasSum := by
    intro y hy
    have hy' : ‖y‖ < r := by
      rw [Metric.mem_eball, edist_zero_right] at hy
      have hlt : ENNReal.ofReal ‖y‖ < ENNReal.ofReal (r / 2) := by
        rwa [← ofReal_norm] at hy
      have hhalf := (ENNReal.ofReal_lt_ofReal_iff (by linarith)).mp hlt
      linarith
    have h := ha y hy'
    rw [zero_add]
    refine h.congr_fun fun n => ?_
    rw [FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul]

private theorem eq_of_hasSum_mul_pow_eq_local {a b : ℕ → ℂ} {f : ℂ → ℂ} {r : ℝ} (hr : 0 < r)
    (ha : ∀ w : ℂ, ‖w‖ < r → HasSum (fun n => a n * w ^ n) (f w))
    (hb : ∀ w : ℂ, ‖w‖ < r → HasSum (fun n => b n * w ^ n) (f w)) : a = b := by
  have hA := (hasFPowerSeriesOnBall_of_hasSum_local hr ha).hasFPowerSeriesAt
  have hB := (hasFPowerSeriesOnBall_of_hasSum_local hr hb).hasFPowerSeriesAt
  have h := hA.eq_formalMultilinearSeries hB
  funext n
  have h1 := congrArg (fun p : FormalMultilinearSeries ℂ ℂ ℂ => p n (fun _ => (1 : ℂ))) h
  simpa only [FormalMultilinearSeries.ofScalars_apply_eq, one_pow, smul_eq_mul, mul_one] using h1

private theorem coeff_eq_iteratedDeriv_div_factorial_of_hasSum_local
    {a : ℕ → ℂ} {f : ℂ → ℂ} {r : ℝ} (hr : 0 < r)
    (ha : ∀ w : ℂ, ‖w‖ < r → HasSum (fun n => a n * w ^ n) (f w)) (n : ℕ) :
    a n = iteratedDeriv n f 0 / n.factorial := by
  have hball := hasFPowerSeriesOnBall_of_hasSum_local hr ha
  have hdiff : DifferentiableOn ℂ f (Metric.ball (0 : ℂ) (r / 2)) := by
    have h := hball.differentiableOn
    rwa [Metric.eball_ofReal] at h
  have hb : ∀ w : ℂ, ‖w‖ < r / 2 →
      HasSum (fun n => (iteratedDeriv n f 0 / n.factorial) * w ^ n) (f w) := by
    intro w hw
    have h := Complex.hasSum_taylorSeries_on_ball hdiff (z := w) (by simpa using hw)
    refine h.congr_fun fun n => ?_
    rw [sub_zero, smul_eq_mul, smul_eq_mul]
    ring
  have ha' : ∀ w : ℂ, ‖w‖ < r / 2 → HasSum (fun n => a n * w ^ n) (f w) :=
    fun w hw => ha w (by linarith)
  exact congrFun (eq_of_hasSum_mul_pow_eq_local (by linarith) ha' hb) n
private def resolventTraceCoeff (K : ι × ι → ℂ) : ℕ → ℂ
  | 0 => 0
  | n + 1 => ∑' i, hsPow K (n + 1) (i, i)

omit [DecidableEq ι] in
private theorem resolventTraceCoeff_hasSum {K : ι × ι → ℂ} (hK : IsHS K)
    {w : ℂ} (hw : ‖w‖ * hsNorm K < 1) :
    HasSum (fun n : ℕ => resolventTraceCoeff K n * w ^ n) (resolventTrace K w) := by
  let F : ℕ → ℂ := fun n => resolventTraceCoeff K n * w ^ n
  have htail : Summable (fun n : ℕ => F (n + 1)) := by
    exact (resolventTrace_summable hK w hw).congr (by
      intro n
      simp only [F, resolventTraceCoeff]
      ring)
  have hF : Summable F := (summable_nat_add_iff 1).mp htail
  have hsum : (∑' n : ℕ, F n) = resolventTrace K w := by
    calc
      (∑' n : ℕ, F n) = (∑ i ∈ Finset.range 1, F i) + ∑' n : ℕ, F (n + 1) :=
        (hF.sum_add_tsum_nat_add 1).symm
      _ = ∑' n : ℕ, w ^ (n + 1) * (∑' i, hsPow K (n + 1) (i, i)) := by
        simp only [F, resolventTraceCoeff, Finset.sum_range_succ, Finset.sum_range_zero,
          zero_mul, zero_add]
        apply tsum_congr
        intro n
        ring
      _ = resolventTrace K w := rfl
  simpa only [F, hsum] using hF.hasSum

omit [DecidableEq ι] in
private theorem resolventTraceCoeff_eq_taylorCoeff {K : ι × ι → ℂ} (hK : IsHS K)
    (n : ℕ) : taylorCoeff (resolventTrace K) n = resolventTraceCoeff K n := by
  let r : ℝ := detRadius K
  have hr0 : 0 < r := detRadius_pos K
  have hr : r * hsNorm K < 1 := detRadius_mul_hsNorm_lt K
  have hsum : ∀ w : ℂ, ‖w‖ < r →
      HasSum (fun n : ℕ => resolventTraceCoeff K n * w ^ n) (resolventTrace K w) := by
    intro w hw
    apply resolventTraceCoeff_hasSum hK
    exact lt_of_le_of_lt
      (mul_le_mul_of_nonneg_right (le_of_lt hw) (hsNorm_nonneg K)) hr
  have hcoeff :=
    coeff_eq_iteratedDeriv_div_factorial_of_hasSum_local hr0 hsum n
  simpa [taylorCoeff, div_eq_mul_inv, mul_comm] using hcoeff.symm

omit [DecidableEq ι] in
private theorem resolventTrace_analyticAt_zero {K : ι × ι → ℂ} (hK : IsHS K) :
    AnalyticAt ℂ (resolventTrace K) 0 := by
  let r : ℝ := detRadius K
  have hr0 : 0 < r := detRadius_pos K
  have hr : r * hsNorm K < 1 := detRadius_mul_hsNorm_lt K
  have hsum : ∀ w : ℂ, ‖w‖ < r →
      HasSum (fun n : ℕ => resolventTraceCoeff K n * w ^ n) (resolventTrace K w) := by
    intro w hw
    apply resolventTraceCoeff_hasSum hK
    exact lt_of_le_of_lt
      (mul_le_mul_of_nonneg_right (le_of_lt hw) (hsNorm_nonneg K)) hr
  exact (hasFPowerSeriesOnBall_of_hasSum_local hr0 hsum).analyticAt

private theorem taylorPS_congr_of_eventuallyEq_local {f g : ℂ → ℂ}
    (hfg : f =ᶠ[nhds (0 : ℂ)] g) :
    GaloisForLFunctions.taylorPS f = GaloisForLFunctions.taylorPS g := by
  ext n
  rw [GaloisForLFunctions.coeff_taylorPS, GaloisForLFunctions.coeff_taylorPS,
    hfg.iteratedDeriv_eq n]

private theorem taylorPS_mul_of_analyticAt_local {u v : ℂ → ℂ}
    (hu : AnalyticAt ℂ u 0) (hv : AnalyticAt ℂ v 0) :
    GaloisForLFunctions.taylorPS (u * v) =
      GaloisForLFunctions.taylorPS u * GaloisForLFunctions.taylorPS v := by
  ext N
  rw [GaloisForLFunctions.coeff_taylorPS, PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    iteratedDeriv_mul hu.contDiffAt hv.contDiffAt, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mem_range, Nat.lt_succ_iff] at hi
  rw [GaloisForLFunctions.coeff_taylorPS, GaloisForLFunctions.coeff_taylorPS]
  have hfac : (N.choose i : ℂ) * (i.factorial : ℂ) * ((N - i).factorial : ℂ) =
      (N.factorial : ℂ) := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hi
  have hi0 : (i.factorial : ℂ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero i
  have hNi0 : ((N - i).factorial : ℂ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (N - i)
  have hN0 : (N.factorial : ℂ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero N
  field_simp
  rw [← hfac]
  ring

theorem detCoeff_four_eq_trace {K : ι × ι → ℂ} (hK : IsHS K) :
    detCoeff K 4 =
      (∑' i, hsPow K 1 (i, i)) ^ 2 / 8 -
        (∑' i, hsPow K 3 (i, i)) / 4 := by
  let r : ℝ := detRadius K
  have hr0 : 0 < r := detRadius_pos K
  have hr : r * hsNorm K < 1 := detRadius_mul_hsNorm_lt K
  have hD : AnalyticAt ℂ (fredholmDet K) 0 :=
    (fredholmDet_differentiableOn hK r hr).analyticAt
      (isOpen_ball.mem_nhds (show (0 : ℂ) ∈ ball 0 r by simpa using hr0))
  have hR : AnalyticAt ℂ (resolventTrace K) 0 := resolventTrace_analyticAt_zero hK
  have hlocal :
      deriv (fredholmDet K) =ᶠ[nhds (0 : ℂ)]
        fredholmDet K * (-resolventTrace K) := by
    filter_upwards [isOpen_ball.mem_nhds
      (show (0 : ℂ) ∈ ball 0 r by simpa using hr0)] with z hz
    exact (hasDerivAt_fredholmDet hK r hr z hz).deriv
  have hps : GaloisForLFunctions.taylorPS (deriv (fredholmDet K)) =
      GaloisForLFunctions.taylorPS (fredholmDet K) *
        GaloisForLFunctions.taylorPS (-resolventTrace K) := by
    calc
      GaloisForLFunctions.taylorPS (deriv (fredholmDet K)) =
          GaloisForLFunctions.taylorPS (fredholmDet K * (-resolventTrace K)) :=
        taylorPS_congr_of_eventuallyEq_local hlocal
      _ = GaloisForLFunctions.taylorPS (fredholmDet K) *
          GaloisForLFunctions.taylorPS (-resolventTrace K) :=
        taylorPS_mul_of_analyticAt_local hD hR.neg
  have hdet0 : fredholmDet K 0 = 1 := by
    simp [fredholmDet, fredholmExp]
  have hD0 : PowerSeries.coeff 0 (GaloisForLFunctions.taylorPS (fredholmDet K)) = 1 := by
    rw [GaloisForLFunctions.coeff_taylorPS]
    simpa [iteratedDeriv_zero] using hdet0
  have hD1 : PowerSeries.coeff 1 (GaloisForLFunctions.taylorPS (fredholmDet K)) = 0 := by
    rw [GaloisForLFunctions.coeff_taylorPS]
    simpa [detCoeff, taylorCoeff, div_eq_mul_inv, mul_comm] using detCoeff_one_eq_zero hK
  have hD2 : PowerSeries.coeff 2 (GaloisForLFunctions.taylorPS (fredholmDet K)) =
      -(∑' i, hsPow K 1 (i, i)) / 2 := by
    rw [GaloisForLFunctions.coeff_taylorPS]
    simpa [detCoeff, taylorCoeff, div_eq_mul_inv, mul_comm] using
      detCoeff_two_eq_neg_half_traceSquare hK
  have hRcoeff (n : ℕ) :
      PowerSeries.coeff n (GaloisForLFunctions.taylorPS (-resolventTrace K)) =
        -resolventTraceCoeff K n := by
    calc
      PowerSeries.coeff n (GaloisForLFunctions.taylorPS (-resolventTrace K)) =
          -(iteratedDeriv n (resolventTrace K) 0 / (n.factorial : ℂ)) := by
        rw [GaloisForLFunctions.coeff_taylorPS, iteratedDeriv_neg]
        ring
      _ = -taylorCoeff (resolventTrace K) n := by
        simp [taylorCoeff, div_eq_mul_inv]
        ring
      _ = -resolventTraceCoeff K n := by
        rw [resolventTraceCoeff_eq_taylorCoeff hK n]
  have hR0 : PowerSeries.coeff 0 (GaloisForLFunctions.taylorPS (-resolventTrace K)) = 0 := by
    rw [hRcoeff]
    simp [resolventTraceCoeff]
  have hR1 : PowerSeries.coeff 1 (GaloisForLFunctions.taylorPS (-resolventTrace K)) =
      -(∑' i, hsPow K 1 (i, i)) := by
    rw [hRcoeff]
    rfl
  have hR3 : PowerSeries.coeff 3 (GaloisForLFunctions.taylorPS (-resolventTrace K)) =
      -(∑' i, hsPow K 3 (i, i)) := by
    rw [hRcoeff]
    rfl
  have hrec := congrArg (PowerSeries.coeff 3) hps
  rw [GaloisForLFunctions.taylorPS_deriv, PowerSeries.coeff_derivative,
    PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at hrec
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add] at hrec
  rw [hD0, hD1, hD2, hR0, hR1, hR3] at hrec
  norm_num at hrec
  have hcoef4 : iteratedDeriv 4 (fredholmDet K) 0 / 24 = detCoeff K 4 := by
    rw [detCoeff, taylorCoeff]
    norm_num [Nat.factorial]
    ring
  rw [hcoef4] at hrec
  linear_combination hrec / 4

/-- The fourth coefficient of the entire Hilbert--Carleman determinant is determined by
its square and fourth holomorphic traces. -/
theorem taylorCoeff_entireDet2_four {K : ι × ι → ℂ} (hK : IsHS K) :
    taylorCoeff (entireDet2 K) 4 =
      (∑' i, hsPow K 1 (i, i)) ^ 2 / 8 -
        (∑' i, hsPow K 3 (i, i)) / 4 := by
  rw [taylorCoeff_entireDet2_eq_detCoeff hK, detCoeff_four_eq_trace hK]


/-- Squaring an entire function of value one and vanishing linear coefficient doubles its
quadratic Taylor coefficient. -/
theorem taylorCoeff_sq_two_of_value_one_of_linear_zero
    {f : ℂ → ℂ} (hf : Differentiable ℂ f) (h0 : f 0 = 1)
    (h1 : taylorCoeff f 1 = 0) :
    taylorCoeff (fun z => f z ^ 2) 2 = 2 * taylorCoeff f 2 := by
  have hcf : ContDiffAt ℂ 2 f 0 := hf.contDiff.contDiffAt
  have h1' : iteratedDeriv 1 f 0 = 0 := by
    simpa [taylorCoeff] using h1
  rw [taylorCoeff]
  rw [show (fun z : ℂ => f z ^ 2) = f * f by
    funext z
    simp [pow_two]]
  rw [iteratedDeriv_mul hcf hcf]
  simp only [Finset.sum_range_succ, Nat.choose_self, Nat.choose_one_right,
    Nat.sub_zero, Nat.sub_self]
  simp [h0, h1', taylorCoeff]
  ring

/-- Squaring an entire function of value one and vanishing linear coefficient gives the
fourth Taylor coefficient `2 f₄ + f₂²`. -/
theorem taylorCoeff_sq_four_of_value_one_of_linear_zero
    {f : ℂ → ℂ} (hf : Differentiable ℂ f) (h0 : f 0 = 1)
    (h1 : taylorCoeff f 1 = 0) :
    taylorCoeff (fun z => f z ^ 2) 4 =
      2 * taylorCoeff f 4 + (taylorCoeff f 2) ^ 2 := by
  have hcf : ContDiffAt ℂ 4 f 0 := hf.contDiff.contDiffAt
  have h1' : iteratedDeriv 1 f 0 = 0 := by
    simpa [taylorCoeff] using h1
  rw [taylorCoeff]
  rw [show (fun z : ℂ => f z ^ 2) = f * f by
    funext z
    simp [pow_two]]
  rw [iteratedDeriv_mul hcf hcf]
  simp only [Finset.sum_range_succ, Nat.choose_self, Nat.choose_one_right,
    Nat.choose_two_right, Nat.sub_zero, Nat.sub_self]
  simp [h0, h1', taylorCoeff]
  ring

end GaloisForLFunctions.HTGeometry
