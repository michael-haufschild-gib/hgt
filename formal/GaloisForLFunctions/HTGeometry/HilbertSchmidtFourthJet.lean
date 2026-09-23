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
/-- Every Taylor coefficient of the Hilbert--Schmidt resolvent is its matching
holomorphic power trace.  This exposes the all-order local data needed to
compare a source resolvent with a carrier. -/
theorem taylorCoeff_resolventTrace_eq_trace {K : ι × ι → ℂ} (hK : IsHS K)
    (n : ℕ) :
    taylorCoeff (resolventTrace K) n =
      if n = 0 then 0 else ∑' i, hsPow K n (i, i) := by
  rw [resolventTraceCoeff_eq_taylorCoeff hK n]
  cases n with
  | zero => simp [resolventTraceCoeff]
  | succ n => simp [resolventTraceCoeff]

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

/-- The cubic coefficient of the Hilbert--Carleman determinant is its cubic
holomorphic trace. -/
theorem detCoeff_three_eq_neg_third_traceCube {K : ι × ι → ℂ} (hK : IsHS K) :
    detCoeff K 3 = -(∑' i, hsPow K 2 (i, i)) / 3 := by
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
  have hD0 : PowerSeries.coeff 0 (GaloisForLFunctions.taylorPS (fredholmDet K)) = 1 := by
    rw [GaloisForLFunctions.coeff_taylorPS]
    simp [fredholmDet, fredholmExp]
  have hD1 : PowerSeries.coeff 1 (GaloisForLFunctions.taylorPS (fredholmDet K)) = 0 := by
    rw [GaloisForLFunctions.coeff_taylorPS]
    simpa [detCoeff, taylorCoeff, div_eq_mul_inv, mul_comm] using detCoeff_one_eq_zero hK
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
  have hR2 : PowerSeries.coeff 2 (GaloisForLFunctions.taylorPS (-resolventTrace K)) =
      -(∑' i, hsPow K 2 (i, i)) := by
    rw [hRcoeff]
    rfl
  have hrec := congrArg (PowerSeries.coeff 2) hps
  rw [GaloisForLFunctions.taylorPS_deriv, PowerSeries.coeff_derivative,
    PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at hrec
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add] at hrec
  rw [hD0, hD1, hR0, hR2] at hrec
  norm_num at hrec
  have hcoef3 : iteratedDeriv 3 (fredholmDet K) 0 / 6 = detCoeff K 3 := by
    rw [detCoeff, taylorCoeff]
    norm_num [Nat.factorial]
    ring
  rw [hcoef3] at hrec
  linear_combination hrec / 3

/-- The fourth coefficient of the entire Hilbert--Carleman determinant is determined by
its square and fourth holomorphic traces. -/
theorem taylorCoeff_entireDet2_four {K : ι × ι → ℂ} (hK : IsHS K) :
    taylorCoeff (entireDet2 K) 4 =
      (∑' i, hsPow K 1 (i, i)) ^ 2 / 8 -
        (∑' i, hsPow K 3 (i, i)) / 4 := by
  rw [taylorCoeff_entireDet2_eq_detCoeff hK, detCoeff_four_eq_trace hK]

/-- The cubic coefficient of the entire Hilbert--Carleman determinant is its cubic
holomorphic trace. -/
theorem taylorCoeff_entireDet2_three {K : ι × ι → ℂ} (hK : IsHS K) :
    taylorCoeff (entireDet2 K) 3 = -(∑' i, hsPow K 2 (i, i)) / 3 := by
  rw [taylorCoeff_entireDet2_eq_detCoeff hK, detCoeff_three_eq_neg_third_traceCube hK]


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

/-- Squaring an entire function of value one and vanishing linear coefficient doubles its
cubic Taylor coefficient. -/
theorem taylorCoeff_sq_three_of_value_one_of_linear_zero
    {f : ℂ → ℂ} (hf : Differentiable ℂ f) (h0 : f 0 = 1)
    (h1 : taylorCoeff f 1 = 0) :
    taylorCoeff (fun z => f z ^ 2) 3 = 2 * taylorCoeff f 3 := by
  have hcf : ContDiffAt ℂ 3 f 0 := hf.contDiff.contDiffAt
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

/-- Reflection pairing removes the odd sector without changing the quadratic jet of a
center-normalized function with zero linear coefficient. -/
theorem taylorCoeff_reflectionProduct_two_of_value_one_of_linear_zero
    {f : ℂ → ℂ} (hf : Differentiable ℂ f) (h0 : f 0 = 1)
    (h1 : taylorCoeff f 1 = 0) :
    taylorCoeff (fun z => f z * f (-z)) 2 = 2 * taylorCoeff f 2 := by
  have hcf : ContDiffAt ℂ 2 f 0 := hf.contDiff.contDiffAt
  have hnegdiff : Differentiable ℂ (fun z : ℂ => f (-z)) :=
    hf.comp differentiable_neg
  have hcfneg : ContDiffAt ℂ 2 (fun z : ℂ => f (-z)) 0 :=
    hnegdiff.contDiff.contDiffAt
  have h1' : iteratedDeriv 1 f 0 = 0 := by
    simpa [taylorCoeff] using h1
  have hneg (n : ℕ) :
      iteratedDeriv n (fun z : ℂ => f (-z)) 0 =
        (-1 : ℂ) ^ n • iteratedDeriv n f 0 := by
    simpa using iteratedDeriv_comp_neg n f 0
  rw [taylorCoeff]
  rw [show (fun z : ℂ => f z * f (-z)) = f * (fun z : ℂ => f (-z)) by rfl]
  rw [iteratedDeriv_mul hcf hcfneg]
  simp only [Finset.sum_range_succ, Nat.choose_self, Nat.choose_one_right,
    Nat.sub_zero, Nat.sub_self]
  rw [hneg 2, hneg 1, hneg 0]
  simp [h0, h1', taylorCoeff]
  ring

/-- Reflection pairing removes the odd sector without changing the quartic jet of a
center-normalized function with zero linear coefficient. -/
theorem taylorCoeff_reflectionProduct_four_of_value_one_of_linear_zero
    {f : ℂ → ℂ} (hf : Differentiable ℂ f) (h0 : f 0 = 1)
    (h1 : taylorCoeff f 1 = 0) :
    taylorCoeff (fun z => f z * f (-z)) 4 =
      2 * taylorCoeff f 4 + (taylorCoeff f 2) ^ 2 := by
  have hcf : ContDiffAt ℂ 4 f 0 := hf.contDiff.contDiffAt
  have hnegdiff : Differentiable ℂ (fun z : ℂ => f (-z)) :=
    hf.comp differentiable_neg
  have hcfneg : ContDiffAt ℂ 4 (fun z : ℂ => f (-z)) 0 :=
    hnegdiff.contDiff.contDiffAt
  have h1' : iteratedDeriv 1 f 0 = 0 := by
    simpa [taylorCoeff] using h1
  have hneg (n : ℕ) :
      iteratedDeriv n (fun z : ℂ => f (-z)) 0 =
        (-1 : ℂ) ^ n • iteratedDeriv n f 0 := by
    simpa using iteratedDeriv_comp_neg n f 0
  rw [taylorCoeff]
  rw [show (fun z : ℂ => f z * f (-z)) = f * (fun z : ℂ => f (-z)) by rfl]
  rw [iteratedDeriv_mul hcf hcfneg]
  simp only [Finset.sum_range_succ, Nat.choose_self, Nat.choose_one_right,
    Nat.choose_two_right, Nat.sub_zero, Nat.sub_self]
  rw [hneg 4, hneg 3, hneg 2, hneg 1, hneg 0]
  simp [h0, h1', taylorCoeff]
  ring

/-- The sixth coefficient of a Hilbert--Carleman determinant is fixed by the
second through sixth holomorphic traces. -/
theorem detCoeff_six_eq_trace {K : ι × ι → ℂ} (hK : IsHS K) :
    detCoeff K 6 =
      -(∑' i, hsPow K 5 (i, i)) / 6 +
        (∑' i, hsPow K 1 (i, i)) * (∑' i, hsPow K 3 (i, i)) / 8 +
        (∑' i, hsPow K 2 (i, i)) ^ 2 / 18 -
        (∑' i, hsPow K 1 (i, i)) ^ 3 / 48 := by
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
  have hD3 : PowerSeries.coeff 3 (GaloisForLFunctions.taylorPS (fredholmDet K)) =
      -(∑' i, hsPow K 2 (i, i)) / 3 := by
    rw [GaloisForLFunctions.coeff_taylorPS]
    simpa [detCoeff, taylorCoeff, div_eq_mul_inv, mul_comm] using
      detCoeff_three_eq_neg_third_traceCube hK
  have hD4 : PowerSeries.coeff 4 (GaloisForLFunctions.taylorPS (fredholmDet K)) =
      (∑' i, hsPow K 1 (i, i)) ^ 2 / 8 -
        (∑' i, hsPow K 3 (i, i)) / 4 := by
    rw [GaloisForLFunctions.coeff_taylorPS]
    simpa [detCoeff, taylorCoeff, div_eq_mul_inv, mul_comm] using detCoeff_four_eq_trace hK
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
  have hRn (n : ℕ) : PowerSeries.coeff (n + 1)
      (GaloisForLFunctions.taylorPS (-resolventTrace K)) =
      -(∑' i, hsPow K (n + 1) (i, i)) := by
    rw [hRcoeff]
    rfl
  have hrec := congrArg (PowerSeries.coeff 5) hps
  rw [GaloisForLFunctions.taylorPS_deriv, PowerSeries.coeff_derivative,
    PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at hrec
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add] at hrec
  rw [hD0, hD1, hD2, hD3, hD4, hR0,
    hRn 0, hRn 1, hRn 2, hRn 3, hRn 4] at hrec
  norm_num at hrec
  have hcoef6 : iteratedDeriv 6 (fredholmDet K) 0 / 720 = detCoeff K 6 := by
    rw [detCoeff, taylorCoeff]
    norm_num [Nat.factorial]
    ring
  rw [hcoef6] at hrec
  linear_combination hrec / 6

/-- The sixth Taylor coefficient of the entire regularized determinant is its
sixth determinant coefficient. -/
theorem taylorCoeff_entireDet2_six {K : ι × ι → ℂ} (hK : IsHS K) :
    taylorCoeff (entireDet2 K) 6 =
      -(∑' i, hsPow K 5 (i, i)) / 6 +
        (∑' i, hsPow K 1 (i, i)) * (∑' i, hsPow K 3 (i, i)) / 8 +
        (∑' i, hsPow K 2 (i, i)) ^ 2 / 18 -
        (∑' i, hsPow K 1 (i, i)) ^ 3 / 48 := by
  rw [taylorCoeff_entireDet2_eq_detCoeff hK, detCoeff_six_eq_trace hK]

/-- Reflection pairing removes odd sectors from the sixth jet. -/
theorem taylorCoeff_reflectionProduct_six_of_value_one_of_linear_zero
    {f : ℂ → ℂ} (hf : Differentiable ℂ f) (h0 : f 0 = 1)
    (h1 : taylorCoeff f 1 = 0) :
    taylorCoeff (fun z => f z * f (-z)) 6 =
      2 * taylorCoeff f 6 + 2 * taylorCoeff f 2 * taylorCoeff f 4 -
        (taylorCoeff f 3) ^ 2 := by
  have hcf : ContDiffAt ℂ 6 f 0 := hf.contDiff.contDiffAt
  have hnegdiff : Differentiable ℂ (fun z : ℂ => f (-z)) :=
    hf.comp differentiable_neg
  have hcfneg : ContDiffAt ℂ 6 (fun z : ℂ => f (-z)) 0 :=
    hnegdiff.contDiff.contDiffAt
  have h1' : iteratedDeriv 1 f 0 = 0 := by
    simpa [taylorCoeff] using h1
  have hneg (n : ℕ) :
      iteratedDeriv n (fun z : ℂ => f (-z)) 0 =
        (-1 : ℂ) ^ n • iteratedDeriv n f 0 := by
    simpa using iteratedDeriv_comp_neg n f 0
  rw [taylorCoeff]
  rw [show (fun z : ℂ => f z * f (-z)) = f * (fun z : ℂ => f (-z)) by rfl]
  rw [iteratedDeriv_mul hcf hcfneg]
  simp only [Finset.sum_range_succ, Nat.choose_self, Nat.choose_one_right,
    Nat.choose_two_right, Nat.sub_zero, Nat.sub_self]
  rw [hneg 6, hneg 5, hneg 4, hneg 3, hneg 2, hneg 1, hneg 0]
  simp [h0, h1', taylorCoeff]
  norm_num [Nat.choose]
  ring

/-- Reflection pairing has an explicit eighth jet: every odd trace contribution cancels after
the two reflected factors are multiplied. -/
theorem taylorCoeff_reflectionProduct_eight_of_value_one_of_linear_zero
    {f : ℂ → ℂ} (hf : Differentiable ℂ f) (h0 : f 0 = 1)
    (h1 : taylorCoeff f 1 = 0) :
    taylorCoeff (fun z => f z * f (-z)) 8 =
      2 * taylorCoeff f 8 + 2 * taylorCoeff f 2 * taylorCoeff f 6 -
        2 * taylorCoeff f 3 * taylorCoeff f 5 + (taylorCoeff f 4) ^ 2 := by
  have hcf : ContDiffAt ℂ 8 f 0 := hf.contDiff.contDiffAt
  have hnegdiff : Differentiable ℂ (fun z : ℂ => f (-z)) :=
    hf.comp differentiable_neg
  have hcfneg : ContDiffAt ℂ 8 (fun z : ℂ => f (-z)) 0 :=
    hnegdiff.contDiff.contDiffAt
  have h1' : iteratedDeriv 1 f 0 = 0 := by
    simpa [taylorCoeff] using h1
  have hneg (n : ℕ) :
      iteratedDeriv n (fun z : ℂ => f (-z)) 0 =
        (-1 : ℂ) ^ n • iteratedDeriv n f 0 := by
    simpa using iteratedDeriv_comp_neg n f 0
  rw [taylorCoeff]
  rw [show (fun z : ℂ => f z * f (-z)) = f * (fun z : ℂ => f (-z)) by rfl]
  rw [iteratedDeriv_mul hcf hcfneg]
  simp only [Finset.sum_range_succ, Nat.choose_self, Nat.choose_one_right,
    Nat.choose_two_right, Nat.sub_zero, Nat.sub_self]
  rw [hneg 8, hneg 7, hneg 6, hneg 5, hneg 4, hneg 3, hneg 2, hneg 1, hneg 0]
  simp [h0, h1', taylorCoeff]
  norm_num [Nat.choose]
  ring

private theorem fredholmDet_taylor_ode {K : ι × ι → ℂ} (hK : IsHS K) :
    GaloisForLFunctions.taylorPS (deriv (fredholmDet K)) =
      GaloisForLFunctions.taylorPS (fredholmDet K) *
        GaloisForLFunctions.taylorPS (-resolventTrace K) := by
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
  calc
    GaloisForLFunctions.taylorPS (deriv (fredholmDet K)) =
        GaloisForLFunctions.taylorPS (fredholmDet K * (-resolventTrace K)) :=
      taylorPS_congr_of_eventuallyEq_local hlocal
    _ = GaloisForLFunctions.taylorPS (fredholmDet K) *
        GaloisForLFunctions.taylorPS (-resolventTrace K) :=
      taylorPS_mul_of_analyticAt_local hD hR.neg

private theorem coeff_taylorPS_fredholmDet_eq_detCoeff {K : ι × ι → ℂ} (n : ℕ) :
    PowerSeries.coeff n (GaloisForLFunctions.taylorPS (fredholmDet K)) = detCoeff K n := by
  rw [GaloisForLFunctions.coeff_taylorPS, detCoeff, taylorCoeff]
  ring

private theorem coeff_taylorPS_neg_resolventTrace {K : ι × ι → ℂ} (hK : IsHS K)
    (n : ℕ) :
    PowerSeries.coeff n (GaloisForLFunctions.taylorPS (-resolventTrace K)) =
      if n = 0 then 0 else -(∑' i, hsPow K n (i, i)) := by
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
    _ = if n = 0 then 0 else -(∑' i, hsPow K n (i, i)) := by
      cases n with
      | zero => simp [resolventTraceCoeff]
      | succ n => simp [resolventTraceCoeff]

/-- The fifth determinant coefficient is the first odd jet that is needed for an eighth-order
reflection calculation. -/
theorem detCoeff_five_eq_trace {K : ι × ι → ℂ} (hK : IsHS K) :
    detCoeff K 5 =
      -(∑' i, hsPow K 4 (i, i)) / 5 +
        (∑' i, hsPow K 1 (i, i)) * (∑' i, hsPow K 2 (i, i)) / 6 := by
  have hps := fredholmDet_taylor_ode hK
  have hD0 : PowerSeries.coeff 0 (GaloisForLFunctions.taylorPS (fredholmDet K)) = 1 := by
    rw [coeff_taylorPS_fredholmDet_eq_detCoeff]
    simp [detCoeff, taylorCoeff, fredholmDet, fredholmExp]
  have hD1 : PowerSeries.coeff 1 (GaloisForLFunctions.taylorPS (fredholmDet K)) = 0 := by
    rw [coeff_taylorPS_fredholmDet_eq_detCoeff]
    exact detCoeff_one_eq_zero hK
  have hD2 : PowerSeries.coeff 2 (GaloisForLFunctions.taylorPS (fredholmDet K)) =
      -(∑' i, hsPow K 1 (i, i)) / 2 := by
    rw [coeff_taylorPS_fredholmDet_eq_detCoeff]
    exact detCoeff_two_eq_neg_half_traceSquare hK
  have hD3 : PowerSeries.coeff 3 (GaloisForLFunctions.taylorPS (fredholmDet K)) =
      -(∑' i, hsPow K 2 (i, i)) / 3 := by
    rw [coeff_taylorPS_fredholmDet_eq_detCoeff]
    exact detCoeff_three_eq_neg_third_traceCube hK
  have hD4 : PowerSeries.coeff 4 (GaloisForLFunctions.taylorPS (fredholmDet K)) =
      (∑' i, hsPow K 1 (i, i)) ^ 2 / 8 -
        (∑' i, hsPow K 3 (i, i)) / 4 := by
    rw [coeff_taylorPS_fredholmDet_eq_detCoeff]
    exact detCoeff_four_eq_trace hK
  have hrec := congrArg (PowerSeries.coeff 4) hps
  rw [GaloisForLFunctions.taylorPS_deriv, PowerSeries.coeff_derivative,
    PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at hrec
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add] at hrec
  rw [hD0, hD1, hD2, hD3, hD4,
    coeff_taylorPS_neg_resolventTrace hK 0,
    coeff_taylorPS_neg_resolventTrace hK 1,
    coeff_taylorPS_neg_resolventTrace hK 2,
    coeff_taylorPS_neg_resolventTrace hK 3,
    coeff_taylorPS_neg_resolventTrace hK 4] at hrec
  norm_num at hrec
  have hcoef5 : iteratedDeriv 5 (fredholmDet K) 0 / 120 = detCoeff K 5 := by
    rw [detCoeff, taylorCoeff]
    norm_num [Nat.factorial]
    ring
  rw [hcoef5] at hrec
  linear_combination hrec / 5

/-- The seventh determinant coefficient supplies the final odd term which cancels in the eighth
signed reflection jet. -/
theorem detCoeff_seven_eq_trace {K : ι × ι → ℂ} (hK : IsHS K) :
    detCoeff K 7 =
      -(∑' i, hsPow K 6 (i, i)) / 7 +
        (∑' i, hsPow K 1 (i, i)) * (∑' i, hsPow K 4 (i, i)) / 10 +
        (∑' i, hsPow K 2 (i, i)) * (∑' i, hsPow K 3 (i, i)) / 12 -
        (∑' i, hsPow K 1 (i, i)) ^ 2 * (∑' i, hsPow K 2 (i, i)) / 24 := by
  have hps := fredholmDet_taylor_ode hK
  have hD0 : PowerSeries.coeff 0 (GaloisForLFunctions.taylorPS (fredholmDet K)) = 1 := by
    rw [coeff_taylorPS_fredholmDet_eq_detCoeff]
    simp [detCoeff, taylorCoeff, fredholmDet, fredholmExp]
  have hD1 : PowerSeries.coeff 1 (GaloisForLFunctions.taylorPS (fredholmDet K)) = 0 := by
    rw [coeff_taylorPS_fredholmDet_eq_detCoeff]
    exact detCoeff_one_eq_zero hK
  have hD2 : PowerSeries.coeff 2 (GaloisForLFunctions.taylorPS (fredholmDet K)) =
      -(∑' i, hsPow K 1 (i, i)) / 2 := by
    rw [coeff_taylorPS_fredholmDet_eq_detCoeff]
    exact detCoeff_two_eq_neg_half_traceSquare hK
  have hD3 : PowerSeries.coeff 3 (GaloisForLFunctions.taylorPS (fredholmDet K)) =
      -(∑' i, hsPow K 2 (i, i)) / 3 := by
    rw [coeff_taylorPS_fredholmDet_eq_detCoeff]
    exact detCoeff_three_eq_neg_third_traceCube hK
  have hD4 : PowerSeries.coeff 4 (GaloisForLFunctions.taylorPS (fredholmDet K)) =
      (∑' i, hsPow K 1 (i, i)) ^ 2 / 8 -
        (∑' i, hsPow K 3 (i, i)) / 4 := by
    rw [coeff_taylorPS_fredholmDet_eq_detCoeff]
    exact detCoeff_four_eq_trace hK
  have hD5 : PowerSeries.coeff 5 (GaloisForLFunctions.taylorPS (fredholmDet K)) =
      -(∑' i, hsPow K 4 (i, i)) / 5 +
        (∑' i, hsPow K 1 (i, i)) * (∑' i, hsPow K 2 (i, i)) / 6 := by
    rw [coeff_taylorPS_fredholmDet_eq_detCoeff]
    exact detCoeff_five_eq_trace hK
  have hD6 : PowerSeries.coeff 6 (GaloisForLFunctions.taylorPS (fredholmDet K)) =
      -(∑' i, hsPow K 5 (i, i)) / 6 +
        (∑' i, hsPow K 1 (i, i)) * (∑' i, hsPow K 3 (i, i)) / 8 +
        (∑' i, hsPow K 2 (i, i)) ^ 2 / 18 -
        (∑' i, hsPow K 1 (i, i)) ^ 3 / 48 := by
    rw [coeff_taylorPS_fredholmDet_eq_detCoeff]
    exact detCoeff_six_eq_trace hK
  have hrec := congrArg (PowerSeries.coeff 6) hps
  rw [GaloisForLFunctions.taylorPS_deriv, PowerSeries.coeff_derivative,
    PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at hrec
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add] at hrec
  rw [hD0, hD1, hD2, hD3, hD4, hD5, hD6,
    coeff_taylorPS_neg_resolventTrace hK 0,
    coeff_taylorPS_neg_resolventTrace hK 1,
    coeff_taylorPS_neg_resolventTrace hK 2,
    coeff_taylorPS_neg_resolventTrace hK 3,
    coeff_taylorPS_neg_resolventTrace hK 4,
    coeff_taylorPS_neg_resolventTrace hK 5,
    coeff_taylorPS_neg_resolventTrace hK 6] at hrec
  norm_num at hrec
  have hcoef7 : iteratedDeriv 7 (fredholmDet K) 0 / 5040 = detCoeff K 7 := by
    rw [detCoeff, taylorCoeff]
    norm_num [Nat.factorial]
    ring
  rw [hcoef7] at hrec
  linear_combination hrec / 7

/-- The eighth Hilbert--Carleman determinant coefficient is the exact finite trace polynomial
needed to test a signed K-RVM determinant against the order-seven Xi cumulant. -/
theorem detCoeff_eight_eq_trace {K : ι × ι → ℂ} (hK : IsHS K) :
    detCoeff K 8 =
      -(∑' i, hsPow K 7 (i, i)) / 8 +
        (∑' i, hsPow K 1 (i, i)) * (∑' i, hsPow K 5 (i, i)) / 12 +
        (∑' i, hsPow K 2 (i, i)) * (∑' i, hsPow K 4 (i, i)) / 15 +
        (∑' i, hsPow K 3 (i, i)) ^ 2 / 32 -
        (∑' i, hsPow K 1 (i, i)) ^ 2 * (∑' i, hsPow K 3 (i, i)) / 32 -
        (∑' i, hsPow K 1 (i, i)) * (∑' i, hsPow K 2 (i, i)) ^ 2 / 36 +
        (∑' i, hsPow K 1 (i, i)) ^ 4 / 384 := by
  have hps := fredholmDet_taylor_ode hK
  have hD0 : PowerSeries.coeff 0 (GaloisForLFunctions.taylorPS (fredholmDet K)) = 1 := by
    rw [coeff_taylorPS_fredholmDet_eq_detCoeff]
    simp [detCoeff, taylorCoeff, fredholmDet, fredholmExp]
  have hD1 : PowerSeries.coeff 1 (GaloisForLFunctions.taylorPS (fredholmDet K)) = 0 := by
    rw [coeff_taylorPS_fredholmDet_eq_detCoeff]
    exact detCoeff_one_eq_zero hK
  have hD2 : PowerSeries.coeff 2 (GaloisForLFunctions.taylorPS (fredholmDet K)) =
      -(∑' i, hsPow K 1 (i, i)) / 2 := by
    rw [coeff_taylorPS_fredholmDet_eq_detCoeff]
    exact detCoeff_two_eq_neg_half_traceSquare hK
  have hD3 : PowerSeries.coeff 3 (GaloisForLFunctions.taylorPS (fredholmDet K)) =
      -(∑' i, hsPow K 2 (i, i)) / 3 := by
    rw [coeff_taylorPS_fredholmDet_eq_detCoeff]
    exact detCoeff_three_eq_neg_third_traceCube hK
  have hD4 : PowerSeries.coeff 4 (GaloisForLFunctions.taylorPS (fredholmDet K)) =
      (∑' i, hsPow K 1 (i, i)) ^ 2 / 8 -
        (∑' i, hsPow K 3 (i, i)) / 4 := by
    rw [coeff_taylorPS_fredholmDet_eq_detCoeff]
    exact detCoeff_four_eq_trace hK
  have hD5 : PowerSeries.coeff 5 (GaloisForLFunctions.taylorPS (fredholmDet K)) =
      -(∑' i, hsPow K 4 (i, i)) / 5 +
        (∑' i, hsPow K 1 (i, i)) * (∑' i, hsPow K 2 (i, i)) / 6 := by
    rw [coeff_taylorPS_fredholmDet_eq_detCoeff]
    exact detCoeff_five_eq_trace hK
  have hD6 : PowerSeries.coeff 6 (GaloisForLFunctions.taylorPS (fredholmDet K)) =
      -(∑' i, hsPow K 5 (i, i)) / 6 +
        (∑' i, hsPow K 1 (i, i)) * (∑' i, hsPow K 3 (i, i)) / 8 +
        (∑' i, hsPow K 2 (i, i)) ^ 2 / 18 -
        (∑' i, hsPow K 1 (i, i)) ^ 3 / 48 := by
    rw [coeff_taylorPS_fredholmDet_eq_detCoeff]
    exact detCoeff_six_eq_trace hK
  have hD7 : PowerSeries.coeff 7 (GaloisForLFunctions.taylorPS (fredholmDet K)) =
      -(∑' i, hsPow K 6 (i, i)) / 7 +
        (∑' i, hsPow K 1 (i, i)) * (∑' i, hsPow K 4 (i, i)) / 10 +
        (∑' i, hsPow K 2 (i, i)) * (∑' i, hsPow K 3 (i, i)) / 12 -
        (∑' i, hsPow K 1 (i, i)) ^ 2 * (∑' i, hsPow K 2 (i, i)) / 24 := by
    rw [coeff_taylorPS_fredholmDet_eq_detCoeff]
    exact detCoeff_seven_eq_trace hK
  have hrec := congrArg (PowerSeries.coeff 7) hps
  rw [GaloisForLFunctions.taylorPS_deriv, PowerSeries.coeff_derivative,
    PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at hrec
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add] at hrec
  rw [hD0, hD1, hD2, hD3, hD4, hD5, hD6, hD7,
    coeff_taylorPS_neg_resolventTrace hK 0,
    coeff_taylorPS_neg_resolventTrace hK 1,
    coeff_taylorPS_neg_resolventTrace hK 2,
    coeff_taylorPS_neg_resolventTrace hK 3,
    coeff_taylorPS_neg_resolventTrace hK 4,
    coeff_taylorPS_neg_resolventTrace hK 5,
    coeff_taylorPS_neg_resolventTrace hK 6,
    coeff_taylorPS_neg_resolventTrace hK 7] at hrec
  norm_num at hrec
  have hcoef8 : iteratedDeriv 8 (fredholmDet K) 0 / 40320 = detCoeff K 8 := by
    rw [detCoeff, taylorCoeff]
    norm_num [Nat.factorial]
    ring
  rw [hcoef8] at hrec
  linear_combination hrec / 8

/-- The eighth Taylor coefficient of the entire regularized determinant is its eighth finite
Hilbert--Carleman trace polynomial. -/
theorem taylorCoeff_entireDet2_eight {K : ι × ι → ℂ} (hK : IsHS K) :
    taylorCoeff (entireDet2 K) 8 =
      -(∑' i, hsPow K 7 (i, i)) / 8 +
        (∑' i, hsPow K 1 (i, i)) * (∑' i, hsPow K 5 (i, i)) / 12 +
        (∑' i, hsPow K 2 (i, i)) * (∑' i, hsPow K 4 (i, i)) / 15 +
        (∑' i, hsPow K 3 (i, i)) ^ 2 / 32 -
        (∑' i, hsPow K 1 (i, i)) ^ 2 * (∑' i, hsPow K 3 (i, i)) / 32 -
        (∑' i, hsPow K 1 (i, i)) * (∑' i, hsPow K 2 (i, i)) ^ 2 / 36 +
        (∑' i, hsPow K 1 (i, i)) ^ 4 / 384 := by
  rw [taylorCoeff_entireDet2_eq_detCoeff hK, detCoeff_eight_eq_trace hK]

end GaloisForLFunctions.HTGeometry
