import GaloisForLFunctions.RHTower.TraceHankelSequenceCone
import Mathlib.Analysis.Complex.Liouville

/-!
# Analytic trace--Hankel instability

This file lifts the coefficient-level Hankel-cone result to genuine analytic
functions.  A Cauchy estimate shows that changing a sufficiently remote even
Taylor coefficient is arbitrarily small on every strictly smaller disc, while
one monomial-square test detects the change exactly.
-/

noncomputable section

namespace RHTower

open Complex Metric Set Filter Topology

/-- The real moment sequence read from the even Taylor coefficients at the
origin.  On a Schwarz-real even germ these are its actual real coefficients. -/
def analyticTraceMoments (f : ℂ → ℂ) (n : ℕ) : ℝ :=
  ((iteratedDeriv (2 * n) f 0) / ((2 * n).factorial : ℂ)).re

/-- Analytic trace--Hankel positivity means positivity of the moment sequence
formed from the even Taylor coefficients. -/
def AnalyticTraceHankelNonnegative (f : ℂ → ℂ) : Prop :=
  SequenceTraceHankelNonnegative (analyticTraceMoments f)

/-- The remote even-coefficient perturbation.  Its exponent `4N` targets
moment coordinate `2N`. -/
def remoteEvenPerturbation (f : ℂ → ℂ) (N : ℕ) (z : ℂ) : ℂ :=
  f z - (analyticTraceMoments f (2 * N) + 1 : ℝ) * z ^ (4 * N)

/-- The perturbation sets the selected real even Taylor coefficient to `-1`
exactly. -/
theorem analyticTraceMoments_remoteEvenPerturbation
    {f : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) (N : ℕ) :
    analyticTraceMoments (remoteEvenPerturbation f N) (2 * N) = -1 := by
  let k : ℕ := 4 * N
  let c : ℂ := (analyticTraceMoments f (2 * N) + 1 : ℝ)
  have hfk : ContDiffAt ℂ (k : WithTop ℕ∞) f 0 := hf.contDiffAt
  have hpow : ContDiffAt ℂ (k : WithTop ℕ∞) (fun z : ℂ => z ^ k) 0 := by fun_prop
  have hcpow : ContDiffAt ℂ (k : WithTop ℕ∞) (fun z : ℂ => c * z ^ k) 0 :=
    contDiffAt_const.mul hpow
  have hderiv :
      iteratedDeriv k (remoteEvenPerturbation f N) 0 =
        iteratedDeriv k f 0 - c * (k.factorial : ℂ) := by
    have hsub := iteratedDeriv_sub hfk hcpow
    rw [iteratedDeriv_const_mul c hpow, iteratedDeriv_fun_pow_zero, if_pos rfl] at hsub
    have hfun : remoteEvenPerturbation f N =
        f - fun z : ℂ => c * z ^ k := by
      funext z
      simp [remoteEvenPerturbation, k, c]
    rw [hfun]
    exact hsub
  unfold analyticTraceMoments
  have hkfac : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
  have hindex : 2 * (2 * N) = k := by omega
  rw [hindex, hderiv]
  rw [sub_div, mul_div_cancel_right₀ c hkfac]
  change ((iteratedDeriv k f 0 / (k.factorial : ℂ)).re - c.re) = -1
  simp only [ofReal_add, ofReal_one, add_re, ofReal_re, one_re, c]
  have hm : (iteratedDeriv k f 0 / (k.factorial : ℂ)).re =
      analyticTraceMoments f (2 * N) := by
    unfold analyticTraceMoments
    rw [hindex]
  rw [hm]
  ring

/-- Every remote perturbation fails trace--Hankel positivity, witnessed by the
single polynomial square `X^(2N)`. -/
theorem remoteEvenPerturbation_not_traceHankel
    {f : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) (N : ℕ) :
    ¬ AnalyticTraceHankelNonnegative (remoteEvenPerturbation f N) := by
  intro h
  have hmono := h (Polynomial.X ^ N)
  rw [sequenceTraceHankel_X_pow] at hmono
  have hidx : N + N = 2 * N := by omega
  rw [hidx, analyticTraceMoments_remoteEvenPerturbation hf] at hmono
  linarith

/-- Cauchy's estimate for the selected Taylor coefficient. -/
theorem norm_evenTaylorCoefficient_le
    {f : ℂ → ℂ} {r B : ℝ} (hr : 0 < r)
    (hf : DiffContOnCl ℂ f (ball 0 r))
    (hB : ∀ z ∈ sphere (0 : ℂ) r, ‖f z‖ ≤ B) (N : ℕ) :
    ‖iteratedDeriv (4 * N) f 0 / ((4 * N).factorial : ℂ)‖ ≤
      B / r ^ (4 * N) := by
  have hc := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le
    (4 * N) hr hf hB
  have hfac : (0 : ℝ) < (4 * N).factorial := by positivity
  rw [norm_div, Complex.norm_natCast]
  calc
    ‖iteratedDeriv (4 * N) f 0‖ / ((4 * N).factorial : ℝ)
        ≤ (((4 * N).factorial : ℝ) * B / r ^ (4 * N)) /
            ((4 * N).factorial : ℝ) := div_le_div_of_nonneg_right hc hfac.le
    _ = B / r ^ (4 * N) := by field_simp

/-- The remote perturbations converge uniformly back to `f` on every closed
disc of radius `r₀ < r₁`, provided `r₀ < 1`.  This is the analytic
empty-interior statement in the exact compact-open neighborhood form. -/
theorem eventually_remoteEvenPerturbation_uniformly_close
    {f : ℂ → ℂ} {r₀ r₁ B ε : ℝ}
    (hr₀ : 0 ≤ r₀) (hr₀1 : r₀ < 1) (hr01 : r₀ < r₁)
    (hf : DiffContOnCl ℂ f (ball 0 r₁))
    (hB : ∀ z ∈ sphere (0 : ℂ) r₁, ‖f z‖ ≤ B)
    (hB0 : 0 ≤ B) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ z ∈ closedBall (0 : ℂ) r₀,
      ‖remoteEvenPerturbation f N z - f z‖ < ε := by
  have hr₁ : 0 < r₁ := lt_of_le_of_lt hr₀ hr01
  let a : ℝ := r₀ / r₁
  have ha0 : 0 ≤ a := div_nonneg hr₀ hr₁.le
  have ha1 : a < 1 := (div_lt_one hr₁).2 hr01
  have ha4_0 : 0 ≤ a ^ 4 := pow_nonneg ha0 4
  have ha4_1 : a ^ 4 < 1 := pow_lt_one₀ ha0 ha1 (by omega)
  have hr04_0 : 0 ≤ r₀ ^ 4 := pow_nonneg hr₀ 4
  have hr04_1 : r₀ ^ 4 < 1 := pow_lt_one₀ hr₀ hr₀1 (by omega)
  have hta : Tendsto (fun N : ℕ => (a ^ 4) ^ N) atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one ha4_0 ha4_1
  have htr : Tendsto (fun N : ℕ => (r₀ ^ 4) ^ N) atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hr04_0 hr04_1
  have ht : Tendsto (fun N : ℕ => B * a ^ (4 * N) + r₀ ^ (4 * N))
      atTop (nhds 0) := by
    convert (hta.const_mul B).add htr using 1 <;> simp [pow_mul]
  have hevent : ∀ᶠ N : ℕ in atTop,
      B * a ^ (4 * N) + r₀ ^ (4 * N) < ε :=
    (tendsto_order.1 ht).2 ε hε
  obtain ⟨N, hN⟩ := hevent.exists
  refine ⟨N, fun z hz => ?_⟩
  have hznorm : ‖z‖ ≤ r₀ := by simpa [mem_closedBall, dist_zero_right] using hz
  have hfat : AnalyticAt ℂ f 0 :=
    (hf.differentiableOn.analyticOnNhd isOpen_ball) 0 (by simpa [mem_ball] using hr₁)
  have hcoef := norm_evenTaylorCoefficient_le hr₁ hf hB N
  have hreal : |analyticTraceMoments f (2 * N)| ≤ B / r₁ ^ (4 * N) := by
    calc
      |analyticTraceMoments f (2 * N)|
          ≤ ‖iteratedDeriv (4 * N) f 0 / ((4 * N).factorial : ℂ)‖ := by
            unfold analyticTraceMoments
            rw [show 2 * (2 * N) = 4 * N by omega]
            exact Complex.abs_re_le_norm _
      _ ≤ B / r₁ ^ (4 * N) := hcoef
  have hscalar : |analyticTraceMoments f (2 * N) + 1| ≤
      B / r₁ ^ (4 * N) + 1 := by
    calc
      |analyticTraceMoments f (2 * N) + 1|
          ≤ |analyticTraceMoments f (2 * N)| + |(1 : ℝ)| := abs_add_le _ _
      _ ≤ B / r₁ ^ (4 * N) + 1 := by norm_num; gcongr
  have hzpow : ‖z‖ ^ (4 * N) ≤ r₀ ^ (4 * N) :=
    pow_le_pow_left₀ (norm_nonneg z) hznorm _
  have hbound : ‖remoteEvenPerturbation f N z - f z‖ ≤
      B * a ^ (4 * N) + r₀ ^ (4 * N) := by
    rw [remoteEvenPerturbation]
    simp only [sub_sub_cancel_left, norm_neg, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      norm_pow]
    calc
      |analyticTraceMoments f (2 * N) + 1| * ‖z‖ ^ (4 * N)
          ≤ (B / r₁ ^ (4 * N) + 1) * r₀ ^ (4 * N) := by
            gcongr
      _ = B * a ^ (4 * N) + r₀ ^ (4 * N) := by
            dsimp [a]
            rw [div_pow]
            field_simp
  exact hbound.trans_lt hN

end RHTower
