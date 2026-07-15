import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Injectivity of absolutely convergent generalized Dirichlet series

This file supplies the analytic uniqueness theorem used by the ray-complete translation carrier.
The frequencies are a strictly increasing positive real sequence.  Absolute convergence at one
real point is enough: after absorbing that point into the coefficients, successive exponential
rescaling recovers every coefficient.
-/

open Complex Filter Topology

noncomputable section

namespace GaloisForLFunctions.RHTower

/-- A generalized Dirichlet series with real frequencies. -/
def generalizedDirichletSeries (mu : ℕ → ℝ) (a : ℕ → ℂ) (s : ℂ) : ℂ :=
  ∑' n : ℕ, a n * Complex.exp (-(mu n : ℂ) * s)

private lemma norm_generalizedDirichletTerm_real
    (mu : ℕ → ℝ) (a : ℕ → ℂ) (n : ℕ) (x : ℝ) :
    ‖a n * Complex.exp (-(mu n : ℂ) * (x : ℂ))‖ = ‖a n‖ * Real.exp (-mu n * x) := by
  rw [norm_mul, Complex.norm_exp]
  congr 1
  simp

/-- Absolute convergence at `sigma` gives a uniform exponential bound on every farther-right real
point, with rate equal to the smallest frequency. -/
theorem norm_generalizedDirichletSeries_real_le
    {mu : ℕ → ℝ} (hmu : Monotone mu) (hmu0 : 0 < mu 0)
    {a : ℕ → ℂ} {sigma x : ℝ}
    (ha : Summable fun n => ‖a n‖ * Real.exp (-mu n * sigma)) (hx : sigma ≤ x) :
    ‖generalizedDirichletSeries mu a x‖ ≤
      (∑' n, ‖a n‖ * Real.exp (-mu n * sigma)) *
        Real.exp (-mu 0 * (x - sigma)) := by
  let w : ℕ → ℝ := fun n => ‖a n‖ * Real.exp (-mu n * sigma)
  let decay : ℝ := Real.exp (-mu 0 * (x - sigma))
  have hmu_le (n : ℕ) : mu 0 ≤ mu n := hmu (Nat.zero_le n)
  have hdecay_nonneg : 0 ≤ decay := (Real.exp_pos _).le
  have hterm (n : ℕ) :
      ‖a n * Complex.exp (-(mu n : ℂ) * (x : ℂ))‖ ≤ w n * decay := by
    rw [norm_generalizedDirichletTerm_real]
    have hfac : Real.exp (-mu n * (x - sigma)) ≤ decay := by
      apply Real.exp_le_exp.mpr
      nlinarith [hmu_le n]
    have hsplit : Real.exp (-mu n * x) =
        Real.exp (-mu n * sigma) * Real.exp (-mu n * (x - sigma)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [hsplit]
    calc
      ‖a n‖ * (Real.exp (-mu n * sigma) * Real.exp (-mu n * (x - sigma))) =
          (‖a n‖ * Real.exp (-mu n * sigma)) * Real.exp (-mu n * (x - sigma)) := by ring
      _ ≤ (‖a n‖ * Real.exp (-mu n * sigma)) * decay :=
        mul_le_mul_of_nonneg_left hfac
          (mul_nonneg (norm_nonneg _) (Real.exp_pos _).le)
      _ = w n * decay := rfl
  have hnorm : Summable (fun n =>
      ‖a n * Complex.exp (-(mu n : ℂ) * (x : ℂ))‖) :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) hterm (ha.mul_right decay)
  calc
    ‖generalizedDirichletSeries mu a x‖ ≤
        ∑' n, ‖a n * Complex.exp (-(mu n : ℂ) * (x : ℂ))‖ := by
      exact norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' n, w n * decay :=
      hnorm.tsum_le_tsum hterm (ha.mul_right decay)
    _ = (∑' n, w n) * decay := tsum_mul_right

/-- Successive exponential rescaling recovers the first coefficient not already known to vanish.
This is the generalized-frequency analogue of `LSeries.tendsto_cpow_mul_atTop`. -/
theorem generalizedDirichletSeries_tendsto_scaled
    {mu : ℕ → ℝ} (hmu : StrictMono mu) (hmu0 : 0 < mu 0)
    {a : ℕ → ℂ} (ha : Summable fun n => ‖a n‖) {k : ℕ}
    (hzero : ∀ n < k, a n = 0) :
    Tendsto (fun x : ℝ => (Real.exp (mu k * x) : ℂ) *
      generalizedDirichletSeries mu a x) atTop (𝓝 (a k)) := by
  let F : ℝ → ℕ → ℂ := fun x n =>
    if k < n then a n * (Real.exp (-(mu n - mu k) * x) : ℂ) else 0
  have hmu_pos (n : ℕ) : 0 < mu n :=
    hmu0.trans_le (hmu.monotone (Nat.zero_le n))
  have hs (x : ℝ) (hx : 0 ≤ x) :
      Summable (fun n => a n * Complex.exp (-(mu n : ℂ) * (x : ℂ))) := by
    apply Summable.of_norm
    refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) ?_ ha
    intro n
    rw [norm_generalizedDirichletTerm_real]
    have hexp : Real.exp (-mu n * x) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by nlinarith [hmu_pos n])
    nlinarith [norm_nonneg (a n)]
  have hF_summable : Summable (fun n => ‖F 0 n‖) := by
    refine ha.indicator {n | k < n} |>.congr ?_
    intro n
    by_cases hn : k < n
    · simp [F, hn]
    · simp [F, hn]
  have hF_tendsto (n : ℕ) : Tendsto (fun x => F x n) atTop (𝓝 0) := by
    by_cases hn : k < n
    · have hgap : 0 < mu n - mu k := sub_pos.mpr (hmu hn)
      have hscalar : Tendsto (fun x : ℝ => Real.exp (-(mu n - mu k) * x)) atTop (𝓝 0) :=
        Real.tendsto_exp_atBot.comp
          (tendsto_id.const_mul_atTop_of_neg (neg_lt_zero.mpr hgap))
      simpa [F, hn] using hscalar.ofReal.const_mul (a n)
    · simp [F, hn]
  have hF_bound : ∀ᶠ x in atTop, ∀ n, ‖F x n‖ ≤ ‖F 0 n‖ := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx n
    by_cases hn : k < n
    · simp only [F, hn, if_true, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        mul_zero, Real.exp_zero, abs_one]
      rw [abs_of_pos (Real.exp_pos _)]
      have hgap : 0 < mu n - mu k := sub_pos.mpr (hmu hn)
      have hexp : Real.exp (-(mu n - mu k) * x) ≤ 1 :=
        Real.exp_le_one_iff.mpr (by nlinarith)
      exact mul_le_mul_of_nonneg_left hexp (norm_nonneg _)
    · simp [F, hn]
  have htail : Tendsto (fun x => ∑' n, F x n) atTop (𝓝 0) := by
    rw [show (0 : ℂ) = ∑' _ : ℕ, (0 : ℂ) from tsum_zero.symm]
    exact tendsto_tsum_of_dominated_convergence hF_summable hF_tendsto hF_bound
  have hidentity : ∀ᶠ x in atTop,
      (Real.exp (mu k * x) : ℂ) * generalizedDirichletSeries mu a x =
        a k + ∑' n, F x n := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
    rw [generalizedDirichletSeries, ← tsum_mul_left]
    have hsx := hs x hx
    have hscaled : Summable (fun n => (Real.exp (mu k * x) : ℂ) *
        (a n * Complex.exp (-(mu n : ℂ) * (x : ℂ)))) := hsx.mul_left _
    rw [hscaled.tsum_eq_add_tsum_ite k]
    have hmain : (Real.exp (mu k * x) : ℂ) *
        (a k * Complex.exp (-(mu k : ℂ) * (x : ℂ))) = a k := by
      rw [Complex.ofReal_exp]
      push_cast
      calc
        Complex.exp (mu k * x) *
            (a k * Complex.exp (-(mu k : ℂ) * (x : ℂ))) =
            a k * (Complex.exp (mu k * x) *
              Complex.exp (-(mu k : ℂ) * (x : ℂ))) := by ring
        _ = a k := by rw [← Complex.exp_add]; simp
    rw [hmain]
    congr 1
    apply tsum_congr
    intro n
    by_cases hnk : n = k
    · subst n
      simp [F]
    by_cases hlt : n < k
    · have hnot : ¬ k < n := not_lt_of_ge (Nat.le_of_lt hlt)
      simp [F, hnk, hnot, hzero n hlt]
    · have hkn : k < n := lt_of_le_of_ne (Nat.le_of_not_gt hlt) (Ne.symm hnk)
      simp only [if_neg hnk, F, hkn, if_true]
      simp only [Complex.ofReal_exp]
      push_cast
      calc
        Complex.exp (mu k * x) *
            (a n * Complex.exp (-(mu n : ℂ) * (x : ℂ))) =
            a n * (Complex.exp (mu k * x) *
              Complex.exp (-(mu n : ℂ) * (x : ℂ))) := by ring
        _ = a n * Complex.exp (-(mu n - mu k) * x) := by
          rw [← Complex.exp_add]
          congr 1
          push_cast
          ring
  have hadd : Tendsto (fun x => a k + ∑' n, F x n) atTop (𝓝 (a k + 0)) :=
    tendsto_const_nhds.add htail
  simpa using Tendsto.congr' (EventuallyEq.symm hidentity) hadd

/-- An absolutely convergent generalized Dirichlet series with strictly increasing positive
frequencies determines every coefficient from its values on a far-right real ray. -/
theorem generalizedDirichletSeries_coeff_eq_zero_of_eventuallyEq_zero
    {mu : ℕ → ℝ} (hmu : StrictMono mu) (hmu0 : 0 < mu 0)
    {a : ℕ → ℂ} (ha : Summable fun n => ‖a n‖)
    (hzero : (fun x : ℝ => generalizedDirichletSeries mu a x) =ᶠ[atTop] 0) :
    ∀ n, a n = 0 := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
      have hscaledZero :
          (fun x : ℝ => (Real.exp (mu n * x) : ℂ) *
            generalizedDirichletSeries mu a x) =ᶠ[atTop] 0 := by
        filter_upwards [hzero] with x hx
        simp [hx]
      have ht := generalizedDirichletSeries_tendsto_scaled hmu hmu0 ha
        (k := n) (fun m hm => ih m hm)
      have ht0 : Tendsto (fun _ : ℝ => (0 : ℂ)) atTop (𝓝 (a n)) :=
        ht.congr' hscaledZero
      have hz : (0 : ℂ) = a n := by
        simpa only [tendsto_const_nhds_iff] using ht0
      exact hz.symm

/-- Shift the absolute-convergence line into the coefficients. -/
theorem generalizedDirichletSeries_coeff_eq_zero_of_absolutelySummable_at
    {mu : ℕ → ℝ} (hmu : StrictMono mu) (hmu0 : 0 < mu 0)
    {a : ℕ → ℂ} {sigma : ℝ}
    (ha : Summable fun n => ‖a n‖ * Real.exp (-mu n * sigma))
    (hzero : (fun x : ℝ => generalizedDirichletSeries mu a x) =ᶠ[atTop] 0) :
    ∀ n, a n = 0 := by
  let b : ℕ → ℂ := fun n => a n * Complex.exp (-(mu n : ℂ) * (sigma : ℂ))
  have hb : Summable fun n => ‖b n‖ := by
    simpa [b, norm_mul, Complex.norm_exp] using ha
  have hshift : ∀ y : ℝ,
      generalizedDirichletSeries mu b y = generalizedDirichletSeries mu a (y + sigma) := by
    intro y
    apply tsum_congr
    intro n
    simp only [b]
    rw [mul_assoc, ← Complex.exp_add]
    congr 1
    ring
  have hzeroB : (fun y : ℝ => generalizedDirichletSeries mu b y) =ᶠ[atTop] 0 := by
    have hcomp := hzero.comp_tendsto (tendsto_atTop_add_const_right atTop sigma tendsto_id)
    filter_upwards [hcomp] with y hy
    rw [hshift]
    simpa using hy
  have hbzero := generalizedDirichletSeries_coeff_eq_zero_of_eventuallyEq_zero hmu hmu0 hb hzeroB
  intro n
  have := hbzero n
  exact (mul_eq_zero.mp this).resolve_right (Complex.exp_ne_zero _)

end GaloisForLFunctions.RHTower
