import GaloisForLFunctions.HTGeometry.MaximumTermCentralIndex

/-!
# Super-Gaussian coefficient decay makes the central index sublogarithmic

An entire function whose Taylor coefficients satisfy `‖a n‖ ≤ M·exp(−A n²)` has central index at
most `2 log r / A` at every large radius: the central term would otherwise be smaller than a fixed
nonzero term.  If such an estimate holds for *every* `A > 0` — which is exactly what entireness of a
one-sided periodic heat orbit at every complex backward time gives — the central index is
`o(log r)`.

This is the growth half of the entire-heat differential-order floor: a multiplicative Fourier anchor
of an everywhere-entire heat orbit has a central index far below the logarithm, hence maximum
modulus `exp(o((log r)²))`.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter

variable {a : ℕ → ℂ}

/-- A Gaussian coefficient bound has a positive constant as soon as one coefficient is nonzero. -/
theorem pos_of_gaussian_decay {A M : ℝ}
    (hM : ∀ n : ℕ, ‖a n‖ ≤ M * Real.exp (-A * (n : ℝ) ^ 2)) {n₀ : ℕ} (hn₀ : a n₀ ≠ 0) : 0 < M := by
  by_contra hcon
  push Not at hcon
  have h2 : M * Real.exp (-A * (n₀ : ℝ) ^ 2) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg hcon (Real.exp_pos _).le
  exact hn₀ (norm_eq_zero.mp (le_antisymm (le_trans (hM n₀) h2) (norm_nonneg _)))

/-- **Gaussian coefficient decay bounds the central index**, at every radius past the threshold
where the Gaussian factor has fallen below the size of one nonzero coefficient. -/
theorem centralIndex_le_of_gaussian_decay_of_lt (ha : EntireCoeffs a)
    {A M : ℝ} (hA : 0 < A) (hM : ∀ n : ℕ, ‖a n‖ ≤ M * Real.exp (-A * (n : ℝ) ^ 2))
    {n₀ : ℕ} (hn₀ : a n₀ ≠ 0) {r : ℝ} (hr : 1 < r)
    (hthr : M * Real.exp (-(2 * (Real.log r) ^ 2 / A)) < ‖a n₀‖) :
    (centralIndex a r : ℝ) ≤ 2 * Real.log r / A := by
  set L : ℝ := Real.log r with hLdef
  have hL : 0 < L := Real.log_pos hr
  have hr0 : 0 < r := lt_trans one_pos hr
  set ν : ℕ := centralIndex a r with hνdef
  by_contra hcon
  push Not at hcon
  -- `ν` attains the maximum term, so it dominates the `n₀` term
  have hattain : ‖a ν‖ * r ^ ν = maxTerm a r := term_centralIndex_eq ha hr0 hn₀
  have hdom : ‖a n₀‖ * r ^ n₀ ≤ ‖a ν‖ * r ^ ν := by
    rw [hattain]; exact term_le_maxTerm ha hr0 n₀
  -- rewrite the powers as exponentials
  have hpow : ∀ n : ℕ, r ^ n = Real.exp ((n : ℝ) * L) := by
    intro n
    rw [hLdef, ← Real.log_pow, Real.exp_log (pow_pos hr0 n)]
  -- the Gaussian bound on the central coefficient
  have hgauss : ‖a ν‖ * r ^ ν ≤ M * Real.exp (-A * (ν : ℝ) ^ 2 + (ν : ℝ) * L) := by
    rw [hpow ν, Real.exp_add, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right (hM ν) (Real.exp_pos _).le
  -- the exponent is very negative
  have hνge : 2 * L / A ≤ (ν : ℝ) := hcon.le
  have hνnn : (0 : ℝ) ≤ (ν : ℝ) := Nat.cast_nonneg ν
  have hkey : -A * (ν : ℝ) ^ 2 + (ν : ℝ) * L ≤ -(2 * L ^ 2 / A) := by
    have h1 : 2 * L ≤ A * (ν : ℝ) := by
      rw [div_le_iff₀ hA] at hνge
      linarith
    have h2 : -A * (ν : ℝ) ^ 2 + (ν : ℝ) * L = (ν : ℝ) * (L - A * (ν : ℝ)) := by ring
    have h3 : L - A * (ν : ℝ) ≤ -L := by linarith
    have h4 : (ν : ℝ) * (L - A * (ν : ℝ)) ≤ (ν : ℝ) * (-L) :=
      mul_le_mul_of_nonneg_left h3 hνnn
    have h6 : (ν : ℝ) * (-L) ≤ (2 * L / A) * (-L) := by
      have hneg : (-L) ≤ 0 := by linarith
      exact mul_le_mul_of_nonpos_right hνge hneg
    have h7 : (2 * L / A) * (-L) = -(2 * L ^ 2 / A) := by field_simp
    rw [h2]
    linarith [h4, h6, h7.le, h7.ge]
  -- combine
  have hfinal : ‖a n₀‖ * r ^ n₀ ≤ M * Real.exp (-(2 * L ^ 2 / A)) := by
    refine le_trans hdom (le_trans hgauss ?_)
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hkey) (le_of_lt (pos_of_gaussian_decay hM hn₀))
  have hone : (1 : ℝ) ≤ r ^ n₀ := one_le_pow₀ hr.le
  have : ‖a n₀‖ ≤ M * Real.exp (-(2 * L ^ 2 / A)) := by
    refine le_trans ?_ hfinal
    nlinarith [norm_nonneg (a n₀)]
  exact absurd this (not_le.mpr hthr)

/-- The Gaussian threshold is met at every large radius. -/
theorem eventually_gaussian_threshold {A M : ℝ} (hA : 0 < A) {n₀ : ℕ} (hn₀ : a n₀ ≠ 0) :
    ∀ᶠ r : ℝ in atTop, M * Real.exp (-(2 * (Real.log r) ^ 2 / A)) < ‖a n₀‖ := by
  have hlog : Tendsto Real.log atTop atTop := Real.tendsto_log_atTop
  have hsq : Tendsto (fun r : ℝ => (Real.log r) ^ 2) atTop atTop :=
    (tendsto_pow_atTop (two_ne_zero)).comp hlog
  have hdiv : Tendsto (fun r : ℝ => 2 * (Real.log r) ^ 2 / A) atTop atTop :=
    Filter.Tendsto.atTop_div_const hA (hsq.const_mul_atTop (by norm_num : (0:ℝ) < 2))
  have hneg : Tendsto (fun r : ℝ => -(2 * (Real.log r) ^ 2 / A)) atTop atBot :=
    tendsto_neg_atTop_atBot.comp hdiv
  have hexp : Tendsto (fun r : ℝ => Real.exp (-(2 * (Real.log r) ^ 2 / A))) atTop (nhds 0) :=
    Real.tendsto_exp_atBot.comp hneg
  have hmul : Tendsto (fun r : ℝ => M * Real.exp (-(2 * (Real.log r) ^ 2 / A))) atTop (nhds 0) := by
    simpa using hexp.const_mul M
  exact hmul.eventually_lt_const (norm_pos_iff.mpr hn₀)

/-- **Gaussian coefficient decay bounds the central index at every large radius.** -/
theorem eventually_centralIndex_le_of_gaussian_decay (ha : EntireCoeffs a)
    {A M : ℝ} (hA : 0 < A) (hM : ∀ n : ℕ, ‖a n‖ ≤ M * Real.exp (-A * (n : ℝ) ^ 2))
    {n₀ : ℕ} (hn₀ : a n₀ ≠ 0) :
    ∀ᶠ r : ℝ in atTop, (centralIndex a r : ℝ) ≤ 2 * Real.log r / A := by
  filter_upwards [eventually_gt_atTop (1 : ℝ),
    eventually_gaussian_threshold (a := a) (A := A) (M := M) hA hn₀] with r hr hthr
  exact centralIndex_le_of_gaussian_decay_of_lt ha hA hM hn₀ hr hthr

/-- **Super-Gaussian coefficient decay makes the central index `o(log r)`.** -/
theorem tendsto_centralIndex_div_log_zero (ha : EntireCoeffs a)
    (hdecay : ∀ A : ℝ, 0 < A → ∃ M : ℝ, ∀ n : ℕ, ‖a n‖ ≤ M * Real.exp (-A * (n : ℝ) ^ 2))
    {n₀ : ℕ} (hn₀ : a n₀ ≠ 0) :
    Tendsto (fun r : ℝ => (centralIndex a r : ℝ) / Real.log r) atTop (nhds 0) := by
  refine NormedAddGroup.tendsto_nhds_zero.mpr fun ε hε => ?_
  obtain ⟨M, hM⟩ := hdecay (4 / ε) (by positivity)
  filter_upwards [eventually_gt_atTop (1 : ℝ),
    eventually_centralIndex_le_of_gaussian_decay ha (A := 4 / ε) (M := M) (by positivity) hM hn₀]
    with r hr hν
  have hL : 0 < Real.log r := Real.log_pos hr
  have hnn : (0 : ℝ) ≤ (centralIndex a r : ℝ) / Real.log r :=
    div_nonneg (Nat.cast_nonneg _) hL.le
  rw [Real.norm_eq_abs, abs_of_nonneg hnn, div_lt_iff₀ hL]
  have h2 : 2 * Real.log r / (4 / ε) = ε / 2 * Real.log r := by
    field_simp
    ring
  calc (centralIndex a r : ℝ) ≤ 2 * Real.log r / (4 / ε) := hν
    _ = ε / 2 * Real.log r := h2
    _ < ε * Real.log r := by nlinarith

end GaloisForLFunctions.HTGeometry
