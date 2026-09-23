import GaloisForLFunctions.RHTower.ZetaVerticalGrowth

/-!
# Growth of ζ′ near the one-line

`|ζ′(σ+it)| ≤ 112·log²|t|` for `|t| ≥ 9` and
`1 − 1/(4·log|t|) ≤ σ ≤ 3/2`: the Cauchy estimate on the disc of radius
`1/(4·log|t|)`, whose points stay inside the vertical-growth region
(`log|Im| ≤ 2·log|t|` there, so the sphere bound is `28·log|t|`).
-/

noncomputable section

namespace RHTower

open Set Metric

set_option maxHeartbeats 1600000 in
/-- **Growth bound for ζ′**: `|ζ′(σ+it)| ≤ 112·log²|t|` for `|t| ≥ 9`,
`1 − 1/(4 log|t|) ≤ σ ≤ 3/2`. -/
theorem abs_deriv_riemannZeta_le_sq_log {σ t : ℝ} (ht : 9 ≤ |t|)
    (hσ1 : 1 - 1 / (4 * Real.log |t|) ≤ σ) (hσ2 : σ ≤ 3 / 2) :
    ‖deriv riemannZeta (↑σ + ↑t * Complex.I)‖
      ≤ 112 * Real.log |t| ^ (2 : ℕ) := by
  have ht0 : (0 : ℝ) < |t| := by linarith
  have ht1 : (1 : ℝ) ≤ |t| := by linarith
  -- `log|t| > 2` as in the growth bound
  have hexp2 := exp_two_lt_eight
  have hlogt2 : 2 < Real.log |t| := by
    have h1 : Real.log (Real.exp 2) < Real.log |t| :=
      Real.log_lt_log (Real.exp_pos 2) (by linarith)
    rwa [Real.log_exp] at h1
  have hL0 : (0 : ℝ) < Real.log |t| := by linarith
  have hr0 : (0 : ℝ) < 1 / (4 * Real.log |t|) := by positivity
  have hr8 : 1 / (4 * Real.log |t|) ≤ 1 / 8 := by
    apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
    linarith
  -- facts about points of the closed disc
  have hdisc : ∀ w : ℂ,
      w ∈ closedBall (↑σ + ↑t * Complex.I) (1 / (4 * Real.log |t|)) →
      8 ≤ |w.im| ∧ 1 - 1 / Real.log |w.im| ≤ w.re ∧ w.re ≤ 2
        ∧ Real.log |w.im| ≤ 2 * Real.log |t| := by
    intro w hw
    rw [mem_closedBall, dist_eq_norm] at hw
    have hre : (↑σ + ↑t * Complex.I).re = σ := by
      simp [Complex.add_re, Complex.mul_re]
    have him : (↑σ + ↑t * Complex.I).im = t := by
      simp [Complex.add_im, Complex.mul_im]
    have hwre : |w.re - σ| ≤ 1 / (4 * Real.log |t|) := by
      have h1 := Complex.abs_re_le_norm (w - (↑σ + ↑t * Complex.I))
      rw [Complex.sub_re, hre] at h1
      linarith
    have hwim : |w.im - t| ≤ 1 / (4 * Real.log |t|) := by
      have h1 := Complex.abs_im_le_norm (w - (↑σ + ↑t * Complex.I))
      rw [Complex.sub_im, him] at h1
      linarith
    have hwre' := abs_le.1 hwre
    have hwim' := abs_le.1 hwim
    -- `|w.im| ∈ [|t| − 1/8, |t| + 1/8]`
    have habs1 : |t| - 1 / 8 ≤ |w.im| := by
      have h1 : |t| - |w.im| ≤ |t - w.im| := by
        calc |t| - |w.im| ≤ |(|t| - |w.im|)| := le_abs_self _
          _ ≤ |t - w.im| := abs_abs_sub_abs_le_abs_sub _ _
      have h2 : |t - w.im| ≤ 1 / (4 * Real.log |t|) := by
        rw [abs_sub_comm]
        exact hwim
      linarith [hr8]
    have habs2 : |w.im| ≤ |t| + 1 / 8 := by
      have h1 : |w.im| - |t| ≤ |w.im - t| := by
        calc |w.im| - |t| ≤ |(|w.im| - |t|)| := le_abs_self _
          _ ≤ |w.im - t| := abs_abs_sub_abs_le_abs_sub _ _
      linarith [hr8, hwim]
    have h8 : (8 : ℝ) ≤ |w.im| := by linarith
    have hwim0 : (0 : ℝ) < |w.im| := by linarith
    -- `log|w.im| ≤ 2 log|t|` since `|w.im| ≤ |t|²`
    have hsq : |w.im| ≤ |t| ^ (2 : ℕ) := by
      nlinarith
    have hlog2L : Real.log |w.im| ≤ 2 * Real.log |t| := by
      have h1 : Real.log |w.im| ≤ Real.log (|t| ^ (2 : ℕ)) :=
        Real.log_le_log hwim0 hsq
      rwa [Real.log_pow, Nat.cast_ofNat] at h1
    have hlogw0 : (0 : ℝ) < Real.log |w.im| := by
      have h1 : Real.log 8 ≤ Real.log |w.im| :=
        Real.log_le_log (by norm_num) h8
      have h2 : (0 : ℝ) < Real.log 8 :=
        Real.log_pos (by norm_num)
      linarith
    refine ⟨h8, ?_, by linarith [hwre'.2], hlog2L⟩
    -- `1 − 1/log|w.im| ≤ w.re`
    have h1 : 1 / (2 * Real.log |t|) ≤ 1 / Real.log |w.im| := by
      apply div_le_div_of_nonneg_left (by norm_num) hlogw0 hlog2L
    have h2 : σ - 1 / (4 * Real.log |t|) ≤ w.re := by linarith [hwre'.1]
    have h3 : 1 - 1 / (2 * Real.log |t|)
        ≤ σ - 1 / (4 * Real.log |t|) := by
      have : 1 / (2 * Real.log |t|) = 1 / (4 * Real.log |t|)
          + 1 / (4 * Real.log |t|) := by
        field_simp
        ring
      linarith
    linarith
  -- differentiability on the closed disc
  have hdiff : DiffContOnCl ℂ riemannZeta
      (ball (↑σ + ↑t * Complex.I) (1 / (4 * Real.log |t|))) := by
    apply DifferentiableOn.diffContOnCl
    rw [closure_ball _ (ne_of_gt hr0)]
    intro w hw
    obtain ⟨h8, _, _, _⟩ := hdisc w hw
    have hne1 : w ≠ 1 := by
      intro h
      rw [h] at h8
      simp at h8
      linarith
    exact (differentiableAt_riemannZeta hne1).differentiableWithinAt
  -- the sphere bound
  have hsphere : ∀ w ∈ sphere (↑σ + ↑t * Complex.I)
      (1 / (4 * Real.log |t|)),
      ‖riemannZeta w‖ ≤ 28 * Real.log |t| := by
    intro w hw
    obtain ⟨h8, hσ1', hσ2', hlog2L⟩ :=
      hdisc w (sphere_subset_closedBall hw)
    have h1 : ‖riemannZeta (↑w.re + ↑w.im * Complex.I)‖
        ≤ 14 * Real.log |w.im| :=
      abs_riemannZeta_le_log h8 hσ1' hσ2'
    rw [Complex.re_add_im] at h1
    linarith
  -- Cauchy's estimate at order one
  have hcauchy := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le
    1 hr0 hdiff hsphere
  rw [iteratedDeriv_one] at hcauchy
  refine le_trans hcauchy ?_
  simp only [Nat.factorial_one, Nat.cast_one, pow_one, one_mul]
  have hid : 28 * Real.log |t| / (1 / (4 * Real.log |t|))
      = 112 * Real.log |t| ^ (2 : ℕ) := by
    field_simp
    ring
  linarith [hid]

end RHTower
