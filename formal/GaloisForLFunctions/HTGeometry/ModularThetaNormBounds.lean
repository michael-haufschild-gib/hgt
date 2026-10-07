import GaloisForLFunctions.Bottcher.CuspLimits

/-!
# Uniform theta bounds above the modular fundamental-domain floor

The explicit lower bound for the normalized second theta constant controls
the reciprocal modular lambda at the cusp. No zero simplicity is used.
-/

open Complex Filter Topology

namespace Bottcher

private theorem exp_neg_pi_im_le_quarter {τ : ℂ} (hτ : (4 : ℝ) / 5 ≤ τ.im) :
    Real.exp (-Real.pi * τ.im) ≤ 1 / 4 := by
  have hπ : 3 < Real.pi := Real.pi_gt_three
  have hτ0 : 0 ≤ τ.im := by linarith
  have harg : 2 ≤ Real.pi * τ.im := by nlinarith
  have he1 : 2 ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have he2 : 4 ≤ Real.exp 2 := by
    have hm := mul_le_mul he1 he1 (by norm_num : (0 : ℝ) ≤ 2) (Real.exp_pos 1).le
    rw [← Real.exp_add] at hm
    norm_num at hm ⊢
    exact hm
  rw [neg_mul, Real.exp_neg,
    inv_le_comm₀ (Real.exp_pos _) (by norm_num : (0 : ℝ) < 1 / 4)]
  norm_num only [one_div, inv_inv]
  nlinarith [he2.trans (Real.exp_le_exp.mpr harg)]

private theorem theta_geometric_sum_le {r : ℝ} (hr0 : 0 ≤ r) (hr4 : r ≤ 1 / 4) :
    Summable (fun n : ℤ => r ^ n.natAbs) ∧
      (∑' n : ℤ, r ^ n.natAbs) ≤ 5 / 3 := by
  have hr1 : r < 1 := by linarith
  have hnat := summable_geometric_of_lt_one hr0 hr1
  have hs : Summable (fun n : ℤ => r ^ n.natAbs) := by
    rw [summable_int_iff_summable_nat_and_neg]
    exact ⟨by simpa using hnat, by simpa using hnat⟩
  refine ⟨hs, ?_⟩
  have heven : (fun n : ℤ => r ^ n.natAbs).Even := fun n => by simp
  rw [tsum_int_eq_zero_add_two_mul_tsum_pnat heven hs]
  have hp : (∑' n : ℕ+, r ^ ((n : ℤ)).natAbs) = r / (1 - r) := by
    simp only [Int.natAbs_natCast]
    rw [tsum_pnat_eq_tsum_succ (f := fun k => r ^ k),
      show (fun n : ℕ => r ^ (n + 1)) = (fun n => r * r ^ n) from
        by funext n; rw [pow_succ]; ring,
      tsum_mul_left, tsum_geometric_of_lt_one hr0 hr1, div_eq_mul_inv]
  rw [hp]
  norm_num only [Int.natAbs_zero, pow_zero, nsmul_eq_mul]
  have hfrac : r / (1 - r) ≤ 1 / 3 := by
    rw [div_le_iff₀ (by linarith : 0 < 1 - r)]
    linarith
  linarith

private theorem norm_jacobiTheta_sub_one_le_two_thirds {τ : ℂ}
    (hτ : (4 : ℝ) / 5 ≤ τ.im) : ‖jacobiTheta τ - 1‖ ≤ 2 / 3 := by
  have hτ0 : 0 < τ.im := by linarith
  have hr4 := exp_neg_pi_im_le_quarter hτ
  have hr0 := (Real.exp_pos (-Real.pi * τ.im)).le
  refine (norm_jacobiTheta_sub_one_le hτ0).trans ?_
  rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith : 0 < 1 - Real.exp (-Real.pi * τ.im))]
  linarith

/-- Uniform upper and lower bounds for theta three at the fundamental-domain floor. -/
theorem thetaThree_norm_bounds {τ : ℂ} (hτ : (4 : ℝ) / 5 ≤ τ.im) :
    1 / 3 ≤ ‖thetaThree τ‖ ∧ ‖thetaThree τ‖ ≤ 5 / 3 := by
  have heq : thetaThree τ = jacobiTheta τ := (jacobiTheta_eq_jacobiTheta₂ τ).symm
  rw [heq]
  have hb := norm_jacobiTheta_sub_one_le_two_thirds hτ
  have h1 := norm_sub_norm_le (1 : ℂ) (jacobiTheta τ)
  have h2 := norm_sub_norm_le (jacobiTheta τ) (1 : ℂ)
  rw [norm_sub_rev] at h1
  norm_num only [norm_one] at h1 h2
  constructor <;> linarith

/-- Theta four has the same bounds, by translating the theta-three argument. -/
theorem thetaFour_norm_bounds {τ : ℂ} (hτ : (4 : ℝ) / 5 ≤ τ.im) :
    1 / 3 ≤ ‖thetaFour τ‖ ∧ ‖thetaFour τ‖ ≤ 5 / 3 := by
  have hb := thetaThree_norm_bounds (τ := τ + 1) (by simpa using hτ)
  simpa only [thetaFour_eq, thetaThree, ← jacobiTheta_eq_jacobiTheta₂] using hb

/-- Removing the exponential cusp factor leaves theta two uniformly away from zero. -/
theorem thetaTwo_normalized_norm_bounds {τ : ℂ} (hτ : (4 : ℝ) / 5 ≤ τ.im) :
    1 / 3 ≤ ‖jacobiTheta₂ (τ / 2) τ‖ ∧ ‖jacobiTheta₂ (τ / 2) τ‖ ≤ 11 / 3 := by
  have hτ0 : 0 < τ.im := by linarith
  let r := Real.exp (-Real.pi * τ.im)
  obtain ⟨hgsum, hgbound⟩ := theta_geometric_sum_le
    (Real.exp_pos (-Real.pi * τ.im)).le (exp_neg_pi_im_le_quarter hτ)
  let f : ℤ → ℂ := fun n => jacobiTheta₂_term n (τ / 2) τ
  have hfsum : Summable f := (summable_jacobiTheta₂_term_iff (τ / 2) τ).mpr hτ0
  let c : ℤ → ℂ := fun n => if n = 0 ∨ n = -1 then 1 else 0
  have hcHS : HasSum c (∑ i ∈ ({0, -1} : Finset ℤ), c i) := by
    apply hasSum_sum_of_ne_finset_zero
    intro n hn
    dsimp [c]
    rw [if_neg]
    rintro (rfl | rfl) <;> simp at hn
  have hc_tsum : ∑' n, c n = 2 := by
    rw [hcHS.tsum_eq, Finset.sum_pair (show (0 : ℤ) ≠ -1 by norm_num)]
    norm_num [c]
  have hbound : ∀ n : ℤ, ‖f n - c n‖ ≤ r ^ n.natAbs := by
    intro n
    by_cases hn : n = 0 ∨ n = -1
    · rcases hn with rfl | rfl
      · simp [f, c, jacobiTheta₂_half_term_zero]
      · simp [f, c, jacobiTheta₂_half_term_negone]
        positivity
    · have hc0 : c n = 0 := if_neg hn
      rw [hc0, sub_zero]
      change ‖jacobiTheta₂_term n (τ / 2) τ‖ ≤ _
      rw [norm_jacobiTheta₂_half_term]
      have hcomp := sq_add_self_ge_abs n (fun he => hn (Or.inr he))
      have habs : (n.natAbs : ℝ) = |(n : ℝ)| := by
        rw [← Int.cast_natCast, Int.natCast_natAbs, Int.cast_abs]
      dsimp [r]
      rw [← Real.exp_nat_mul]
      apply Real.exp_le_exp.mpr
      nlinarith [mul_pos Real.pi_pos hτ0]
  have hfcsum : Summable (fun n => ‖f n - c n‖) :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) hbound hgsum
  have hkey : ‖jacobiTheta₂ (τ / 2) τ - 2‖ ≤ 5 / 3 := by
    have he : jacobiTheta₂ (τ / 2) τ - 2 = ∑' n, (f n - c n) := by
      rw [Summable.tsum_sub hfsum hcHS.summable, hc_tsum]
      rfl
    rw [he]
    exact (norm_tsum_le_tsum_norm hfcsum).trans
      ((Summable.tsum_mono hfcsum hgsum hbound).trans hgbound)
  have h1 := norm_sub_norm_le (2 : ℂ) (jacobiTheta₂ (τ / 2) τ)
  have h2 := norm_sub_norm_le (jacobiTheta₂ (τ / 2) τ) (2 : ℂ)
  rw [norm_sub_rev] at h1
  norm_num only [norm_ofNat] at h1 h2
  constructor <;> linarith

/-- The sole exponentially small theta constant has an explicit matching lower bound. -/
theorem thetaTwo_norm_bounds {τ : ℂ} (hτ : (4 : ℝ) / 5 ≤ τ.im) :
    Real.exp (-Real.pi * τ.im / 4) / 3 ≤ ‖thetaTwo τ‖ ∧
      ‖thetaTwo τ‖ ≤ (11 / 3) * Real.exp (-Real.pi * τ.im / 4) := by
  have hb := thetaTwo_normalized_norm_bounds hτ
  have he : ‖thetaTwo τ‖ = Real.exp (-Real.pi * τ.im / 4) *
      ‖jacobiTheta₂ (τ / 2) τ‖ := by
    rw [thetaTwo, norm_mul, Complex.norm_exp]
    congr 2
    simp [Complex.mul_im, Complex.mul_re]
  rw [he]
  constructor
  · have := mul_le_mul_of_nonneg_left hb.1 (Real.exp_pos (-Real.pi * τ.im / 4)).le
    linarith
  · have := mul_le_mul_of_nonneg_left hb.2 (Real.exp_pos (-Real.pi * τ.im / 4)).le
    linarith

end Bottcher
