import GaloisForLFunctions.HTGeometry.CanonicalProductGrowth
import GaloisForLFunctions.HTGeometry.InfiniteProductNearOne

/-!
# Real-line bounds for genus-one products with real zeros

For a square-summable family of nonzero points `a_i` let `P(z) = ∏ (1 - z/a_i) e^{z/a_i}` and
`S = ∑ 1/|a_i|²`.

* On the real line, if every `a_i` is real, `|P(s)| ≤ e^{S s²/2}`. The factor bound is
  `|1 - w| e^{w} ≤ e^{w²/2}` for real `w`, from `log x ≤ x - 1`; it is an equality at `w = 2`.
* Near the origin, `|P(z) - 1| ≤ e^{S |z|²} - 1` whenever `|z| ≤ |a_i|` for every `i`, from
  `|E₁(w) - 1| ≤ |w|²` on the unit disc.
-/

open Complex Filter Topology

namespace RHTower

/-- `|(1 - w) e^{w}| ≤ e^{w²/2}` for real `w`. -/
theorem norm_weierstrassE1_ofReal_le (w : ℝ) :
    ‖weierstrassE1 (w : ℂ)‖ ≤ Real.exp (w ^ 2 / 2) := by
  rw [weierstrassE1, norm_mul, Complex.norm_exp, ofReal_re]
  have h1 : ‖(1 : ℂ) - (w : ℂ)‖ = |1 - w| := by
    rw [← ofReal_one, ← ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  rw [h1]
  by_cases hw : w = 1
  · subst hw
    simp only [sub_self, abs_zero, zero_mul]
    positivity
  · have hpos : 0 < |1 - w| := abs_pos.mpr (sub_ne_zero.mpr (Ne.symm hw))
    have hlog := Real.log_le_sub_one_of_pos hpos
    rw [← Real.exp_log hpos, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    rcases lt_or_gt_of_ne hw with h | h
    · rw [abs_of_pos (by linarith)] at hlog ⊢
      nlinarith [sq_nonneg w]
    · rw [abs_of_neg (by linarith)] at hlog ⊢
      nlinarith [sq_nonneg (w - 2)]

/-- **The real-line bound.** If every zero is real, `|P(s)| ≤ e^{S s²/2}` for real `s`. -/
theorem norm_canonicalProductE1Indexed_ofReal_le {ι : Type*} (a : ι → ℂ) (ha : ∀ i, a i ≠ 0)
    (hsum : Summable fun i => 1 / ‖a i‖ ^ (2 : ℕ)) (hreal : ∀ i, (a i).im = 0) (s : ℝ) :
    ‖canonicalProductE1Indexed a (s : ℂ)‖ ≤
      Real.exp (s ^ 2 / 2 * ∑' i, 1 / ‖a i‖ ^ (2 : ℕ)) := by
  set u : ι → ℝ := fun i => s ^ 2 / 2 * (1 / ‖a i‖ ^ (2 : ℕ)) with hu
  have husum : Summable u := hsum.mul_left _
  have hdsum : Summable (fun i => weierstrassE1 ((s : ℂ) / a i) - 1) :=
    (canonicalProductE1Indexed_sub_one_norm_summable a ha hsum (s : ℂ)).of_norm
  have hfac : Multipliable (fun i => weierstrassE1 ((s : ℂ) / a i)) := by
    have hm := Complex.multipliable_one_add_of_summable hdsum
    convert hm using 1
    ext i
    ring
  have hexpsum : Summable (fun i => Real.log (Real.exp (u i))) := by simpa using husum
  have hexpmult : Multipliable (fun i => Real.exp (u i)) :=
    Real.multipliable_of_summable_log (fun i => Real.exp_pos _) hexpsum
  have hfactor : ∀ i, ‖weierstrassE1 ((s : ℂ) / a i)‖ ≤ Real.exp (u i) := by
    intro i
    obtain ⟨r, hr⟩ : ∃ r : ℝ, a i = (r : ℂ) :=
      ⟨(a i).re, by apply Complex.ext <;> simp [hreal i]⟩
    have hr0 : r ≠ 0 := by
      intro h; apply ha i; rw [hr, h, ofReal_zero]
    have hw : (s : ℂ) / a i = ((s / r : ℝ) : ℂ) := by rw [hr]; push_cast; ring
    rw [hw]
    refine (norm_weierstrassE1_ofReal_le _).trans (Real.exp_le_exp.mpr (le_of_eq ?_))
    rw [hu]
    simp only
    rw [hr, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    field_simp
  rw [canonicalProductE1Indexed, hfac.norm_tprod]
  calc (∏' i, ‖weierstrassE1 ((s : ℂ) / a i)‖) ≤ ∏' i, Real.exp (u i) := by
        apply le_of_tendsto_of_tendsto' hfac.norm.hasProd hexpmult.hasProd
        intro t
        exact Finset.prod_le_prod (fun i _ => norm_nonneg _) (fun i _ => hfactor i)
    _ = Real.exp (∑' i, u i) := by
        simpa only [Real.log_exp] using
          (Real.rexp_tsum_eq_tprod (fun i => Real.exp_pos _) hexpsum).symm
    _ = Real.exp (s ^ 2 / 2 * ∑' i, 1 / ‖a i‖ ^ (2 : ℕ)) := by rw [hu, tsum_mul_left]

/-- **Near the origin the product stays near one.** If `|z| ≤ |a_i|` for every `i`, then
`|P(z) - 1| ≤ e^{S|z|²} - 1`. -/
theorem norm_canonicalProductE1Indexed_sub_one_le {ι : Type*} (a : ι → ℂ) (ha : ∀ i, a i ≠ 0)
    (hsum : Summable fun i => 1 / ‖a i‖ ^ (2 : ℕ)) {z : ℂ} (hz : ∀ i, ‖z‖ ≤ ‖a i‖) :
    ‖canonicalProductE1Indexed a z - 1‖ ≤
      Real.exp (‖z‖ ^ 2 * ∑' i, 1 / ‖a i‖ ^ (2 : ℕ)) - 1 := by
  set v : ι → ℂ := fun i => weierstrassE1 (z / a i) - 1 with hv
  have hvle : ∀ i, ‖v i‖ ≤ ‖z‖ ^ 2 * (1 / ‖a i‖ ^ (2 : ℕ)) := by
    intro i
    have hpos : 0 < ‖a i‖ := norm_pos_iff.mpr (ha i)
    have h1 : ‖z / a i‖ ≤ 1 := by
      rw [norm_div, div_le_one hpos]
      exact hz i
    have h2 := weierstrassE1_sub_one_norm_le h1
    rw [norm_div, div_pow] at h2
    rw [hv]
    calc ‖weierstrassE1 (z / a i) - 1‖ ≤ ‖z‖ ^ (2 : ℕ) / ‖a i‖ ^ (2 : ℕ) := h2
      _ = ‖z‖ ^ 2 * (1 / ‖a i‖ ^ (2 : ℕ)) := by ring
  have hvsum : Summable fun i => ‖v i‖ :=
    (hsum.mul_left _).of_nonneg_of_le (fun _ => norm_nonneg _) hvle
  have hfac : HasProd (fun i => 1 + v i) (canonicalProductE1Indexed a z) := by
    have hm : Multipliable (fun i => 1 + v i) :=
      Complex.multipliable_one_add_of_summable hvsum.of_norm
    have heq : (fun i => 1 + v i) = fun i => weierstrassE1 (z / a i) := by
      funext i
      simp [hv]
    rw [canonicalProductE1Indexed, ← heq]
    exact hm.hasProd
  refine GaloisForLFunctions.HTGeometry.norm_tprod_one_add_sub_one_le hfac hvsum ?_
  rw [← tsum_mul_left]
  exact Summable.tsum_le_tsum hvle hvsum (hsum.mul_left _)

end RHTower
