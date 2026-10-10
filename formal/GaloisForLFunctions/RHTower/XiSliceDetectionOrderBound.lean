import GaloisForLFunctions.RHTower.XiHorizontalSliceTaylorPositivity

/-!
# The order at which a slice detects an off-line zero

At the ordinate `γ` of a zero `ρ` of `ξ` with displacement `δ = |Re ρ − ½|`, the slice product
`g_γ(x) = ξ(½+x+iγ) ξ(½−x+iγ)` vanishes at the real point `x = δ` (`xiSliceProduct_abs_eq_zero`).
If its first `N` Taylor coefficients were nonnegative, the value `g_γ(δ) = 0` would have to come
from the tail `Σ_{n ≥ N} c_n δ^n`.  By Cauchy's estimate the tail is at most
`M (δ/R)^N/(1 − δ/R)` for any `R > δ`, where `M` bounds `|g_γ|` on `|x| = R`.

**Theorem** (`exists_re_xiSliceCoeff_neg_of_tail_lt`).  If `M (δ/R)^N/(1 − δ/R) < c_0(γ)`, then
some coefficient `c_n(γ)` with `n < N` has negative real part.

So a zero at displacement `δ` is seen by the slice at its own ordinate at order
`N ≈ log(M(R)/c_0(γ))/log(R/δ)`.  The closer the zero is to the critical line, the lower the order.
The cone and near-double laws (`XiSliceCoeffNearDoublePositivity`) give the opposite bound:
orders below the critical shadowing depth stay positive.  The two bounds bracket the detection
order of an off-line zero.
-/

open Complex Metric

namespace RHTower

noncomputable section

/-- **Cauchy's estimate for the slice coefficients.** -/
theorem norm_xiSliceCoeff_le {t R M : ℝ} (hR : 0 < R)
    (hM : ∀ x ∈ sphere (0 : ℂ) R, ‖xiSliceProduct t x‖ ≤ M) (n : ℕ) :
    ‖xiSliceCoeff t n‖ ≤ M / R ^ n := by
  have hd := differentiable_xiSliceProduct t
  have hdiff : DiffContOnCl ℂ (xiSliceProduct t) (ball 0 R) := hd.diffContOnCl
  have h := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n hR hdiff hM
  have hfac : (0 : ℝ) < (n.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos n
  unfold xiSliceCoeff
  rw [norm_mul, norm_inv, Complex.norm_natCast]
  calc ((n.factorial : ℝ))⁻¹ * ‖iteratedDeriv n (xiSliceProduct t) 0‖
      ≤ ((n.factorial : ℝ))⁻¹ * ((n.factorial : ℝ) * M / R ^ n) :=
        mul_le_mul_of_nonneg_left h (inv_nonneg.mpr hfac.le)
    _ = M / R ^ n := by field_simp

/-- **Detection order of an off-line zero.**  Let `ρ` be a zero of `ξ`, `δ = |Re ρ − ½|`, and
`R > δ` with `|g_γ| ≤ M` on `|x| = R`, `γ = Im ρ`.  If `M (δ/R)^N/(1 − δ/R) < Re c_0(γ)`, then
some slice coefficient `c_n(γ)`, `n < N`, has negative real part. -/
theorem exists_re_xiSliceCoeff_neg_of_tail_lt {ρ : ℂ} (hρ : xi ρ = 0) {R M : ℝ}
    (hR : |ρ.re - 1 / 2| < R) (hM : ∀ x ∈ sphere (0 : ℂ) R, ‖xiSliceProduct ρ.im x‖ ≤ M)
    {N : ℕ} (hN : M * (|ρ.re - 1 / 2| / R) ^ N / (1 - |ρ.re - 1 / 2| / R) <
      (xiSliceCoeff ρ.im 0).re) :
    ∃ n < N, (xiSliceCoeff ρ.im n).re < 0 := by
  by_contra hall
  push Not at hall
  set δ : ℝ := |ρ.re - 1 / 2| with hδ
  have hδ0 : 0 ≤ δ := abs_nonneg _
  have hR0 : 0 < R := lt_of_le_of_lt hδ0 hR
  set r : ℝ := δ / R with hr
  have hr0 : 0 ≤ r := div_nonneg hδ0 hR0.le
  have hr1 : r < 1 := (div_lt_one hR0).mpr hR
  have hcoef := norm_xiSliceCoeff_le hR0 hM
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hcoef 0 |>.trans (by simp))
  have hc0 : (xiSliceCoeff ρ.im 0).re ≤ M := by
    have := hcoef 0
    simp only [pow_zero, div_one] at this
    exact (Complex.re_le_norm _).trans this
  -- the trivial order `N = 0`
  rcases Nat.eq_zero_or_pos N with rfl | hNpos
  · simp only [pow_zero, mul_one] at hN
    have : M ≤ M / (1 - r) := le_div_self hM0 (by linarith) (by linarith)
    linarith
  -- the Taylor series at the real point `δ`, split at `N`
  have hsum := hasSum_xiSliceCoeff ρ.im (δ : ℂ)
  rw [xiSliceProduct_abs_eq_zero hρ] at hsum
  have htail := (hasSum_nat_add_iff' N).mpr hsum
  -- the tail is small
  have hg : HasSum (fun n : ℕ => M * r ^ N * r ^ n) (M * r ^ N / (1 - r)) := by
    have := (hasSum_geometric_of_lt_one hr0 hr1).mul_left (M * r ^ N)
    simpa [div_eq_mul_inv] using this
  have hbound : ∀ n : ℕ, ‖xiSliceCoeff ρ.im (n + N) * (δ : ℂ) ^ (n + N)‖ ≤ M * r ^ N * r ^ n := by
    intro n
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hδ0]
    calc ‖xiSliceCoeff ρ.im (n + N)‖ * δ ^ (n + N) ≤ M / R ^ (n + N) * δ ^ (n + N) :=
          mul_le_mul_of_nonneg_right (hcoef _) (pow_nonneg hδ0 _)
      _ = M * r ^ N * r ^ n := by
          rw [hr, div_pow, div_pow, pow_add, pow_add]
          field_simp
  have htailnorm := htail.norm_le_of_bounded hg hbound
  -- the head is at least `c_0`
  have hhead : (xiSliceCoeff ρ.im 0).re ≤
      (∑ i ∈ Finset.range N, xiSliceCoeff ρ.im i * (δ : ℂ) ^ i).re := by
    rw [Complex.re_sum]
    have hterm : ∀ i ∈ Finset.range N, 0 ≤ (xiSliceCoeff ρ.im i * (δ : ℂ) ^ i).re := by
      intro i hi
      rw [← Complex.ofReal_pow, Complex.re_mul_ofReal]
      exact mul_nonneg (hall i (Finset.mem_range.mp hi)) (pow_nonneg hδ0 _)
    have h0 := Finset.single_le_sum hterm (Finset.mem_range.mpr hNpos)
    simpa using h0
  have hre : (∑ i ∈ Finset.range N, xiSliceCoeff ρ.im i * (δ : ℂ) ^ i).re ≤
      M * r ^ N / (1 - r) := by
    have e : (∑ i ∈ Finset.range N, xiSliceCoeff ρ.im i * (δ : ℂ) ^ i) =
        -(0 - ∑ i ∈ Finset.range N, xiSliceCoeff ρ.im i * (δ : ℂ) ^ i) := by ring
    rw [e, Complex.neg_re]
    exact (neg_le_abs _).trans ((Complex.abs_re_le_norm _).trans htailnorm)
  have : M * (δ / R) ^ N / (1 - δ / R) = M * r ^ N / (1 - r) := rfl
  linarith

end

end RHTower
