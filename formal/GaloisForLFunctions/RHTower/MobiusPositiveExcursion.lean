import GaloisForLFunctions.RHTower.MobiusOrderLowerBound

/-!
# Positive excursions recur

If only finitely many Hermitian mixed convolution coefficients were positive, the positive part of
the radial series would be a polynomial, hence bounded on `0 < r < 1`.  The radial generating
function would then be bounded near the boundary, which is decay at exponent `0`, and the Mellin
obstruction rules that out because a zeta zero sits strictly to the right of `0`.

So for every order `k` the coefficients `Re R_k(N)` are positive for infinitely many `N`.  At `k = 1`
this is the recurrence of positive values of the binary additive Möbius self-convolution.
-/

namespace RHTower

/-- Taking the `2k`-th root of a bound on `‖z^k‖²`. -/
private theorem norm_le_rpow_of_norm_pow_sq_le {z : ℂ} {M : ℝ} {k : ℕ} (hk : 0 < k)
    (h : ‖z ^ k‖ ^ 2 ≤ M) :
    ‖z‖ ≤ M ^ ((2 * (k : ℝ))⁻¹) := by
  have hkR : (0 : ℝ) < 2 * (k : ℝ) := by
    have : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr hk
    linarith
  have hpow : ‖z‖ ^ (2 * k) ≤ M := by
    rwa [norm_pow, ← pow_mul, mul_comm k 2] at h
  have hcast : ‖z‖ ^ ((2 * (k : ℝ))) = ‖z‖ ^ (2 * k) := by
    rw [show (2 * (k : ℝ)) = ((2 * k : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
  have hle : ‖z‖ ^ ((2 * (k : ℝ))) ≤ M := by rw [hcast]; exact hpow
  have hmono := Real.rpow_le_rpow (by positivity) hle (le_of_lt (inv_pos.mpr hkR))
  rwa [← Real.rpow_mul (norm_nonneg z), mul_inv_cancel₀ (ne_of_gt hkR), Real.rpow_one] at hmono

/-- **Finitely many positive coefficients would bound the source.**  If every coefficient outside a
finite set is nonpositive, the radial generating function is bounded, which is decay at exponent
`0`. -/
theorem mobiusDiscreteLaplaceDecay_zero_of_nonpos_outside
    {k : ℕ} (hk : 0 < k) (S : Finset ℕ)
    (hS : ∀ N : ℕ, N ∉ S → (mixedAdditiveConvolutionPower mobiusCoeff k N).re ≤ 0) :
    MobiusDiscreteLaplaceDecay 0 := by
  classical
  set B : ℝ := ∑ N ∈ S, max ((mixedAdditiveConvolutionPower mobiusCoeff k N).re) 0 with hBdef
  have hB0 : 0 ≤ B := Finset.sum_nonneg fun N _ => le_max_right _ _
  refine ⟨B ^ ((2 * (k : ℝ))⁻¹), 1, Real.rpow_nonneg hB0 _, one_pos, ?_⟩
  intro x hx _
  set r : ℝ := Real.exp (-x) with hr
  have hr0 : (0 : ℝ) ≤ r := (Real.exp_pos _).le
  have hr1 : r ≤ 1 := by
    rw [hr]
    exact Real.exp_le_one_iff.mpr (by linarith)
  set bfun : ℕ → ℝ := fun N =>
    if N ∈ S then max ((mixedAdditiveConvolutionPower mobiusCoeff k N).re) 0 else 0 with hbdef
  have hbnonneg : ∀ N, 0 ≤ bfun N := by
    intro N
    rw [hbdef]
    by_cases hN : N ∈ S <;> simp [hN]
  have hupper : ∀ N : ℕ,
      (mixedAdditiveConvolutionPower mobiusCoeff k N).re ≤ bfun N := by
    intro N
    rw [hbdef]
    by_cases hN : N ∈ S
    · simp only [hN, if_pos]
      exact le_max_left _ _
    · simp only [hN, if_neg, not_false_iff]
      exact hS N hN
  have hzero : ∀ N : ℕ, N ∉ S → bfun N * r ^ N = 0 := by
    intro N hN
    rw [hbdef]
    simp [hN]
  have hbsum : Summable fun N : ℕ => bfun N * r ^ N :=
    summable_of_ne_finset_zero hzero
  have htsum : (∑' N : ℕ, bfun N * r ^ N) ≤ B := by
    rw [tsum_eq_sum hzero, hBdef]
    refine Finset.sum_le_sum fun N hN => ?_
    have hrn : r ^ N ≤ 1 := pow_le_one₀ hr0 hr1
    have hbn : 0 ≤ bfun N := hbnonneg N
    calc bfun N * r ^ N ≤ bfun N * 1 := mul_le_mul_of_nonneg_left hrn hbn
      _ = bfun N := mul_one _
      _ = max ((mixedAdditiveConvolutionPower mobiusCoeff k N).re) 0 := by
          rw [hbdef]; simp [hN]
  have hR8 := norm_sq_pow_le_tsum_of_mixedAdditiveConvolutionPower_upper
    mobiusCoeff k r hr0 (summable_norm_mobiusCoeff_mul_pow hx) bfun hupper hbsum
  have hbound : ‖(∑' N : ℕ, mobiusCoeff N * ((r : ℝ) : ℂ) ^ N) ^ k‖ ^ 2 ≤ B :=
    hR8.trans htsum
  have hroot := norm_le_rpow_of_norm_pow_sq_le hk hbound
  rw [mobiusDiscreteLaplaceTransform_eq_tsum]
  refine hroot.trans (le_of_eq ?_)
  rw [neg_zero, Real.rpow_zero, mul_one]

/-- **Positive excursions recur.**  For every order `k` and every finite set of indices, some index
outside it carries a positive coefficient. -/
theorem exists_notMem_pos_mixedAdditiveConvolutionPower
    {k : ℕ} (hk : 0 < k) (S : Finset ℕ) :
    ∃ N : ℕ, N ∉ S ∧ 0 < (mixedAdditiveConvolutionPower mobiusCoeff k N).re := by
  by_contra hcon
  have hnp : ∀ N : ℕ, N ∉ S →
      (mixedAdditiveConvolutionPower mobiusCoeff k N).re ≤ 0 := by
    intro N hN
    by_contra hpos
    exact hcon ⟨N, hN, not_le.mp hpos⟩
  obtain ⟨ρ, hzero, h1, hre⟩ := exists_riemannZeta_eq_zero_lt_re (by norm_num : (0 : ℝ) < 1 / 2)
  exact not_mobiusDiscreteLaplaceDecay_of_riemannZeta_eq_zero le_rfl hre h1 hzero
    (mobiusDiscreteLaplaceDecay_zero_of_nonpos_outside hk S hnp)

/-- The set of indices carrying a positive coefficient is infinite. -/
theorem infinite_pos_mixedAdditiveConvolutionPower {k : ℕ} (hk : 0 < k) :
    {N : ℕ | 0 < (mixedAdditiveConvolutionPower mobiusCoeff k N).re}.Infinite := by
  intro hfin
  obtain ⟨N, hNmem, hNpos⟩ :=
    exists_notMem_pos_mixedAdditiveConvolutionPower hk hfin.toFinset
  exact hNmem (hfin.mem_toFinset.mpr hNpos)

end RHTower
