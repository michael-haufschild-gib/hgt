import GaloisForLFunctions.RHTower.RiemannAutocorrMomentCancellation
import GaloisForLFunctions.RHTower.WeilWorkDeficitUniformDerivativeBudget

/-!
# Uniform order budgets for actual kernel moment cancellation

The corpus factorial envelope controls all derivatives with the same constants.
Taylor division leaves only a cubic factor in the order, which a geometric
budget absorbs. No smoothness or analytic premise is added.
-/

open scoped BigOperators

namespace RHTower

theorem exists_riemannKernelDeriv_uniform_factorial_cubic_envelope :
    ∃ B C : ℝ, 0 < B ∧ 1 ≤ C ∧ ∀ (k : ℕ) (x : ℝ),
      ‖riemannKernelDeriv k x‖ ≤
        B * C ^ k * ((k + 2).factorial : ℝ) * Real.exp (-3 * |x|) := by
  obtain ⟨B, C, hB, hC, _, hbound⟩ :=
    WeilWorkDeficitDerivativeBudget.kernel_derivative_factorial_envelope
      (a := 1) (by norm_num) (by linarith [Real.pi_gt_three])
  refine ⟨B, max 1 C, hB, le_max_left _ _, ?_⟩
  intro k x
  have hsmall : Real.exp (-Real.exp (2 * |x|)) * Real.exp (-|x|) ≤
      Real.exp (-3 * |x|) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    linarith [Real.add_one_le_exp (2 * |x|)]
  have hb := hbound k x
  simp only [one_mul] at hb
  calc
    ‖riemannKernelDeriv k x‖ ≤
        B * C ^ k * ((k + 2).factorial : ℝ) * Real.exp (-Real.exp (2 * |x|)) *
          Real.exp (-|x|) := hb
    _ = (B * C ^ k * ((k + 2).factorial : ℝ)) *
        (Real.exp (-Real.exp (2 * |x|)) * Real.exp (-|x|)) := by ring
    _ ≤ (B * C ^ k * ((k + 2).factorial : ℝ)) * Real.exp (-3 * |x|) :=
      mul_le_mul_of_nonneg_left hsmall (by positivity)
    _ ≤ B * (max 1 C) ^ k * ((k + 2).factorial : ℝ) * Real.exp (-3 * |x|) := by
      gcongr
      exact le_max_right _ _

private theorem uniform_moment_factorial_ratio (r : ℕ) :
    ((r + 3).factorial : ℝ) / (r.factorial : ℝ) ≤ 6 * (8 : ℝ) ^ r := by
  have hfac : ((r + 3).factorial : ℝ) / (r.factorial : ℝ) =
      ((r : ℝ) + 1) * ((r : ℝ) + 2) * ((r : ℝ) + 3) := by
    rw [Nat.factorial_succ, Nat.factorial_succ, Nat.factorial_succ]
    push_cast
    field_simp
    ring
  have h1 : (r : ℝ) + 1 ≤ (2 : ℝ) ^ r := by
    exact_mod_cast Nat.succ_le_of_lt (Nat.lt_two_pow_self (n := r))
  have h2 : (r : ℝ) + 2 ≤ 2 * (2 : ℝ) ^ r := by nlinarith [Nat.cast_nonneg (α := ℝ) r]
  have h3 : (r : ℝ) + 3 ≤ 3 * (2 : ℝ) ^ r := by nlinarith [Nat.cast_nonneg (α := ℝ) r]
  rw [hfac]
  calc
    ((r : ℝ) + 1) * ((r : ℝ) + 2) * ((r : ℝ) + 3) ≤
        (2 : ℝ) ^ r * (2 * (2 : ℝ) ^ r) * (3 * (2 : ℝ) ^ r) := by gcongr
    _ = 6 * (8 : ℝ) ^ r := by
      rw [show (8 : ℝ) = 2 * 2 * 2 by norm_num]
      simp only [mul_pow]
      ring

/-- The same geometric budget controls every Taylor degree. -/
theorem exists_riemannKernelReal_uniform_taylor_envelope :
    ∃ D L : ℝ, 0 < D ∧ 1 ≤ L ∧ ∀ (r : ℕ) (x h : ℝ), 0 ≤ h → h ≤ 1 →
      |riemannKernelReal (x + h) -
        ∑ p ∈ Finset.range (r + 1),
          ((p.factorial : ℝ)⁻¹ * h ^ p) * (riemannKernelDeriv p x).re| ≤
        D * L ^ r * Real.exp (-3 * |x|) * h ^ (r + 1) := by
  obtain ⟨B, C, hB, hC1, hder⟩ := exists_riemannKernelDeriv_uniform_factorial_cubic_envelope
  have hC : 0 < C := by linarith
  refine ⟨6 * B * C * Real.exp 3, 8 * C, by positivity, by linarith, ?_⟩
  intro r x h h0 h1
  let A : ℝ := B * C ^ (r + 1) * ((r + 3).factorial : ℝ)
  have hA : 0 < A := by dsimp [A]; positivity
  have ht := riemannKernelDeriv_taylor_bound_of_envelope r 0 hA
    (fun z => by simpa only [A, Nat.zero_add, Nat.add_assoc] using hder (r + 1) z) x h h0 h1
  have hre := Complex.abs_re_le_norm (riemannKernelDeriv 0 (x + h) -
    ∑ p ∈ Finset.range (r + 1),
      ((p.factorial : ℝ)⁻¹ * h ^ p) • riemannKernelDeriv (0 + p) x)
  simp only [Nat.zero_add, riemannKernelDeriv_zero, riemannPhiKernel_eq_ofReal,
    Complex.sub_re, Complex.re_sum, Complex.smul_re, smul_eq_mul, Complex.ofReal_re] at hre ht
  have hcoef : A * Real.exp 3 / (r.factorial : ℝ) ≤
      (6 * B * C * Real.exp 3) * (8 * C) ^ r := by
    calc
      A * Real.exp 3 / (r.factorial : ℝ) =
          (B * C * Real.exp 3) * C ^ r * (((r + 3).factorial : ℝ) / (r.factorial : ℝ)) := by
        dsimp [A]
        rw [pow_succ]
        ring
      _ ≤ (B * C * Real.exp 3) * C ^ r * (6 * (8 : ℝ) ^ r) := by
        gcongr
        exact uniform_moment_factorial_ratio r
      _ = (6 * B * C * Real.exp 3) * (8 * C) ^ r := by rw [mul_pow]; ring
  exact (hre.trans ht).trans (by gcongr)

theorem exists_riemannKernelReal_uniform_moment_cancellation_envelope :
    ∃ D L : ℝ, 0 < D ∧ 1 ≤ L ∧ ∀ (r : ℕ) (ι : Type) [Fintype ι]
      (c h : ι → ℝ) (H : ℝ),
      0 ≤ H → H ≤ 1 → (∀ i, 0 ≤ h i ∧ h i ≤ H) →
      (∀ p ≤ r, ∑ i, c i * h i ^ p = 0) → ∀ x : ℝ,
      |∑ i, c i * riemannKernelReal (x + h i)| ≤
        D * L ^ r * Real.exp (-3 * |x|) * (∑ i, |c i|) * H ^ (r + 1) := by
  obtain ⟨D, L, hD, hL, hbound⟩ := exists_riemannKernelReal_uniform_taylor_envelope
  refine ⟨D, L, hD, hL, ?_⟩
  intro r
  exact riemannKernelReal_moment_cancellation_of_taylor_bound r
    (D := D * L ^ r) (by positivity) (hbound r)

theorem exists_riemannAutocorr_uniform_moment_cancellation_envelope :
    ∃ E L : ℝ, 0 < E ∧ 1 ≤ L ∧ ∀ (r : ℕ) (ι : Type) [Fintype ι]
      (c h : ι → ℝ) (H : ℝ),
      0 ≤ H → H ≤ 1 → (∀ i, 0 ≤ h i ∧ h i ≤ H) →
      (∀ p ≤ r, ∑ i, c i * h i ^ p = 0) → ∀ y : ℝ,
      |∑ i, c i * riemannAutocorr (y - h i)| ≤
        E * L ^ r * Real.exp (-2 * |y|) * (∑ i, |c i|) * H ^ (r + 1) := by
  obtain ⟨D, L, hD, hL, hkernel⟩ := exists_riemannKernelReal_uniform_moment_cancellation_envelope
  obtain ⟨T, hT, htransfer⟩ := exists_riemannAutocorr_moment_transfer_constant
  refine ⟨T * D, L, mul_pos hT hD, hL, ?_⟩
  intro r ι _ c h H hH0 hH1 hh hm y
  have ht := htransfer r (D * L ^ r) (by positivity) (hkernel r) ι c h H hH0 hH1 hh hm y
  simpa only [mul_assoc] using ht

end RHTower
