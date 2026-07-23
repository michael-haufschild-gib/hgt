import GaloisForLFunctions.HTGeometry.SampledSmallComplex
import GaloisForLFunctions.HTGeometry.FactorialGrowthBounds

/-!
# Window decay from sampled decay, with explicit exponential constants

Specialisation of the complex sampled-smallness estimate to the canonical
node separation `η = 1/(4(N+1))`:

`‖H x‖ ≤ 2·e^{6(N+1)}·ε₀ + 2·M/(N+1)!`

on a unit window carrying `N+1` such samples of size `≤ ε₀`, with
`‖H^{(N+1)}‖ ≤ M` along the window.  The factorial reciprocal is further
bounded by the superexponential `e^{-n(log n - 1)}`, the form used in
rate-transfer arguments where the derivative bound decays only at a fixed
exponential rate.
-/

noncomputable section

namespace HTGeometry

open Set

/-- Superexponential decay of the factorial reciprocal:
`1/n! ≤ e^{-n(log n - 1)}`. -/
theorem one_div_factorial_le_superexp {n : ℕ} (hn : 1 ≤ n) :
    (1:ℝ) / n.factorial ≤ Real.exp (-((n : ℝ) * (Real.log n - 1))) := by
  have hn0 : (0:ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hfac : (0:ℝ) < (n.factorial : ℝ) := by positivity
  have h := pow_mul_exp_neg_le_factorial n
  have hpow : ((n : ℝ)) ^ n = Real.exp ((n : ℝ) * Real.log n) := by
    conv_lhs => rw [← Real.exp_log hn0]
    rw [← Real.exp_nat_mul]
  rw [hpow, ← Real.exp_add] at h
  rw [div_le_iff₀ hfac]
  calc (1:ℝ) = Real.exp (-((n : ℝ) * (Real.log n - 1)))
        * Real.exp ((n : ℝ) * (Real.log n - 1)) := by
        rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
    _ ≤ Real.exp (-((n : ℝ) * (Real.log n - 1))) * (n.factorial : ℝ) := by
        apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg _)
        calc Real.exp ((n : ℝ) * (Real.log n - 1))
            = Real.exp ((n : ℝ) * Real.log n + -(n : ℝ)) := by
              congr 1
              ring
          _ ≤ (n.factorial : ℝ) := h

/-- **Window decay with explicit constants**: at the canonical separation
`η = 1/(4(N+1))`, sampled smallness propagates to the window with the
exponential constant `2e^{6(N+1)}` and the factorially small remainder. -/
theorem norm_le_window_of_sampled
    {N : ℕ} {H : ℂ → ℂ} (hH : Differentiable ℂ H)
    {s : Finset ℝ} (hcard : s.card = N + 1)
    {a : ℝ} (hsub : ↑s ⊆ Set.Icc a (a + 1))
    (hsep : ∀ t ∈ s, ∀ u ∈ s, t ≠ u →
      1 / (4 * ((N : ℝ) + 1)) ≤ |t - u|)
    {M : ℝ}
    (hM : ∀ t ∈ Set.Icc a (a + 1), ‖iteratedDeriv (N + 1) H (t : ℂ)‖ ≤ M)
    {ε₀ : ℝ} (hε₀0 : 0 ≤ ε₀) (hε₀ : ∀ t ∈ s, ‖H (t : ℂ)‖ ≤ ε₀)
    {x : ℝ} (hx : x ∈ Set.Icc a (a + 1)) :
    ‖H (x : ℂ)‖ ≤ 2 * Real.exp (6 * ((N : ℝ) + 1)) * ε₀
      + 2 * (M / (N + 1).factorial) := by
  have hη : (0:ℝ) < 1 / (4 * ((N : ℝ) + 1)) := by positivity
  have h := norm_le_of_sampled_small_complex hH hcard hsub hη hsep hM hε₀ hx
  have hconst := interpolation_constant_le N
  have hconst' : ((N : ℝ) + 1) * (2 ^ N
      / ((1 / (4 * ((N : ℝ) + 1))) ^ N * N.factorial))
      ≤ Real.exp (6 * ((N : ℝ) + 1)) := by
    rw [← mul_div_assoc]
    exact hconst
  calc ‖H (x : ℂ)‖
      ≤ 2 * (((N : ℝ) + 1) * (2 ^ N
          / ((1 / (4 * ((N : ℝ) + 1))) ^ N * N.factorial)) * ε₀
        + M / (N + 1).factorial) := h
    _ ≤ 2 * (Real.exp (6 * ((N : ℝ) + 1)) * ε₀
        + M / (N + 1).factorial) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        exact add_le_add (mul_le_mul_of_nonneg_right hconst' hε₀0) le_rfl
    _ = 2 * Real.exp (6 * ((N : ℝ) + 1)) * ε₀
        + 2 * (M / (N + 1).factorial) := by ring

end HTGeometry
