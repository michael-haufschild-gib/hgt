import GaloisForLFunctions.RHTower.Sieve.RamareComplex

/-!
# The Dirichlet polynomial at low heights

At height `w` the phase `n^{2πiw} = e^{2πi w log n}` has total variation `2π|w| log M` across
`n ≤ M`, so Abel summation transfers the cancellation of the coefficients' partial sums directly:

```text
‖ ∑_{n ≤ M} a(n)·n^{2πiw} ‖  ≤  B·( 1 + 2π|w|·log M ) ,      B = max_k | ∑_{n ≤ k} a(n) | .
```

For `a = μ` the corpus's `mertensSup M = o(M)` makes this `o(M)·(1 + 2π|w| log M)`, which beats the
trivial size `M` for `|w| ≪ 1/log M`.  That is the low-height half of the card's residue: below
`1/log M` the off-diagonal is controlled by the prime number theorem alone, and only the moderate
heights need the Ramaré factorization.
-/

noncomputable section

namespace RHTower.Sieve

open Finset

/-- A unit phase differs from `1` by at most its argument. -/
theorem norm_exp_mul_I_sub_one_le (θ : ℝ) :
    ‖Complex.exp ((θ : ℂ) * Complex.I) - 1‖ ≤ |θ| := by
  have hre : (Complex.exp ((θ : ℂ) * Complex.I) - 1).re = Real.cos θ - 1 := by
    simp [Complex.exp_mul_I, Complex.cos_ofReal_re, Complex.sin_ofReal_re]
  have him : (Complex.exp ((θ : ℂ) * Complex.I) - 1).im = Real.sin θ := by
    simp [Complex.exp_mul_I, Complex.sin_ofReal_re,
      Complex.cos_ofReal_im, Complex.sin_ofReal_im]
  rw [Complex.norm_eq_sqrt_sq_add_sq, hre, him]
  have hhalf : Real.cos θ = 1 - 2 * Real.sin (θ / 2) ^ 2 := by
    have := Real.cos_two_mul_eq_one_sub (θ / 2)
    rw [show 2 * (θ / 2) = θ by ring] at this
    linarith
  have hkey : (Real.cos θ - 1) ^ 2 + Real.sin θ ^ 2 = 4 * Real.sin (θ / 2) ^ 2 := by
    have hpy : Real.sin θ ^ 2 = 1 - Real.cos θ ^ 2 := by
      have := Real.sin_sq_add_cos_sq θ
      linarith
    rw [hpy, hhalf]
    ring
  rw [hkey]
  have hsin : |Real.sin (θ / 2)| ≤ |θ / 2| := Real.abs_sin_le_abs
  have habs : |θ / 2| = |θ| / 2 := by
    rw [abs_div]
    norm_num
  have hle : 4 * Real.sin (θ / 2) ^ 2 ≤ |θ| ^ 2 := by
    have hsin2 : |Real.sin (θ / 2)| ≤ |θ| / 2 := by
      rw [← habs]
      exact hsin
    have h1 : Real.sin (θ / 2) ^ 2 = |Real.sin (θ / 2)| ^ 2 := (sq_abs _).symm
    rw [h1]
    nlinarith [hsin2, abs_nonneg (Real.sin (θ / 2)), abs_nonneg θ]
  calc Real.sqrt (4 * Real.sin (θ / 2) ^ 2) ≤ Real.sqrt (|θ| ^ 2) := Real.sqrt_le_sqrt hle
    _ = |θ| := Real.sqrt_sq (abs_nonneg θ)

/-- Two unit phases differ by at most the difference of their arguments. -/
theorem norm_exp_mul_I_sub_le (a b : ℝ) :
    ‖Complex.exp ((a : ℂ) * Complex.I) - Complex.exp ((b : ℂ) * Complex.I)‖ ≤ |a - b| := by
  have hfac : Complex.exp ((a : ℂ) * Complex.I) - Complex.exp ((b : ℂ) * Complex.I)
      = Complex.exp ((b : ℂ) * Complex.I) * (Complex.exp (((a - b : ℝ) : ℂ) * Complex.I) - 1) := by
    rw [mul_sub, mul_one, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  rw [hfac, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
  exact norm_exp_mul_I_sub_one_le (a - b)

/-- **Abel's inequality with a complex weight of bounded variation.** -/
theorem norm_sum_mul_le_of_bounded_partial_bv {g : ℕ → ℝ} {φ : ℕ → ℂ} {B : ℝ} (n : ℕ)
    (hB : ∀ k, k ≤ n → |∑ j ∈ Finset.range k, g j| ≤ B) :
    ‖∑ i ∈ Finset.range n, φ i * ((g i : ℝ) : ℂ)‖
      ≤ B * (‖φ (n - 1)‖ + ∑ i ∈ Finset.range (n - 1), ‖φ (i + 1) - φ i‖) := by
  have hB0 : 0 ≤ B := le_trans (abs_nonneg _) (hB 0 (Nat.zero_le n))
  have hS : ∀ k, k ≤ n → ‖∑ j ∈ Finset.range k, ((g j : ℝ) : ℂ)‖ ≤ B := by
    intro k hk
    have hcast : ∑ j ∈ Finset.range k, ((g j : ℝ) : ℂ)
        = (((∑ j ∈ Finset.range k, g j : ℝ)) : ℂ) := by push_cast; ring
    rw [hcast, Complex.norm_real, Real.norm_eq_abs]
    exact hB k hk
  have hparts := Finset.sum_range_by_parts φ (fun j => ((g j : ℝ) : ℂ)) n
  simp only [smul_eq_mul] at hparts
  rw [hparts]
  refine le_trans (norm_sub_le _ _) ?_
  have hhead : ‖φ (n - 1) * ∑ i ∈ Finset.range n, ((g i : ℝ) : ℂ)‖ ≤ ‖φ (n - 1)‖ * B := by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hS n le_rfl) (norm_nonneg _)
  have htail : ‖∑ i ∈ Finset.range (n - 1),
      (φ (i + 1) - φ i) * ∑ j ∈ Finset.range (i + 1), ((g j : ℝ) : ℂ)‖
      ≤ (∑ i ∈ Finset.range (n - 1), ‖φ (i + 1) - φ i‖) * B := by
    refine le_trans (norm_sum_le _ _) ?_
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun i hi => ?_
    rw [Finset.mem_range] at hi
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hS (i + 1) (by omega)) (norm_nonneg _)
  nlinarith [hhead, htail, hB0]

/-- The phase of the Dirichlet polynomial. -/
def logPhase (w : ℝ) (n : ℕ) : ℂ :=
  Complex.exp (((2 * Real.pi * (w * Real.log n) : ℝ) : ℂ) * Complex.I)

theorem norm_logPhase (w : ℝ) (n : ℕ) : ‖logPhase w n‖ = 1 := by
  rw [logPhase, Complex.norm_exp_ofReal_mul_I]

theorem norm_logPhase_sub_le (w : ℝ) (m n : ℕ) :
    ‖logPhase w n - logPhase w m‖
      ≤ 2 * Real.pi * |w| * |Real.log n - Real.log m| := by
  rw [logPhase, logPhase]
  refine le_trans (norm_exp_mul_I_sub_le _ _) (le_of_eq ?_)
  have hval : 2 * Real.pi * (w * Real.log n) - 2 * Real.pi * (w * Real.log m)
      = (2 * Real.pi * w) * (Real.log n - Real.log m) := by ring
  rw [hval, abs_mul, abs_mul,
    abs_of_nonneg (by positivity : (0:ℝ) ≤ 2 * Real.pi)]

/-- **The Dirichlet polynomial at a real coefficient sequence, by Abel summation.** -/
theorem norm_logPoly_le_partial (a : ℕ → ℝ) (M : ℕ) {B : ℝ}
    (hB : ∀ k, k ≤ M → |∑ j ∈ Finset.range k, a (j + 1)| ≤ B) (w : ℝ) :
    ‖logPoly (fun n => ((a n : ℝ) : ℂ)) (Finset.Icc 1 M) w‖
      ≤ B * (1 + 2 * Real.pi * |w| * Real.log M) := by
  classical
  have hreindex : logPoly (fun n => ((a n : ℝ) : ℂ)) (Finset.Icc 1 M) w
      = ∑ i ∈ Finset.range M, logPhase w (i + 1) * ((a (i + 1) : ℝ) : ℂ) := by
    rw [logPoly, ← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
    refine Finset.sum_congr (by norm_num) fun i _ => ?_
    rw [logPhase]
    have hidx : 1 + i = i + 1 := by omega
    rw [hidx]
    ring
  rw [hreindex]
  refine le_trans (norm_sum_mul_le_of_bounded_partial_bv (g := fun j => a (j + 1))
    (φ := fun i => logPhase w (i + 1)) M hB) ?_
  refine mul_le_mul_of_nonneg_left ?_ (le_trans (abs_nonneg _) (hB 0 (Nat.zero_le M)))
  have hhead : ‖logPhase w (M - 1 + 1)‖ = 1 := norm_logPhase w _
  rw [hhead]
  refine add_le_add le_rfl ?_
  have hterm : ∀ i ∈ Finset.range (M - 1),
      ‖logPhase w (i + 1 + 1) - logPhase w (i + 1)‖
        ≤ 2 * Real.pi * |w| * (Real.log ((i : ℝ) + 2) - Real.log ((i : ℝ) + 1)) := by
    intro i _
    have hmono : Real.log ((i : ℝ) + 1) ≤ Real.log ((i : ℝ) + 2) :=
      Real.log_le_log (by positivity) (by linarith)
    have hc1 : ((i + 1 + 1 : ℕ) : ℝ) = (i : ℝ) + 2 := by push_cast; ring
    have hc2 : ((i + 1 : ℕ) : ℝ) = (i : ℝ) + 1 := by push_cast; ring
    have hb := norm_logPhase_sub_le w (i + 1) (i + 1 + 1)
    rw [hc1, hc2, abs_of_nonneg (by linarith :
      (0:ℝ) ≤ Real.log ((i : ℝ) + 2) - Real.log ((i : ℝ) + 1))] at hb
    exact hb
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [← Finset.mul_sum]
  have htel : ∑ i ∈ Finset.range (M - 1),
      (Real.log ((i : ℝ) + 2) - Real.log ((i : ℝ) + 1))
      = Real.log (((M - 1 : ℕ) : ℝ) + 1) - Real.log ((0 : ℝ) + 1) := by
    have hz := Finset.sum_range_sub (fun i : ℕ => Real.log ((i : ℝ) + 1)) (M - 1)
    simp only [Nat.cast_zero] at hz
    have hcong : ∀ i ∈ Finset.range (M - 1),
        Real.log (((i + 1 : ℕ) : ℝ) + 1) - Real.log ((i : ℝ) + 1)
          = Real.log ((i : ℝ) + 2) - Real.log ((i : ℝ) + 1) := by
      intro i _
      have : ((i + 1 : ℕ) : ℝ) + 1 = (i : ℝ) + 2 := by push_cast; ring
      rw [this]
    rw [← Finset.sum_congr rfl hcong]
    exact hz
  rw [htel, zero_add, Real.log_one, sub_zero]
  rcases Nat.eq_zero_or_pos M with hM | hM
  · subst hM
    simp
  · have hMcast : ((M - 1 : ℕ) : ℝ) + 1 = (M : ℝ) := by
      have : ((M - 1 : ℕ) : ℝ) = (M : ℝ) - 1 := by
        rw [Nat.cast_sub hM]
        norm_num
      rw [this]
      ring
    rw [hMcast]

end RHTower.Sieve

end
