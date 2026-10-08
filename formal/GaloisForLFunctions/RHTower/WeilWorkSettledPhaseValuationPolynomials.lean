import GaloisForLFunctions.RHTower.WeilWorkSettledPhaseValuationExponential

/-!
# Finite polynomials for valuation endpoints

The coefficient of fixed valuation in a convolution exponential supported on
prime multiples is a finite polynomial. The limit argument therefore needs no
interchange of a radial limit with an infinite sum over valuations or powers.
-/

noncomputable section

open Complex Filter
open scoped Topology
open GaloisForLFunctions.HTGeometry

namespace RHTower.WeilSingularArithmetic

/-- Ordinary coefficients of a formal power, defined by finite convolution. -/
def valuationPowerPolynomial (ell : ℕ → ℝ) : ℕ → ℕ → ℝ
  | 0, k => if k = 0 then 1 else 0
  | r + 1, k => ∑ j ∈ Finset.range (k + 1),
      ell j * valuationPowerPolynomial ell r (k - j)

/-- Coefficient of degree `k` in the formal exponential when `ell 0 = 0`. -/
def valuationExponentialPolynomial (ell : ℕ → ℝ) (k : ℕ) : ℝ :=
  ∑ r ∈ Finset.range (k + 1), valuationPowerPolynomial ell r k / (r.factorial : ℝ)

theorem LSeries_valuationPart_convPow_zero {p : ℕ} (hp : p.Prime)
    (f : ℕ → ℂ) (k : ℕ) (s : ℂ) :
    LSeries (valuationPart p k (dirichletConvPow f 0)) s =
      if k = 0 then 1 else 0 := by
  have he : valuationPart p k (dirichletConvPow f 0) =
      (if k = 0 then (1 : ℂ) else 0) • dirichletConvPow f 0 := by
    funext n
    by_cases hn : n = 1
    · subst n
      simp only [valuationPart, valuationMask_eq_factorization hp (by omega : (1 : ℕ) ≠ 0),
        dirichletConvPow, Pi.smul_apply, smul_eq_mul]
      by_cases hk : k = 0 <;> simp [hk, eq_comm]
    · simp [valuationPart, dirichletConvPow, hn]
  rw [he, LSeries_smul, LSeries_dirichletConvPow_zero, mul_one]

/-- Finite convolution preserves every fixed valuation endpoint. -/
theorem tendsto_valuationPart_convPow {p : ℕ} (hp : p.Prime) {f : ℕ → ℂ}
    {ell : ℕ → ℝ}
    (hf : ∀ σ : ℝ, 1 < σ → LSeriesSummable f (σ : ℂ))
    (hell : ∀ k : ℕ, Tendsto (fun σ : ℝ => LSeries (valuationPart p k f) (σ : ℂ))
      (𝓝[>] 1) (𝓝 (ell k : ℂ))) (r k : ℕ) :
    Tendsto (fun σ : ℝ => LSeries (valuationPart p k (dirichletConvPow f r)) (σ : ℂ))
      (𝓝[>] 1) (𝓝 (valuationPowerPolynomial ell r k : ℂ)) := by
  induction r generalizing k with
  | zero =>
    by_cases hk : k = 0 <;>
      simp [LSeries_valuationPart_convPow_zero hp, valuationPowerPolynomial, hk]
  | succ r ih =>
    have ht := tendsto_finsetSum (Finset.range (k + 1)) fun j _ =>
      (hell j).mul (ih (k - j))
    have he : (∑ j ∈ Finset.range (k + 1),
        (ell j : ℂ) * (valuationPowerPolynomial ell r (k - j) : ℂ)) =
        (valuationPowerPolynomial ell (r + 1) k : ℂ) := by
      simp only [valuationPowerPolynomial, Complex.ofReal_sum, Complex.ofReal_mul]
    rw [he] at ht
    apply ht.congr'
    filter_upwards [self_mem_nhdsWithin] with σ hσ
    exact (LSeries_valuationPart_convolution hp k (hf σ hσ)
      (lseriesSummable_dirichletConvPow (hf σ hσ) r).1).symm

/-- The full convolution exponential has a finite polynomial limit at each depth. -/
theorem tendsto_valuationPart_dirichletExp {p : ℕ} (hp : p.Prime) {f : ℕ → ℂ}
    {ell : ℕ → ℝ} (h0 : f 0 = 0) (h1 : f 1 = 0)
    (hsupport : ∀ n, ¬p ∣ n → f n = 0)
    (hf : ∀ σ : ℝ, 1 < σ → LSeriesSummable f (σ : ℂ))
    (hell : ∀ k : ℕ, Tendsto (fun σ : ℝ => LSeries (valuationPart p k f) (σ : ℂ))
      (𝓝[>] 1) (𝓝 (ell k : ℂ))) (k : ℕ) :
    Tendsto (fun σ : ℝ => LSeries (valuationPart p k (dirichletExp f)) (σ : ℂ))
      (𝓝[>] 1) (𝓝 (valuationExponentialPolynomial ell k : ℂ)) := by
  have ht := tendsto_finsetSum (Finset.range (k + 1)) fun r _ =>
    (tendsto_valuationPart_convPow hp hf hell r k).const_mul ((r.factorial : ℂ)⁻¹)
  have he : (∑ r ∈ Finset.range (k + 1),
      (r.factorial : ℂ)⁻¹ * (valuationPowerPolynomial ell r k : ℂ)) =
      (valuationExponentialPolynomial ell k : ℂ) := by
    simp only [valuationExponentialPolynomial, Complex.ofReal_sum]
    push_cast
    exact Finset.sum_congr rfl fun r _ => by ring
  rw [he] at ht
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with σ hσ
  rw [valuationPart_dirichletExp_finite h0 h1 hsupport,
    LSeries_sum (fun r _ => (summable_valuationPart p k
      (lseriesSummable_dirichletConvPow (hf σ hσ) r).1).smul ((r.factorial : ℂ)⁻¹))]
  simp only [LSeries_smul]

end RHTower.WeilSingularArithmetic
