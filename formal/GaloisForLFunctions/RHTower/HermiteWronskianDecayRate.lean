import GaloisForLFunctions.RHTower.HermiteWeightedDerivativeIntegrable
import GaloisForLFunctions.HTGeometry.PolynomialGaussianDecayRate

/-!
# A rate for truncated Hermite orthogonality

`integral_hermiteFun_mul_eq` evaluates the truncated inner product of two Hermite functions at
different rungs exactly, as the increment of their Wronskian divided by twice the rung difference.
The Wronskian itself is a polynomial times `e^{-ξ²}`, because each factor is a polynomial times
`e^{-ξ²/2}`, so the quantitative polynomial-Gaussian estimate turns that identity into an explicit
inverse-power bound:

```text
|∫_{-R}^{R} h_m h_n|  ≤  K / R^k          for every `k` and every `R ≥ 1`.
```

This is the missing rate in the qualitative `tendsto_integral_hermiteFun_mul`.
-/

noncomputable section

open Filter Topology

namespace RHTower

open GaloisForLFunctions.HTGeometry

/-- The Hermite Wronskian in polynomial-times-Gaussian form. -/
theorem exists_poly_hermiteWronskian (m n : ℕ) :
    ∃ r : Polynomial ℝ, ∀ x : ℝ, hermiteWronskian m n x = r.eval x * Real.exp (-x ^ (2 : ℕ)) := by
  obtain ⟨pm, hpm⟩ := exists_poly_hermiteFun m
  obtain ⟨pn, hpn⟩ := exists_poly_hermiteFun n
  obtain ⟨qm, hqm⟩ := deriv_hermiteFun_poly m
  obtain ⟨qn, hqn⟩ := deriv_hermiteFun_poly n
  refine ⟨qm * pn - pm * qn, fun x => ?_⟩
  have hexp : Real.exp (-(1 / 2 * x ^ (2 : ℕ))) * Real.exp (-(1 / 2 * x ^ (2 : ℕ))) = Real.exp (-x ^ (2 : ℕ)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  simp only [hermiteWronskian, hpm, hpn, hqm, hqn, Polynomial.eval_sub, Polynomial.eval_mul]
  rw [← hexp]
  ring

/-- **Every inverse power bounds the Hermite Wronskian outside the unit interval.** -/
theorem exists_bound_hermiteWronskian (m n : ℕ) (k : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x : ℝ, 1 ≤ |x| → |hermiteWronskian m n x| ≤ K / |x| ^ k := by
  obtain ⟨r, hr⟩ := exists_poly_hermiteWronskian m n
  refine ⟨polyCoeffMass r * ((r.natDegree + k).factorial : ℝ),
    mul_nonneg (polyCoeffMass_nonneg r) (by positivity), fun x hx => ?_⟩
  rw [hr x, abs_mul, abs_of_pos (Real.exp_pos _)]
  exact abs_eval_mul_exp_neg_sq_le r k hx

/-- Two distinct natural numbers are at unit distance at least, as reals. -/
theorem one_le_abs_sub_of_ne {m n : ℕ} (hmn : m ≠ n) : (1 : ℝ) ≤ |(n : ℝ) - (m : ℝ)| := by
  rcases Nat.lt_or_ge n m with h | h
  · have hle : (n : ℝ) + 1 ≤ (m : ℝ) := by exact_mod_cast Nat.succ_le_of_lt h
    rw [abs_of_nonpos (by linarith)]
    linarith
  · rcases Nat.eq_or_lt_of_le h with h' | h'
    · exact absurd h' hmn
    · have hle : (m : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast Nat.succ_le_of_lt h'
      rw [abs_of_nonneg (by linarith)]
      linarith

/-- **A rate for truncated Hermite orthogonality.**  The symmetric truncated inner product of two
Hermite functions at distinct rungs is bounded by an explicit constant divided by any prescribed
power of the truncation. -/
theorem exists_bound_integral_hermiteFun_mul {m n : ℕ} (hmn : m ≠ n) (k : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ R : ℝ, 1 ≤ R →
      |∫ x in (-R)..R, hermiteFun m x * hermiteFun n x| ≤ K / R ^ k := by
  obtain ⟨K, hK0, hK⟩ := exists_bound_hermiteWronskian m n k
  refine ⟨K, hK0, fun R hR => ?_⟩
  have hR0 : (0 : ℝ) < R := lt_of_lt_of_le one_pos hR
  have habsR : |R| = R := abs_of_pos hR0
  have habsnR : |(-R)| = R := by rw [abs_neg, habsR]
  have hRk : (0 : ℝ) < R ^ k := pow_pos hR0 k
  have h1 : |hermiteWronskian m n R| ≤ K / R ^ k := by
    have h := hK R (by rw [habsR]; exact hR)
    rwa [habsR] at h
  have h2 : |hermiteWronskian m n (-R)| ≤ K / R ^ k := by
    have h := hK (-R) (by rw [habsnR]; exact hR)
    rwa [habsnR] at h
  have hnum : |hermiteWronskian m n R - hermiteWronskian m n (-R)| ≤ 2 * (K / R ^ k) := by
    have hsplit : hermiteWronskian m n R - hermiteWronskian m n (-R)
        = hermiteWronskian m n R + -(hermiteWronskian m n (-R)) := by ring
    rw [hsplit]
    have h := abs_add_le (hermiteWronskian m n R) (-(hermiteWronskian m n (-R)))
    rw [abs_neg] at h
    linarith
  have hd : (1 : ℝ) ≤ |(n : ℝ) - (m : ℝ)| := one_le_abs_sub_of_ne hmn
  have hden : |2 * ((n : ℝ) - (m : ℝ))| = 2 * |(n : ℝ) - (m : ℝ)| := by
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  rw [integral_hermiteFun_mul_eq hmn, abs_div, hden, div_le_iff₀ (by linarith)]
  have hKR : 0 ≤ K / R ^ k := div_nonneg hK0 hRk.le
  nlinarith [hnum, hd, hKR]

end RHTower

end
