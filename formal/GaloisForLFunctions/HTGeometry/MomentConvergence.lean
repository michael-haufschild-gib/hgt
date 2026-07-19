import GaloisForLFunctions.HTGeometry.TruncatedPower

/-!
# Moment convergence from weak convergence

Weak convergence tests against bounded continuous functions only, so it does not directly give
convergence of `∫ xᵏ`.  A uniform bound on the even moments repairs this: the truncation error is
`2 (∫ x^{2k}) / Rᵏ` on both sides by `abs_integral_sub_integral_truncPow_le`, so choosing `R` large
makes both outer terms of

`|∫ xᵏ dν − ∫ xᵏ dμ| ≤ |∫ xᵏ dν − ∫ T dν| + |∫ T dν − ∫ T dμ| + |∫ T dμ − ∫ xᵏ dμ|`

small uniformly in `ν`, while the middle term converges for fixed `R` because `T = truncPow R k` is
bounded and continuous.

The exponent must be at least `1`: for `k = 0` the factor `Rᵏ` does not grow and the argument gives
nothing, though the conclusion is then trivial anyway.
-/

open scoped BigOperators
open MeasureTheory Filter

namespace HTGeometry

/-- A radius whose `k`-th power exceeds any prescribed bound, for `k ≥ 1`. -/
theorem exists_pow_gt {k : ℕ} (hk : 1 ≤ k) (c : ℝ) : ∃ R : ℝ, 0 < R ∧ c < R ^ k := by
  refine ⟨max 1 (c + 1), lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  have h1 : (1 : ℝ) ≤ max 1 (c + 1) := le_max_left _ _
  have h2 : c + 1 ≤ max 1 (c + 1) := le_max_right _ _
  have h3 : (max 1 (c + 1)) ^ 1 ≤ (max 1 (c + 1)) ^ k := pow_le_pow_right₀ h1 hk
  rw [pow_one] at h3
  linarith

/-- Three-term triangle inequality. -/
theorem abs_sub_le_three (a b c d : ℝ) : |a - d| ≤ |a - b| + |b - c| + |c - d| := by
  have h1 : |a - d| ≤ |a - b| + |b - d| := abs_sub_le a b d
  have h2 : |b - d| ≤ |b - c| + |c - d| := abs_sub_le b c d
  linarith

/-- **Moment convergence.**  Weak convergence plus a uniform bound on the even moments gives
convergence of the `k`-th moments. -/
theorem tendsto_integral_pow_of_uniform_even_moment
    {μ : Measure ℝ} {νs : ℕ → Measure ℝ} {k : ℕ} (hk : 1 ≤ k) {M : ℝ}
    (hweak : ∀ f : BoundedContinuousFunction ℝ ℝ,
      Tendsto (fun i => ∫ x, f x ∂(νs i)) atTop (nhds (∫ x, f x ∂μ)))
    (hMν : ∀ᶠ i in atTop, ∫ x, x ^ (2 * k) ∂(νs i) ≤ M)
    (hMμ : ∫ x, x ^ (2 * k) ∂μ ≤ M)
    (hiν : ∀ i, Integrable (fun x : ℝ => x ^ k) (νs i))
    (hiν2 : ∀ i, Integrable (fun x : ℝ => x ^ (2 * k)) (νs i))
    (hiνt : ∀ (R : ℝ), 0 < R → ∀ i : ℕ, Integrable (truncPow R k) (νs i))
    (hiμ : Integrable (fun x : ℝ => x ^ k) μ)
    (hiμ2 : Integrable (fun x : ℝ => x ^ (2 * k)) μ)
    (hiμt : ∀ R : ℝ, 0 < R → Integrable (truncPow R k) μ) :
    Tendsto (fun i => ∫ x, x ^ k ∂(νs i)) atTop (nhds (∫ x, x ^ k ∂μ)) := by
  refine Metric.tendsto_atTop.mpr fun ε hε => ?_
  obtain ⟨R, hR, hRc⟩ := exists_pow_gt hk (8 * M / ε)
  have hRk : (0 : ℝ) < R ^ k := pow_pos hR k
  have hkey : 2 * M / R ^ k < ε / 4 := by
    rw [div_lt_iff₀ hRk]
    rw [div_lt_iff₀ hε] at hRc
    nlinarith [hRk, hε]
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp (hweak (truncPowBCF R hR.le k)) (ε / 2) (by linarith)
  obtain ⟨N2, hN2⟩ := Filter.eventually_atTop.mp hMν
  refine ⟨max N N2, fun i hi => ?_⟩
  have hiN : N ≤ i := le_of_max_le_left hi
  have hiN2 : N2 ≤ i := le_of_max_le_right hi
  have hmid : |(∫ x, truncPow R k x ∂(νs i)) - ∫ x, truncPow R k x ∂μ| < ε / 2 := by
    have h := hN i hiN
    rw [Real.dist_eq] at h
    simpa using h
  have hbν : |(∫ x, x ^ k ∂(νs i)) - ∫ x, truncPow R k x ∂(νs i)|
      ≤ 2 * (∫ x, x ^ (2 * k) ∂(νs i)) / R ^ k :=
    abs_integral_sub_integral_truncPow_le hR k (hiν i) (hiνt R hR i) (hiν2 i)
  have hbμ : |(∫ x, x ^ k ∂μ) - ∫ x, truncPow R k x ∂μ|
      ≤ 2 * (∫ x, x ^ (2 * k) ∂μ) / R ^ k :=
    abs_integral_sub_integral_truncPow_le hR k hiμ (hiμt R hR) hiμ2
  have hbν' : 2 * (∫ x, x ^ (2 * k) ∂(νs i)) / R ^ k ≤ 2 * M / R ^ k := by
    gcongr
    exact hN2 i hiN2
  have hbμ' : 2 * (∫ x, x ^ (2 * k) ∂μ) / R ^ k ≤ 2 * M / R ^ k := by
    gcongr
  have hswap : |(∫ x, truncPow R k x ∂μ) - ∫ x, x ^ k ∂μ|
      = |(∫ x, x ^ k ∂μ) - ∫ x, truncPow R k x ∂μ| := abs_sub_comm _ _
  rw [Real.dist_eq]
  calc |(∫ x, x ^ k ∂(νs i)) - ∫ x, x ^ k ∂μ|
      ≤ |(∫ x, x ^ k ∂(νs i)) - ∫ x, truncPow R k x ∂(νs i)|
        + |(∫ x, truncPow R k x ∂(νs i)) - ∫ x, truncPow R k x ∂μ|
        + |(∫ x, truncPow R k x ∂μ) - ∫ x, x ^ k ∂μ| := abs_sub_le_three _ _ _ _
    _ < ε := by
        rw [hswap]
        linarith

end HTGeometry
