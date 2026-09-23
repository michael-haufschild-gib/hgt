import GaloisForLFunctions.RHTower.SigmaUniformBound

/-!
# The weighted remainder mass under the σ-contraction

Chaining the discrete Fubini, the uniform σ bound, and the scale
summatories:

`∑_{v ≤ N} |R(v)|(1/v − 1/(v+1))·(log N − log v)
   ≤ (a − g/L)·(½log²N + 1) + C₁·(log N + 2)`.

This is the σ-side estimate the fiber transfer multiplies by `2N`; the
leading coefficient `(a − g/L)·½` against the second inequality's
`½log²N` normalization is what closes the ratio recursion strictly below
`a`.
-/

noncomputable section

namespace RHTower

open ArithmeticFunction Finset

set_option maxHeartbeats 1000000 in
theorem weighted_sigma_total_le {a δ ρ κ : ℝ} {Q x₀ x₁ : ℕ}
    (ha : 0 < a) (hδ : 0 < δ) (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1 / 2)
    (hκ : 0 ≤ κ) (hQ1 : 1 ≤ Q)
    (hQ : 40 / δ + 2 < Real.log Q)
    (hx₁1 : 1 ≤ x₁) (hx₀x₁ : x₀ ≤ x₁) (hx₁ρ : 2 / ρ ≤ (x₁ : ℝ))
    (hε'a : δ + ρ * (Real.log (1 / ρ) + 3) + κ ≤ a)
    (hratio : ∀ t : ℕ, x₀ ≤ t → |psiRemainder t| ≤ a * t)
    (hjunk1 : ∀ t : ℕ, x₁ < t →
      2 * Real.sqrt t * Real.log t ≤ κ / 2 * t)
    (hbase0 : Real.log ((Q * x₁ : ℕ) : ℝ) + 1 ≤ κ / 2 * x₁)
    (hbase : Real.log ((2 * Q : ℕ) : ℝ) ≤ κ / 2 * x₁)
    {N : ℕ} (hN : 2 ≤ N) :
    ∑ v ∈ Finset.Icc 1 N, |psiRemainder v|
        * (1 / (v : ℝ) - 1 / ((v : ℝ) + 1)) * (Real.log N - Real.log v)
      ≤ (a - (a - (δ + ρ * (Real.log (1 / ρ) + 3) + κ)) * (ρ / 3)
            / Real.log ((2 * Q : ℕ) : ℝ))
          * (Real.log N ^ (2 : ℕ) / 2 + 1)
        + ((a - (δ + ρ * (Real.log (1 / ρ) + 3) + κ)) * (ρ / 3)
            + 14 * a / x₁ + 8 * (Real.log x₁ + 2))
          * (Real.log N + 2) := by
  set θc : ℝ := a - (a - (δ + ρ * (Real.log (1 / ρ) + 3) + κ)) * (ρ / 3)
    / Real.log ((2 * Q : ℕ) : ℝ) with hθc
  set C₁ : ℝ := (a - (δ + ρ * (Real.log (1 / ρ) + 3) + κ)) * (ρ / 3)
    + 14 * a / x₁ + 8 * (Real.log x₁ + 2) with hC₁
  have hθa := gain_div_log_le ha hδ hρ0 hρ1 hκ hQ1 hε'a
  have hθc0 : 0 ≤ θc := by
    rw [hθc]
    linarith
  have hg0 : 0 ≤ (a - (δ + ρ * (Real.log (1 / ρ) + 3) + κ)) * (ρ / 3) :=
    mul_nonneg (by linarith) (by linarith)
  have hlogx₁0 : 0 ≤ Real.log x₁ :=
    Real.log_nonneg (by exact_mod_cast hx₁1)
  have hC₁0 : 0 ≤ C₁ := by
    rw [hC₁]
    have : 0 ≤ 14 * a / (x₁ : ℝ) := by positivity
    linarith
  -- Fubini + reindex
  have h1 := weighted_sigma_le N
  have hreindex : ∑ t ∈ Finset.Ioc 1 N,
      (1 / ((t - 1 : ℕ) : ℝ)) * sigmaPartial (t - 1)
      = ∑ s ∈ Finset.Icc 1 (N - 1), (1 / (s : ℝ)) * sigmaPartial s := by
    apply Finset.sum_nbij' (i := fun t => t - 1) (j := fun s => s + 1)
    · intro t ht
      rw [Finset.mem_Ioc] at ht
      rw [Finset.mem_Icc]
      omega
    · intro s hs
      rw [Finset.mem_Icc] at hs
      rw [Finset.mem_Ioc]
      omega
    · intro t ht
      rw [Finset.mem_Ioc] at ht
      omega
    · intro s _
      omega
    · intro t _
      rfl
  -- per-scale uniform bound
  have huniform := sigmaPartial_le_of_ratio ha hδ hρ0 hρ1 hκ hQ1 hQ hx₁1
    hx₀x₁ hx₁ρ hε'a hratio hjunk1 hbase0 hbase
  have hterm : ∀ s ∈ Finset.Icc 1 (N - 1),
      (1 / (s : ℝ)) * sigmaPartial s
        ≤ θc * (Real.log s / s) + C₁ * (1 / s) := by
    intro s hs
    rw [Finset.mem_Icc] at hs
    have hs0 : (0 : ℝ) < s := by exact_mod_cast (by omega : 0 < s)
    have hu := huniform s hs.1
    calc (1 / (s : ℝ)) * sigmaPartial s
        ≤ (1 / (s : ℝ)) * (θc * Real.log s + C₁) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          rw [hθc, hC₁]
          linarith [hu]
      _ = θc * (Real.log s / s) + C₁ * (1 / s) := by
          field_simp
  -- scale summatories
  have hN1 : 1 ≤ N - 1 := by omega
  have hlogdiv := sum_log_div_le (N - 1) hN1
  have hinv := sum_inv_le (N - 1) hN1
  -- monotonicity to `N`
  have hmono : Real.log ((N - 1 : ℕ) : ℝ) ≤ Real.log N :=
    Real.log_le_log (by exact_mod_cast (by omega : 0 < N - 1))
      (by exact_mod_cast (by omega : N - 1 ≤ N))
  have hlog0 : 0 ≤ Real.log ((N - 1 : ℕ) : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hN1)
  have hsqmono : Real.log ((N - 1 : ℕ) : ℝ) ^ (2 : ℕ) ≤ Real.log N ^ (2 : ℕ) :=
    pow_le_pow_left₀ hlog0 hmono 2
  -- assemble
  calc ∑ v ∈ Finset.Icc 1 N, |psiRemainder v|
        * (1 / (v : ℝ) - 1 / ((v : ℝ) + 1)) * (Real.log N - Real.log v)
      ≤ ∑ t ∈ Finset.Ioc 1 N,
          (1 / ((t - 1 : ℕ) : ℝ)) * sigmaPartial (t - 1) := h1
    _ = ∑ s ∈ Finset.Icc 1 (N - 1), (1 / (s : ℝ)) * sigmaPartial s :=
        hreindex
    _ ≤ ∑ s ∈ Finset.Icc 1 (N - 1),
          (θc * (Real.log s / s) + C₁ * (1 / s)) :=
        Finset.sum_le_sum hterm
    _ = θc * ∑ s ∈ Finset.Icc 1 (N - 1), Real.log s / s
        + C₁ * ∑ s ∈ Finset.Icc 1 (N - 1), 1 / (s : ℝ) := by
        rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    _ ≤ θc * (Real.log ((N - 1 : ℕ) : ℝ) ^ (2 : ℕ) / 2 + 1)
        + C₁ * (Real.log ((N - 1 : ℕ) : ℝ) + 2) := by
        have hm1 := mul_le_mul_of_nonneg_left hlogdiv hθc0
        have hm2 := mul_le_mul_of_nonneg_left hinv hC₁0
        linarith
    _ ≤ θc * (Real.log N ^ (2 : ℕ) / 2 + 1) + C₁ * (Real.log N + 2) := by
        have hm1 : θc * (Real.log ((N - 1 : ℕ) : ℝ) ^ (2 : ℕ) / 2 + 1)
            ≤ θc * (Real.log N ^ (2 : ℕ) / 2 + 1) := by
          apply mul_le_mul_of_nonneg_left _ hθc0
          linarith
        have hm2 : C₁ * (Real.log ((N - 1 : ℕ) : ℝ) + 2)
            ≤ C₁ * (Real.log N + 2) := by
          apply mul_le_mul_of_nonneg_left _ hC₁0
          linarith
        linarith

end RHTower
