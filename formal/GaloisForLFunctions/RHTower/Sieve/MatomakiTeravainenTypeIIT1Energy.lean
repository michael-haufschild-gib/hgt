import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenTypeIIT1TwoBlockEnergy
import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenTypeIILargeSetCount

namespace RHTower.Sieve

open Finset Filter Topology

noncomputable section

/-- Full literal `T₁` contribution in Proposition 4.2. The output is the paper's fixed-polylog
multiple of the short factor's pointwise square, with no analytic premise left. -/
theorem exists_matomakiTeravainen_typeII_T1_energy_divisor_bounded
    {eps mu Cprod C₁ C₂ : ℝ}
    (heps : 0 < eps) (hepss : eps ≤ 1 / 4000)
    (hmu : 0 < mu) (hmulo : 3 * eps ≤ mu)
    (hmuhi : mu ≤ (9 : ℝ) / 11 - 10 * eps)
    (hCprod : 0 < Cprod) (hC₁ : 1 ≤ C₁) (hC₂ : 1 ≤ C₂)
    (k w₁ w₂ : ℕ) :
    ∃ T₀ : ℝ, 1 ≤ T₀ ∧
      ∀ (T : ℝ)
        (N₁ A₁ : ℕ) (a₁ : Fin N₁ → ℂ)
        (N₂ A₂ : ℕ) (a₂ : Fin N₂ → ℂ)
        (S : Finset ℝ) (B₁ : ℝ),
      T₀ ≤ T →
      1 ≤ N₁ → N₁ ≤ 2 * A₁ →
      1 ≤ N₂ → N₂ ≤ 2 * A₂ →
      1 < (A₁ : ℝ) → 1 < (A₂ : ℝ) →
      T ^ mu ≤ (A₁ : ℝ) →
      (A₁ : ℝ) ≤ T ^ ((2 : ℝ) / 11 + 4 * eps) →
      T / (Cprod * (1 + |Real.log T|) ^ k) ≤ (A₁ : ℝ) * (A₂ : ℝ) →
      (A₁ : ℝ) * (A₂ : ℝ) ≤ T * (Cprod * (1 + |Real.log T|) ^ k) →
      (∀ n : Fin N₁,
        ‖a₁ n‖ ≤ C₁ * ((((n : ℕ) + 1).divisors.card : ℝ) ^ w₁)) →
      (∀ n : Fin N₂,
        ‖a₂ n‖ ≤ C₂ * ((((n : ℕ) + 1).divisors.card : ℝ) ^ w₂)) →
      (∀ n : Fin N₁, a₁ n ≠ 0 →
        A₁ ≤ (n : ℕ) + 1 ∧ (n : ℕ) + 1 ≤ 2 * A₁) →
      (∀ n : Fin N₂, a₂ n ≠ 0 →
        A₂ ≤ (n : ℕ) + 1 ∧ (n : ℕ) + 1 ≤ 2 * A₂) →
      (∀ x ∈ S, ∀ y ∈ S, x ≠ y → 1 ≤ |x - y|) →
      (∀ x ∈ S, ∀ y ∈ S, |x - y| ≤ 2 * T) →
      (∀ t ∈ S, matomakiTeravainenDirichletAmplitude N₁ a₁ t ≤ B₁) →
      ∑ t ∈ matomakiTeravainenTypeIILargeAmplitudeSet
          S N₁ A₁ a₁ N₂ A₂ a₂ (10 * eps),
        matomakiTeravainenDirichletAmplitude N₁ a₁ t ^ 2 *
          matomakiTeravainenDirichletAmplitude N₂ a₂ t ^ 2 ≤
        16384 * B₁ ^ 2 * (1 + |Real.log T|) * C₂ ^ 2 *
          (2 * (1 + |Real.log T|)) ^ (2 ^ (2 * (w₂ + 1)) - 1) := by
  obtain ⟨Tcount, hTcount, hcount⟩ :=
    exists_matomakiTeravainen_typeII_T1_large_set_count_power
      heps hepss hmu hmulo hmuhi hCprod hC₁ hC₂ k w₁ w₂
  obtain ⟨Tprod, hTprod, hprod⟩ :=
    exists_matomakiTeravainen_polylog_product_window hCprod heps k
  let T₀ : ℝ := max 2 (max Tcount Tprod)
  refine ⟨T₀, le_trans (by norm_num) (le_max_left _ _), ?_⟩
  intro T N₁ A₁ a₁ N₂ A₂ a₂ S B₁ hT hN₁ hNA₁ hN₂ hNA₂ hA₁ hA₂
    hA₁mu hA₁hi hprodLo hprodHi hpoint₁ hpoint₂ hsupp₁ hsupp₂ hsep hspread hB₁
  have hTc : Tcount ≤ T :=
    (le_trans (le_max_left _ _) (le_max_right _ _)).trans hT
  have hTp : Tprod ≤ T :=
    (le_trans (le_max_right _ _) (le_max_right _ _)).trans hT
  have hTone : 1 ≤ T := hTcount.trans hTc
  have hTgt : 1 < T := lt_of_lt_of_le (by norm_num) ((le_max_left _ _).trans hT)
  have hprodWindow := hprod T ((A₁ : ℝ) * (A₂ : ℝ)) hTp hprodLo hprodHi
  have hlong := matomakiTeravainen_typeII_long_factor_window
    hTgt (by positivity : 0 < (A₁ : ℝ)) hprodWindow.1 hprodWindow.2
    hA₁mu hA₁hi (by linarith) (by linarith)
  have hA₂T : (A₂ : ℝ) ≤ T := by
    have hexp : 1 - 2 * eps ≤ (1 : ℝ) := by linarith
    exact hlong.2.trans (by
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hTone hexp)
  let T₁ : Finset ℝ := matomakiTeravainenTypeIILargeAmplitudeSet
    S N₁ A₁ a₁ N₂ A₂ a₂ (10 * eps)
  have hcardT₁ : (T₁.card : ℝ) ≤ T ^ (21 * eps) := by
    dsimp only [T₁]
    exact hcount T N₁ A₁ a₁ N₂ A₂ a₂ S hTc hN₁ hNA₁ hN₂ hNA₂ hA₁ hA₂
      hA₁mu hA₁hi hprodLo hprodHi hpoint₁ hpoint₂ hsupp₁ hsupp₂ hsep hspread
  have hresult := matomakiTeravainen_typeII_T1_unraised_factor_energy_divisor_bounded
    heps hepss hTone (le_trans (by norm_num) hC₂) N₂ A₂ w₂ hN₂ hNA₂ hA₂T a₂ hpoint₂ hlong.1
    hcardT₁
    (by
      intro x hx y hy hxy
      exact hsep x (Finset.mem_filter.1 hx).1 y (Finset.mem_filter.1 hy).1 hxy)
    (by
      intro x hx y hy
      exact hspread x (Finset.mem_filter.1 hx).1 y (Finset.mem_filter.1 hy).1)
    hsupp₂ (matomakiTeravainenDirichletAmplitude N₁ a₁) (B := B₁)
    (by intro t ht; exact norm_nonneg _)
    (by intro t ht; exact hB₁ t (Finset.mem_filter.1 ht).1)
  simpa only [T₁] using hresult

end

end RHTower.Sieve
