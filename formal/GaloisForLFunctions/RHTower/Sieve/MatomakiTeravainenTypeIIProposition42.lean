import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenTypeIIT1Energy
import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenTypeIIT2PowerSaving
import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenTypeIIT3PowerSaving

/-!
# Matomäki--Teräväinen Proposition 4.2: finite Type-II assembly

The three literal amplitude regimes are assembled without disjointness assumptions or hidden
asymptotic premises.  The large-values input is Jutila's Lemma 4.1 up to `σ = 23/100`
(`energyLargeValuesBound_jutila`); the middle regime keeps the explicit `T^(-eps^(2 : ℕ)/20)`
saving.
-/

namespace RHTower.Sieve

open Finset

noncomputable section

/-- Proposition 4.2 for divisor-bounded dyadic Dirichlet factors, amplitude thresholds up to
`23/100 - 5ε`. The conclusion keeps the exact `T₁` polylogarithmic term and the separate `T₂`,
`T₃` power savings. -/
theorem exists_matomakiTeravainen_typeII_proposition42
    {eps mu eta sigma₀ Cprod C₁ C₂ : ℝ}
    (heps : 0 < eps) (hepss : eps ≤ 1 / 4000)
    (hmu : 0 < mu) (hmulo : 3 * eps ≤ mu)
    (hmuhi : mu ≤ (9 : ℝ) / 11 - 10 * eps)
    (heta : 0 < eta)
    (hcap : sigma₀ + eta + eps ^ 2 / 20 ≤ 23 / 100 - 5 * eps)
    (hCprod : 1 ≤ Cprod) (hC₁ : 1 ≤ C₁) (hC₂ : 1 ≤ C₂)
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
      (∀ q ∈ S, matomakiTeravainenDirichletAmplitude N₁ a₁ q ≤ 1) →
      (∀ q ∈ S, matomakiTeravainenDirichletAmplitude N₂ a₂ q ≤ 1) →
      (∀ q ∈ S,
        (A₁ : ℝ) ^ (-sigma₀) ≤ matomakiTeravainenDirichletAmplitude N₁ a₁ q ∨
        (A₂ : ℝ) ^ (-sigma₀) ≤ matomakiTeravainenDirichletAmplitude N₂ a₂ q) →
      (∀ x ∈ S, ∀ y ∈ S, x ≠ y → 1 ≤ |x - y|) →
      (∀ x ∈ S, ∀ y ∈ S, |x - y| ≤ 2 * T) →
      (∀ q ∈ S, matomakiTeravainenDirichletAmplitude N₁ a₁ q ≤ B₁) →
      ∑ q ∈ S,
        matomakiTeravainenDirichletAmplitude N₁ a₁ q ^ 2 *
          matomakiTeravainenDirichletAmplitude N₂ a₂ q ^ 2 ≤
        16384 * B₁ ^ 2 * (1 + |Real.log T|) * C₂ ^ 2 *
            (2 * (1 + |Real.log T|)) ^ (2 ^ (2 * (w₂ + 1)) - 1) +
          T ^ (-(eps ^ 2 / 20)) + T ^ (-(1 : ℝ) / 2) := by
  obtain ⟨Tlarge, hTlarge, hlargeEnergy⟩ :=
    exists_matomakiTeravainen_typeII_T1_energy_divisor_bounded
      heps hepss hmu hmulo hmuhi (zero_lt_one.trans_le hCprod) hC₁ hC₂ k w₁ w₂
  have htau : 5 * eps + eps ^ 2 / 20 ≤ 10 * eps := by
    nlinarith [sq_nonneg eps]
  obtain ⟨Tmiddle, hTmiddle, hmiddleEnergy⟩ :=
    exists_matomakiTeravainen_typeII_T2_power_saving_divisor_bounded
      heps hepss hmu hmulo hmuhi heta htau hcap hCprod hC₁ hC₂ k w₁ w₂
  obtain ⟨Tsmall, hTsmall, hsmallEnergy⟩ :=
    exists_matomakiTeravainen_typeII_T3_power_saving_divisor_bounded
      (zero_le_one.trans hC₁) (zero_le_one.trans hC₂) w₁ w₂
  obtain ⟨Tprod, hTprod, hprodWindow⟩ :=
    exists_matomakiTeravainen_polylog_product_window
      (zero_lt_one.trans_le hCprod) heps k
  let T₀ : ℝ := max 2 (max Tlarge (max Tmiddle (max Tsmall Tprod)))
  refine ⟨T₀, le_trans (by norm_num) (le_max_left _ _), ?_⟩
  intro T N₁ A₁ a₁ N₂ A₂ a₂ S B₁ hT hN₁ hNA₁ hN₂ hNA₂ hA₁ hA₂
    hA₁mu hA₁hi hprodLo hprodHi hpoint₁ hpoint₂ hsupp₁ hsupp₂
    hF₁one hF₂one hsourceLarge hsep hspread hB₁
  have hTtwo : 2 ≤ T := (le_max_left _ _).trans hT
  have hTone : 1 ≤ T := one_le_two.trans hTtwo
  have hTgt : 1 < T := one_lt_two.trans_le hTtwo
  have hTlargeT : Tlarge ≤ T :=
    ((le_max_left _ _).trans (le_max_right _ _)).trans hT
  have hTmiddleT : Tmiddle ≤ T :=
    (((le_max_left _ _).trans (le_max_right _ _)).trans
      (le_max_right _ _)).trans hT
  have hTsmallT : Tsmall ≤ T :=
    ((((le_max_left _ _).trans (le_max_right _ _)).trans
      (le_max_right _ _)).trans (le_max_right _ _)).trans hT
  have hTprodT : Tprod ≤ T :=
    ((((le_max_right _ _).trans (le_max_right _ _)).trans
      (le_max_right _ _)).trans (le_max_right _ _)).trans hT
  have hprodPower := hprodWindow T ((A₁ : ℝ) * (A₂ : ℝ)) hTprodT hprodLo hprodHi
  have hlong := matomakiTeravainen_typeII_long_factor_window
    hTgt (by positivity : 0 < (A₁ : ℝ)) hprodPower.1 hprodPower.2
    hA₁mu hA₁hi (by linarith) (by linarith)
  have hA₁T : (A₁ : ℝ) ≤ T := by
    calc
      (A₁ : ℝ) ≤ T ^ ((2 : ℝ) / 11 + 4 * eps) := hA₁hi
      _ ≤ T ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hTone (by linarith)
      _ = T := Real.rpow_one T
  have hA₂T : (A₂ : ℝ) ≤ T := by
    calc
      (A₂ : ℝ) ≤ T ^ (1 - 2 * eps) := hlong.2
      _ ≤ T ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hTone (by linarith)
      _ = T := Real.rpow_one T
  let F₁ : ℝ → ℝ := matomakiTeravainenDirichletAmplitude N₁ a₁
  let F₂ : ℝ → ℝ := matomakiTeravainenDirichletAmplitude N₂ a₂
  let S₁ := matomakiTeravainenTypeIILargeAmplitudeSet
    S N₁ A₁ a₁ N₂ A₂ a₂ (10 * eps)
  let S₃ := S.filter fun q => F₁ q < T⁻¹ ∨ F₂ q < T⁻¹
  let S₂ := S.filter fun q => q ∉ S₁ ∧ q ∉ S₃
  have hcover : S ⊆ S₁ ∪ S₂ ∪ S₃ := by
    intro q hq
    by_cases hq₁ : q ∈ S₁
    · simp [hq₁]
    by_cases hq₃ : q ∈ S₃
    · simp [hq₃]
    · simp [S₂, hq, hq₁, hq₃]
  have henergy₁ : ∑ q ∈ S₁, F₁ q ^ 2 * F₂ q ^ 2 ≤
      16384 * B₁ ^ 2 * (1 + |Real.log T|) * C₂ ^ 2 *
        (2 * (1 + |Real.log T|)) ^ (2 ^ (2 * (w₂ + 1)) - 1) := by
    simpa only [S₁, F₁, F₂] using hlargeEnergy T N₁ A₁ a₁ N₂ A₂ a₂ S B₁
      hTlargeT hN₁ hNA₁ hN₂ hNA₂ hA₁ hA₂ hA₁mu hA₁hi hprodLo hprodHi
      hpoint₁ hpoint₂ hsupp₁ hsupp₂ hsep hspread hB₁
  have henergy₂ : ∑ q ∈ S₂, F₁ q ^ 2 * F₂ q ^ 2 ≤ T ^ (-(eps ^ 2 / 20)) := by
    apply hmiddleEnergy T N₁ A₁ a₁ N₂ A₂ a₂ S₂ hTmiddleT
      hN₁ hNA₁ hN₂ hNA₂ hA₁ hA₂ hA₁mu hA₁hi hprodLo hprodHi
      hpoint₁ hpoint₂ hsupp₁ hsupp₂
    · intro q hq
      have hqS : q ∈ S := (Finset.mem_filter.1 hq).1
      have hq₃ : q ∉ S₃ := (Finset.mem_filter.1 hq).2.2
      have hnot : ¬(F₁ q < T⁻¹ ∨ F₂ q < T⁻¹) := by
        simpa [S₃, hqS] using hq₃
      simpa only [F₁] using le_of_not_gt (not_or.mp hnot).1
    · intro q hq
      have hqS : q ∈ S := (Finset.mem_filter.1 hq).1
      have hq₃ : q ∉ S₃ := (Finset.mem_filter.1 hq).2.2
      have hnot : ¬(F₁ q < T⁻¹ ∨ F₂ q < T⁻¹) := by
        simpa [S₃, hqS] using hq₃
      simpa only [F₂] using le_of_not_gt (not_or.mp hnot).2
    · intro q hq
      exact hF₁one q (Finset.mem_filter.1 hq).1
    · intro q hq
      exact hF₂one q (Finset.mem_filter.1 hq).1
    · intro q hq
      have hqS : q ∈ S := (Finset.mem_filter.1 hq).1
      have hq₁ : q ∉ S₁ := (Finset.mem_filter.1 hq).2.1
      have hnot : ¬((A₁ : ℝ) ^ (-(10 * eps)) ≤ F₁ q ∨
          (A₂ : ℝ) ^ (-(10 * eps)) ≤ F₂ q) := by
        simpa [S₁, matomakiTeravainenTypeIILargeAmplitudeSet, F₁, F₂, hqS] using hq₁
      exact lt_of_not_ge (not_or.mp hnot).1
    · intro q hq
      have hqS : q ∈ S := (Finset.mem_filter.1 hq).1
      have hq₁ : q ∉ S₁ := (Finset.mem_filter.1 hq).2.1
      have hnot : ¬((A₁ : ℝ) ^ (-(10 * eps)) ≤ F₁ q ∨
          (A₂ : ℝ) ^ (-(10 * eps)) ≤ F₂ q) := by
        simpa [S₁, matomakiTeravainenTypeIILargeAmplitudeSet, F₁, F₂, hqS] using hq₁
      exact lt_of_not_ge (not_or.mp hnot).2
    · intro q hq
      exact hsourceLarge q (Finset.mem_filter.1 hq).1
    · intro x hx y hy hxy
      exact hsep x (Finset.mem_filter.1 hx).1 y (Finset.mem_filter.1 hy).1 hxy
    · intro x hx y hy
      exact hspread x (Finset.mem_filter.1 hx).1 y (Finset.mem_filter.1 hy).1
  have henergy₃ : ∑ q ∈ S₃, F₁ q ^ 2 * F₂ q ^ 2 ≤ T ^ (-(1 : ℝ) / 2) := by
    apply hsmallEnergy T N₁ A₁ a₁ N₂ A₂ a₂ S₃ hTsmallT
      hN₁ hNA₁ hA₁T hN₂ hNA₂ hA₂T hpoint₁ hpoint₂ hsupp₁ hsupp₂
    · intro x hx y hy hxy
      exact hsep x (Finset.mem_filter.1 hx).1 y (Finset.mem_filter.1 hy).1 hxy
    · intro x hx y hy
      exact hspread x (Finset.mem_filter.1 hx).1 y (Finset.mem_filter.1 hy).1
    · intro q hq
      rcases (Finset.mem_filter.1 hq).2 with hq₁ | hq₂
      · exact Or.inl (by simpa only [F₁, Real.rpow_neg_one] using hq₁.le)
      · exact Or.inr (by simpa only [F₂, Real.rpow_neg_one] using hq₂.le)
  have hassembled := matomakiTeravainen_typeII_partition_energy
    (S := S) (S₁ := S₁) (S₂ := S₂) (S₃ := S₃)
    (w := fun q => F₁ q ^ 2 * F₂ q ^ 2) hcover
    (fun q => mul_nonneg (sq_nonneg _) (sq_nonneg _)) henergy₁ henergy₂ henergy₃
  simpa only [F₁, F₂] using hassembled

end

end RHTower.Sieve
