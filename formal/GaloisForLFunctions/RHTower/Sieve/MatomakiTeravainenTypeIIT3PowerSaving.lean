import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenTypeIIT1TwoBlockEnergy
import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenTypeIIPartition
import GaloisForLFunctions.RHTower.Sieve.HuxleyExplicitLargeValues
import GaloisForLFunctions.RHTower.Sieve.PolylogRpowDomination

namespace RHTower.Sieve

open Finset Filter Topology

noncomputable section

/-- Exact `T₃` estimate with separate pointwise square envelopes for the two factors. -/
theorem matomakiTeravainen_typeII_T3_energy_of_sq_bounds
    {α : Type*} {S : Finset α} {F₁ F₂ : α → ℝ} {T K₁ K₂ : ℝ}
    (hT : 0 < T)
    (hF₁0 : ∀ q ∈ S, 0 ≤ F₁ q) (hF₂0 : ∀ q ∈ S, 0 ≤ F₂ q)
    (hK₁ : 0 ≤ K₁) (hK₂ : 0 ≤ K₂)
    (hF₁sq : ∀ q ∈ S, F₁ q ^ 2 ≤ K₁)
    (hF₂sq : ∀ q ∈ S, F₂ q ^ 2 ≤ K₂)
    (hsmall : ∀ q ∈ S, F₁ q ≤ T ^ (-(1 : ℝ)) ∨ F₂ q ≤ T ^ (-(1 : ℝ))) :
    ∑ q ∈ S, F₁ q ^ 2 * F₂ q ^ 2 ≤
      (S.card : ℝ) * T ^ (-(2 : ℝ)) * (K₁ + K₂) := by
  have hTinv0 : 0 ≤ T ^ (-(1 : ℝ)) := Real.rpow_nonneg hT.le _
  have hTinv20 : 0 ≤ T ^ (-(2 : ℝ)) := Real.rpow_nonneg hT.le _
  have hinvSq : (T ^ (-(1 : ℝ))) ^ 2 = T ^ (-(2 : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hT.le]
    congr 1
    norm_num
  have hpoint : ∀ q ∈ S,
      F₁ q ^ 2 * F₂ q ^ 2 ≤ T ^ (-(2 : ℝ)) * (K₁ + K₂) := by
    intro q hq
    rcases hsmall q hq with hsmall₁ | hsmall₂
    · have hsquare : F₁ q ^ 2 ≤ T ^ (-(2 : ℝ)) := by
        rw [← hinvSq]
        exact pow_le_pow_left₀ (hF₁0 q hq) hsmall₁ 2
      calc
        F₁ q ^ 2 * F₂ q ^ 2 ≤ T ^ (-(2 : ℝ)) * K₂ :=
          mul_le_mul hsquare (hF₂sq q hq) (sq_nonneg _) hTinv20
        _ ≤ T ^ (-(2 : ℝ)) * (K₁ + K₂) := by
          gcongr
          linarith
    · have hsquare : F₂ q ^ 2 ≤ T ^ (-(2 : ℝ)) := by
        rw [← hinvSq]
        exact pow_le_pow_left₀ (hF₂0 q hq) hsmall₂ 2
      calc
        F₁ q ^ 2 * F₂ q ^ 2 ≤ K₁ * T ^ (-(2 : ℝ)) :=
          mul_le_mul (hF₁sq q hq) hsquare (sq_nonneg _) hK₁
        _ = T ^ (-(2 : ℝ)) * K₁ := by ring
        _ ≤ T ^ (-(2 : ℝ)) * (K₁ + K₂) := by
          gcongr
          linarith
  calc
    ∑ q ∈ S, F₁ q ^ 2 * F₂ q ^ 2
        ≤ ∑ _q ∈ S, T ^ (-(2 : ℝ)) * (K₁ + K₂) :=
      Finset.sum_le_sum hpoint
    _ = (S.card : ℝ) * T ^ (-(2 : ℝ)) * (K₁ + K₂) := by
      simp [mul_assoc]

/-- Pairwise one-spacing and diameter `2T` reduce `T₃` to a square-envelope budget. -/
theorem matomakiTeravainen_typeII_T3_power_saving_of_sq_bounds
    {S : Finset ℝ} {F₁ F₂ : ℝ → ℝ} {T K₁ K₂ : ℝ}
    (hT : 1 ≤ T)
    (hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → 1 ≤ |x - y|)
    (hspread : ∀ x ∈ S, ∀ y ∈ S, |x - y| ≤ 2 * T)
    (hF₁0 : ∀ q ∈ S, 0 ≤ F₁ q) (hF₂0 : ∀ q ∈ S, 0 ≤ F₂ q)
    (hK₁ : 0 ≤ K₁) (hK₂ : 0 ≤ K₂)
    (hF₁sq : ∀ q ∈ S, F₁ q ^ 2 ≤ K₁)
    (hF₂sq : ∀ q ∈ S, F₂ q ^ 2 ≤ K₂)
    (hsmall : ∀ q ∈ S, F₁ q ≤ T ^ (-(1 : ℝ)) ∨ F₂ q ≤ T ^ (-(1 : ℝ)))
    (henvelope : 3 * (K₁ + K₂) ≤ T ^ ((1 : ℝ) / 2)) :
    ∑ q ∈ S, F₁ q ^ 2 * F₂ q ^ 2 ≤ T ^ (-(1 : ℝ) / 2) := by
  have hTpos : 0 < T := zero_lt_one.trans_le hT
  have hcard := card_le_of_pairwise_spread (by norm_num : (0 : ℝ) < 1)
    (by positivity : 0 ≤ 2 * T) S hsep hspread
  have hcard3 : (S.card : ℝ) ≤ 3 * T := by
    norm_num at hcard
    linarith
  have hbase := matomakiTeravainen_typeII_T3_energy_of_sq_bounds hTpos
    hF₁0 hF₂0 hK₁ hK₂ hF₁sq hF₂sq hsmall
  have hKsum0 : 0 ≤ K₁ + K₂ := add_nonneg hK₁ hK₂
  calc
    ∑ q ∈ S, F₁ q ^ 2 * F₂ q ^ 2
        ≤ (S.card : ℝ) * T ^ (-(2 : ℝ)) * (K₁ + K₂) := hbase
    _ ≤ (3 * T) * T ^ (-(2 : ℝ)) * (K₁ + K₂) := by gcongr
    _ = T ^ (-(1 : ℝ)) * (3 * (K₁ + K₂)) := by
      have hprod : T * T ^ (-(2 : ℝ)) = T ^ (-(1 : ℝ)) := by
        calc
          T * T ^ (-(2 : ℝ)) = T ^ (1 : ℝ) * T ^ (-(2 : ℝ)) := by
            rw [Real.rpow_one]
          _ = T ^ ((1 : ℝ) + (-(2 : ℝ))) :=
            (Real.rpow_add hTpos (1 : ℝ) (-(2 : ℝ))).symm
          _ = T ^ (-(1 : ℝ)) := by norm_num
      calc
        3 * T * T ^ (-(2 : ℝ)) * (K₁ + K₂) =
            3 * (T * T ^ (-(2 : ℝ))) * (K₁ + K₂) := by ring
        _ = T ^ (-(1 : ℝ)) * (3 * (K₁ + K₂)) := by rw [hprod]; ring
    _ ≤ T ^ (-(1 : ℝ)) * T ^ ((1 : ℝ) / 2) := by
      gcongr
    _ = T ^ (-(1 : ℝ) / 2) := by
      rw [← Real.rpow_add hTpos]
      congr 1
      ring

/-- Literal divisor-bounded data closes `T₃`: pairwise spacing supplies cardinality, the exact
two-block Cauchy bound supplies fixed-polylog pointwise envelopes, and eventual domination absorbs
those envelopes into the published `T^{-1/2}` saving. -/
theorem exists_matomakiTeravainen_typeII_T3_power_saving_divisor_bounded
    {C₁ C₂ : ℝ} (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) (w₁ w₂ : ℕ) :
    ∃ T₀ : ℝ, 1 ≤ T₀ ∧
      ∀ (T : ℝ)
        (N₁ A₁ : ℕ) (a₁ : Fin N₁ → ℂ)
        (N₂ A₂ : ℕ) (a₂ : Fin N₂ → ℂ)
        (S : Finset ℝ),
      T₀ ≤ T →
      1 ≤ N₁ → N₁ ≤ 2 * A₁ → (A₁ : ℝ) ≤ T →
      1 ≤ N₂ → N₂ ≤ 2 * A₂ → (A₂ : ℝ) ≤ T →
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
      (∀ q ∈ S,
        matomakiTeravainenDirichletAmplitude N₁ a₁ q ≤ T ^ (-(1 : ℝ)) ∨
        matomakiTeravainenDirichletAmplitude N₂ a₂ q ≤ T ^ (-(1 : ℝ))) →
      ∑ q ∈ S,
        matomakiTeravainenDirichletAmplitude N₁ a₁ q ^ 2 *
          matomakiTeravainenDirichletAmplitude N₂ a₂ q ^ 2 ≤
        T ^ (-(1 : ℝ) / 2) := by
  let E₁ : ℕ := 2 ^ (2 * (w₁ + 1)) - 1
  let E₂ : ℕ := 2 ^ (2 * (w₂ + 1)) - 1
  let D₁ : ℝ := 24 * C₁ ^ 2 * 2 ^ E₁
  let D₂ : ℝ := 24 * C₂ ^ 2 * 2 ^ E₂
  have hdom₁ := eventually_const_mul_rpow_polylog_le_rpow
    (C := D₁) (α := (0 : ℝ)) (β := (1 : ℝ) / 4) E₁ (by norm_num)
  have hdom₂ := eventually_const_mul_rpow_polylog_le_rpow
    (C := D₂) (α := (0 : ℝ)) (β := (1 : ℝ) / 4) E₂ (by norm_num)
  obtain ⟨T₁, hT₁⟩ := eventually_atTop.1 hdom₁
  obtain ⟨T₂, hT₂⟩ := eventually_atTop.1 hdom₂
  let T₀ : ℝ := max 16 (max T₁ T₂)
  refine ⟨T₀, le_trans (by norm_num) (le_max_left _ _), ?_⟩
  intro T N₁ A₁ a₁ N₂ A₂ a₂ S hT hN₁ hNA₁ hA₁T hN₂ hNA₂ hA₂T
    hpoint₁ hpoint₂ hsupp₁ hsupp₂ hsep hspread hsmall
  have hT16 : 16 ≤ T := (le_max_left _ _).trans hT
  have hTone : 1 ≤ T := by linarith
  have hTpos : 0 < T := zero_lt_one.trans_le hTone
  have hdomT₁ := hT₁ T ((le_trans (le_max_left _ _) (le_max_right _ _)).trans hT)
  have hdomT₂ := hT₂ T ((le_trans (le_max_right _ _) (le_max_right _ _)).trans hT)
  let K₁ : ℝ := 8 * C₁ ^ 2 *
    (2 * (1 + |Real.log T|)) ^ E₁
  let K₂ : ℝ := 8 * C₂ ^ 2 *
    (2 * (1 + |Real.log T|)) ^ E₂
  have hK₁ : 0 ≤ K₁ := by dsimp only [K₁]; positivity
  have hK₂ : 0 ≤ K₂ := by dsimp only [K₂]; positivity
  have hthreeK₁ : 3 * K₁ ≤ T ^ ((1 : ℝ) / 4) := by
    have hrewrite : 3 * K₁ = D₁ * T ^ (0 : ℝ) * (1 + |Real.log T|) ^ E₁ := by
      dsimp only [K₁, D₁]
      rw [mul_pow]
      norm_num
      ring
    rw [hrewrite]
    exact hdomT₁
  have hthreeK₂ : 3 * K₂ ≤ T ^ ((1 : ℝ) / 4) := by
    have hrewrite : 3 * K₂ = D₂ * T ^ (0 : ℝ) * (1 + |Real.log T|) ^ E₂ := by
      dsimp only [K₂, D₂]
      rw [mul_pow]
      norm_num
      ring
    rw [hrewrite]
    exact hdomT₂
  have hquarterTwo : 2 ≤ T ^ ((1 : ℝ) / 4) := by
    have h16pow : (16 : ℝ) ^ ((1 : ℝ) / 4) ≤ T ^ ((1 : ℝ) / 4) :=
      Real.rpow_le_rpow (by norm_num) hT16 (by norm_num)
    norm_num at h16pow ⊢
    exact h16pow
  have henvelope : 3 * (K₁ + K₂) ≤ T ^ ((1 : ℝ) / 2) := by
    have hsum : 3 * (K₁ + K₂) ≤ 2 * T ^ ((1 : ℝ) / 4) := by linarith
    have hsq : 2 * T ^ ((1 : ℝ) / 4) ≤
        T ^ ((1 : ℝ) / 4) * T ^ ((1 : ℝ) / 4) := by
      nlinarith [Real.rpow_nonneg hTpos.le ((1 : ℝ) / 4)]
    calc
      3 * (K₁ + K₂) ≤ 2 * T ^ ((1 : ℝ) / 4) := hsum
      _ ≤ T ^ ((1 : ℝ) / 4) * T ^ ((1 : ℝ) / 4) := hsq
      _ = T ^ ((1 : ℝ) / 2) := by
        rw [← Real.rpow_add hTpos]
        congr 1
        ring
  apply matomakiTeravainen_typeII_T3_power_saving_of_sq_bounds hTone hsep hspread
    (fun q _hq => norm_nonneg _) (fun q _hq => norm_nonneg _) hK₁ hK₂
    (fun q _hq => by
      dsimp only [K₁, E₁]
      exact matomakiTeravainen_dirichletAmplitude_sq_le_polylog
        hTone hC₁ N₁ A₁ w₁ hN₁ hNA₁ hA₁T a₁ hpoint₁ hsupp₁ q)
    (fun q _hq => by
      dsimp only [K₂, E₂]
      exact matomakiTeravainen_dirichletAmplitude_sq_le_polylog
        hTone hC₂ N₂ A₂ w₂ hN₂ hNA₂ hA₂T a₂ hpoint₂ hsupp₂ q)
    hsmall henvelope

end

end RHTower.Sieve
