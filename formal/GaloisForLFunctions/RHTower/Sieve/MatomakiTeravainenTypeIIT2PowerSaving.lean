import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenTypeIIDyadicBudget

namespace RHTower.Sieve

open Finset Filter Topology

noncomputable section

/-! This module closes the `T₂` amplitude-energy branch of Matomäki--Teräväinen Proposition 4.2
from literal divisor-bounded coefficients and the paper's Type-II scale data. Raising degrees,
coefficient energy, Huxley windows, amplitude cells, dyadic grid height, and every finite loss are
selected or absorbed internally. -/

/-- Literal Type-II data yields the full `T₂` power saving. No coefficient-energy, raised-degree,
cell-count, grid-size, logarithmic-correction, or finite-budget premise remains. -/
theorem exists_matomakiTeravainen_typeII_T2_power_saving_divisor_bounded
    {eps mu eta tau sigma₀ Cprod C₁ C₂ : ℝ}
    (heps : 0 < eps) (hepss : eps ≤ 1 / 4000)
    (hmu : 0 < mu) (hmulo : 3 * eps ≤ mu)
    (hmuhi : mu ≤ (9 : ℝ) / 11 - 10 * eps)
    (heta : 0 < eta)
    (htau : 5 * eps + eps ^ 2 / 20 ≤ tau)
    (hcap : sigma₀ + eta + eps ^ 2 / 20 ≤ 7 / 32 - 5 * eps)
    (hCprod : 1 ≤ Cprod) (hC₁ : 1 ≤ C₁) (hC₂ : 1 ≤ C₂)
    (k w₁ w₂ : ℕ) :
    ∃ T₀ : ℝ, 1 ≤ T₀ ∧
      ∀ (T : ℝ)
        (N₁ A₁ : ℕ) (a₁ : Fin N₁ → ℂ)
        (N₂ A₂ : ℕ) (a₂ : Fin N₂ → ℂ)
        (S : Finset ℝ),
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
      (∀ q ∈ S, T⁻¹ ≤ matomakiTeravainenDirichletAmplitude N₁ a₁ q) →
      (∀ q ∈ S, T⁻¹ ≤ matomakiTeravainenDirichletAmplitude N₂ a₂ q) →
      (∀ q ∈ S, matomakiTeravainenDirichletAmplitude N₁ a₁ q ≤ 1) →
      (∀ q ∈ S, matomakiTeravainenDirichletAmplitude N₂ a₂ q ≤ 1) →
      (∀ q ∈ S,
        matomakiTeravainenDirichletAmplitude N₁ a₁ q < (A₁ : ℝ) ^ (-tau)) →
      (∀ q ∈ S,
        matomakiTeravainenDirichletAmplitude N₂ a₂ q < (A₂ : ℝ) ^ (-tau)) →
      (∀ q ∈ S,
        (A₁ : ℝ) ^ (-sigma₀) ≤ matomakiTeravainenDirichletAmplitude N₁ a₁ q ∨
        (A₂ : ℝ) ^ (-sigma₀) ≤ matomakiTeravainenDirichletAmplitude N₂ a₂ q) →
      (∀ x ∈ S, ∀ y ∈ S, x ≠ y → 1 ≤ |x - y|) →
      (∀ x ∈ S, ∀ y ∈ S, |x - y| ≤ 2 * T) →
      ∑ q ∈ S,
        matomakiTeravainenDirichletAmplitude N₁ a₁ q ^ 2 *
          matomakiTeravainenDirichletAmplitude N₂ a₂ q ^ 2 ≤
            T ^ (-(eps ^ 2 / 20)) := by
  let L : ℕ := ⌈1 / mu⌉₊
  obtain ⟨Tcell, hTcell, hcell⟩ :=
    exists_matomakiTeravainen_typeII_selected_cell_counts_divisor_bounded
      heps hepss hmu hmulo hmuhi heta htau hcap (lt_of_lt_of_le zero_lt_one hCprod)
      hC₁ hC₂ k w₁ w₂
  obtain ⟨Tcorr, hTcorr, hcorr⟩ :=
    exists_matomakiTeravainen_dyadic_log_correction hmu heta
  obtain ⟨Tprod, hTprod, hprodWindow⟩ :=
    exists_matomakiTeravainen_polylog_product_window
      (lt_of_lt_of_le zero_lt_one hCprod) heps k
  have hgridConstant : 0 ≤ matomakiTeravainenDyadicGridConstant ^ 2 := sq_nonneg _
  have hbudgetEvent := eventually_matomakiTeravainen_typeII_dyadic_budget
    (sigma₀ := sigma₀) (eta := eta) (C := (L + 1 : ℝ))
    (Cprod := Cprod) (Cgrid := matomakiTeravainenDyadicGridConstant ^ 2)
    heps (by positivity) hCprod hgridConstant k 2
  obtain ⟨Tbudget, hbudget⟩ := eventually_atTop.1 hbudgetEvent
  let T₀ : ℝ := max 2 (max Tcell (max Tcorr (max Tprod Tbudget)))
  refine ⟨T₀, le_trans (by norm_num) (le_max_left _ _), ?_⟩
  intro T N₁ A₁ a₁ N₂ A₂ a₂ S hT
    hN₁ hNA₁ hN₂ hNA₂ hA₁ hA₂ hA₁mu hA₁hi hprodLo hprodHi
    hpoint₁ hpoint₂ hsupp₁ hsupp₂ hlow₁ hlow₂ hF₁one hF₂one
    hupper₁ hupper₂ hlarge hsep hspread
  let F₁ : ℝ → ℝ := matomakiTeravainenDirichletAmplitude N₁ a₁
  let F₂ : ℝ → ℝ := matomakiTeravainenDirichletAmplitude N₂ a₂
  let V : ℝ := T⁻¹
  let J : ℕ := matomakiTeravainenDyadicHeight T
  let K : ℝ := Cprod * (1 + |Real.log T|) ^ k
  have hT2 : 2 ≤ T := le_trans (le_max_left _ _) hT
  have hT1 : 1 ≤ T := by linarith
  have hTgt : 1 < T := by linarith
  have hT0 : 0 < T := lt_of_lt_of_le zero_lt_one hT1
  have hTcellT : Tcell ≤ T :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hT
  have hTcorrT : Tcorr ≤ T :=
    le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _))
      (le_max_right _ _)) hT
  have hTprodT : Tprod ≤ T :=
    le_trans (le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _))
      (le_max_right _ _)) (le_max_right _ _)) hT
  have hTbudgetT : Tbudget ≤ T :=
    le_trans (le_trans (le_trans (le_trans (le_max_right _ _) (le_max_right _ _))
      (le_max_right _ _)) (le_max_right _ _)) hT
  have hP : 1 ≤ 1 + |Real.log T| := by linarith [abs_nonneg (Real.log T)]
  have hK : 1 ≤ K := by
    dsimp only [K]
    calc
      (1 : ℝ) = 1 * 1 := by ring
      _ ≤ Cprod * (1 + |Real.log T|) ^ k :=
        mul_le_mul hCprod (one_le_pow₀ hP) (by norm_num) (by linarith)
  have hK0 : 0 < K := lt_of_lt_of_le zero_lt_one hK
  have hTprod : T ≤ K * ((A₁ : ℝ) * (A₂ : ℝ)) := by
    have hprodLo' : T / K ≤ (A₁ : ℝ) * (A₂ : ℝ) := by
      simpa only [K] using hprodLo
    have h := (div_le_iff₀ hK0).1 hprodLo'
    simpa only [mul_comm] using h
  have hV : 0 < V := by dsimp only [V]; positivity
  have hterminal : 1 < (2 : ℝ) ^ J * V := by
    have hpow := lt_two_pow_matomakiTeravainenDyadicHeight hT1
    dsimp only [J, V]
    calc
      (1 : ℝ) = T * T⁻¹ := by field_simp
      _ < (2 : ℝ) ^ matomakiTeravainenDyadicHeight T * T⁻¹ :=
        mul_lt_mul_of_pos_right hpow (inv_pos.mpr hT0)
  have hhigh₁ : ∀ q ∈ S, F₁ q < (2 : ℝ) ^ J * V := by
    intro q hq
    exact (hF₁one q hq).trans_lt hterminal
  have hhigh₂ : ∀ q ∈ S, F₂ q < (2 : ℝ) ^ J * V := by
    intro q hq
    exact (hF₂one q hq).trans_lt hterminal
  have hcount := hcell T N₁ A₁ a₁ N₂ A₂ a₂ S V V J J hTcellT
    hN₁ hNA₁ hN₂ hNA₂ hA₁ hA₂ hA₁mu hA₁hi hprodLo hprodHi
    hpoint₁ hpoint₂ hsupp₁ hsupp₂ hV hV hF₁one hF₂one
    hupper₁ hupper₂ hlarge hsep hspread
  have hcorr₁ := hcorr T (A₁ : ℝ) hTcorrT hA₁ hA₁mu
  have hprodPowerWindow := hprodWindow T ((A₁ : ℝ) * (A₂ : ℝ))
    hTprodT hprodLo hprodHi
  have hlongWindow := matomakiTeravainen_typeII_long_factor_window
    hTgt (by positivity : 0 < (A₁ : ℝ))
    hprodPowerWindow.1 hprodPowerWindow.2
    hA₁mu hA₁hi (by linarith) (by linarith)
  have hA₂mu : T ^ mu ≤ (A₂ : ℝ) :=
    (Real.rpow_le_rpow_of_exponent_le hT1 hmuhi).trans hlongWindow.1
  have hcorr₂ := hcorr T (A₂ : ℝ) hTcorrT hA₂ hA₂mu
  have hcorrMax :
      max (Real.log 2 / Real.log (A₁ : ℝ))
        (Real.log 2 / Real.log (A₂ : ℝ)) ≤ eta := max_le hcorr₁ hcorr₂
  have hcard :=
    card_matomakiTeravainenActiveAmplitudeIndices_dyadicHeight_le_polylog
      S F₁ F₂ V V hT1
  have hdelta : (eps ^ 2 / 10) / 2 = eps ^ 2 / 20 := by ring
  have hbudgetFinal :
      ((matomakiTeravainenActiveAmplitudeIndices S F₁ F₂ V V J J).card : ℝ) *
          (16 * (L + 1 : ℝ) * K ^ (2 * (sigma₀ +
            max (Real.log 2 / Real.log (A₁ : ℝ))
              (Real.log 2 / Real.log (A₂ : ℝ))))) ≤
        T ^ ((eps ^ 2 / 10) / 2) := by
    have hb := hbudget T hTbudgetT
      (I := ((matomakiTeravainenActiveAmplitudeIndices S F₁ F₂ V V J J).card : ℝ))
      (corr := max (Real.log 2 / Real.log (A₁ : ℝ))
        (Real.log 2 / Real.log (A₂ : ℝ))) (by positivity) (by simpa [J] using hcard) hcorrMax
    rw [hdelta]
    simpa only [K] using hb
  have hresult := matomakiTeravainen_typeII_T2_dyadic_cover_power_saving
    (S := S) (F₁ := F₁) (F₂ := F₂) (T := T) (M₁ := (A₁ : ℝ)) (M₂ := (A₂ : ℝ))
    (K := K) (V₁ := V) (V₂ := V) (sigma₀ := sigma₀) (delta := eps ^ 2 / 10)
    (C := (L + 1 : ℝ)) (J₁ := J) (J₂ := J)
    hT0 hA₁ hA₂ hK hTprod hV hV
    (by intro q; exact norm_nonneg _) (by intro q; exact norm_nonneg _)
    hF₁one hF₂one
    (by simpa only [F₁, V] using hlow₁) (by simpa only [F₂, V] using hlow₂)
    hhigh₁ hhigh₂ hlarge (by positivity) hcount hbudgetFinal
  simpa only [F₁, F₂, hdelta] using hresult

end

end RHTower.Sieve
