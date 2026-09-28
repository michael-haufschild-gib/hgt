import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenTypeIICellCount
import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenTypeIIWindowTransfer

namespace RHTower.Sieve

open Finset

noncomputable section

/-- Proposition 4.2 Type-II scale data internally selects the short raising degree and leaves the
long factor unraised. Fixed polylogarithmic product distortion, coefficient energy, amplitude-strip
admission, and both Huxley windows are all discharged before the active-cell count is returned. -/
theorem exists_matomakiTeravainen_typeII_selected_cell_counts_divisor_bounded
    {eps mu eta tau sigma₀ Cprod C₁ C₂ : ℝ}
    (heps : 0 < eps) (hepss : eps ≤ 1 / 4000)
    (hmu : 0 < mu) (hmulo : 3 * eps ≤ mu)
    (hmuhi : mu ≤ (9 : ℝ) / 11 - 10 * eps)
    (heta : 0 < eta)
    (htau : 5 * eps + eps ^ 2 / 20 ≤ tau)
    (hcap : sigma₀ + eta + eps ^ 2 / 20 ≤ 23 / 100 - 5 * eps)
    (hCprod : 0 < Cprod) (hC₁ : 1 ≤ C₁) (hC₂ : 1 ≤ C₂)
    (k w₁ w₂ : ℕ) :
    let L : ℕ := ⌈1 / mu⌉₊
    ∃ T₀ : ℝ, 1 ≤ T₀ ∧
      ∀ (T : ℝ)
        (N₁ A₁ : ℕ) (a₁ : Fin N₁ → ℂ)
        (N₂ A₂ : ℕ) (a₂ : Fin N₂ → ℂ)
        (S : Finset ℝ) (V₁ V₂ : ℝ) (J₁ J₂ : ℕ),
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
      0 < V₁ → 0 < V₂ →
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
      ∀ ij ∈ matomakiTeravainenActiveAmplitudeIndices S
          (matomakiTeravainenDirichletAmplitude N₁ a₁)
          (matomakiTeravainenDirichletAmplitude N₂ a₂) V₁ V₂ J₁ J₂,
        ((matomakiTeravainenAmplitudeCell S
          (matomakiTeravainenDirichletAmplitude N₁ a₁)
          (matomakiTeravainenDirichletAmplitude N₂ a₂) V₁ V₂ ij).card : ℝ) ≤
            (L + 1 : ℝ) * T ^
              (2 * min
                (matomakiTeravainenAmplitudeSigma (A₁ : ℝ) V₁ ij.1)
                (matomakiTeravainenAmplitudeSigma (A₂ : ℝ) V₂ ij.2) -
                eps ^ 2 / 10) := by
  let L : ℕ := ⌈1 / mu⌉₊
  have hL : 1 ≤ L := by
    dsimp only [L]
    exact Nat.one_le_ceil_iff.2 (by positivity)
  obtain ⟨Tcell, hTcell, hcell⟩ :=
    exists_matomakiTeravainen_typeII_actual_cell_counts_divisor_bounded
      heps (hepss.trans (by norm_num)) hmu heta htau hcap hC₁ hC₂ w₁ w₂ L
  obtain ⟨Tprod, hTprod, hprod⟩ :=
    exists_matomakiTeravainen_polylog_product_window hCprod heps k
  let T₀ : ℝ := max 2 (max Tcell Tprod)
  refine ⟨T₀, le_trans (by norm_num) (le_max_left _ _), ?_⟩
  intro T N₁ A₁ a₁ N₂ A₂ a₂ S V₁ V₂ J₁ J₂ hT
    hN₁ hNA₁ hN₂ hNA₂ hA₁ hA₂ hA₁mu hA₁hi hprodLo hprodHi
    hpoint₁ hpoint₂ hsupp₁ hsupp₂ hV₁ hV₂ hF₁one hF₂one
    hupper₁ hupper₂ hlarge hsep hspread
  have hTgt : 1 < T := lt_of_lt_of_le (by norm_num) (le_trans (le_max_left _ _) hT)
  have hTcellT : Tcell ≤ T :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hT
  have hTprodT : Tprod ≤ T :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hT
  have hprodWindow := hprod T ((A₁ : ℝ) * (A₂ : ℝ)) hTprodT hprodLo hprodHi
  have hlong := matomakiTeravainen_typeII_long_factor_window
    hTgt (by positivity : 0 < (A₁ : ℝ)) hprodWindow.1 hprodWindow.2
    hA₁mu hA₁hi (by linarith) (by linarith)
  have hA₂mu : T ^ mu ≤ (A₂ : ℝ) :=
    (Real.rpow_le_rpow_of_exponent_le hTgt.le hmuhi).trans hlong.1
  obtain ⟨ell, hell, hellL, hshortLo, hshortHi⟩ :=
    exists_pow_mem_matomakiTeravainen_huxley_window_bounded hTgt hA₁
      heps hepss hmu hA₁mu hA₁hi
  have hshortLo' : T ^ ((9 : ℝ) / 11 - 10 * eps) ≤
      ((A₁ ^ ell : ℕ) : ℝ) :=
    by
      have hpow : T ^ ((9 : ℝ) / 11 - 10 * eps) ≤ T ^ ((9 : ℝ) / 11) :=
        Real.rpow_le_rpow_of_exponent_le hTgt.le (by linarith)
      simpa only [Nat.cast_pow] using hpow.trans hshortLo
  have hshortHi' : ((A₁ ^ ell : ℕ) : ℝ) ≤ T ^ (1 - 2 * eps) := by
    simpa only [Nat.cast_pow] using hshortHi
  have hlongLo : T ^ ((9 : ℝ) / 11 - 10 * eps) ≤
      ((A₂ ^ 1 : ℕ) : ℝ) := by simpa using hlong.1
  have hlongHi : ((A₂ ^ 1 : ℕ) : ℝ) ≤ T ^ (1 - 2 * eps) := by
    simpa using hlong.2
  apply hcell T N₁ A₁ ell a₁ N₂ A₂ 1 a₂ S V₁ V₂ J₁ J₂ hTcellT
    hN₁ hNA₁ hN₂ hNA₂ hA₁ hA₂ hell hellL (by norm_num) hL
    hA₁mu hA₂mu hshortLo' hshortHi' hlongLo hlongHi
    hpoint₁ hpoint₂ hsupp₁ hsupp₂ hV₁ hV₂ hF₁one hF₂one
    hupper₁ hupper₂ hlarge hsep hspread

end

end RHTower.Sieve
