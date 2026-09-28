import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenCoefficientEnergySchedule
import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenAmplitudeStrip

namespace RHTower.Sieve

open Finset

noncomputable section

/-- Literal divisor-bounded Type-II data supplies each active-cell Huxley count. The abstract
coefficient energies and branchwise amplitude-strip premises are discharged internally. -/
theorem exists_matomakiTeravainen_typeII_actual_cell_counts_divisor_bounded
    {eps mu eta tau sigma₀ C₁ C₂ : ℝ}
    (heps : 0 < eps) (hepss : eps ≤ 1 / 1000)
    (hmu : 0 < mu) (heta : 0 < eta)
    (htau : 5 * eps + eps ^ 2 / 20 ≤ tau)
    (hcap : sigma₀ + eta + eps ^ 2 / 20 ≤ 23 / 100 - 5 * eps)
    (hC₁ : 1 ≤ C₁) (hC₂ : 1 ≤ C₂) (w₁ w₂ L : ℕ) :
    ∃ T₀ : ℝ, 1 ≤ T₀ ∧
      ∀ (T : ℝ)
        (N₁ A₁ ell₁ : ℕ) (a₁ : Fin N₁ → ℂ)
        (N₂ A₂ ell₂ : ℕ) (a₂ : Fin N₂ → ℂ)
        (S : Finset ℝ) (V₁ V₂ : ℝ) (J₁ J₂ : ℕ),
      T₀ ≤ T →
      1 ≤ N₁ → N₁ ≤ 2 * A₁ →
      1 ≤ N₂ → N₂ ≤ 2 * A₂ →
      1 < (A₁ : ℝ) → 1 < (A₂ : ℝ) →
      0 < ell₁ → ell₁ ≤ L → 0 < ell₂ → ell₂ ≤ L →
      T ^ mu ≤ (A₁ : ℝ) → T ^ mu ≤ (A₂ : ℝ) →
      T ^ ((9 : ℝ) / 11 - 10 * eps) ≤ ((A₁ ^ ell₁ : ℕ) : ℝ) →
      ((A₁ ^ ell₁ : ℕ) : ℝ) ≤ T ^ (1 - 2 * eps) →
      T ^ ((9 : ℝ) / 11 - 10 * eps) ≤ ((A₂ ^ ell₂ : ℕ) : ℝ) →
      ((A₂ ^ ell₂ : ℕ) : ℝ) ≤ T ^ (1 - 2 * eps) →
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
  obtain ⟨Tcount, hTcount, hcount⟩ :=
    exists_matomakiTeravainen_typeII_actual_cell_counts_scheduled_energy heps hepss L
  obtain ⟨TE₁, hTE₁, henergy₁⟩ :=
    exists_matomakiTeravainen_coefficient_energy_schedule heps hC₁ w₁ L
  obtain ⟨TE₂, hTE₂, henergy₂⟩ :=
    exists_matomakiTeravainen_coefficient_energy_schedule heps hC₂ w₂ L
  obtain ⟨Tcorr, hTcorr, hcorr⟩ :=
    exists_matomakiTeravainen_dyadic_log_correction hmu heta
  let T₀ : ℝ := max Tcount (max TE₁ (max TE₂ Tcorr))
  refine ⟨T₀, ?_, ?_⟩
  · exact hTcount.trans (le_max_left _ _)
  intro T N₁ A₁ ell₁ a₁ N₂ A₂ ell₂ a₂ S V₁ V₂ J₁ J₂
    hT hN₁ hNA₁ hN₂ hNA₂ hA₁ hA₂ hell₁ hellL₁ hell₂ hellL₂
    hA₁mu hA₂mu hbaseLo₁ hbaseHi₁ hbaseLo₂ hbaseHi₂
    hpoint₁ hpoint₂ hsupp₁ hsupp₂ hV₁ hV₂ hF₁one hF₂one
    hupper₁ hupper₂ hlarge hsep hspread
  have hTc : Tcount ≤ T := le_trans (le_max_left _ _) hT
  have hTE₁T : TE₁ ≤ T :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hT
  have hTE₂T : TE₂ ≤ T :=
    le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _))
      (le_max_right _ _)) hT
  have hTcorrT : Tcorr ≤ T :=
    le_trans (le_trans (le_trans (le_max_right _ _) (le_max_right _ _))
      (le_max_right _ _)) hT
  obtain ⟨Q₁, hQ₁, hQ₁3, hE₁⟩ :=
    henergy₁ T N₁ A₁ ell₁ a₁ hTE₁T hN₁ hNA₁ hell₁ hellL₁
      hA₁ hbaseHi₁ hpoint₁
  obtain ⟨Q₂, hQ₂, hQ₂3, hE₂⟩ :=
    henergy₂ T N₂ A₂ ell₂ a₂ hTE₂T hN₂ hNA₂ hell₂ hellL₂
      hA₂ hbaseHi₂ hpoint₂
  have hcorr₁ := hcorr T (A₁ : ℝ) hTcorrT hA₁ hA₁mu
  have hcorr₂ := hcorr T (A₂ : ℝ) hTcorrT hA₂ hA₂mu
  have hcorrMax :
      max (Real.log 2 / Real.log (A₁ : ℝ))
          (Real.log 2 / Real.log (A₂ : ℝ)) ≤ eta := max_le hcorr₁ hcorr₂
  have hstrip : ∀ ij ∈ matomakiTeravainenActiveAmplitudeIndices S
      (matomakiTeravainenDirichletAmplitude N₁ a₁)
      (matomakiTeravainenDirichletAmplitude N₂ a₂) V₁ V₂ J₁ J₂,
      (matomakiTeravainenAmplitudeSigma (A₁ : ℝ) V₁ ij.1 ≤
          matomakiTeravainenAmplitudeSigma (A₂ : ℝ) V₂ ij.2 →
        5 * eps + eps ^ 2 / 20 ≤
            matomakiTeravainenAmplitudeSigma (A₁ : ℝ) V₁ ij.1 ∧
          matomakiTeravainenAmplitudeSigma (A₁ : ℝ) V₁ ij.1 + eps ^ 2 / 20 ≤
            23 / 100 - 5 * eps) ∧
      (matomakiTeravainenAmplitudeSigma (A₂ : ℝ) V₂ ij.2 <
          matomakiTeravainenAmplitudeSigma (A₁ : ℝ) V₁ ij.1 →
        5 * eps + eps ^ 2 / 20 ≤
            matomakiTeravainenAmplitudeSigma (A₂ : ℝ) V₂ ij.2 ∧
          matomakiTeravainenAmplitudeSigma (A₂ : ℝ) V₂ ij.2 + eps ^ 2 / 20 ≤
            23 / 100 - 5 * eps) := by
    intro ij hij
    exact matomakiTeravainen_active_amplitude_strip hA₁ hA₂ hV₁ hV₂
      hupper₁ hupper₂ htau hlarge hcorrMax hcap hij
  apply hcount T N₁ A₁ ell₁ Q₁ a₁ N₂ A₂ ell₂ Q₂ a₂
    S V₁ V₂ (L + 1 : ℝ) J₁ J₂ hTc hQ₁ hQ₁3 hQ₂ hQ₂3
    hA₁ hA₂ hell₁ hellL₁ hell₂ hellL₂ hV₁ hV₂ hF₁one hF₂one
    hbaseLo₁ hbaseHi₁ hbaseLo₂ hbaseHi₂
  · intro ij hij hside
    exact ((hstrip ij hij).1 hside).1
  · intro ij hij hside
    exact ((hstrip ij hij).1 hside).2
  · intro ij hij hside
    exact ((hstrip ij hij).2 hside).1
  · intro ij hij hside
    exact ((hstrip ij hij).2 hside).2
  · exact hsupp₁
  · exact hE₁
  · exact hsupp₂
  · exact hE₂
  · exact hsep
  · exact hspread
  · positivity
  · exact_mod_cast Nat.add_le_add_right hellL₁ 1
  · exact_mod_cast Nat.add_le_add_right hellL₂ 1

end

end RHTower.Sieve
