import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenRaisedSchedule

/-!
# Scheduled actual amplitude-cell counts for Matomäki--Teräväinen Proposition 4.2

This removes every block-by-block Huxley range, threshold-loss, and energy-threshold premise from
the actual two-factor cell theorem.  The sole scalar inputs are source windows for the two raised
lower edges, a fixed raising cap, and an interior amplitude strip.
-/

namespace RHTower.Sieve

open Finset

/-- Actual two-factor Type-II cell counts after uniform epsilon rescaling. -/
theorem exists_matomakiTeravainen_typeII_actual_cell_counts_scheduled_energy
    {eps : ℝ} (heps : 0 < eps) (hepss : eps ≤ 1 / 1000) (L : ℕ) :
    ∃ T₀ : ℝ, 1 ≤ T₀ ∧
      ∀ (T : ℝ)
        (N₁ A₁ ell₁ : ℕ) (Q₁ : ℝ) (a₁ : Fin N₁ → ℂ)
        (N₂ A₂ ell₂ : ℕ) (Q₂ : ℝ) (a₂ : Fin N₂ → ℂ)
        (S : Finset ℝ) (V₁ V₂ C : ℝ) (J₁ J₂ : ℕ),
      T₀ ≤ T →
      1 ≤ Q₁ → Q₁ ^ 3 ≤ T ^ (eps ^ 2) →
      1 ≤ Q₂ → Q₂ ^ 3 ≤ T ^ (eps ^ 2) →
      1 < (A₁ : ℝ) → 1 < (A₂ : ℝ) →
      0 < ell₁ → ell₁ ≤ L → 0 < ell₂ → ell₂ ≤ L →
      0 < V₁ → 0 < V₂ →
      (∀ q ∈ S, matomakiTeravainenDirichletAmplitude N₁ a₁ q ≤ 1) →
      (∀ q ∈ S, matomakiTeravainenDirichletAmplitude N₂ a₂ q ≤ 1) →
      T ^ ((9 : ℝ) / 11 - 10 * eps) ≤ ((A₁ ^ ell₁ : ℕ) : ℝ) →
      ((A₁ ^ ell₁ : ℕ) : ℝ) ≤ T ^ (1 - 2 * eps) →
      T ^ ((9 : ℝ) / 11 - 10 * eps) ≤ ((A₂ ^ ell₂ : ℕ) : ℝ) →
      ((A₂ ^ ell₂ : ℕ) : ℝ) ≤ T ^ (1 - 2 * eps) →
      (∀ ij ∈ matomakiTeravainenActiveAmplitudeIndices S
          (matomakiTeravainenDirichletAmplitude N₁ a₁)
          (matomakiTeravainenDirichletAmplitude N₂ a₂) V₁ V₂ J₁ J₂,
        matomakiTeravainenAmplitudeSigma (A₁ : ℝ) V₁ ij.1 ≤
          matomakiTeravainenAmplitudeSigma (A₂ : ℝ) V₂ ij.2 →
        5 * eps + eps ^ 2 / 20 ≤
          matomakiTeravainenAmplitudeSigma (A₁ : ℝ) V₁ ij.1) →
      (∀ ij ∈ matomakiTeravainenActiveAmplitudeIndices S
          (matomakiTeravainenDirichletAmplitude N₁ a₁)
          (matomakiTeravainenDirichletAmplitude N₂ a₂) V₁ V₂ J₁ J₂,
        matomakiTeravainenAmplitudeSigma (A₁ : ℝ) V₁ ij.1 ≤
          matomakiTeravainenAmplitudeSigma (A₂ : ℝ) V₂ ij.2 →
        matomakiTeravainenAmplitudeSigma (A₁ : ℝ) V₁ ij.1 + eps ^ 2 / 20 ≤
          7 / 32 - 5 * eps) →
      (∀ ij ∈ matomakiTeravainenActiveAmplitudeIndices S
          (matomakiTeravainenDirichletAmplitude N₁ a₁)
          (matomakiTeravainenDirichletAmplitude N₂ a₂) V₁ V₂ J₁ J₂,
        matomakiTeravainenAmplitudeSigma (A₂ : ℝ) V₂ ij.2 <
          matomakiTeravainenAmplitudeSigma (A₁ : ℝ) V₁ ij.1 →
        5 * eps + eps ^ 2 / 20 ≤
          matomakiTeravainenAmplitudeSigma (A₂ : ℝ) V₂ ij.2) →
      (∀ ij ∈ matomakiTeravainenActiveAmplitudeIndices S
          (matomakiTeravainenDirichletAmplitude N₁ a₁)
          (matomakiTeravainenDirichletAmplitude N₂ a₂) V₁ V₂ J₁ J₂,
        matomakiTeravainenAmplitudeSigma (A₂ : ℝ) V₂ ij.2 <
          matomakiTeravainenAmplitudeSigma (A₁ : ℝ) V₁ ij.1 →
        matomakiTeravainenAmplitudeSigma (A₂ : ℝ) V₂ ij.2 + eps ^ 2 / 20 ≤
          7 / 32 - 5 * eps) →
      (∀ n : Fin N₁, a₁ n ≠ 0 →
        A₁ ≤ (n : ℕ) + 1 ∧ (n : ℕ) + 1 ≤ 2 * A₁) →
      (∑ j : Fin (N₁ ^ ell₁), ‖convPow N₁ ell₁ a₁ j‖ ^ 2 ≤
        Q₁ * ((A₁ ^ ell₁ : ℕ) : ℝ)) →
      (∀ n : Fin N₂, a₂ n ≠ 0 →
        A₂ ≤ (n : ℕ) + 1 ∧ (n : ℕ) + 1 ≤ 2 * A₂) →
      (∑ j : Fin (N₂ ^ ell₂), ‖convPow N₂ ell₂ a₂ j‖ ^ 2 ≤
        Q₂ * ((A₂ ^ ell₂ : ℕ) : ℝ)) →
      (∀ x ∈ S, ∀ y ∈ S, x ≠ y → 1 ≤ |x - y|) →
      (∀ x ∈ S, ∀ y ∈ S, |x - y| ≤ 2 * T) →
      0 ≤ C → (ell₁ + 1 : ℝ) ≤ C → (ell₂ + 1 : ℝ) ≤ C →
      ∀ ij ∈ matomakiTeravainenActiveAmplitudeIndices S
          (matomakiTeravainenDirichletAmplitude N₁ a₁)
          (matomakiTeravainenDirichletAmplitude N₂ a₂) V₁ V₂ J₁ J₂,
        ((matomakiTeravainenAmplitudeCell S
          (matomakiTeravainenDirichletAmplitude N₁ a₁)
          (matomakiTeravainenDirichletAmplitude N₂ a₂) V₁ V₂ ij).card : ℝ) ≤
            C * T ^
              (2 * min
                (matomakiTeravainenAmplitudeSigma (A₁ : ℝ) V₁ ij.1)
                (matomakiTeravainenAmplitudeSigma (A₂ : ℝ) V₂ ij.2) -
                eps ^ 2 / 10) := by
  let kappa : ℝ := eps ^ 2 / 20
  have hkappa : 0 < kappa := by dsimp [kappa]; positivity
  obtain ⟨Tcount, hTcount, hcount⟩ :=
    exists_matomakiTeravainen_typeII_actual_cell_counts_energy heps hepss
  obtain ⟨Tschedule, hTschedule, hschedule⟩ :=
    exists_matomakiTeravainen_raised_huxley_schedule heps hepss hkappa L
  refine ⟨max Tcount Tschedule, le_trans hTcount (le_max_left _ _), ?_⟩
  intro T N₁ A₁ ell₁ Q₁ a₁ N₂ A₂ ell₂ Q₂ a₂ S V₁ V₂ C J₁ J₂
    hT hQ₁ hQ₁3 hQ₂ hQ₂3 hA₁ hA₂ hell₁ hellL₁ hell₂ hellL₂ hV₁ hV₂
    hF₁one hF₂one hbaseLo₁ hbaseHi₁ hbaseLo₂ hbaseHi₂
    hsigmaLo₁ hsigmaHi₁ hsigmaLo₂ hsigmaHi₂
    hsupp₁ henergy₁ hsupp₂ henergy₂ hsep hspread hC hellC₁ hellC₂
  have hTc : Tcount ≤ T := le_trans (le_max_left _ _) hT
  have hTs : Tschedule ≤ T := le_trans (le_max_right _ _) hT
  have hT1 : 1 ≤ T := hTschedule.trans hTs
  have hone3 : (1 : ℝ) ^ 3 ≤ T ^ (eps ^ 2) := by
    rw [one_pow]
    exact Real.one_le_rpow hT1 (sq_nonneg eps)
  have hrhoLoFixed : 5 * eps + kappa ≤ (1 : ℝ) / 8 := by
    dsimp [kappa]
    nlinarith [sq_nonneg eps]
  have hrhoHiFixed : (1 : ℝ) / 8 + kappa ≤ 7 / 32 - 5 * eps := by
    dsimp [kappa]
    nlinarith [sq_nonneg eps]
  have hfixed₁ := hschedule T A₁ ell₁ ((1 : ℝ) / 8) 1 hTs hell₁ hellL₁
    hbaseLo₁ hbaseHi₁ hrhoLoFixed hrhoHiFixed (by norm_num) hone3
  have hfixed₂ := hschedule T A₂ ell₂ ((1 : ℝ) / 8) 1 hTs hell₂ hellL₂
    hbaseLo₂ hbaseHi₂ hrhoLoFixed hrhoHiFixed (by norm_num) hone3
  apply hcount T N₁ A₁ ell₁ kappa Q₁ a₁ N₂ A₂ ell₂ kappa Q₂ a₂
    S V₁ V₂ C J₁ J₂ hTc hQ₁ hQ₁3 hQ₂ hQ₂3 hA₁ hA₂ hell₁ hell₂ hV₁ hV₂
    hF₁one hF₂one
  · intro r
    exact (hfixed₁ r).1
  · intro r
    exact (hfixed₁ r).2.1
  · intro r
    exact (hfixed₁ r).2.2.1
  · intro ij hij hside r
    exact (hschedule T A₁ ell₁
      (matomakiTeravainenAmplitudeSigma (A₁ : ℝ) V₁ ij.1) Q₁
      hTs hell₁ hellL₁ hbaseLo₁ hbaseHi₁
      (hsigmaLo₁ ij hij hside) (hsigmaHi₁ ij hij hside) hQ₁ hQ₁3 r).2.2.2.1
  · intro ij hij hside r
    exact (hschedule T A₁ ell₁
      (matomakiTeravainenAmplitudeSigma (A₁ : ℝ) V₁ ij.1) Q₁
      hTs hell₁ hellL₁ hbaseLo₁ hbaseHi₁
      (hsigmaLo₁ ij hij hside) (hsigmaHi₁ ij hij hside) hQ₁ hQ₁3 r).2.2.2.2.1
  · intro ij hij hside r
    exact (hschedule T A₁ ell₁
      (matomakiTeravainenAmplitudeSigma (A₁ : ℝ) V₁ ij.1) Q₁
      hTs hell₁ hellL₁ hbaseLo₁ hbaseHi₁
      (hsigmaLo₁ ij hij hside) (hsigmaHi₁ ij hij hside) hQ₁ hQ₁3 r).2.2.2.2.2.1
  · intro ij hij hside r
    exact (hschedule T A₁ ell₁
      (matomakiTeravainenAmplitudeSigma (A₁ : ℝ) V₁ ij.1) Q₁
      hTs hell₁ hellL₁ hbaseLo₁ hbaseHi₁
      (hsigmaLo₁ ij hij hside) (hsigmaHi₁ ij hij hside) hQ₁ hQ₁3 r).2.2.2.2.2.2
  · intro r
    exact (hfixed₂ r).1
  · intro r
    exact (hfixed₂ r).2.1
  · intro r
    exact (hfixed₂ r).2.2.1
  · intro ij hij hside r
    exact (hschedule T A₂ ell₂
      (matomakiTeravainenAmplitudeSigma (A₂ : ℝ) V₂ ij.2) Q₂
      hTs hell₂ hellL₂ hbaseLo₂ hbaseHi₂
      (hsigmaLo₂ ij hij hside) (hsigmaHi₂ ij hij hside) hQ₂ hQ₂3 r).2.2.2.1
  · intro ij hij hside r
    exact (hschedule T A₂ ell₂
      (matomakiTeravainenAmplitudeSigma (A₂ : ℝ) V₂ ij.2) Q₂
      hTs hell₂ hellL₂ hbaseLo₂ hbaseHi₂
      (hsigmaLo₂ ij hij hside) (hsigmaHi₂ ij hij hside) hQ₂ hQ₂3 r).2.2.2.2.1
  · intro ij hij hside r
    exact (hschedule T A₂ ell₂
      (matomakiTeravainenAmplitudeSigma (A₂ : ℝ) V₂ ij.2) Q₂
      hTs hell₂ hellL₂ hbaseLo₂ hbaseHi₂
      (hsigmaLo₂ ij hij hside) (hsigmaHi₂ ij hij hside) hQ₂ hQ₂3 r).2.2.2.2.2.1
  · intro ij hij hside r
    exact (hschedule T A₂ ell₂
      (matomakiTeravainenAmplitudeSigma (A₂ : ℝ) V₂ ij.2) Q₂
      hTs hell₂ hellL₂ hbaseLo₂ hbaseHi₂
      (hsigmaLo₂ ij hij hside) (hsigmaHi₂ ij hij hside) hQ₂ hQ₂3 r).2.2.2.2.2.2
  · exact hsupp₁
  · exact henergy₁
  · exact hsupp₂
  · exact henergy₂
  · exact hsep
  · exact hspread
  · exact hC
  · exact hellC₁
  · exact hellC₂
  · dsimp [kappa]
    nlinarith [sq_nonneg eps]
  · dsimp [kappa]
    nlinarith [sq_nonneg eps]

end RHTower.Sieve
