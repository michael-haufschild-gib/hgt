import GaloisForLFunctions.RHTower.HardyZPhaseAsymptotic
import GaloisForLFunctions.RHTower.HardyZSignChange

/-!
# Terminal Hardy-phase finite-certificate zero law

Every phase level above the exact Riemann--Siegel phase minimum has a unique positive-tail height.
Ordered phase levels therefore select ordered heights.  At those canonical heights, any common
finite symmetrized Euler--Maclaurin level whose endpoint values clear their explicit error budgets
and have opposite signs forces a genuine critical-line zeta zero between them.
-/

open Set

namespace RHTower

noncomputable section

/-- **Terminal phase finite-certificate law.**  Ordered terminal Hardy phase levels have unique
ordered height representatives, and every certified finite sign bracket at those representatives
forces a critical-line zeta zero. -/
theorem exists_terminalHardyPhase_finiteCertificateZeroLaw :
    ∃ T : ℝ, 0 < T ∧ gammaHardyPhaseRate T = 0 ∧
      ∀ y₁ y₂ : ℝ, gammaHardyTheta T ≤ y₁ → y₁ ≤ y₂ →
        ∃ t₁ t₂ : ℝ,
          T ≤ t₁ ∧ T ≤ t₂ ∧
          gammaHardyTheta t₁ = y₁ ∧ gammaHardyTheta t₂ = y₂ ∧
          (∀ s : ℝ, T ≤ s → gammaHardyTheta s = y₁ → s = t₁) ∧
          (∀ s : ℝ, T ≤ s → gammaHardyTheta s = y₂ → s = t₂) ∧
          t₁ ≤ t₂ ∧
          ∀ N : ℕ, 1 ≤ N →
            hardySEMError N t₁ < |hardySEM N t₁| →
            hardySEMError N t₂ < |hardySEM N t₂| →
            hardySEM N t₁ * hardySEM N t₂ < 0 →
              ∃ τ ∈ Icc t₁ t₂, riemannZeta (linePt τ) = 0 := by
  obtain ⟨T, hT, -⟩ := existsUnique_pos_gammaHardyPhaseRate_eq_zero
  have hbij := gammaHardyTheta_bijOn_Ici_of_rate_eq_zero hT.1 hT.2
  have hmono := (gammaHardyTheta_morseGeometry_of_rate_eq_zero hT.1 hT.2).2
  refine ⟨T, hT.1, hT.2, ?_⟩
  intro y₁ y₂ hy₁ hy₁₂
  have hy₂ : gammaHardyTheta T ≤ y₂ := hy₁.trans hy₁₂
  obtain ⟨t₁, ht₁, heq₁⟩ := hbij.2.2 (Set.mem_Ici.mpr hy₁)
  obtain ⟨t₂, ht₂, heq₂⟩ := hbij.2.2 (Set.mem_Ici.mpr hy₂)
  have ht₁₂ : t₁ ≤ t₂ := by
    by_contra hnot
    have ht₂₁ : t₂ < t₁ := lt_of_not_ge hnot
    have hphase := hmono ht₂ ht₁ ht₂₁
    rw [heq₁, heq₂] at hphase
    exact (not_lt_of_ge hy₁₂) hphase
  refine ⟨t₁, t₂, ht₁, ht₂, heq₁, heq₂, ?_, ?_, ht₁₂, ?_⟩
  · intro s hs hseq
    exact hmono.injOn (Set.mem_Ici.mpr hs) ht₁ (hseq.trans heq₁.symm)
  · intro s hs hseq
    exact hmono.injOn (Set.mem_Ici.mpr hs) ht₂ (hseq.trans heq₂.symm)
  · intro N hN hmargin₁ hmargin₂ hsign
    exact exists_riemannZeta_line_zero_of_hardySEM_certified_sign_bracket
      hN ht₁₂ hmargin₁ hmargin₂ hsign

end

end RHTower
