import GaloisForLFunctions.HTGeometry.ObserverTemporalPhaseSupportLaw

/-!
# Temporal phase-valuation tomography

The scale-indexed limiting phase laws determine the analytic birth
valuation, rather than merely reflecting it. For an active projective
character, its limiting Fourier coefficient first ceases to equal one at
exactly its spectral birth order.
-/

open Filter MeasureTheory Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- One projective character has unlocked under a phase law when its
Fourier coefficient is no longer identically one. -/
def PhaseLawCharacterUnlocked
    {d : Type*} [Fintype d]
    (μ : ProbabilityMeasure (UnitAddTorus d))
    (k : ProjectiveCharacter d) : Prop :=
  projectivePhaseLawFourierCoefficient μ k ≠ 1

/-- First scale at which one character unlocks in a sequence of phase
laws. -/
noncomputable def firstPhaseLawCharacterUnlockingOrder
    {d : Type*} [Fintype d]
    (μ : ℕ → ProbabilityMeasure (UnitAddTorus d))
    (k : ProjectiveCharacter d)
    (hunlocks : ∃ r, PhaseLawCharacterUnlocked (μ r) k) : ℕ :=
  by
    classical
    exact Nat.find hunlocks

/-- At a fixed observation horizon, an active character is unlocked in the
limiting phase law exactly when its analytic birth order has been reached. -/
theorem finiteAnalyticPhaseLaw_characterUnlocked_iff_birthOrder_le
    {d : Type*} [Fintype d]
    (energy : d → ℂ → ℂ)
    (series : d → FormalMultilinearSeries ℂ ℂ ℂ)
    (henergy : ∀ i, HasFPowerSeriesAt (energy i) (series i) 0)
    (omega : ℝ → d → ℝ)
    (hreal : ∀ i, ∀ᶠ (g : ℝ) in 𝓝[>] (0 : ℝ),
      energy i (g : ℂ) = (omega g i : ℂ))
    {τ : ℝ} (hτ : 0 < τ)
    (r : ℕ)
    (μ : ProbabilityMeasure (UnitAddTorus d))
    (hμ :
      Tendsto
        (fun g =>
          finiteTorusPhaseProbabilityMeasure
            (omega g) (τ / g ^ r))
        (𝓝[>] 0) (𝓝 μ))
    (k : ProjectiveCharacter d)
    (hactive :
      SpectralCharacterActive (spectralTaylorJet series) k) :
    PhaseLawCharacterUnlocked μ k ↔
      spectralCharacterBirthOrder
        (spectralTaylorJet series) k hactive ≤ r := by
  obtain ⟨ν, hν, hνunique⟩ :=
    existsUnique_finiteAnalyticTemporalPhaseSupport
      energy series henergy omega hreal r hτ
  have hμν : μ = ν :=
    tendsto_nhds_unique hμ hν.1
  subst μ
  have hcoefficient :
      projectivePhaseLawFourierCoefficient ν k = 1 ↔
        phaseLawConstraint ν k := by
    symm
    simpa [projectivePhaseLawFourierCoefficient] using
      phaseLawConstraint_iff_integral_eq_one ν k
  have hmembership :
      k ∈ spectralConstraintFiltration
          (spectralTaylorJet series) (r + 1) ↔
        r < spectralCharacterBirthOrder
          (spectralTaylorJet series) k hactive := by
    rw [mem_spectralConstraintFiltration_iff_le_birthOrder
      hactive]
    omega
  unfold PhaseLawCharacterUnlocked
  rw [hν.2 k, hmembership] at hcoefficient
  have hunlocked := not_congr hcoefficient
  exact hunlocked.trans (by omega)

/-- **Exact temporal tomography law.** For every active character, any
choice of the unique limiting phase law at every inverse-power horizon
recovers its analytic birth valuation as the first horizon at which that
character unlocks. -/
theorem firstPhaseLawCharacterUnlockingOrder_eq_birthOrder
    {d : Type*} [Fintype d]
    (energy : d → ℂ → ℂ)
    (series : d → FormalMultilinearSeries ℂ ℂ ℂ)
    (henergy : ∀ i, HasFPowerSeriesAt (energy i) (series i) 0)
    (omega : ℝ → d → ℝ)
    (hreal : ∀ i, ∀ᶠ (g : ℝ) in 𝓝[>] (0 : ℝ),
      energy i (g : ℂ) = (omega g i : ℂ))
    {τ : ℝ} (hτ : 0 < τ)
    (μ : ℕ → ProbabilityMeasure (UnitAddTorus d))
    (hμ : ∀ r,
      Tendsto
        (fun g =>
          finiteTorusPhaseProbabilityMeasure
            (omega g) (τ / g ^ r))
        (𝓝[>] 0) (𝓝 (μ r)))
    (k : ProjectiveCharacter d)
    (hactive :
      SpectralCharacterActive (spectralTaylorJet series) k) :
    ∃ hunlocks : ∃ r, PhaseLawCharacterUnlocked (μ r) k,
      firstPhaseLawCharacterUnlockingOrder μ k hunlocks =
        spectralCharacterBirthOrder
          (spectralTaylorJet series) k hactive := by
  classical
  let b :=
    spectralCharacterBirthOrder
      (spectralTaylorJet series) k hactive
  have hunlockAtBirth :
      PhaseLawCharacterUnlocked (μ b) k :=
    (finiteAnalyticPhaseLaw_characterUnlocked_iff_birthOrder_le
      energy series henergy omega hreal hτ b (μ b) (hμ b)
      k hactive).mpr le_rfl
  let hunlocks : ∃ r, PhaseLawCharacterUnlocked (μ r) k :=
    ⟨b, hunlockAtBirth⟩
  refine ⟨hunlocks, ?_⟩
  unfold firstPhaseLawCharacterUnlockingOrder
  apply le_antisymm
  · exact Nat.find_min' hunlocks hunlockAtBirth
  · exact
      (finiteAnalyticPhaseLaw_characterUnlocked_iff_birthOrder_le
        energy series henergy omega hreal hτ
        (Nat.find hunlocks) (μ (Nat.find hunlocks))
        (hμ (Nat.find hunlocks)) k hactive).mp
        (Nat.find_spec hunlocks)

end

end GaloisForLFunctions.HTGeometry
