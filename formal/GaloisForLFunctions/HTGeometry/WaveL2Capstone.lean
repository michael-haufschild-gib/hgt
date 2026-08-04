import GaloisForLFunctions.HTGeometry.WaveDominationSub
import GaloisForLFunctions.HTGeometry.WaveL2Uniqueness

/-!
# Uniqueness with hypotheses on each solution separately

The last remaining asymmetry of the square-integrable uniqueness theorem was its dominating
hypothesis, which spoke about the difference of the two solutions. Factor-wise domination is closed
under differences, so the hypothesis can be moved onto each solution separately. What results is a
uniqueness theorem whose every assumption is square integrability or uniform-in-time domination by a
square-integrable function, of one solution at a time.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory

open scoped ContDiff

section Capstone

variable {d : ℕ} {u₁ u₂ V : ℝ × (Fin d → ℝ) → ℝ}

/-- A field whose value, time derivative, second time derivative, spatial derivatives and mixed
derivatives are dominated, uniformly on unit time intervals, by square-integrable functions. -/
def FactorDominated (u : ℝ × (Fin d → ℝ) → ℝ) : Prop :=
  ∀ t : ℝ, ∃ (gT gTT gU : (Fin d → ℝ) → ℝ) (gS gST : Fin d → (Fin d → ℝ) → ℝ),
    MemLp gT 2 (volume : Measure (Fin d → ℝ)) ∧
    MemLp gTT 2 (volume : Measure (Fin d → ℝ)) ∧
    MemLp gU 2 (volume : Measure (Fin d → ℝ)) ∧
    (∀ i : Fin d, MemLp (gS i) 2 (volume : Measure (Fin d → ℝ))) ∧
    (∀ i : Fin d, MemLp (gST i) 2 (volume : Measure (Fin d → ℝ))) ∧
    (∀ s ∈ Metric.ball t 1, ∀ x, |waveDirDeriv (timeDir d) u (s, x)| ≤ gT x) ∧
    (∀ s ∈ Metric.ball t 1, ∀ x,
      |waveDirDeriv (timeDir d) (waveDirDeriv (timeDir d) u) (s, x)| ≤ gTT x) ∧
    (∀ s ∈ Metric.ball t 1, ∀ x, |u (s, x)| ≤ gU x) ∧
    (∀ (i : Fin d), ∀ s ∈ Metric.ball t 1, ∀ x,
      |waveDirDeriv (spaceDir d i) u (s, x)| ≤ gS i x) ∧
    (∀ (i : Fin d), ∀ s ∈ Metric.ball t 1, ∀ x,
      |waveDirDeriv (timeDir d) (waveDirDeriv (spaceDir d i) u) (s, x)| ≤ gST i x)

/-- **Uniqueness, with every hypothesis about one solution at a time.** -/
theorem eq_of_solvesWaveEq_of_memLp_of_factorDominated
    (h₁ : L2Solution u₁) (h₂ : L2Solution u₂)
    (hd₁ : FactorDominated u₁) (hd₂ : FactorDominated u₂)
    (hs₁ : SolvesWaveEq u₁ V) (hs₂ : SolvesWaveEq u₂ V) (hVcont : Continuous V)
    {M : ℝ} (hM : ∀ p, |V p| ≤ M)
    (hval : ∀ x : Fin d → ℝ, u₁ ((0 : ℝ), x) = u₂ ((0 : ℝ), x))
    (hder : ∀ x : Fin d → ℝ, waveDirDeriv (timeDir d) u₁ ((0 : ℝ), x)
      = waveDirDeriv (timeDir d) u₂ ((0 : ℝ), x))
    (t : ℝ) (x : Fin d → ℝ) : u₁ (t, x) = u₂ (t, x) := by
  refine eq_of_solvesWaveEq_of_memLp h₁ h₂ hs₁ hs₂ hVcont hM (fun r => ?_) hval hder t x
  obtain ⟨gT₁, gTT₁, gU₁, gS₁, gST₁, hgT₁, hgTT₁, hgU₁, hgS₁, hgST₁,
    hT₁, hTT₁, hU₁, hS₁, hST₁⟩ := hd₁ r
  obtain ⟨gT₂, gTT₂, gU₂, gS₂, gST₂, hgT₂, hgTT₂, hgU₂, hgS₂, hgST₂,
    hT₂, hTT₂, hU₂, hS₂, hST₂⟩ := hd₂ r
  exact exists_bound_of_factor_memLp_sub h₁.smooth h₂.smooth r
    hgT₁ hgTT₁ hgU₁ hgS₁ hgST₁ hgT₂ hgTT₂ hgU₂ hgS₂ hgST₂
    hT₁ hTT₁ hU₁ hS₁ hST₁ hT₂ hTT₂ hU₂ hS₂ hST₂

/-- The difference of two square-integrable, factor-dominated solutions is a decaying solution. -/
theorem decayingSolution_sub_of_memLp_of_factorDominated
    (h₁ : L2Solution u₁) (h₂ : L2Solution u₂)
    (hd₁ : FactorDominated u₁) (hd₂ : FactorDominated u₂)
    (hs₁ : SolvesWaveEq u₁ V) (hs₂ : SolvesWaveEq u₂ V) (hVcont : Continuous V)
    {M : ℝ} (hM : ∀ p, |V p| ≤ M) :
    DecayingSolution (fun q => u₁ q - u₂ q) V := by
  have hsub := h₁.sub h₂
  refine decayingSolution_of_memLp_two hsub.smooth
    (solvesWaveEq_sub h₁.smooth h₂.smooth hs₁ hs₂)
    hsub.sliceL2 hsub.dirL2 hsub.spaceL2 hsub.gradL2 hsub.gradDirL2 hsub.lapL2
    hVcont ⟨M, hM⟩ (fun r => ?_)
  obtain ⟨gT₁, gTT₁, gU₁, gS₁, gST₁, hgT₁, hgTT₁, hgU₁, hgS₁, hgST₁,
    hT₁, hTT₁, hU₁, hS₁, hST₁⟩ := hd₁ r
  obtain ⟨gT₂, gTT₂, gU₂, gS₂, gST₂, hgT₂, hgTT₂, hgU₂, hgS₂, hgST₂,
    hT₂, hTT₂, hU₂, hS₂, hST₂⟩ := hd₂ r
  exact exists_bound_of_factor_memLp_sub h₁.smooth h₂.smooth r
    hgT₁ hgTT₁ hgU₁ hgS₁ hgST₁ hgT₂ hgTT₂ hgU₂ hgS₂ hgST₂
    hT₁ hTT₁ hU₁ hS₁ hST₁ hT₂ hTT₂ hU₂ hS₂ hST₂

/-- **Continuous dependence in the square-integrable class.** -/
theorem waveEnergy_sub_le_exp_abs_of_memLp
    (h₁ : L2Solution u₁) (h₂ : L2Solution u₂)
    (hd₁ : FactorDominated u₁) (hd₂ : FactorDominated u₂)
    (hs₁ : SolvesWaveEq u₁ V) (hs₂ : SolvesWaveEq u₂ V) (hVcont : Continuous V)
    {M : ℝ} (hM : ∀ p, |V p| ≤ M) (t : ℝ) :
    waveEnergy (fun q => u₁ q - u₂ q) t
      ≤ waveEnergy (fun q => u₁ q - u₂ q) 0 * Real.exp ((M + 1) * |t|) :=
  waveEnergy_le_exp_abs_of_decaying
    (decayingSolution_sub_of_memLp_of_factorDominated h₁ h₂ hd₁ hd₂ hs₁ hs₂ hVcont hM) hM t

end Capstone

end GaloisForLFunctions.HTGeometry
