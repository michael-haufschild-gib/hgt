import GaloisForLFunctions.RHTower.WeilPaperCompletedGammaEnergy

/-!
# Bounded perturbations of completed gamma-energy minimization

The paid gamma integral is a real lower semicontinuous function on each compact
budget completion. Adding any bounded continuous real spectral penalty preserves
lower semicontinuity and attainment, including every prescribed observation.
-/

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal BoundedContinuousFunction
noncomputable section
namespace RHTower.WeilWorkPBAP

/-- The actual gamma integral on the completion retains its uniform lower bound. -/
theorem paperCompletedGammaExpectation_lower (B : ℝ)
    (μ : PaperPoleCompensatedCompletion B) :
    -(10 + Real.log 4) ≤ ∫ ξ, paperSpectralGammaWeight ξ ∂(μ.1 : Measure ℝ) := by
  have h : 0 ≤ ∫ ξ, paperSpectralGammaWeight ξ + (10 + Real.log 4) ∂(μ.1 : Measure ℝ) :=
    integral_nonneg fun ξ =>
      (paperSpectralLogWeight_nonneg ξ).trans (paperSpectralLogWeight_le_gamma ξ)
  rw [integral_add (integrable_paperSpectralGammaWeight_completion B μ) (integrable_const _),
    integral_const, probReal_univ, one_smul] at h
  linarith

/-- The finite real gamma integral itself is lower semicontinuous on every paid completion. -/
theorem lowerSemicontinuous_paperCompletedGammaExpectation (B : ℝ) :
    LowerSemicontinuous (fun μ : PaperPoleCompensatedCompletion B =>
      ∫ ξ, paperSpectralGammaWeight ξ ∂(μ.1 : Measure ℝ)) := by
  apply lowerSemicontinuous_iff_isClosed_preimage.mpr
  intro a
  by_cases ha : 0 ≤ a + (10 + Real.log 4)
  · have heq :
        (fun μ : PaperPoleCompensatedCompletion B =>
          ∫ ξ, paperSpectralGammaWeight ξ ∂(μ.1 : Measure ℝ)) ⁻¹' Iic a =
        (fun μ : PaperPoleCompensatedCompletion B => paperExtendedCompensatedEnergy μ.1) ⁻¹'
          Iic (ENNReal.ofReal (a + (10 + Real.log 4))) := by
      ext μ
      change (∫ ξ, paperSpectralGammaWeight ξ ∂(μ.1 : Measure ℝ)) ≤ a ↔ _
      rw [Set.mem_preimage, Set.mem_Iic, paperExtendedCompensatedEnergy_completion_eq]
      constructor
      · intro h
        exact ENNReal.ofReal_le_ofReal (by linarith)
      · intro h
        have hr := ENNReal.toReal_mono ENNReal.ofReal_ne_top h
        have hn : 0 ≤ (∫ ξ, paperSpectralGammaWeight ξ ∂(μ.1 : Measure ℝ)) +
            (10 + Real.log 4) := by
          have := paperCompletedGammaExpectation_lower B μ
          linarith
        rw [ENNReal.toReal_ofReal hn, ENNReal.toReal_ofReal ha] at hr
        linarith
    rw [heq]
    exact (lowerSemicontinuous_paperExtendedCompensatedEnergy.comp
      continuous_subtype_val).isClosed_preimage _
  · have heq :
        (fun μ : PaperPoleCompensatedCompletion B =>
          ∫ ξ, paperSpectralGammaWeight ξ ∂(μ.1 : Measure ℝ)) ⁻¹' Iic a = ∅ := by
      ext μ
      constructor
      · intro h
        change (∫ ξ, paperSpectralGammaWeight ξ ∂(μ.1 : Measure ℝ)) ≤ a at h
        have := paperCompletedGammaExpectation_lower B μ
        exfalso
        linarith
      · intro h
        exact False.elim h
    rw [heq]
    exact isClosed_empty

/-- Gamma expectation with a bounded continuous real spectral penalty. -/
def paperPerturbedGammaExpectation (G : ℝ →ᵇ ℝ) (μ : ProbabilityMeasure ℝ) : ℝ :=
  (∫ ξ, paperSpectralGammaWeight ξ ∂(μ : Measure ℝ)) + ∫ ξ, G ξ ∂(μ : Measure ℝ)

/-- On the paid completion the objective is the integral of the actual perturbed symbol. -/
theorem paperPerturbedGammaExpectation_eq_integral (B : ℝ)
    (μ : PaperPoleCompensatedCompletion B) (G : ℝ →ᵇ ℝ) :
    paperPerturbedGammaExpectation G μ.1 =
      ∫ ξ, paperSpectralGammaWeight ξ + G ξ ∂(μ.1 : Measure ℝ) :=
  (integral_add (integrable_paperSpectralGammaWeight_completion B μ) (G.integrable _)).symm

/-- Every bounded continuous penalty preserves real lower semicontinuity. -/
theorem lowerSemicontinuous_paperCompletedPerturbedGammaExpectation
    (B : ℝ) (G : ℝ →ᵇ ℝ) :
    LowerSemicontinuous (fun μ : PaperPoleCompensatedCompletion B =>
      paperPerturbedGammaExpectation G μ.1) :=
  (lowerSemicontinuous_paperCompletedGammaExpectation B).add
    ((ProbabilityMeasure.continuous_integral_boundedContinuousFunction G).comp
      continuous_subtype_val).lowerSemicontinuous

/-- The same lower semicontinuity holds with every prescribed complex observation. -/
theorem lowerSemicontinuous_paperObservedPerturbedGammaExpectation
    {ι : Type*} (c : ComplexNullMixture) (F : ι → ℝ →ᵇ ℂ) (G : ℝ →ᵇ ℝ) :
    LowerSemicontinuous (fun μ : PaperObservedSpectralCompletion c F =>
      paperPerturbedGammaExpectation G μ.1) := by
  have hc : Continuous (fun μ : PaperObservedSpectralCompletion c F =>
      (⟨μ.1, paperObservedSpectralCompletion_subset_budget c F μ.2⟩ :
        PaperPoleCompensatedCompletion (paperPoleCompensatedEnergy c.1))) :=
    continuous_subtype_val.subtype_mk _
  exact (lowerSemicontinuous_paperCompletedPerturbedGammaExpectation _ G).comp hc

/-- Bounded perturbations of the gamma objective attain their minima in the budget completion. -/
theorem exists_paperCompletedPerturbedGamma_minimizer
    (c : NormalizedMixture) (G : ℝ →ᵇ ℝ) :
    ∃ μ : PaperPoleCompensatedCompletion (paperPoleCompensatedEnergy c),
      ∀ ν : PaperPoleCompensatedCompletion (paperPoleCompensatedEnergy c),
        paperPerturbedGammaExpectation G μ.1 ≤ paperPerturbedGammaExpectation G ν.1 := by
  let μ₀ : PaperPoleCompensatedCompletion (paperPoleCompensatedEnergy c) :=
    ⟨spectralProbability c, subset_closure ⟨c,
      show paperPoleCompensatedEnergy c ≤ paperPoleCompensatedEnergy c from le_rfl, rfl⟩⟩
  obtain ⟨μ, _, hμ⟩ := LowerSemicontinuousOn.exists_isMinOn
    (s := Set.univ) ⟨μ₀, Set.mem_univ _⟩ isCompact_univ
    ((lowerSemicontinuous_paperCompletedPerturbedGammaExpectation _ G).lowerSemicontinuousOn Set.univ)
  exact ⟨μ, fun ν => hμ (Set.mem_univ ν)⟩

/-- Bounded perturbations attain minima preserving all observations and integer origin constraints. -/
theorem exists_paperObservedPerturbedGamma_minimizer
    {ι : Type*} (c : ComplexNullMixture) (F : ι → ℝ →ᵇ ℂ) (G : ℝ →ᵇ ℝ) :
    ∃ μ : PaperObservedSpectralCompletion c F,
      ∀ ν : PaperObservedSpectralCompletion c F,
        paperPerturbedGammaExpectation G μ.1 ≤ paperPerturbedGammaExpectation G ν.1 := by
  let μ₀ : PaperObservedSpectralCompletion c F :=
    ⟨spectralProbability c.1, spectralProbability_mem_paperObservedSpectralCompletion c F⟩
  obtain ⟨μ, _, hμ⟩ := LowerSemicontinuousOn.exists_isMinOn
    (s := Set.univ) ⟨μ₀, Set.mem_univ _⟩ isCompact_univ
    ((lowerSemicontinuous_paperObservedPerturbedGammaExpectation c F G).lowerSemicontinuousOn Set.univ)
  exact ⟨μ, fun ν => hμ (Set.mem_univ ν)⟩

end RHTower.WeilWorkPBAP
