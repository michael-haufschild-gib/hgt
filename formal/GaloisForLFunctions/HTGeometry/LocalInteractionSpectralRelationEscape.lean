import GaloisForLFunctions.HTGeometry.AnalyticSpectralRelationEscape
import GaloisForLFunctions.HTGeometry.LocalInteractionLiftAnalyticRelationLaw

/-!
# From local interaction rigidity to an unordered spectral obstruction

The interaction-lift kernel theorem says that any branch relation surviving
every selected local-layer perturbation is constant.  A nonzero balanced
integer relation cannot be constant.  Therefore every labeling of that
relation is nontrivial on the local analytic chart; finite analytic escape
then produces one chart point avoiding every labeling simultaneously.
-/

open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- **Local interaction relation-escape bridge.** A chart whose persistent
relations restrict to the selected-layer witnesses has a nonzero unordered
coefficient obstruction for every nonzero balanced integer character,
provided the interaction lift is connected. -/
theorem exists_localInteraction_coefficientObstruction_eval_ne_zero
    {α ρ P : Type*}
    [Fintype α] [Fintype ρ]
    [DecidableEq α] [DecidableEq ρ]
    [Nonempty α] [Nonempty ρ]
    [NormedAddCommGroup P] [NormedSpace ℂ P]
    (energy : α → ℝ) (hmax : MaximallyProjectiveEnergy energy)
    (transition : Matrix α α ℂ)
    (k : α × ρ → ℤ)
    (hbalanced : SpectralCharacterBalanced k) (hk : k ≠ 0)
    (branch : α × ρ → P → ℂ)
    (U : Set P)
    (hUopen : IsOpen U) (hUconnected : IsPreconnected U)
    (hUnonempty : U.Nonempty)
    (hbranch : ∀ i, AnalyticOnNhd ℂ (branch i) U)
    (hrestrict :
      ∀ σ : Equiv.Perm (α × ρ),
        (∀ p ∈ U,
          ∑ i,
            permutedSpectralCoefficient k σ i *
              branch i p = 0) →
        ∀ r s, r ≠ s →
          SelectedLayerAnalyticRelationWitness
            energy transition
              (permutedSpectralCoefficient k σ) r s)
    (hlift :
      (crossLayerLiftGraph
        (transitionSupportGraph transition) ρ).Preconnected) :
    ∃ p ∈ U,
      MvPolynomial.eval₂ (Rat.castHom ℂ)
          (fun i : Fin (Fintype.card (α × ρ)) =>
            MvPolynomial.eval₂ (Rat.castHom ℂ)
              (fun j => branch j p)
              (MvPolynomial.esymm (α × ρ) ℚ (i + 1)))
          (spectralRelationCoefficientPolynomial k) ≠ 0 := by
  have hlabel :
      ∀ σ : Equiv.Perm (α × ρ),
        ∃ p ∈ U,
          permutedAnalyticSpectralRelation k branch σ p ≠ 0 := by
    intro σ
    by_contra hnone
    push Not at hnone
    have hfixed :
        ∀ p ∈ U,
          ∑ i,
            permutedSpectralCoefficient k σ i *
              branch i p = 0 := by
      intro p hp
      rw [sum_permutedSpectralCoefficient_eq_relation]
      exact hnone p hp
    have hconstant :
        ∀ x y,
          permutedSpectralCoefficient k σ x =
            permutedSpectralCoefficient k σ y :=
      selectedLayerAnalyticRelation_constant_of_preconnected
        energy hmax transition
        (permutedSpectralCoefficient k σ)
        (hrestrict σ hfixed) hlift
    exact
      (permutedSpectralCoefficient_not_constant
        hbalanced hk σ) hconstant
  exact
    exists_coefficientObstruction_eval_ne_zero_of_analytic
      k branch U hUopen hUconnected hUnonempty hbranch hlabel

end

end GaloisForLFunctions.HTGeometry
