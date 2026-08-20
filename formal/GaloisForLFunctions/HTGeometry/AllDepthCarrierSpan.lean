import GaloisForLFunctions.HTGeometry.AllDepthCarrierJets

/-!
# The span of the jets of translates of the universal carrier

Every finite constant-coefficient differential-translation operator applied to the universal
carrier lies in one `ℂ`-subspace of the meromorphic germ field, and the carrier of a smaller
direction set lies in the carrier span of a larger one, because the coface law exhibits it as a
translation defect.

* `carrierSpan`, `carrierAtomCombination_mem_carrierSpan`;
* **`carrierSpan_erase_le`** — deleting a direction keeps the span;
* `exists_multiAtomRealization_matching` — an atom sum with exactly a prescribed lattice-invariant
  divisor of bounded order.
-/

open Filter Set Topology Complex
open scoped Differential BigOperators

namespace GaloisForLFunctions

open Bottcher HTGeometry

noncomputable section

attribute [local instance] ellipticGammaRationalBaseDomain
  ellipticGammaRationalBaseComplexAlgebraMero ellipticGammaRationalBaseComplexDifferential
  ellipticGammaRationalBaseMeroDifferential ellipticGammaRationalBaseMeroCharZero
  ellipticGammaRationalBaseComplexDifferentialAlgebra

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The `ℂ`-span of all jets of all translates of the universal carrier of a direction set. -/
def carrierSpan (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) (s : Finset ι) :
    Submodule ℂ (meroField (Set.univ : Set ℂ)) :=
  Submodule.span ℂ
    {y | ∃ (j : ℕ) (b : ℂ),
      y = differentialJet j (addTranslationMeroEquiv b (universalCarrierMero τ hτ s))}

theorem mem_carrierSpan_of_jet (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) (s : Finset ι)
    (j : ℕ) (b : ℂ) :
    differentialJet j (addTranslationMeroEquiv b (universalCarrierMero τ hτ s))
      ∈ carrierSpan τ hτ s :=
  Submodule.subset_span ⟨j, b, rfl⟩

theorem carrierAtomCombination_mem_carrierSpan (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im)
    (s : Finset ι) (k : ι) (N : ℕ) (R : Finset ℂ) (c : ℕ → ℂ → ℂ) :
    carrierAtomCombination τ hτ s k N R c ∈ carrierSpan τ hτ s := by
  classical
  rw [carrierAtomCombination]
  refine Submodule.sum_mem _ fun j _ => Submodule.sum_mem _ fun q _ => ?_
  have hmem := mem_carrierSpan_of_jet τ hτ s j ((1 + τ k) - q)
  have hsmul := Submodule.smul_mem (carrierSpan τ hτ s)
    (c j q / ((-1 : ℂ) ^ j * (j.factorial : ℂ))) hmem
  rwa [Algebra.smul_def] at hsmul

/-- **Deleting a direction keeps the carrier span.**  The carrier of the smaller set is the
translation defect of the carrier of the larger one. -/
theorem carrierSpan_erase_le (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im) (s : Finset ι) {k : ι}
    (hk : k ∈ s) : carrierSpan τ hτ (s \ {k}) ≤ carrierSpan τ hτ s := by
  classical
  have hdefect : universalCarrierMero τ hτ (s \ {k})
      = addTranslationMeroEquiv (τ k) (universalCarrierMero τ hτ s)
        - universalCarrierMero τ hτ s := by
    have hqJ : k ∉ (Finset.univ : Finset ι) \ s := by
      simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, not_not]
      exact hk
    have hco := multipleEllipticGammaLogDerivFaceMero_addTranslation_sub τ hτ
      ((Finset.univ : Finset ι) \ s) k hqJ
    have hunion : insert k ((Finset.univ : Finset ι) \ s) = (Finset.univ : Finset ι) \ (s \ {k}) := by
      ext m
      simp only [Finset.mem_insert, Finset.mem_sdiff, Finset.mem_univ, true_and,
        Finset.mem_singleton, not_and, not_not]
      constructor
      · rintro (rfl | hm)
        · intro _
          rfl
        · intro hms
          exact absurd hms hm
      · intro hm
        by_cases hms : m ∈ s
        · exact Or.inl (hm hms)
        · exact Or.inr hms
    rw [universalCarrierMero, universalCarrierMero, ← hunion, ← hco]
  rw [carrierSpan]
  refine Submodule.span_le.mpr ?_
  rintro y ⟨j, b, rfl⟩
  rw [hdefect, map_sub, differentialJet_sub, addTranslationMeroEquiv_add]
  exact Submodule.sub_mem _ (mem_carrierSpan_of_jet τ hτ s j (b + τ k))
    (mem_carrierSpan_of_jet τ hτ s j b)

end

end GaloisForLFunctions
