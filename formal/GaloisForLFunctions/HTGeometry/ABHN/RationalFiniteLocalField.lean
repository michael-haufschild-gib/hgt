import GaloisForLFunctions.HTGeometry.ABHN.Places
import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.NumberTheory.Padics.HeightOneSpectrum
import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.RingTheory.Henselian

/-!
# Nonarchimedean local fields at finite rational places

This module installs the valuative-relation interface on each finite completion of `ℚ` and
proves that it is a nonarchimedean local field.  The proof transports local compactness through
Mathlib's explicit equivalence with the corresponding `p`-adic field.  It supplies the local-field
input for the nonarchimedean component of ABHN; no local Brauer invariant is assumed here.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

open IsDedekindDomain
open scoped ValuativeRel WithZero WithZeroMulInt

noncomputable section

universe u v

/-- A locally compact nontrivially valued field has the local-field structure associated with
its given valuation. -/
theorem isNonarchimedeanLocalField_of_valued_of_locallyCompact
    (K : Type u) (Γ : Type v) [Field K] [LinearOrderedCommGroupWithZero Γ] [Valued K Γ]
    [LocallyCompactSpace K] [(Valued.v : Valuation K Γ).IsNontrivial] :
    letI : ValuativeRel K := .ofValuation (Valued.v : Valuation K Γ)
    IsNonarchimedeanLocalField K := by
  letI : ValuativeRel K := .ofValuation (Valued.v : Valuation K Γ)
  letI : (Valued.v : Valuation K Γ).Compatible := .ofValuation _
  refine {
    toIsValuativeTopology := ?_
    toLocallyCompactSpace := inferInstance
    toIsNontrivial := ?_ }
  · apply IsValuativeTopology.of_mem_nhds_zero_iff_vle (Valued.v : Valuation K Γ)
    intro s
    exact Valued.is_topological_valuation s
  · exact
      (ValuativeRel.isNontrivial_iff_isNontrivial (Valued.v : Valuation K Γ)).mpr
        (show (Valued.v : Valuation K Γ).IsNontrivial from inferInstance)

/-- The valuative relation on a finite rational completion comes from its completed adic
valuation. -/
noncomputable instance rationalFiniteCompletionValuativeRel (v : NumberField.FinitePlace ℚ) :
    ValuativeRel (v.maximalIdeal.adicCompletion ℚ) :=
  .ofValuation (Valued.v : Valuation (v.maximalIdeal.adicCompletion ℚ) ℤᵐ⁰)

/-- The completed adic valuation is compatible with the chosen valuative relation. -/
instance rationalFiniteCompletionValuationCompatible (v : NumberField.FinitePlace ℚ) :
    (Valued.v : Valuation (v.maximalIdeal.adicCompletion ℚ) ℤᵐ⁰).Compatible :=
  .ofValuation _

/-- Finite rational completions are locally compact, transported from their `p`-adic models. -/
noncomputable instance rationalFiniteCompletionLocallyCompact (v : NumberField.FinitePlace ℚ) :
    LocallyCompactSpace (v.maximalIdeal.adicCompletion ℚ) := by
  letI : Fact (Rat.HeightOneSpectrum.primesEquiv v.maximalIdeal).1.Prime :=
    ⟨(Rat.HeightOneSpectrum.primesEquiv v.maximalIdeal).2⟩
  letI : LocallyCompactSpace ℚ_[Rat.HeightOneSpectrum.primesEquiv v.maximalIdeal] :=
    inferInstance
  exact Topology.IsOpenEmbedding.locallyCompactSpace ((Rat.HeightOneSpectrum.adicCompletion.padicEquiv v.maximalIdeal).toHomeomorph.isOpenEmbedding)

/-- Every finite completion of `ℚ` is a nonarchimedean local field. -/
noncomputable instance rationalFiniteCompletionIsNonarchimedeanLocalField
    (v : NumberField.FinitePlace ℚ) :
    IsNonarchimedeanLocalField (v.maximalIdeal.adicCompletion ℚ) := by
  exact isNonarchimedeanLocalField_of_valued_of_locallyCompact
    (v.maximalIdeal.adicCompletion ℚ) ℤᵐ⁰

/-- The valuative relation is preserved by the packaged finite-place completion reduction. -/
noncomputable instance rationalFinitePlaceCompletionTopologicalSpace
    (v : NumberField.FinitePlace ℚ) :
    TopologicalSpace (completion ℚ (.finite v)) := by
  change TopologicalSpace (v.maximalIdeal.adicCompletion ℚ)
  infer_instance

/-- The valuative relation is preserved by the packaged finite-place completion reduction. -/
noncomputable instance rationalFinitePlaceCompletionValuativeRel (v : NumberField.FinitePlace ℚ) :
    ValuativeRel (completion ℚ (.finite v)) := by
  change ValuativeRel (v.maximalIdeal.adicCompletion ℚ)
  infer_instance

/-- The packaged completion at a finite rational place is a nonarchimedean local field. -/
noncomputable instance rationalFinitePlaceCompletionIsNonarchimedeanLocalField
    (v : NumberField.FinitePlace ℚ) :
    IsNonarchimedeanLocalField (completion ℚ (.finite v)) := by
  change IsNonarchimedeanLocalField (v.maximalIdeal.adicCompletion ℚ)
  infer_instance

/-- The valuation ring at a finite rational completion is a discrete valuation ring.  This is
the integral local input needed before defining ramification or an unramified Brauer subgroup. -/
noncomputable instance rationalFinitePlaceCompletionIsDiscreteValuationRing
    (v : NumberField.FinitePlace ℚ) :
    IsDiscreteValuationRing 𝒪[completion ℚ (.finite v)] := by
  infer_instance

/-- The residue field at a finite rational completion is finite.  This is a prerequisite for the
standard nonarchimedean local class-field-theory construction, not that construction itself. -/
noncomputable instance rationalFinitePlaceCompletionFiniteResidueField
    (v : NumberField.FinitePlace ℚ) :
    Finite 𝓀[completion ℚ (.finite v)] := by
  infer_instance

/-- The valuation ring of a finite rational completion is complete for its maximal-ideal adic
topology. This is the formal Hensel-lifting input for unramified local theory. -/
theorem rationalFinitePlaceCompletion_isAdicComplete
    (v : NumberField.FinitePlace ℚ) :
    IsAdicComplete 𝓂[completion ℚ (.finite v)] 𝒪[completion ℚ (.finite v)] := by
  letI := IsTopologicalAddGroup.rightUniformSpace (completion ℚ (.finite v))
  letI := isUniformAddGroup_of_addCommGroup (G := completion ℚ (.finite v))
  infer_instance

/-- The valuation ring of every finite completion of `ℚ` is henselian. This supports Hensel
lifting and the unramified-extension layer that precedes local class field theory. -/
theorem rationalFinitePlaceCompletion_henselianRing
    (v : NumberField.FinitePlace ℚ) :
    HenselianRing 𝒪[completion ℚ (.finite v)] 𝓂[completion ℚ (.finite v)] := by
  letI : IsAdicComplete 𝓂[completion ℚ (.finite v)] 𝒪[completion ℚ (.finite v)] :=
    rationalFinitePlaceCompletion_isAdicComplete v
  infer_instance

/-- The valuation ring at a finite rational completion is a henselian local ring. This packages
the Hensel-lifting statement in the form used for unramified finite extensions. -/
theorem rationalFinitePlaceCompletion_henselianLocalRing
    (v : NumberField.FinitePlace ℚ) :
    HenselianLocalRing 𝒪[completion ℚ (.finite v)] := by
  letI : HenselianRing 𝒪[completion ℚ (.finite v)] 𝓂[completion ℚ (.finite v)] :=
    rationalFinitePlaceCompletion_henselianRing v
  refine { toIsLocalRing := inferInstance, is_henselian := ?_ }
  intro f hf a₀ ha₀ hderivative
  exact HenselianRing.is_henselian f hf a₀ ha₀ (hderivative.map (Ideal.Quotient.mk _))

end

end GaloisForLFunctions.HTGeometry.ABHN
