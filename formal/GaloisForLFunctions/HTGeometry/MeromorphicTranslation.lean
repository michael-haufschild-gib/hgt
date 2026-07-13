import GaloisForLFunctions.HTGeometry.MeromorphicDifferentialField
import GaloisForLFunctions.HTGeometry.SemilinearKaehlerDescent
import Mathlib.Analysis.Calculus.Deriv.Shift

/-!
# Translation automorphisms of the meromorphic differential field

Additive translation of the complex variable lifts from analytic germs to
the meromorphic fraction field and commutes with its quotient-rule
derivation. This is the concrete difference-differential carrier for
translation functional equations.
-/

open Filter Topology Set Function
open scoped Differential

namespace GaloisForLFunctions

open Bottcher

noncomputable section

def addTranslation (q : ℂ) : ℂ → ℂ := fun z ↦ z + q

theorem analyticOnNhd_addTranslation (q : ℂ) (U : Set ℂ) :
    AnalyticOnNhd ℂ (addTranslation q) U :=
  analyticOnNhd_id.add analyticOnNhd_const

theorem addTranslation_comp_neg (q : ℂ) (U : Set ℂ) :
    Set.EqOn (addTranslation q ∘ addTranslation (-q)) id U := by
  intro z hz
  simp [addTranslation]

noncomputable def addTranslationAnalyticEquiv (q : ℂ) :
    analyticSubring (Set.univ : Set ℂ) ≃+*
      analyticSubring (Set.univ : Set ℂ) :=
  precompAnalyticEquiv
    (analyticOnNhd_addTranslation q _)
    (analyticOnNhd_addTranslation (-q) _)
    (Set.mapsTo_univ _ _) (Set.mapsTo_univ _ _)
    (addTranslation_comp_neg q _)
    (by simpa using addTranslation_comp_neg (-q) (Set.univ : Set ℂ))

noncomputable def addTranslationMeroEquiv (q : ℂ) :
    meroField (Set.univ : Set ℂ) ≃+* meroField (Set.univ : Set ℂ) :=
  precompMeroEquiv
    (analyticOnNhd_addTranslation q _)
    (analyticOnNhd_addTranslation (-q) _)
    (Set.mapsTo_univ _ _) (Set.mapsTo_univ _ _)
    (addTranslation_comp_neg q _)
    (by simpa using addTranslation_comp_neg (-q) (Set.univ : Set ℂ))
    isOpen_univ isPreconnected_univ Set.univ_nonempty

theorem addTranslationMeroEquiv_algebraMap (q : ℂ)
    (a : analyticSubring (Set.univ : Set ℂ)) :
    letI := Bottcher.isDomain_analyticSubring Set.univ isOpen_univ
      isPreconnected_univ Set.univ_nonempty
    addTranslationMeroEquiv q
        (algebraMap (analyticSubring Set.univ) (meroField Set.univ) a) =
      algebraMap (analyticSubring Set.univ) (meroField Set.univ)
        (addTranslationAnalyticEquiv q a) := by
  letI := Bottcher.isDomain_analyticSubring Set.univ isOpen_univ
    isPreconnected_univ Set.univ_nonempty
  exact precompMeroEquiv_algebraMap
    (analyticOnNhd_addTranslation q _)
    (analyticOnNhd_addTranslation (-q) _)
    (Set.mapsTo_univ _ _) (Set.mapsTo_univ _ _)
    (addTranslation_comp_neg q _)
    (by simpa using addTranslation_comp_neg (-q) (Set.univ : Set ℂ))
    isOpen_univ isPreconnected_univ Set.univ_nonempty a

theorem addTranslationAnalyticEquiv_deriv (q : ℂ)
    (a : analyticSubring (Set.univ : Set ℂ)) :
    addTranslationAnalyticEquiv q
        (analyticSubringDeriv isOpen_univ a) =
      analyticSubringDeriv isOpen_univ
        (addTranslationAnalyticEquiv q a) := by
  obtain ⟨f, hf, hfa⟩ := a.2
  apply Subtype.ext
  let htr : Tendsto (addTranslation q) (𝓟 Set.univ) (𝓟 Set.univ) :=
    tendsto_principal_principal.mpr (Set.mapsTo_univ _ _)
  change
    (analyticGermDeriv isOpen_univ (a : Germ (𝓟 Set.univ) ℂ)).compTendsto
        (addTranslation q) htr =
      analyticGermDeriv isOpen_univ
        ((a : Germ (𝓟 Set.univ) ℂ).compTendsto (addTranslation q) htr)
  rw [← hfa]
  change Germ.ofFun (l := 𝓟 Set.univ) (fun z ↦ deriv f (z + q)) =
    Germ.ofFun (l := 𝓟 Set.univ) (deriv (fun z : ℂ ↦ f (z + q)))
  rw [Germ.coe_eq]
  exact eventually_principal.mpr fun z hz => by
    rw [deriv_comp_add_const]

theorem addTranslationMeroEquiv_deriv (q : ℂ)
    (z : meroField (Set.univ : Set ℂ)) :
    letI := Bottcher.isDomain_analyticSubring Set.univ isOpen_univ
      isPreconnected_univ Set.univ_nonempty
    letI := meroFieldDifferential isOpen_univ isPreconnected_univ
      Set.univ_nonempty
    addTranslationMeroEquiv q z′ = (addTranslationMeroEquiv q z)′ := by
  let A := analyticSubring (Set.univ : Set ℂ)
  let F := meroField (Set.univ : Set ℂ)
  letI hdom := Bottcher.isDomain_analyticSubring Set.univ isOpen_univ
    isPreconnected_univ Set.univ_nonempty
  letI : Algebra ℤ A := Ring.toIntAlgebra _
  letI : Algebra ℤ F := Ring.toIntAlgebra _
  letI hdiff := meroFieldDifferential isOpen_univ isPreconnected_univ
    Set.univ_nonempty
  let sigmaA : A ≃+* A := addTranslationAnalyticEquiv q
  let sigmaF : F ≃+* F := addTranslationMeroEquiv q
  let Dc : Derivation ℤ F F :=
    (Differential.equiv sigmaF : Differential F).deriv
  have hDc : Dc = Differential.deriv := by
    apply fractionRing_derivation_ext (A := A) (F := F)
    intro a
    change sigmaF.symm (Differential.deriv (sigmaF (algebraMap A F a))) = _
    have hsigma : sigmaF (algebraMap A F a) =
        algebraMap A F (sigmaA a) := by
      exact addTranslationMeroEquiv_algebraMap q a
    rw [hsigma, meroFieldDifferential_algebraMap]
    rw [meroFieldDifferential_algebraMap]
    rw [← addTranslationAnalyticEquiv_deriv]
    have hmap : sigmaF
        (algebraMap A F (analyticSubringDeriv isOpen_univ a)) =
          algebraMap A F
            (sigmaA (analyticSubringDeriv isOpen_univ a)) := by
      exact addTranslationMeroEquiv_algebraMap q _
    have := congrArg sigmaF.symm hmap
    simpa [sigmaF] using this.symm
  have hzconj := Derivation.congr_fun hDc z
  change sigmaF.symm (Differential.deriv (sigmaF z)) = Differential.deriv z at hzconj
  have := congrArg sigmaF hzconj
  simpa [sigmaF] using this.symm

end

end GaloisForLFunctions
