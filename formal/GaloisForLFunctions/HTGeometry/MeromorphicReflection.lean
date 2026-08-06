import GaloisForLFunctions.HTGeometry.MeromorphicTranslation

/-!
# Reflection automorphisms of the meromorphic differential field

Additive translation lifts from analytic germs to the meromorphic fraction field and *commutes*
with its quotient-rule derivation.  The reflection `z ↦ c - z` lifts the same way but
*anti-commutes*: precomposing with an orientation-reversing affine map negates the derivative.

This is the carrier the multiple sine needs.  The multiple sine is the Barnes multiple gamma
reflected, so every statement about its structural translates has to be moved across `z ↦ |ω| - z`
inside the same differential field in which the Barnes ladder is proved.

The construction mirrors `MeromorphicTranslation` exactly, with the reflection supplying its own
inverse because it is an involution, and with the sign appearing in the derivation law.
-/

open Filter Topology Set Function
open scoped Differential

namespace GaloisForLFunctions

open Bottcher

noncomputable section

/-! ### The reflection as an analytic self-map -/

/-- The reflection `z ↦ c - z`. -/
def complexReflection (c : ℂ) : ℂ → ℂ := fun z ↦ c - z

theorem analyticOnNhd_complexReflection (c : ℂ) (U : Set ℂ) :
    AnalyticOnNhd ℂ (complexReflection c) U :=
  analyticOnNhd_const.sub analyticOnNhd_id

/-- The reflection is an involution, so it is its own inverse. -/
theorem complexReflection_comp_self (c : ℂ) (U : Set ℂ) :
    Set.EqOn (complexReflection c ∘ complexReflection c) id U := by
  intro z _
  simp [complexReflection]

/-! ### The induced automorphisms -/

/-- Reflection acting on analytic germs. -/
noncomputable def complexReflectionAnalyticEquiv (c : ℂ) :
    analyticSubring (Set.univ : Set ℂ) ≃+*
      analyticSubring (Set.univ : Set ℂ) :=
  precompAnalyticEquiv
    (analyticOnNhd_complexReflection c _)
    (analyticOnNhd_complexReflection c _)
    (Set.mapsTo_univ _ _) (Set.mapsTo_univ _ _)
    (complexReflection_comp_self c _)
    (complexReflection_comp_self c _)

/-- Reflection acting on the meromorphic field. -/
noncomputable def complexReflectionMeroEquiv (c : ℂ) :
    meroField (Set.univ : Set ℂ) ≃+* meroField (Set.univ : Set ℂ) :=
  precompMeroEquiv
    (analyticOnNhd_complexReflection c _)
    (analyticOnNhd_complexReflection c _)
    (Set.mapsTo_univ _ _) (Set.mapsTo_univ _ _)
    (complexReflection_comp_self c _)
    (complexReflection_comp_self c _)
    isOpen_univ isPreconnected_univ Set.univ_nonempty

theorem complexReflectionMeroEquiv_algebraMap (c : ℂ)
    (a : analyticSubring (Set.univ : Set ℂ)) :
    letI := Bottcher.isDomain_analyticSubring Set.univ isOpen_univ
      isPreconnected_univ Set.univ_nonempty
    complexReflectionMeroEquiv c
        (algebraMap (analyticSubring Set.univ) (meroField Set.univ) a) =
      algebraMap (analyticSubring Set.univ) (meroField Set.univ)
        (complexReflectionAnalyticEquiv c a) := by
  letI := Bottcher.isDomain_analyticSubring Set.univ isOpen_univ
    isPreconnected_univ Set.univ_nonempty
  exact precompMeroEquiv_algebraMap
    (analyticOnNhd_complexReflection c _)
    (analyticOnNhd_complexReflection c _)
    (Set.mapsTo_univ _ _) (Set.mapsTo_univ _ _)
    (complexReflection_comp_self c _)
    (complexReflection_comp_self c _)
    isOpen_univ isPreconnected_univ Set.univ_nonempty a

/-! ### The derivation anti-commutes with the reflection -/

/-- **Anti-commutation on analytic germs.**  Precomposing with `z ↦ c - z` negates the
derivative. -/
theorem complexReflectionAnalyticEquiv_deriv (c : ℂ)
    (a : analyticSubring (Set.univ : Set ℂ)) :
    complexReflectionAnalyticEquiv c
        (analyticSubringDeriv isOpen_univ a) =
      -analyticSubringDeriv isOpen_univ
        (complexReflectionAnalyticEquiv c a) := by
  obtain ⟨f, hf, hfa⟩ := a.2
  apply Subtype.ext
  let htr : Tendsto (complexReflection c) (𝓟 Set.univ) (𝓟 Set.univ) :=
    tendsto_principal_principal.mpr (Set.mapsTo_univ _ _)
  change
    (analyticGermDeriv isOpen_univ (a : Germ (𝓟 Set.univ) ℂ)).compTendsto
        (complexReflection c) htr =
      -analyticGermDeriv isOpen_univ
        ((a : Germ (𝓟 Set.univ) ℂ).compTendsto (complexReflection c) htr)
  rw [← hfa]
  change Germ.ofFun (l := 𝓟 Set.univ) (fun z ↦ deriv f (c - z)) =
    -Germ.ofFun (l := 𝓟 Set.univ) (deriv (fun z : ℂ ↦ f (c - z)))
  rw [← Germ.coe_neg, Germ.coe_eq]
  refine eventually_principal.mpr fun z _ => ?_
  rw [Pi.neg_apply, deriv_comp_const_sub, neg_neg]

/-- **Anti-commutation on the meromorphic field.**  The reflection is a ring automorphism that
negates the derivation: `(reflect x)′ = -reflect (x′)`. -/
theorem complexReflectionMeroEquiv_deriv (c : ℂ)
    (z : meroField (Set.univ : Set ℂ)) :
    letI := Bottcher.isDomain_analyticSubring Set.univ isOpen_univ
      isPreconnected_univ Set.univ_nonempty
    letI := meroFieldDifferential isOpen_univ isPreconnected_univ
      Set.univ_nonempty
    complexReflectionMeroEquiv c z′ = -((complexReflectionMeroEquiv c z)′) := by
  let A := analyticSubring (Set.univ : Set ℂ)
  let F := meroField (Set.univ : Set ℂ)
  letI hdom := Bottcher.isDomain_analyticSubring Set.univ isOpen_univ
    isPreconnected_univ Set.univ_nonempty
  letI : Algebra ℤ A := Ring.toIntAlgebra _
  letI : Algebra ℤ F := Ring.toIntAlgebra _
  letI hdiff := meroFieldDifferential isOpen_univ isPreconnected_univ
    Set.univ_nonempty
  let sigmaA : A ≃+* A := complexReflectionAnalyticEquiv c
  let sigmaF : F ≃+* F := complexReflectionMeroEquiv c
  let Dc : Derivation ℤ F F :=
    -((Differential.equiv sigmaF : Differential F).deriv)
  have hDc : Dc = Differential.deriv := by
    apply fractionRing_derivation_ext (A := A) (F := F)
    intro a
    change -(sigmaF.symm (Differential.deriv (sigmaF (algebraMap A F a)))) = _
    have hsigma : sigmaF (algebraMap A F a) =
        algebraMap A F (sigmaA a) :=
      complexReflectionMeroEquiv_algebraMap c a
    rw [hsigma, meroFieldDifferential_algebraMap, meroFieldDifferential_algebraMap]
    have hanti := complexReflectionAnalyticEquiv_deriv c a
    have hdel : analyticSubringDeriv isOpen_univ (sigmaA a) =
        -sigmaA (analyticSubringDeriv isOpen_univ a) := by
      rw [hanti, neg_neg]
    rw [hdel]
    simp only [map_neg]
    have hmap : sigmaF
        (algebraMap A F (analyticSubringDeriv isOpen_univ a)) =
          algebraMap A F
            (sigmaA (analyticSubringDeriv isOpen_univ a)) :=
      complexReflectionMeroEquiv_algebraMap c _
    rw [← hmap]
    simp only [sigmaF, RingEquiv.symm_apply_apply]
    exact neg_neg _
  have hzconj := Derivation.congr_fun hDc z
  change -(sigmaF.symm (Differential.deriv (sigmaF z))) = Differential.deriv z at hzconj
  have hstep : sigmaF.symm (Differential.deriv (sigmaF z)) = -Differential.deriv z := by
    rw [← hzconj, neg_neg]
  have h := congrArg sigmaF hstep
  rw [RingEquiv.apply_symm_apply] at h
  rw [map_neg] at h
  rw [show (complexReflectionMeroEquiv c) = sigmaF from rfl, h, neg_neg]

end

end GaloisForLFunctions
