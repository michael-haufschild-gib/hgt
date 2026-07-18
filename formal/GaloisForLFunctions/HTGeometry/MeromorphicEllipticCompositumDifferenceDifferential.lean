import GaloisForLFunctions.HTGeometry.MeromorphicEllipticProductSpecialization

/-!
# The finite rank-three action on the paired elliptic compositum

Every additive translation preserves the concrete compositum `E_sigma E_tau`.  This module
restricts the three source translations `1`, `sigma`, and `tau` to that compositum, packages them
as a commuting difference-differential field, and records exact compatibility with the already
constructed action on the global meromorphic field.
-/

open Filter Set
open scoped Differential

namespace GaloisForLFunctions

open Bottcher

noncomputable section

local instance ellipticCompositumDDFDomain :
    IsDomain (analyticSubring (Set.univ : Set ℂ)) :=
  Bottcher.isDomain_analyticSubring Set.univ isOpen_univ
    isPreconnected_univ Set.univ_nonempty

local instance ellipticCompositumDDFComplexAlgebraAnalytic :
    Algebra ℂ (analyticSubring Set.univ) := (constToAnalytic Set.univ).toAlgebra

local instance ellipticCompositumDDFComplexAlgebraMero :
    Algebra ℂ (meroField Set.univ) :=
  ((algebraMap (analyticSubring Set.univ) (meroField Set.univ)).comp
    (constToAnalytic Set.univ)).toAlgebra

local instance ellipticCompositumDDFAmbientDifferential :
    Differential (meroField (Set.univ : Set ℂ)) :=
  meroFieldDifferential isOpen_univ isPreconnected_univ Set.univ_nonempty

local instance ellipticCompositumDDFRestrictedDifferential (sigma tau : ℂ) :
    Differential (meromorphicEllipticCompositum sigma tau) :=
  meromorphicEllipticCompositumDifferential sigma tau

/-! ## Restricting one arbitrary translation -/

/-- Every ambient additive translation maps the paired elliptic compositum onto itself. -/
theorem meromorphicEllipticCompositum_map_addTranslationMeroAlgEquiv
    (sigma tau q : ℂ) :
    (meromorphicEllipticCompositum sigma tau).map
        (addTranslationMeroAlgEquiv q).toAlgHom =
      meromorphicEllipticCompositum sigma tau := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact addTranslationMeroAlgEquiv_mem_ellipticCompositum sigma tau q hx
  · intro x hx
    refine ⟨(addTranslationMeroAlgEquiv q).symm x, ?_, ?_⟩
    · rw [addTranslationMeroAlgEquiv_symm_apply]
      exact addTranslationMeroAlgEquiv_mem_ellipticCompositum
        sigma tau (-q) hx
    · exact (addTranslationMeroAlgEquiv q).apply_symm_apply x

/-- Translation by `q`, restricted to the concrete paired elliptic compositum. -/
noncomputable def meromorphicEllipticCompositumTranslationAlgEquiv
    (sigma tau q : ℂ) :
    meromorphicEllipticCompositum sigma tau ≃ₐ[ℂ]
      meromorphicEllipticCompositum sigma tau :=
  (IntermediateField.equivMap (meromorphicEllipticCompositum sigma tau)
      (addTranslationMeroAlgEquiv q).toAlgHom).trans
    (IntermediateField.equivOfEq
      (meromorphicEllipticCompositum_map_addTranslationMeroAlgEquiv
        sigma tau q))

@[simp]
theorem meromorphicEllipticCompositumTranslationAlgEquiv_apply
    (sigma tau q : ℂ) (x : meromorphicEllipticCompositum sigma tau) :
    ((meromorphicEllipticCompositumTranslationAlgEquiv sigma tau q x :
        meromorphicEllipticCompositum sigma tau) : meroField Set.univ) =
      addTranslationMeroAlgEquiv q (x : meroField Set.univ) := by
  rfl

/-- Restricted translation commutes with the derivation inherited from the ambient meromorphic
field. -/
theorem meromorphicEllipticCompositumTranslation_deriv
    (sigma tau q : ℂ) (x : meromorphicEllipticCompositum sigma tau) :
    meromorphicEllipticCompositumTranslationAlgEquiv sigma tau q x′ =
      (meromorphicEllipticCompositumTranslationAlgEquiv sigma tau q x)′ := by
  apply Subtype.ext
  change addTranslationMeroEquiv q
      (Differential.deriv (x : meroField Set.univ)) =
    Differential.deriv (addTranslationMeroEquiv q (x : meroField Set.univ))
  exact addTranslationMeroEquiv_deriv q (x : meroField Set.univ)

/-! ## The finite source action -/

/-- A chosen finite family of additive periods acting on the paired elliptic compositum. -/
def meromorphicEllipticCompositumDifferenceDifferentialField
    (sigma tau : ℂ) (v : Fin 3 → ℂ) :
    CommutingDifferenceDifferentialField (Fin 3) ℂ
      (meromorphicEllipticCompositum sigma tau) where
  aut i := (meromorphicEllipticCompositumTranslationAlgEquiv
    sigma tau (v i)).toRingEquiv
  aut_comm i j x := by
    apply Subtype.ext
    change addTranslationMeroEquiv (v i)
        (addTranslationMeroEquiv (v j) (x : meroField Set.univ)) =
      addTranslationMeroEquiv (v j)
        (addTranslationMeroEquiv (v i) (x : meroField Set.univ))
    simpa only [addTranslationMeroEquiv_add] using
      congrArg (fun q : ℂ ↦ addTranslationMeroEquiv q (x : meroField Set.univ))
        (add_comm (v i) (v j))
  aut_deriv i x :=
    meromorphicEllipticCompositumTranslation_deriv sigma tau (v i) x
  aut_algebraMap i c := by
    apply Subtype.ext
    change addTranslationMeroEquiv (v i)
        (algebraMap ℂ (meroField Set.univ) c) =
      algebraMap ℂ (meroField Set.univ) c
    exact addTranslationMeroEquiv_algebraMap_complex (v i) c

/-- The actual ordered source translations `1`, `sigma`, and `tau` acting on
`E_sigma E_tau`. -/
abbrev ellipticGammaCompositumDifferenceDifferentialField
    (sigma tau : ℂ) :
    CommutingDifferenceDifferentialField (Fin 3) ℂ
      (meromorphicEllipticCompositum sigma tau) :=
  meromorphicEllipticCompositumDifferenceDifferentialField sigma tau
    (ellipticGammaSourcePeriods sigma tau)

/-! ## Compatibility with the ambient rank-three action -/

/-- Coercing a restricted source translation to the ambient meromorphic field gives exactly the
corresponding global source translation. -/
@[simp]
theorem ellipticGammaCompositum_aut_coe
    (sigma tau : ℂ) (i : Fin 3)
    (x : meromorphicEllipticCompositum sigma tau) :
    (((ellipticGammaCompositumDifferenceDifferentialField sigma tau).aut i x :
        meromorphicEllipticCompositum sigma tau) : meroField Set.univ) =
      (rankThreeGeneratorMeromorphicDifferenceDifferentialField
        (ellipticGammaSourcePeriods sigma tau)).aut i
          (x : meroField Set.univ) := by
  rfl

/-- The inclusion of the paired elliptic compositum intertwines every one of the three source
automorphisms. -/
theorem ellipticGammaCompositum_aut_algebraMap
    (sigma tau : ℂ) (i : Fin 3)
    (x : meromorphicEllipticCompositum sigma tau) :
    (rankThreeGeneratorMeromorphicDifferenceDifferentialField
        (ellipticGammaSourcePeriods sigma tau)).aut i
        (algebraMap (meromorphicEllipticCompositum sigma tau)
          (meroField Set.univ) x) =
      algebraMap (meromorphicEllipticCompositum sigma tau)
        (meroField Set.univ)
        ((ellipticGammaCompositumDifferenceDifferentialField sigma tau).aut i x) := by
  rfl

/-- Under rational independence, the joint fixed field of the three restricted translations is
the embedded complex constant field. -/
theorem ellipticGammaCompositum_jointFixed_iff_constant
    (sigma tau : ℂ)
    (hindependent : LinearIndependent ℚ (ellipticGammaSourcePeriods sigma tau))
    (x : meromorphicEllipticCompositum sigma tau) :
    JointFixed (ellipticGammaCompositumDifferenceDifferentialField sigma tau) x ↔
      ∃ c : ℂ, algebraMap ℂ (meromorphicEllipticCompositum sigma tau) c = x := by
  constructor
  · intro hfixed
    have hambient : JointFixed
        (rankThreeGeneratorMeromorphicDifferenceDifferentialField
          (ellipticGammaSourcePeriods sigma tau))
        (x : meroField Set.univ) := by
      intro i
      simpa using congrArg
        (fun y : meromorphicEllipticCompositum sigma tau ↦
          (y : meroField Set.univ)) (hfixed i)
    obtain ⟨c, hc⟩ :=
      (rankThree_generator_jointFixed_iff_constant
        (ellipticGammaSourcePeriods sigma tau) hindependent
        (x : meroField Set.univ)).mp hambient
    refine ⟨c, ?_⟩
    apply Subtype.ext
    simpa [meromorphicConstantEmbedding] using hc
  · rintro ⟨c, rfl⟩ i
    exact (ellipticGammaCompositumDifferenceDifferentialField sigma tau).aut_algebraMap i c

end

end GaloisForLFunctions
