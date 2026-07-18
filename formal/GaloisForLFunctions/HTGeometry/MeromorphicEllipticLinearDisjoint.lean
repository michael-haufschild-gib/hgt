import GaloisForLFunctions.HTGeometry.MeromorphicEllipticRationalCompositum
import GaloisForLFunctions.HTGeometry.MeromorphicRankThreeSourceBoundary
import GaloisForLFunctions.HTGeometry.SemilinearCircuitDescent
import Mathlib.FieldTheory.LinearDisjoint

/-!
# Linear disjointness of the two elliptic meromorphic fields

Let `E_p` be the field of global meromorphic germs fixed by translation by `1` and by `p`.
When `1`, `sigma`, and `tau` are rationally independent, `E_sigma` and `E_tau` are linearly
disjoint over `C` inside the global meromorphic field.

The proof is semilinear descent.  A complex basis of `E_sigma` is fixed by translation by
`sigma`.  If it acquired a relation over `E_tau`, translating the coefficients by `sigma` and
using the least-support descent theorem would produce a nonzero complex relation.  Indeed, a
coefficient in `E_tau` fixed by translation by `sigma` has the three periods `1`, `sigma`, and
`tau`, so the rank-three fixed-field theorem makes it constant.
-/

open Filter Set

namespace GaloisForLFunctions

open Bottcher

noncomputable section

local instance meromorphicEllipticLinearDisjointDomain :
    IsDomain (analyticSubring (Set.univ : Set ℂ)) :=
  Bottcher.isDomain_analyticSubring Set.univ isOpen_univ
    isPreconnected_univ Set.univ_nonempty

local instance meromorphicEllipticLinearDisjointComplexAlgebraAnalytic :
    Algebra ℂ (analyticSubring Set.univ) := (constToAnalytic Set.univ).toAlgebra

local instance meromorphicEllipticLinearDisjointComplexAlgebraMero :
    Algebra ℂ (meroField Set.univ) :=
  meromorphicEllipticCompositumComplexAlgebraMero

local instance meromorphicEllipticLinearDisjointDifferential :
    Differential (meroField (Set.univ : Set ℂ)) :=
  meroFieldDifferential isOpen_univ isPreconnected_univ Set.univ_nonempty

/-! ## Translation on one elliptic factor -/

/-- Every ambient additive translation maps a concrete elliptic field onto itself. -/
theorem ellipticMeroField_map_addTranslationMeroAlgEquiv (p q : ℂ) :
    (ellipticMeroField p).map (addTranslationMeroAlgEquiv q).toAlgHom =
      ellipticMeroField p := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact addTranslationMeroAlgEquiv_mem_ellipticMeroField p q hx
  · intro x hx
    refine ⟨(addTranslationMeroAlgEquiv q).symm x, ?_, ?_⟩
    · rw [addTranslationMeroAlgEquiv_symm_apply]
      exact addTranslationMeroAlgEquiv_mem_ellipticMeroField p (-q) hx
    · exact (addTranslationMeroAlgEquiv q).apply_symm_apply x

/-- Translation by `q`, restricted to the `(1,p)`-elliptic meromorphic field. -/
noncomputable def ellipticMeroFieldTranslationAlgEquiv (p q : ℂ) :
    ellipticMeroField p ≃ₐ[ℂ] ellipticMeroField p :=
  (IntermediateField.equivMap (ellipticMeroField p)
      (addTranslationMeroAlgEquiv q).toAlgHom).trans
    (IntermediateField.equivOfEq
      (ellipticMeroField_map_addTranslationMeroAlgEquiv p q))

@[simp]
theorem ellipticMeroFieldTranslationAlgEquiv_apply
    (p q : ℂ) (x : ellipticMeroField p) :
    ((ellipticMeroFieldTranslationAlgEquiv p q x : ellipticMeroField p) :
        meroField Set.univ) =
      addTranslationMeroAlgEquiv q (x : meroField Set.univ) := by
  rfl

/-! ## Rank-three fixed coefficients -/

/-- An element of `E_tau` fixed by the restricted `sigma`-translation is a complex constant when
`1`, `sigma`, and `tau` are rationally independent. -/
theorem exists_complex_of_ellipticMeroField_translation_fixed
    (sigma tau : ℂ)
    (hindependent : LinearIndependent ℚ (ellipticGammaSourcePeriods sigma tau))
    (z : ellipticMeroField tau)
    (hz : ellipticMeroFieldTranslationAlgEquiv tau sigma z = z) :
    ∃ c : ℂ, algebraMap ℂ (ellipticMeroField tau) c = z := by
  have hzperiods :
      addTranslationMeroEquiv 1 (z : meroField Set.univ) = z ∧
        addTranslationMeroEquiv tau (z : meroField Set.univ) = z :=
    (mem_ellipticMeroField_iff tau (z : meroField Set.univ)).mp z.2
  have hzsigma :
      addTranslationMeroEquiv sigma (z : meroField Set.univ) = z := by
    have h := congrArg
      (fun w : ellipticMeroField tau => (w : meroField Set.univ)) hz
    simpa using h
  have hjoint : JointFixed
      (rankThreeGeneratorMeromorphicDifferenceDifferentialField
        (ellipticGammaSourcePeriods sigma tau))
      (z : meroField Set.univ) := by
    intro i
    change addTranslationMeroEquiv (ellipticGammaSourcePeriods sigma tau i)
      (z : meroField Set.univ) = z
    fin_cases i
    · simpa [ellipticGammaSourcePeriods] using hzperiods.1
    · simpa [ellipticGammaSourcePeriods] using hzsigma
    · simpa [ellipticGammaSourcePeriods] using hzperiods.2
  obtain ⟨c, hc⟩ :=
    (rankThree_generator_jointFixed_iff_constant
      (ellipticGammaSourcePeriods sigma tau) hindependent
      (z : meroField Set.univ)).mp hjoint
  refine ⟨c, ?_⟩
  apply Subtype.ext
  change algebraMap ℂ (meroField Set.univ) c = (z : meroField Set.univ)
  simpa [meromorphicConstantEmbedding] using hc

/-! ## The tensor-product gate -/

/-- Under rational independence of the common period and the two transverse periods, the two
concrete elliptic meromorphic fields are linearly disjoint over `ℂ`. -/
theorem ellipticMeroFields_linearDisjoint
    (sigma tau : ℂ)
    (hindependent : LinearIndependent ℚ (ellipticGammaSourcePeriods sigma tau)) :
    (ellipticMeroField sigma).LinearDisjoint (ellipticMeroField tau) := by
  letI : SMul ℂ (meroField Set.univ) :=
    meromorphicEllipticCompositumComplexAlgebraMero.toSMul
  letI : Module ℂ (meroField Set.univ) :=
    meromorphicEllipticCompositumComplexAlgebraMero.toModule
  let A := ellipticMeroField sigma
  let B := ellipticMeroField tau
  letI : IsScalarTower ℂ B (meroField Set.univ) :=
    .of_algebraMap_eq fun _ ↦ rfl
  let b := Module.Free.chooseBasis ℂ A
  apply IntermediateField.LinearDisjoint.of_basis_left (A := A) (L := B) b
  let coefficientTranslation : Unit → B ≃+* B :=
    fun _ => (ellipticMeroFieldTranslationAlgEquiv tau sigma).toRingEquiv
  let ambientTranslation : Unit →
      meroField (Set.univ : Set ℂ) ≃+ meroField (Set.univ : Set ℂ) :=
    fun _ => (addTranslationMeroEquiv sigma).toAddEquiv
  have hfixed : ∀ z : B, (∀ i, coefficientTranslation i z = z) →
      ∃ c : ℂ, algebraMap ℂ B c = z := by
    intro z hz
    exact exists_complex_of_ellipticMeroField_translation_fixed
      sigma tau hindependent z (by simpa [coefficientTranslation] using hz ())
  have hsemilinear : ∀ i c m,
      ambientTranslation i (c • m) =
        coefficientTranslation i c • ambientTranslation i m := by
    intro i c m
    change addTranslationMeroEquiv sigma ((c : meroField Set.univ) * m) =
      ((ellipticMeroFieldTranslationAlgEquiv tau sigma c : B) :
          meroField Set.univ) * addTranslationMeroEquiv sigma m
    rw [map_mul, ellipticMeroFieldTranslationAlgEquiv_apply]
    change addTranslationMeroEquiv sigma (c : meroField Set.univ) *
        addTranslationMeroEquiv sigma m =
      addTranslationMeroEquiv sigma (c : meroField Set.univ) *
        addTranslationMeroEquiv sigma m
    rfl
  have hbasisFixed : ∀ i k,
      ambientTranslation i ((A.val ∘ b) k) = (A.val ∘ b) k := by
    intro i k
    have hk : ((b k : A) : meroField Set.univ) ∈ ellipticMeroField sigma := by
      simpa [A] using (b k).2
    change addTranslationMeroEquiv sigma ((b k : A) : meroField Set.univ) =
      ((b k : A) : meroField Set.univ)
    exact ((mem_ellipticMeroField_iff sigma _).mp hk).2
  have hbambient : LinearIndependent ℂ (A.val ∘ b) :=
    b.linearIndependent.map' A.val.toLinearMap
      (LinearMap.ker_eq_bot_of_injective A.val.injective)
  exact semilinear_linearIndependent_of_fixed_field
    coefficientTranslation hfixed ambientTranslation (A.val ∘ b)
    hsemilinear hbasisFixed hbambient

end

end GaloisForLFunctions
