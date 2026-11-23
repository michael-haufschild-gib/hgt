import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.RationalExteriorTrace
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.AffineFiniteEtaleTrace
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.FiniteEtaleFunctionField
import Mathlib.RingTheory.Etale.Field

/-! Trace on an affine inverse-image chart agrees with trace in the function fields. -/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open GlobalTheory.CechDR
open scoped GlobalTheory.CechDR

namespace GlobalTheory.SchemeCohomology

variable {k : Type} [Field k] [CharZero k] {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y]
  {s : X ⟶ Spec (CommRingCat.of k)} {t : Y ⟶ Spec (CommRingCat.of k)}
  {f : Y ⟶ X} [IsFinite f] [IsDominant f] [Etale f]

omit [IsFinite f] [Etale f] [CharZero k] in
theorem functionFieldPullback_scalarTower (hf : f ≫ s = t) :
    letI := sectionFunctionFieldAlgebra s
    letI := sectionFunctionFieldAlgebra t
    letI := f.functionFieldPullback.hom.toAlgebra
    IsScalarTower k X.functionField Y.functionField := by
  letI := sectionFunctionFieldAlgebra s
  letI := sectionFunctionFieldAlgebra t
  letI := f.functionFieldPullback.hom.toAlgebra
  exact IsScalarTower.of_algebraMap_eq fun c => ((functionFieldPullbackAlg f hf).commutes c).symm

omit [Etale f] in
theorem functionFieldPullback_etale (s : X ⟶ Spec (CommRingCat.of k)) :
    letI := f.functionFieldPullback.hom.toAlgebra
    Algebra.Etale X.functionField Y.functionField := by
  letI := sectionFunctionFieldAlgebra s
  letI := f.functionFieldPullback.hom.toAlgebra
  letI : CharZero X.functionField := charZero_of_injective_algebraMap (algebraMap k _).injective
  letI : FiniteDimensional X.functionField Y.functionField := finiteDimensional_functionFieldPullback f
  exact ⟨Algebra.FormallyEtale.of_isSeparable _ _,
    (Algebra.FinitePresentation.of_finiteType
      (R := X.functionField) (A := Y.functionField)).mp inferInstance⟩

/-- Trace of a regular form can be computed after extending it to the function field. -/
theorem affineFormTrace_functionField (hf : f ≫ s = t) {U : X.Opens} (hU : IsAffineOpen U)
    (hη : genericPoint X ∈ U) (p : ℕ) (ω : FormsOn t (f ⁻¹ᵁ U) p) :
    letI : Nonempty U := ⟨⟨genericPoint X, hη⟩⟩
    letI : Nonempty (f ⁻¹ᵁ U) := ⟨⟨genericPoint Y, by
      change f (genericPoint Y) ∈ U
      rwa [f.map_genericPoint_of_isDominant]⟩⟩
    letI := sectionFunctionFieldAlgebra s
    letI := sectionFunctionFieldAlgebra t
    letI := f.functionFieldPullback.hom.toAlgebra
    letI := functionFieldPullback_scalarTower hf
    letI := finiteDimensional_functionFieldPullback f
    letI := functionFieldPullback_etale (f := f) s
    traceDR k X.functionField Y.functionField
      (ExteriorDifferentials.map (sectionToFunctionField t (f ⁻¹ᵁ U)) p ω : DR k Y.functionField) =
      (ExteriorDifferentials.map (sectionToFunctionField s U) p
        (affineFormTrace hf hU p ω) : DR k X.functionField) := by
  let E := X.functionField
  let L := Y.functionField
  let V := f ⁻¹ᵁ U
  have hη' : genericPoint Y ∈ V := by
    change f (genericPoint Y) ∈ U
    rwa [f.map_genericPoint_of_isDominant]
  letI : Nonempty U := ⟨⟨genericPoint X, hη⟩⟩
  letI : Nonempty V := ⟨⟨genericPoint Y, hη'⟩⟩
  letI : Algebra k E := sectionFunctionFieldAlgebra s
  letI : Algebra k L := sectionFunctionFieldAlgebra t
  letI : Algebra E L := f.functionFieldPullback.hom.toAlgebra
  letI : IsScalarTower k E L := functionFieldPullback_scalarTower hf
  letI : FiniteDimensional E L := finiteDimensional_functionFieldPullback f
  letI : Algebra.Etale E L := functionFieldPullback_etale (f := f) s
  let A := SectionRing s U
  let B := SectionRing t V
  let iA : A →ₐ[k] E := sectionToFunctionField s U
  let iB : B →ₐ[k] L := sectionToFunctionField t V
  letI : Algebra A B := (f.app U).hom.toAlgebra
  letI : Algebra A E := (X.germToFunctionField U).hom.toAlgebra
  letI : Algebra B L := (Y.germToFunctionField V).hom.toAlgebra
  letI : Algebra A L := ((algebraMap E L).comp (algebraMap A E)).toAlgebra
  letI : IsScalarTower k A B := .of_algebraMap_eq fun a => ((sectionPullback hf U).commutes a).symm
  letI : IsScalarTower k A E := .of_algebraMap_eq fun a => (iA.commutes a).symm
  letI : IsScalarTower k B L := .of_algebraMap_eq fun a => (iB.commutes a).symm
  letI : IsScalarTower A E L := .of_algebraMap_eq fun _ => rfl
  letI : IsScalarTower A B L := .of_algebraMap_eq fun a => f.functionFieldPullback_germ U hη a
  letI : IsFractionRing A E := functionField_isFractionRing_of_isAffineOpen X U hU
  letI : IsFractionRing B L := functionField_isFractionRing_of_isAffineOpen Y V (hU.preimage f)
  letI : IsDomain B := inferInstanceAs (IsDomain Γ(Y, V))
  letI : Module.Finite A B := f.finite_app U hU
  letI : Algebra.Etale A B := by
    have he := f.etale_appLE hU (hU.preimage f) le_rfl
    rwa [← f.app_eq_appLE] at he
  letI : Algebra.IsPushout A E B L := fractionFields_isPushout fun a b hab => by
    have h := congrArg (algebraMap B L) hab
    simp only [← IsScalarTower.algebraMap_apply A B L, IsScalarTower.algebraMap_apply A E L] at h
    exact (X.germToFunctionField_injective U) ((algebraMap E L).injective h)
  change traceDR k E L ((ExteriorDifferentials.map iB p ω : ExteriorDifferentials k L p) : DR k L) =
    (ExteriorDifferentials.map iA p (affineFormTrace hf hU p ω) : DR k E)
  rw [traceDR_degree, ← algebraFormPullback_eq_map k B L iB rfl,
    ← algebraFormPullback_eq_map k A E iA rfl]
  exact congrArg Subtype.val (finiteEtaleFormTrace_baseChange p ω)

end GlobalTheory.SchemeCohomology
