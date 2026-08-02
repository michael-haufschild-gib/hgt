import GaloisForLFunctions.HTGeometry.FunctionFieldPullback
import GaloisForLFunctions.HTGeometry.AbelianVariety
import GaloisForLFunctions.HTGeometry.FiniteShadowCapacity
import GaloisForLFunctions.HTGeometry.FiniteGeneratorDifferentialEscape
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-!
# Proper compact-kernel function-field capacity

The generic stalk of a dominant locally finite-type morphism of integral schemes is an essentially
finite-type field extension.  Hence its relative function field has finite transcendence degree.
An integer-indexed orbit which factors through such a field cannot be differentially independent:
its zero-jets would already form an impossible countable algebraically independent family.

This supplies the missing direct function-field source for active-quasi-Abelian faithfulness.  The
final theorem no longer assumes compact-kernel cyclic non-independence.  It derives that
non-independence from a proper relative function field and the literal factorization of kernel
orbits through that field.
-/

open CategoryTheory TopologicalSpace
open MonoidalCategory CartesianMonoidalCategory MonObj

namespace AlgebraicGeometry

universe u

noncomputable section

/-- Pullback on function fields along a dominant locally finite-type morphism is essentially of
finite type.  The only extra factor in function-field pullback is the canonical isomorphism
between the two equal generic stalks. -/
theorem Scheme.Hom.functionFieldPullback_essFiniteType
    {X S : Scheme.{u}} [IsIntegral X] [IsIntegral S]
    (s : X ⟶ S) [IsDominant s] [LocallyOfFiniteType s] :
    letI := s.functionFieldAlgebra
    Algebra.EssFiniteType S.functionField X.functionField := by
  letI := s.functionFieldAlgebra
  rw [← RingHom.essFiniteType_algebraMap]
  change s.functionFieldPullback.hom.EssFiniteType
  let e : Inseparable (s (genericPoint X)) (genericPoint S) :=
    Inseparable.of_eq s.map_genericPoint_of_isDominant
  have hfirst :
      (S.presheaf.stalkSpecializes s.dominantGenericSpecializes).hom.EssFiniteType := by
    have heq :
        S.presheaf.stalkSpecializes s.dominantGenericSpecializes =
          (S.presheaf.stalkCongr e).inv := by
      change S.presheaf.stalkSpecializes s.dominantGenericSpecializes =
        S.presheaf.stalkSpecializes e.le
      rfl
    rw [heq]
    exact (RingHom.FiniteType.of_surjective _
      (fun y => ⟨(S.presheaf.stalkCongr e).hom y,
        (S.presheaf.stalkCongr e).hom_inv_id_apply y⟩)).essFiniteType
  exact hfirst.comp (LocallyOfFiniteType.stalkMap s (genericPoint X))

/-- The relative function field of a dominant locally finite-type morphism of integral schemes
has finite transcendence degree. -/
theorem Scheme.Hom.functionField_trdeg_lt_aleph0
    {X S : Scheme.{u}} [IsIntegral X] [IsIntegral S]
    (s : X ⟶ S) [IsDominant s] [LocallyOfFiniteType s] :
    letI := s.functionFieldAlgebra
    Algebra.trdeg S.functionField X.functionField < Cardinal.aleph0 := by
  letI := s.functionFieldAlgebra
  letI : Algebra.EssFiniteType S.functionField X.functionField :=
    s.functionFieldPullback_essFiniteType
  obtain ⟨generators, hgenerators⟩ :=
    IntermediateField.fg_top S.functionField X.functionField
  let generator : {x // x ∈ generators} → X.functionField := fun x => x.1
  have hrange : Set.range generator = (generators : Set X.functionField) := by
    ext x
    simp [generator]
  have hadjoin :
      IntermediateField.adjoin S.functionField (Set.range generator) = ⊤ := by
    rw [hrange, hgenerators]
  have hfinite :=
    GaloisForLFunctions.HTGeometry.adjoin_range_trdeg_lt_aleph0
      (F := S.functionField) (E := X.functionField) generator
  rw [hadjoin] at hfinite
  let e : (⊤ : IntermediateField S.functionField X.functionField) ≃ₐ[S.functionField]
      X.functionField := IntermediateField.topEquiv
  rw [← e.trdeg_eq]
  exact hfinite

end


end AlgebraicGeometry

namespace GaloisForLFunctions.HTGeometry

open AlgebraicGeometry
open scoped Differential

noncomputable section

universe u

/-- An integer-indexed family in a finite-transcendence field cannot be differentially
independent. -/
theorem finiteTrdeg_int_not_differentialIndependent
    {F E : Type*} [Field F] [Field E] [Algebra F E] [Differential E]
    (hfinite : Algebra.trdeg F E < Cardinal.aleph0) (x : ℤ → E) :
    ¬ DifferentialIndependent F x := by
  intro hx
  have hle := hx.algebraicIndependent.lift_cardinalMk_le_trdeg
  have haleph : Cardinal.aleph0 ≤ Algebra.trdeg F E := by
    simpa using hle
  exact (not_lt_of_ge haleph) hfinite

/-- Every integer family in a proper relative function field has finite differential capacity.
Properness supplies local finite type, and the preceding generic-stalk theorem supplies the finite
transcendence bound. -/
theorem properRelativeFunctionField_int_not_differentialIndependent
    {S X : Scheme.{u}} [IsIntegral S] [IsIntegral X]
    (p : X ⟶ S) [IsDominant p] [IsProper p]
    [Differential X.functionField] (x : ℤ → X.functionField) :
    letI := p.functionFieldAlgebra
    ¬ DifferentialIndependent S.functionField x := by
  letI := p.functionFieldAlgebra
  exact finiteTrdeg_int_not_differentialIndependent
    p.functionField_trdeg_lt_aleph0 x

/-- The complete cyclic translation orbit of any rational function on an Abelian variety has
finite differential capacity.  The exponent `n : ℤ` is the literal group power of the translating
rational point, and the orbit is the induced pullback on the actual scheme function field. -/
theorem abelianVarietyTranslationFunctionField_intOrbit_not_differentialIndependent
    {K : Type u} [Field K]
    (A : Over (Spec (.of K))) [GrpObj A] [IsAbelianVariety A]
    [Differential A.left.functionField]
    (x : 𝟙_ (Over (Spec (.of K))) ⟶ A) (z : A.left.functionField) :
    letI := A.hom.functionFieldAlgebra
    ¬ DifferentialIndependent (Spec (.of K)).functionField
      (fun n : ℤ =>
        (abelianVarietyTranslationSchemeIso A (x ^ n)).hom.functionFieldPullback z) := by
  letI := A.hom.functionFieldAlgebra
  exact finiteTrdeg_int_not_differentialIndependent
    A.hom.functionField_trdeg_lt_aleph0 _

/-- If an integer orbit factors injectively through a finite-transcendence field, it cannot be
differentially independent in the ambient differential field. -/
theorem finiteTrdeg_factorized_intOrbit_not_differentialIndependent
    {F E K : Type*} [Field F] [Field E] [Field K]
    [Algebra F E] [Algebra F K] [Differential K]
    (hfinite : Algebra.trdeg F E < Cardinal.aleph0)
    (embed : E →ₐ[F] K) (hembed : Function.Injective embed)
    (compactOrbit : ℤ → E) (orbit : ℤ → K)
    (hfactor : ∀ n, orbit n = embed (compactOrbit n)) :
    ¬ DifferentialIndependent F orbit := by
  intro horbit
  have heq : orbit = fun n => embed (compactOrbit n) := funext hfactor
  rw [heq] at horbit
  have himage : AlgebraicIndependent F (fun n => embed (compactOrbit n)) :=
    horbit.algebraicIndependent
  have hcompact : AlgebraicIndependent F compactOrbit :=
    (AlgHom.algebraicIndependent_iff embed hembed).mp himage
  have hle := hcompact.lift_cardinalMk_le_trdeg
  have haleph : Cardinal.aleph0 ≤ Algebra.trdeg F E := by
    simpa using hle
  exact (not_lt_of_ge haleph) hfinite

/-- **Direct active-quotient necessity from a proper compact-kernel function field.**

Let a torsion-free structural lattice carry a completely differentially free orbit.  Suppose every
cyclic orbit killed by the active quotient factors through one proper relative function field.
Then the active quotient map is injective.  Compact-kernel cyclic non-independence is derived from
properness and factorization; it is not a hypothesis. -/
theorem activeQuotient_injective_of_fullOrbitFree_of_properKernelFunctionField
    {S X : Scheme.{u}} [IsIntegral S] [IsIntegral X]
    (p : X ⟶ S) [IsDominant p] [IsProper p]
    {K L Q : Type*} [Field K] [Algebra S.functionField K] [Differential K]
    [AddCommGroup L] [AddCommGroup Q]
    (embed : X.functionField →+* K)
    (hembed : Function.Injective embed)
    (hembed_base : ∀ r : S.functionField,
      embed (p.functionFieldPullback r) = algebraMap S.functionField K r)
    (compactOrbit : L → ℤ → X.functionField)
    (orbit : L → K) (horbit : DifferentialIndependent S.functionField orbit)
    (q : L →+ Q)
    (hcyclic : ∀ k : L, k ≠ 0 → Function.Injective (fun n : ℤ => n • k))
    (hfactor : ∀ k : L, q k = 0 → k ≠ 0 → ∀ n : ℤ,
      orbit (n • k) = embed (compactOrbit k n)) :
    Function.Injective q := by
  letI := p.functionFieldAlgebra
  let embedAlg : X.functionField →ₐ[S.functionField] K :=
    { toRingHom := embed
      commutes' := hembed_base }
  have hfinite :
      Algebra.trdeg S.functionField X.functionField < Cardinal.aleph0 :=
    p.functionField_trdeg_lt_aleph0
  apply activeQuotient_injective_of_fullOrbitFree_of_kernelCyclic_not
    orbit horbit q hcyclic
  intro k hkq hkne
  exact finiteTrdeg_factorized_intOrbit_not_differentialIndependent
    hfinite embedAlg hembed (compactOrbit k) (fun n : ℤ => orbit (n • k))
    (hfactor k hkq hkne)

/-- Least-dimension consequence of active-palette extraction: every full HT realization supplies
an active quasi-Abelian palette in the same ambient dimension. -/
theorem activeQuasiAbelianDimension_le_hypertranscendenceDimension
    (FullHTRealizable ActivePaletteRealizable : ℕ → Prop)
    (htDim aqaDim : ℕ)
    (hfull : FullHTRealizable htDim)
    (extract : ∀ d, FullHTRealizable d → ActivePaletteRealizable d)
    (haqaLeast : ∀ d, ActivePaletteRealizable d → aqaDim ≤ d) :
    aqaDim ≤ htDim :=
  haqaLeast htDim (extract htDim hfull)

end


end GaloisForLFunctions.HTGeometry
