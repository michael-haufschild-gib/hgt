import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.FiniteFunctionField
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.SectionFunctionField
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen

/-! Function fields of finite étale morphisms of integral schemes. -/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open GaloisForLFunctions.HTGeometry

namespace GlobalTheory.SchemeCohomology

variable {Y Z : Scheme.{0}} [IsIntegral Y] [IsIntegral Z] (c : Y ⟶ Z)

/-- A nonempty étale morphism to an integral scheme is dominant. -/
theorem isDominant_of_etale [Etale c] : IsDominant c :=
  (isDominant_iff c).mpr (c.isOpenMap.isOpen_range.dense (Set.range_nonempty c))

variable {k : Type} [Field k]
  {s : Z ⟶ Spec (CommRingCat.of k)} {t : Y ⟶ Spec (CommRingCat.of k)}

/-- Pullback of the function field as an algebra map over the base field. -/
def functionFieldPullbackAlg [IsDominant c] (hc : c ≫ s = t) :
    letI := sectionFunctionFieldAlgebra s
    letI := sectionFunctionFieldAlgebra t
    Z.functionField →ₐ[k] Y.functionField := by
  let A := Over.mk s
  let B := Over.mk t
  letI : IsIntegral A.left := ‹IsIntegral Z›
  letI : IsIntegral B.left := ‹IsIntegral Y›
  let g : B ⟶ A := Over.homMk c hc
  letI : IsDominant g.left := ‹IsDominant c›
  exact overFunctionFieldPullback B g

/-- Pullback of the function field carries a generic germ to the germ of
the pulled-back section. -/
theorem functionFieldPullbackAlg_germ [IsDominant c] (hc : c ≫ s = t)
    (U : Z.Opens) (hU : genericPoint Z ∈ U) (hV : genericPoint Y ∈ c ⁻¹ᵁ U) (a : Γ(Z, U)) :
    letI := sectionFunctionFieldAlgebra s
    letI := sectionFunctionFieldAlgebra t
    functionFieldPullbackAlg c hc ((Z.presheaf.germ U _ hU).hom a) =
      (Y.presheaf.germ (c ⁻¹ᵁ U) _ hV).hom ((c.app U).hom a) :=
  c.functionFieldPullback_germ U hU a

/-- A finite dominant map makes the source function field finite over the
target function field, with scalars given by pullback. -/
theorem finiteDimensional_functionFieldPullback [IsFinite c] [IsDominant c] :
    letI := c.functionFieldPullback.hom.toAlgebra
    FiniteDimensional Z.functionField Y.functionField := by
  letI := c.functionFieldPullback.hom.toAlgebra
  let η := genericPoint Z
  let U := (Z.affineCover.f (Z.affineCover.idx η)).opensRange
  have hU : IsAffineOpen U := isAffineOpen_opensRange _
  have hη : genericPoint Z ∈ U := Z.affineCover.covers η
  let V := c ⁻¹ᵁ U
  have hV : IsAffineOpen V := hU.preimage c
  have hη' : genericPoint Y ∈ V := by
    change c (genericPoint Y) ∈ U
    rw [c.map_genericPoint_of_isDominant]
    exact hη
  letI : Nonempty V := ⟨⟨genericPoint Y, hη'⟩⟩
  letI : IsFractionRing Γ(Y, V) Y.functionField := functionField_isFractionRing_of_isAffineOpen Y V hV
  let g := (Y.germToFunctionField V).hom
  apply finiteDimensional_of_finite_fraction_image (c.app U).hom (c.finite_app U hU) g
  · intro a
    exact ⟨(Z.presheaf.germ U (genericPoint Z) hη).hom a,
      c.functionFieldPullback_germ U hη a⟩
  · intro z
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective Γ(Y, V) z
    have hgb : g b ≠ 0 := fun h => (mem_nonZeroDivisors_iff_ne_zero.mp hb)
      ((Y.germToFunctionField_injective V) (h.trans (map_zero g).symm))
    exact ⟨a, b, hgb, div_mul_cancel₀ _ hgb⟩

end GlobalTheory.SchemeCohomology
