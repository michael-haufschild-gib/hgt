import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.RingTheory.Smooth.StandardSmoothCotangent

/-!
# Jacobians annihilate relative Kähler differentials

For a square polynomial presentation, the determinant of the relation matrix annihilates the
cokernel of that matrix.  The cotangent exact sequence identifies this cokernel with the relative
Kähler differentials, so the presentation Jacobian annihilates every relative differential.

No regular-sequence, smoothness, domain, or finiteness hypothesis on the algebra is needed.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open Algebra Module MvPolynomial
open scoped Matrix

universe u v w

section LinearAlgebra

variable {R : Type u} [CommRing R]
variable {ι : Type v} [Fintype ι] [DecidableEq ι]

/-- The determinant of an endomorphism of a finite free coordinate module kills its cokernel.
The adjugate of the coordinate matrix produces the required preimage. -/
theorem LinearMap.det_smul_mem_range (f : (ι → R) →ₗ[R] (ι → R)) (x : ι → R) :
    f.det • x ∈ LinearMap.range f := by
  refine ⟨Matrix.adjugate (LinearMap.toMatrix' f) *ᵥ x, ?_⟩
  calc
    f (Matrix.adjugate (LinearMap.toMatrix' f) *ᵥ x)
        = LinearMap.toMatrix' f *ᵥ (Matrix.adjugate (LinearMap.toMatrix' f) *ᵥ x) := by
          rw [LinearMap.toMatrix'_mulVec]
    _ = (LinearMap.toMatrix' f * Matrix.adjugate (LinearMap.toMatrix' f)) *ᵥ x := by
          rw [Matrix.mulVec_mulVec]
    _ = ((LinearMap.toMatrix' f).det • (1 : Matrix ι ι R)) *ᵥ x := by rw [Matrix.mul_adjugate]
    _ = (LinearMap.toMatrix' f).det • x := by rw [Matrix.smul_mulVec, Matrix.one_mulVec]
    _ = f.det • x := by rw [LinearMap.det_toMatrix']

end LinearAlgebra

section Presentation

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable {ι : Type w} [Fintype ι] [DecidableEq ι]

namespace Algebra.PreSubmersivePresentation

variable (P : Algebra.PreSubmersivePresentation R S ι ι)

/-- Linear combination of the distinguished presentation relations in the conormal module. -/
noncomputable def relationCotangent :
    (ι → S) →ₗ[S] P.toExtension.Cotangent :=
  Basis.constr (Pi.basisFun S ι) S fun i =>
    Algebra.Extension.Cotangent.mk (P := P.toExtension) ⟨P.relation i, P.relation_mem_ker i⟩

@[simp]
theorem relationCotangent_single (i : ι) :
    relationCotangent P (Pi.single i 1) =
      Algebra.Extension.Cotangent.mk (P := P.toExtension)
        ⟨P.relation i, P.relation_mem_ker i⟩ := by
  rw [relationCotangent, ← Pi.basisFun_apply, Basis.constr_basis]

/-- For the identity matching of equations with variables, the presentation differential is the
coordinate matrix of the cotangent-complex map on the distinguished relations. -/
theorem repr_cotangentComplex_relationCotangent
    (hmap : P.map = _root_.id) (x : ι → S) :
    P.cotangentSpaceBasis.repr
        (P.toExtension.cotangentComplex (relationCotangent P x)) =
      (Finsupp.linearEquivFunOnFinite S S ι).symm (P.aevalDifferential x) := by
  have key :
      (P.cotangentSpaceBasis.repr.toLinearMap ∘ₗ
          P.toExtension.cotangentComplex ∘ₗ relationCotangent P) =
        (Finsupp.linearEquivFunOnFinite S S ι).symm.toLinearMap ∘ₗ P.aevalDifferential := by
    apply (Pi.basisFun S ι).ext
    intro i
    ext j
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, Pi.basisFun_apply,
      relationCotangent_single, Algebra.Extension.cotangentComplex_mk,
      Finsupp.linearEquivFunOnFinite_symm_apply,
      PreSubmersivePresentation.aevalDifferential_single, hmap, id_eq]
    exact (Generators.cotangentSpaceBasis_repr_tmul _ 1 (P.relation i) j).trans (one_mul _)
  exact LinearMap.congr_fun key x

/-- **Square-presentation Jacobian annihilator.**  When the distinguished relation-to-variable
map is the identity, the presentation Jacobian annihilates every relative Kähler differential. -/
theorem jacobian_smul_kaehler_eq_zero
    (hmap : P.map = _root_.id) (ω : Ω[S⁄R]) :
    P.jacobian • ω = 0 := by
  obtain ⟨x, rfl⟩ := P.toExtension.toKaehler_surjective ω
  obtain ⟨y, hy⟩ :=
    LinearMap.det_smul_mem_range P.aevalDifferential (P.cotangentSpaceBasis.repr x)
  have hz : P.toExtension.cotangentComplex (relationCotangent P y) = P.jacobian • x := by
    apply P.cotangentSpaceBasis.repr.injective
    rw [repr_cotangentComplex_relationCotangent P hmap, hy,
      P.jacobian_eq_det_aevalDifferential, map_smul, map_smul]
    congr 1
    ext j
    simp
  rw [← map_smul, ← hz]
  exact P.toExtension.exact_cotangentComplex_toKaehler.apply_apply_eq_zero _

end Algebra.PreSubmersivePresentation

end Presentation

end

end GaloisForLFunctions.HTGeometry
