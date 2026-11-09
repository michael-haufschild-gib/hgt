import GaloisForLFunctions.HTGeometry.SingularIntegralCokernel
import Mathlib.RingTheory.Discriminant
import Mathlib.LinearAlgebra.Dual.Basis

/-!
# Integral trace discriminants as cokernel counts

The dual basis converts a bilinear form into a lattice endomorphism with
the transposed Gram matrix. Its actual cokernel therefore has cardinality
the absolute Gram determinant, including the infinite singular case.
-/

noncomputable section
namespace GaloisForLFunctions.HTGeometry
open Module

/-- The absolute Gram determinant counts the cokernel of any integral bilinear form. -/
theorem card_bilinearCokernel_eq_natAbs_det
    {L ι : Type*} [AddCommGroup L]
    [Module.Free ℤ L] [Module.Finite ℤ L] [Fintype ι] [DecidableEq ι]
    (b : Basis ι ℤ L) (B : LinearMap.BilinForm ℤ L) :
    Nat.card (Module.Dual ℤ L ⧸ LinearMap.range B) = (B.toMatrix b).det.natAbs := by
  let e : Module.Dual ℤ L ≃ₗ[ℤ] L := b.dualBasis.equivFun.trans b.equivFun.symm
  let F : L →ₗ[ℤ] L := e.toLinearMap.comp B
  let q := Submodule.Quotient.equiv (LinearMap.range B) (LinearMap.range F) e (by
      change Submodule.map e.toLinearMap (LinearMap.range B) =
        LinearMap.range (e.toLinearMap.comp B)
      rw [LinearMap.range_comp])
  rw [Nat.card_congr q.toEquiv, LinearMap.card_quotient_range_eq_natAbs_det_all,
    ← LinearMap.det_toMatrix b]
  have hm : LinearMap.toMatrix b b F = (B.toMatrix b).transpose := by
    ext i j
    simp only [LinearMap.toMatrix_apply, Matrix.transpose_apply, LinearMap.BilinForm.toMatrix_apply]
    change b.equivFun (e (B (b j))) i = B (b j) (b i)
    simp only [e, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply,
      Basis.equivFun_apply, Basis.dualBasis_repr]
  rw [hm, Matrix.det_transpose]

/-- An integral algebra's trace discriminant counts its actual trace cokernel. -/
theorem card_traceCokernel_eq_natAbs_discr
    {A ι : Type*} [CommRing A]
    [Module.Free ℤ A] [Module.Finite ℤ A] [Fintype ι] [DecidableEq ι]
    (b : Basis ι ℤ A) :
    Nat.card (Module.Dual ℤ A ⧸ LinearMap.range (Algebra.traceForm ℤ A)) =
      (Algebra.discr ℤ b).natAbs := by
  rw [card_bilinearCokernel_eq_natAbs_det b, Algebra.discr_def, Algebra.traceMatrix_of_basis]

#print axioms card_bilinearCokernel_eq_natAbs_det
#print axioms card_traceCokernel_eq_natAbs_discr
end GaloisForLFunctions.HTGeometry
