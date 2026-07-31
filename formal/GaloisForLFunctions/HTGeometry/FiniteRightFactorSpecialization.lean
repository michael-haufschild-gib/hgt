import GaloisForLFunctions.HTGeometry.FiniteTypeSpecialization
import Mathlib.RingTheory.TensorProduct.DirectLimitFG
import Mathlib.RingTheory.Flat.Basic

/-!
# Finite support for an arbitrary tensor factor

An element of `A tensor_C B` involves only a finitely generated `C`-subalgebra of the
possibly enormous right factor `B`.  This module turns that direct-limit fact into the exact
interface required by `FiniteTypeSpecialization`.

Two tensors can be lifted simultaneously to one finitely generated right subalgebra.  The
canonical map back to the original tensor product is injective over a field, and it intertwines
an automorphism acting on the left factor.  Consequently the rational product-specialization
descent theorem applies to a certificate over an arbitrary right domain: finite type is recovered
from the numerator and denominator rather than imposed on the whole coefficient algebra.
-/

open scoped TensorProduct

namespace GaloisForLFunctions

noncomputable section

/-- The canonical map obtained by including a right subalgebra into the original tensor factor. -/
def tensorRightSubalgebraMap
    (C A B : Type*) [CommSemiring C] [CommSemiring A] [CommSemiring B]
    [Algebra C A] [Algebra C B] (R : Subalgebra C B) :
    (A ⊗[C] R) →ₐ[C] (A ⊗[C] B) :=
  Algebra.TensorProduct.map (AlgHom.id C A) R.val

@[simp] theorem tensorRightSubalgebraMap_tmul
    (C A B : Type*) [CommSemiring C] [CommSemiring A] [CommSemiring B]
    [Algebra C A] [Algebra C B] (R : Subalgebra C B)
    (a : A) (r : R) :
    tensorRightSubalgebraMap C A B R (a ⊗ₜ[C] r) =
      a ⊗ₜ[C] (r : B) :=
  rfl

/-- Enlarging the finite right subalgebra does not change the resulting tensor in the ambient
product. -/
theorem tensorRightSubalgebraMap_map_inclusion
    (C A B : Type*) [CommSemiring C] [CommSemiring A] [CommSemiring B]
    [Algebra C A] [Algebra C B]
    {R S : Subalgebra C B} (hRS : R ≤ S) (x : A ⊗[C] R) :
    tensorRightSubalgebraMap C A B S
        (Algebra.TensorProduct.map (AlgHom.id C A)
          (Subalgebra.inclusion hRS) x) =
      tensorRightSubalgebraMap C A B R x := by
  induction x with
  | zero => simp
  | tmul a r => rfl
  | add x y hx hy => simp [hx, hy]

/-- After commuting tensor factors, the right-subalgebra map is ordinary right tensoring of the
subalgebra inclusion. -/
theorem comm_tensorRightSubalgebraMap
    (C A B : Type*) [CommSemiring C] [CommSemiring A] [CommSemiring B]
    [Algebra C A] [Algebra C B] (R : Subalgebra C B)
    (x : A ⊗[C] R) :
    Algebra.TensorProduct.comm C A B
        (tensorRightSubalgebraMap C A B R x) =
      LinearMap.rTensor A R.val.toLinearMap
        (Algebra.TensorProduct.comm C A R x) := by
  induction x with
  | zero => simp
  | tmul a r => rfl
  | add x y hx hy => simp [hx, hy]

/-- Over a field, inclusion of a right subalgebra remains injective after tensoring with an
arbitrary algebra. -/
theorem tensorRightSubalgebraMap_injective
    (C A B : Type*) [Field C] [CommRing A] [CommRing B]
    [Algebra C A] [Algebra C B] (R : Subalgebra C B) :
    Function.Injective (tensorRightSubalgebraMap C A B R) := by
  intro x y hxy
  apply (Algebra.TensorProduct.comm C A R).injective
  have hcomm := congrArg (Algebra.TensorProduct.comm C A B) hxy
  rw [comm_tensorRightSubalgebraMap, comm_tensorRightSubalgebraMap] at hcomm
  exact Module.Flat.rTensor_preserves_injective_linearMap
    (M := A) R.val.toLinearMap (fun _ _ h => Subtype.ext h) hcomm

/-- The right-subalgebra inclusion intertwines every automorphism acting on the left tensor
factor. -/
theorem tensorRightSubalgebraMap_tensorLeftAction
    (C A B : Type*) [CommSemiring C] [CommSemiring A] [CommSemiring B]
    [Algebra C A] [Algebra C B]
    (R : Subalgebra C B) (sigma : A ≃ₐ[C] A) (x : A ⊗[C] R) :
    tensorRightSubalgebraMap C A B R
        (tensorLeftAction C A R sigma x) =
      tensorLeftAction C A B sigma
        (tensorRightSubalgebraMap C A B R x) := by
  induction x with
  | zero => simp
  | tmul a r => rfl
  | add x y hx hy => simp [hx, hy]

/-- Every tensor over an arbitrary right algebra is already defined over a finitely generated
right subalgebra. -/
theorem exists_fg_right_subalgebra_lift
    (C A B : Type*) [CommSemiring C] [CommSemiring A] [CommSemiring B]
    [Algebra C A] [Algebra C B] (x : A ⊗[C] B) :
    ∃ R : Subalgebra C B, R.FG ∧
      ∃ xR : A ⊗[C] R,
        tensorRightSubalgebraMap C A B R xR = x := by
  classical
  let xcomm : B ⊗[C] A := Algebra.TensorProduct.comm C A B x
  obtain ⟨R, hR, hx⟩ := TensorProduct.Algebra.exists_of_fg xcomm
  obtain ⟨u, hu⟩ := hx
  let xR : A ⊗[C] R :=
    (Algebra.TensorProduct.comm C A R).symm u
  refine ⟨R, hR, xR, ?_⟩
  apply (Algebra.TensorProduct.comm C A B).injective
  rw [comm_tensorRightSubalgebraMap]
  simpa [xcomm, xR] using hu

/-- A pair of tensors admits lifts to one common finitely generated right subalgebra.  This is the
numerator-denominator form used for fraction certificates. -/
theorem exists_fg_right_subalgebra_lifts_pair
    (C A B : Type*) [CommSemiring C] [CommSemiring A] [CommSemiring B]
    [Algebra C A] [Algebra C B] (x y : A ⊗[C] B) :
    ∃ R : Subalgebra C B, R.FG ∧
      ∃ xR yR : A ⊗[C] R,
        tensorRightSubalgebraMap C A B R xR = x ∧
        tensorRightSubalgebraMap C A B R yR = y := by
  classical
  obtain ⟨R, hR, xR, hxR⟩ :=
    exists_fg_right_subalgebra_lift C A B x
  obtain ⟨S, hS, yS, hyS⟩ :=
    exists_fg_right_subalgebra_lift C A B y
  let T : Subalgebra C B := R ⊔ S
  have hT : T.FG := hR.sup hS
  let xT : A ⊗[C] T :=
    Algebra.TensorProduct.map (AlgHom.id C A)
      (Subalgebra.inclusion (show R ≤ T from le_sup_left)) xR
  let yT : A ⊗[C] T :=
    Algebra.TensorProduct.map (AlgHom.id C A)
      (Subalgebra.inclusion (show S ≤ T from le_sup_right)) yS
  refine ⟨T, hT, xT, yT, ?_, ?_⟩
  · dsimp only [xT]
    rw [tensorRightSubalgebraMap_map_inclusion, hxR]
  · dsimp only [yT]
    rw [tensorRightSubalgebraMap_map_inclusion, hyS]

/-- A finitely generated subalgebra carries the finite-type instance required by algebraic
specialization. -/
theorem finiteTypeOfSubalgebraFG
    {C B : Type*} [CommSemiring C] [CommSemiring B] [Algebra C B]
    (R : Subalgebra C B) (hR : R.FG) : Algebra.FiniteType C R :=
  ⟨(Subalgebra.fg_top R).mpr hR⟩

/-- **Arbitrary-right-factor rational specialization.**  A first-order coboundary identity whose
certificate is a fraction in `A tensor_C B` already has a certificate in `A`, even when the whole
right domain `B` is not finite type.  Only the finitely many right coefficients occurring in the
chosen numerator and denominator are specialized. -/
theorem exists_left_coboundary_of_arbitrary_right_tensor_fraction_identity
    (C A B : Type*) [Field C] [IsAlgClosed C] [Field A]
    [CommRing B] [IsDomain B] [Algebra C A] [Algebra C B]
    (sigma : A ≃ₐ[C] A) (a : A) (N D : A ⊗[C] B) (hD : D ≠ 0)
    (hidentity : tensorLeftAction C A B sigma N * D -
        N * tensorLeftAction C A B sigma D =
      (a ⊗ₜ[C] (1 : B)) * tensorLeftAction C A B sigma D * D) :
    ∃ u : A, sigma u - u = a := by
  obtain ⟨R, hR, NR, DR, hNR, hDR⟩ :=
    exists_fg_right_subalgebra_lifts_pair C A B N D
  letI : Algebra.FiniteType C R := finiteTypeOfSubalgebraFG R hR
  have hDR0 : DR ≠ 0 := by
    intro hzero
    apply hD
    rw [← hDR, hzero, map_zero]
  have hidentityR : tensorLeftAction C A R sigma NR * DR -
        NR * tensorLeftAction C A R sigma DR =
      (a ⊗ₜ[C] (1 : R)) * tensorLeftAction C A R sigma DR * DR := by
    apply tensorRightSubalgebraMap_injective C A B R
    simpa only [map_sub, map_mul, tensorRightSubalgebraMap_tmul,
      tensorRightSubalgebraMap_tensorLeftAction, hNR, hDR,
      Subalgebra.coe_one] using hidentity
  exact exists_left_coboundary_of_tensor_fraction_identity
    C A R sigma a NR DR hDR0 hidentityR

end

end GaloisForLFunctions
