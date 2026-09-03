import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.Finiteness.Basic

/-!
# Integral closures under compatible ring equivalences

This file transports an integral closure across a commutative square of ring equivalences.  It
also transfers module-finiteness across such a square.  The base rings may differ, so the relevant
module equivalence is semilinear rather than linear.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

universe u v w x

variable {A : Type u} {A' : Type v} {B : Type w} {B' : Type x}
  [CommRing A] [CommRing A'] [CommRing B] [CommRing B']

/-- Integrality is preserved by a commutative square of ring equivalences. -/
theorem isIntegral_map_of_ringEquiv_square
    (f : A →+* B) (f' : A' →+* B') (eA : A ≃+* A') (eB : B ≃+* B')
    (h : eB.toRingHom.comp f = f'.comp eA.toRingHom)
    {z : B} (hz : @IsIntegral A B _ _ f.toAlgebra z) :
    @IsIntegral A' B' _ _ f'.toAlgebra (eB z) := by
  letI : Algebra A B := f.toAlgebra
  letI : Algebra A' B' := f'.toAlgebra
  letI : Algebra A B' := (f'.comp eA.toRingHom).toAlgebra
  let g : B →ₐ[A] B' :=
    { eB.toRingHom with
      commutes' := fun a => RingHom.congr_fun h a }
  have hz' : IsIntegral A (eB z) := hz.map g
  exact (eA.isIntegral_iff (by rfl) (eB z)).mp hz'

/-- The inverse equivalences form the inverse commutative square. -/
theorem ringEquiv_inverse_square
    (f : A →+* B) (f' : A' →+* B') (eA : A ≃+* A') (eB : B ≃+* B')
    (h : eB.toRingHom.comp f = f'.comp eA.toRingHom) :
    eB.symm.toRingHom.comp f' = f.comp eA.symm.toRingHom := by
  apply RingHom.ext
  intro a
  apply eB.injective
  simpa using (RingHom.congr_fun h (eA.symm a)).symm

/-- A commutative square of ring equivalences induces an equivalence of integral closures. -/
noncomputable def integralClosureRingEquivOfSquare
    (f : A →+* B) (f' : A' →+* B') (eA : A ≃+* A') (eB : B ≃+* B')
    (h : eB.toRingHom.comp f = f'.comp eA.toRingHom) :
    @integralClosure A B _ _ f.toAlgebra ≃+*
      @integralClosure A' B' _ _ f'.toAlgebra where
  toFun z := ⟨eB z, isIntegral_map_of_ringEquiv_square f f' eA eB h z.2⟩
  invFun z := ⟨eB.symm z,
    isIntegral_map_of_ringEquiv_square f' f eA.symm eB.symm
      (ringEquiv_inverse_square f f' eA eB h) z.2⟩
  left_inv z := Subtype.ext (eB.symm_apply_apply z)
  right_inv z := Subtype.ext (eB.apply_symm_apply z)
  map_mul' x y := Subtype.ext (eB.map_mul x y)
  map_add' x y := Subtype.ext (eB.map_add x y)

/-- Finiteness of a ring homomorphism transfers backwards across a commutative square of ring
equivalences. -/
theorem ringHomFinite_of_equiv_square
    (f : A →+* B) (f' : A' →+* B') (eA : A ≃+* A') (eB : B ≃+* B')
    (h : eB.toRingHom.comp f = f'.comp eA.toRingHom)
    (hf' : f'.Finite) : f.Finite := by
  letI : Algebra A B := f.toAlgebra
  letI : Algebra A' B' := f'.toAlgebra
  haveI : Module.Finite A' B' := hf'
  let e : B' →ₛₗ[eA.symm.toRingHom] B :=
    { eB.symm.toAddEquiv with
      map_smul' := fun a b => by
        change eB.symm (f' a * b) = f (eA.symm a) * eB.symm b
        rw [map_mul]
        congr 1
        apply eB.injective
        simpa using (RingHom.congr_fun h (eA.symm a)).symm }
  letI : RingHomSurjective eA.symm.toRingHom :=
    ⟨eA.symm.surjective⟩
  exact Module.Finite.of_surjective e eB.symm.surjective

/-- Module-finiteness of an integral closure transfers across compatible base and ambient ring
equivalences. -/
theorem ringHomFinite_integralClosure_of_equiv_square
    (f : A →+* B) (f' : A' →+* B') (eA : A ≃+* A') (eB : B ≃+* B')
    (h : eB.toRingHom.comp f = f'.comp eA.toRingHom)
    [Module.Finite A' (@integralClosure A' B' _ _ f'.toAlgebra)] :
    RingHom.Finite
      (algebraMap A (@integralClosure A B _ _ f.toAlgebra)) := by
  let icEquiv := integralClosureRingEquivOfSquare f f' eA eB h
  apply ringHomFinite_of_equiv_square
    (algebraMap A (@integralClosure A B _ _ f.toAlgebra))
    (algebraMap A' (@integralClosure A' B' _ _ f'.toAlgebra)) eA icEquiv
  · apply RingHom.ext
    intro a
    apply Subtype.ext
    exact RingHom.congr_fun h a
  · rw [RingHom.finite_algebraMap]
    infer_instance

end

end GaloisForLFunctions.HTGeometry
