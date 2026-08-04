import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# The exterior power of the dual is the space of alternating forms

An element of the `n`-th exterior power of the dual of a module defines an alternating `n`-form: on
a product of linear forms it is the determinant of the matrix of their values.  For a module with a
finite basis this is an isomorphism, because the exterior products of the dual basis are sent to the
dual basis of the exterior products.  Mathlib builds the pairing but not its bijectivity.

* `formOfExterior` : the alternating form defined by an element of the exterior power of the dual.
* `pairingDual_bijective` : the pairing is bijective for a module with a finite basis.
* `formOfExteriorEquiv` : the exterior power of the dual is the space of alternating forms.
-/

namespace GaloisForLFunctions.HTGeometry

open exteriorPower Module

section Pairing

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- **The alternating form defined by an element of the exterior power of the dual.** -/
noncomputable def formOfExterior (R : Type*) [CommRing R] (M : Type*) [AddCommGroup M]
    [Module R M] (n : ℕ) : ⋀[R]^n (Module.Dual R M) →ₗ[R] (M [⋀^Fin n]→ₗ[R] R) :=
  (exteriorPower.alternatingMapLinearEquiv (R := R) (M := M) (N := R)
    (n := n)).symm.toLinearMap ∘ₗ exteriorPower.pairingDual R M n

/-- **On a product of linear forms the alternating form is the determinant** of the matrix of their
values. -/
theorem formOfExterior_ιMulti {n : ℕ} (φ : Fin n → Module.Dual R M) (v : Fin n → M) :
    formOfExterior R M n (exteriorPower.ιMulti R n φ) v =
      Matrix.det (Matrix.of fun i j => φ j (v i)) := by
  show (exteriorPower.alternatingMapLinearEquiv.symm
    (exteriorPower.pairingDual R M n (exteriorPower.ιMulti R n φ))) v = _
  rw [exteriorPower.alternatingMapLinearEquiv_symm_apply]
  show ((exteriorPower.pairingDual R M n) ((exteriorPower.ιMulti R n) φ))
    ((exteriorPower.ιMulti R n) v) = _
  rw [exteriorPower.pairingDual_ιMulti_ιMulti]

end Pairing

section Bijective

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  {I : Type*} [LinearOrder I] [Fintype I] [DecidableEq I]

/-- The pairing sends the exterior products of the dual basis to the dual basis of the exterior
products. -/
theorem pairingDual_dualBasis_exteriorPower (n : ℕ) (b : Module.Basis I R M)
    (s : Set.powersetCard I n) :
    exteriorPower.pairingDual R M n ((b.dualBasis).exteriorPower n s) =
      ((b.exteriorPower n).dualBasis) s := by
  classical
  rw [exteriorPower.basis_apply]
  have hcoe : ⇑b.dualBasis = b.coord := Module.Basis.coe_dualBasis b
  rw [hcoe]
  show exteriorPower.ιMultiDual R n b s = _
  rw [← exteriorPower.basis_coord]
  exact (congrFun (Module.Basis.coe_dualBasis (b.exteriorPower n)) s).symm

/-- **The pairing between the exterior power of the dual and the dual of the exterior power is
bijective** for a module with a finite basis. -/
theorem pairingDual_bijective (n : ℕ) (b : Module.Basis I R M) :
    Function.Bijective (exteriorPower.pairingDual R M n) := by
  classical
  have h : (exteriorPower.pairingDual R M n) =
      (((b.dualBasis).exteriorPower n).equiv ((b.exteriorPower n).dualBasis)
        (Equiv.refl _)).toLinearMap := by
    refine Module.Basis.ext ((b.dualBasis).exteriorPower n) fun s => ?_
    rw [pairingDual_dualBasis_exteriorPower]
    show _ = (((b.dualBasis).exteriorPower n).equiv ((b.exteriorPower n).dualBasis)
      (Equiv.refl _)) ((b.dualBasis).exteriorPower n s)
    rw [Module.Basis.equiv_apply]
    rfl
  rw [h]
  exact (((b.dualBasis).exteriorPower n).equiv ((b.exteriorPower n).dualBasis)
    (Equiv.refl _)).bijective

/-- **The exterior power of the dual is the space of alternating forms** on a module with a finite
basis. -/
noncomputable def formOfExteriorEquiv (n : ℕ) (b : Module.Basis I R M) :
    ⋀[R]^n (Module.Dual R M) ≃ₗ[R] (M [⋀^Fin n]→ₗ[R] R) :=
  (LinearEquiv.ofBijective (exteriorPower.pairingDual R M n)
    (pairingDual_bijective n b)).trans
    (exteriorPower.alternatingMapLinearEquiv (R := R) (M := M) (N := R) (n := n)).symm

theorem formOfExteriorEquiv_apply (n : ℕ) (b : Module.Basis I R M)
    (x : ⋀[R]^n (Module.Dual R M)) : formOfExteriorEquiv n b x = formOfExterior R M n x := rfl

end Bijective

end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HTGeometry

open exteriorPower Module

section Naturality

variable {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {n : ℕ}

/-- Composition of an alternating form with a linear map, as a linear map in the form. -/
def compLinearMapₗ (T : M →ₗ[R] N) :
    (N [⋀^Fin n]→ₗ[R] R) →ₗ[R] (M [⋀^Fin n]→ₗ[R] R) where
  toFun α := α.compLinearMap T
  map_add' α β := by ext v; rfl
  map_smul' c α := by ext v; rfl

/-- **The alternating form of an element of the exterior power of the dual is natural**: transport
along the exterior power of the transpose is composition with the map. -/
theorem formOfExterior_map_dualMap (n : ℕ) (T : M →ₗ[R] N)
    (x : ⋀[R]^n (Module.Dual R N)) :
    formOfExterior R M n (exteriorPower.map n (T.dualMap) x) =
      (formOfExterior R N n x).compLinearMap T := by
  have hgen : ∀ φ : Fin n → Module.Dual R N,
      formOfExterior R M n (exteriorPower.map n (T.dualMap) (exteriorPower.ιMulti R n φ)) =
        (formOfExterior R N n (exteriorPower.ιMulti R n φ)).compLinearMap T := by
    intro φ
    ext v
    rw [exteriorPower.map_apply_ιMulti, formOfExterior_ιMulti]
    show _ = formOfExterior R N n (exteriorPower.ιMulti R n φ) fun i => T (v i)
    rw [formOfExterior_ιMulti]
    congr 1
  have hlin : ((formOfExterior R M n).comp (exteriorPower.map n (T.dualMap))) =
      (compLinearMapₗ (n := n) T).comp (formOfExterior R N n) := by
    refine exteriorPower.linearMap_ext ?_
    exact AlternatingMap.ext fun φ => hgen φ
  exact LinearMap.congr_fun hlin x

end Naturality

end GaloisForLFunctions.HTGeometry
