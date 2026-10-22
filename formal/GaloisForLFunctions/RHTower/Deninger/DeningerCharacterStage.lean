import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.Algebra.Module.LinearMap.Basic

/-!
# Finite character stages of a lattice

A character of a finite free lattice is exactly its tuple of coordinate values: evaluation at a
basis identifies the characters with the corresponding power of the target.  A lattice map induces
a restriction of characters in the opposite direction, functorially, so the finite stages form a
cofiltered system.

Characters send a power to the corresponding power of the value, which is why the finite stages are
stable under the power maps.

* `deningerCharacterStage` : characters of a finite free lattice are coordinate tuples.
* `deningerCharacterStage_apply_single` : the coordinates are the values at the basis.
* `deningerCharacterRestrict` : the contravariant transition map, with its functoriality.
* `deningerCharacter_zsmul` : a character takes powers to powers.
-/

namespace RHTower

section CharacterStage

variable {A : Type*} [AddCommGroup A]

/-- **The finite character stage.**  Characters of the rank-`r` lattice are `r`-tuples of values:
a character is determined by, and can be prescribed by, its values on a basis. -/
noncomputable def deningerCharacterStage (r : ℕ) (A : Type*) [AddCommGroup A] :
    (Fin r → A) ≃ₗ[ℤ] ((Fin r → ℤ) →ₗ[ℤ] A) :=
  (Pi.basisFun ℤ (Fin r)).constr ℤ

@[simp] theorem deningerCharacterStage_apply_single (r : ℕ) (v : Fin r → A) (i : Fin r) :
    deningerCharacterStage r A v (Pi.single i 1) = v i := by
  simp [deningerCharacterStage]

/-- The contravariant transition map on characters induced by a lattice map. -/
def deningerCharacterRestrict {L L' : Type*} [AddCommGroup L] [AddCommGroup L']
    [Module ℤ L] [Module ℤ L'] (f : L →ₗ[ℤ] L') : (L' →ₗ[ℤ] A) →ₗ[ℤ] (L →ₗ[ℤ] A) where
  toFun P := P.comp f
  map_add' P Q := by
    ext x
    rfl
  map_smul' c P := by
    ext x
    rfl

@[simp] theorem deningerCharacterRestrict_apply {L L' : Type*} [AddCommGroup L] [AddCommGroup L']
    [Module ℤ L] [Module ℤ L'] (f : L →ₗ[ℤ] L') (P : L' →ₗ[ℤ] A) (x : L) :
    deningerCharacterRestrict (A := A) f P x = P (f x) := rfl

/-- **The transition maps are functorial.** -/
theorem deningerCharacterRestrict_comp {L L' L'' : Type*} [AddCommGroup L] [AddCommGroup L']
    [AddCommGroup L''] [Module ℤ L] [Module ℤ L'] [Module ℤ L'']
    (f : L →ₗ[ℤ] L') (g : L' →ₗ[ℤ] L'') (P : L'' →ₗ[ℤ] A) :
    deningerCharacterRestrict (A := A) f (deningerCharacterRestrict (A := A) g P)
      = deningerCharacterRestrict (A := A) (g.comp f) P := rfl

/-- **The transition map of the identity is the identity.** -/
theorem deningerCharacterRestrict_id {L : Type*} [AddCommGroup L] [Module ℤ L]
    (P : L →ₗ[ℤ] A) : deningerCharacterRestrict (A := A) (LinearMap.id) P = P := rfl

/-- **A character takes a power to the power of the value.**  In multiplicative notation this is
`P (a ^ q) = P a ^ q`, the stability of a character stage under the power maps. -/
theorem deningerCharacter_zsmul {L : Type*} [AddCommGroup L] [Module ℤ L]
    (P : L →ₗ[ℤ] A) (q : ℤ) (a : L) : P (q • a) = q • P a := by
  rw [map_zsmul]

end CharacterStage

end RHTower
