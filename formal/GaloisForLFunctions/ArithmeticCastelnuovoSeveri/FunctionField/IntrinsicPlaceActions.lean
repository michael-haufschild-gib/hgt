import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.IntrinsicPlaceEquivalences
import Mathlib.GroupTheory.GroupAction.Basic

/-!
# Automorphism actions on intrinsic places

Constant-field automorphisms act on proper valuation rings by inverse
pullback. Composition agrees with the group law, and the residue-field
transport restricts this action to the actual rational places.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
variable (K L : Type*) [Field K] [Field L] [Algebra K L]

/-- The actual permutation representation on all proper constant-field places. -/
def constantFieldPlaceAutHom : (L ≃ₐ[K] L) →* Equiv.Perm (ConstantFieldPlaces K L) where
  toFun := constantFieldPlaceEquiv
  map_one' := by
    apply Equiv.ext
    intro W
    apply Subtype.ext
    ext x
    rfl
  map_mul' σ τ := by
    apply Equiv.ext
    intro W
    apply Subtype.ext
    ext x
    rfl

/-- Constant-field automorphisms act on the actual proper valuation places. -/
instance constantFieldPlacesAutMulAction : MulAction (L ≃ₐ[K] L) (ConstantFieldPlaces K L) where
  smul σ W := constantFieldPlaceEquiv σ W
  one_smul W := congrArg (fun e : Equiv.Perm (ConstantFieldPlaces K L) => e W)
    (constantFieldPlaceAutHom K L).map_one
  mul_smul σ τ W := congrArg (fun e : Equiv.Perm (ConstantFieldPlaces K L) => e W)
    ((constantFieldPlaceAutHom K L).map_mul σ τ)

/-- The actual permutation representation on rational constant-field places. -/
def rationalConstantFieldPlaceAutHom :
    (L ≃ₐ[K] L) →* Equiv.Perm (RationalConstantFieldPlaces K L) where
  toFun := rationalConstantFieldPlaceEquiv
  map_one' := by
    apply Equiv.ext
    intro W
    apply Subtype.ext
    apply Subtype.ext
    ext x
    rfl
  map_mul' σ τ := by
    apply Equiv.ext
    intro W
    apply Subtype.ext
    apply Subtype.ext
    ext x
    rfl

/-- Constant-field automorphisms act on the actual rational places. -/
instance rationalConstantFieldPlacesAutMulAction :
    MulAction (L ≃ₐ[K] L) (RationalConstantFieldPlaces K L) where
  smul σ W := rationalConstantFieldPlaceEquiv σ W
  one_smul W := congrArg (fun e : Equiv.Perm (RationalConstantFieldPlaces K L) => e W)
    (rationalConstantFieldPlaceAutHom K L).map_one
  mul_smul σ τ W := congrArg (fun e : Equiv.Perm (RationalConstantFieldPlaces K L) => e W)
    ((rationalConstantFieldPlaceAutHom K L).map_mul σ τ)

/-- Forgetting rationality commutes with the actual automorphism actions. -/
theorem rationalConstantFieldPlace_smul_val (σ : L ≃ₐ[K] L)
    (W : RationalConstantFieldPlaces K L) : (σ • W).val = σ • W.val := rfl

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
