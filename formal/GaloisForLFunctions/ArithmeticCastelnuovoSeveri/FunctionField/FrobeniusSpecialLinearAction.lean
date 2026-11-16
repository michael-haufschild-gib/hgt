import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.FrobeniusSpecialLinearFaithfulness
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.FrobeniusKummerHomExt

/-!
# The faithful determinant-one group action

Substitution reverses matrix multiplication on functions. Applying each
substitution to the inverse matrix gives a faithful group homomorphism,
both over the constants and over the explicit invariant subfield.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open Polynomial Matrix
variable (K E : Type*) [Field K] [Fintype K] [Field E] [Algebra K E]
    (γ : Eˣ) (R : ℕ)
local notation "q" => Fintype.card K
local notation "n" => (q ^ 2 - q) * R + q
local notation "L" => FrobeniusSpecialLinearField K E γ R
local notation "x" => algebraMap E[X] L X
local notation "z" => AdjoinRoot.root (frobeniusKummerFieldPolynomial γ (q - 2) R n)

private def matrixRow (M : SpecialLinearGroup (Fin 2) K) (i : Fin 2) : L :=
  algebraMap E L (algebraMap K E (M i 0)) * x + algebraMap E L (algebraMap K E (M i 1))

private theorem matrixRow_map (M N : SpecialLinearGroup (Fin 2) K) (i : Fin 2) :
    frobeniusSpecialLinearHom K E γ R M (matrixRow K E γ R N i) =
      matrixRow K E γ R (N * M) i / frobeniusSpecialLinearDenominator K E γ R M := by
  let D := frobeniusSpecialLinearDenominator K E γ R M
  have hD : D ≠ 0 := frobeniusSpecialLinearDenominator_ne_zero K E γ R M
  apply (eq_div_iff hD).mpr
  rw [matrixRow, map_add, map_mul, AlgHom.commutes, AlgHom.commutes,
    frobeniusSpecialLinearHom_coordinate]
  change ((algebraMap E L (algebraMap K E (N i 0)) *
    ((algebraMap E L (algebraMap K E (M 0 0)) * x +
      algebraMap E L (algebraMap K E (M 0 1))) / D) +
    algebraMap E L (algebraMap K E (N i 1))) * D) = _
  rw [add_mul, mul_assoc, div_mul_cancel₀ _ hD]
  change _ = algebraMap E L (algebraMap K E
    (((N : Matrix (Fin 2) (Fin 2) K) * (M : Matrix (Fin 2) (Fin 2) K)) i 0)) * x +
      algebraMap E L (algebraMap K E
        (((N : Matrix (Fin 2) (Fin 2) K) * (M : Matrix (Fin 2) (Fin 2) K)) i 1))
  simp only [Matrix.mul_apply, Fin.sum_univ_two, map_add, map_mul]
  dsimp only [D, frobeniusSpecialLinearDenominator]
  ring

/-- Function substitution reverses the product of determinant-one matrices. -/
theorem frobeniusSpecialLinearAut_mul (M N : SpecialLinearGroup (Fin 2) K) :
    frobeniusSpecialLinearAut K E γ R M * frobeniusSpecialLinearAut K E γ R N =
      frobeniusSpecialLinearAut K E γ R (N * M) := by
  have hcoord :
      (frobeniusSpecialLinearHom K E γ R M).comp (frobeniusSpecialLinearHom K E γ R N) x =
        frobeniusSpecialLinearHom K E γ R (N * M) x := by
    change frobeniusSpecialLinearHom K E γ R M
      (frobeniusSpecialLinearHom K E γ R N x) = _
    rw [frobeniusSpecialLinearHom_coordinate, frobeniusSpecialLinearHom_coordinate]
    change frobeniusSpecialLinearHom K E γ R M
      (matrixRow K E γ R N 0 / matrixRow K E γ R N 1) =
        matrixRow K E γ R (N * M) 0 / matrixRow K E γ R (N * M) 1
    rw [map_div₀, matrixRow_map, matrixRow_map]
    exact div_div_div_cancel_right₀ (frobeniusSpecialLinearDenominator_ne_zero K E γ R M) _ _
  have hroot :
      (frobeniusSpecialLinearHom K E γ R M).comp (frobeniusSpecialLinearHom K E γ R N) z =
        frobeniusSpecialLinearHom K E γ R (N * M) z := by
    change frobeniusSpecialLinearHom K E γ R M
      (frobeniusSpecialLinearHom K E γ R N z) = _
    rw [frobeniusSpecialLinearHom_root, map_div₀, frobeniusSpecialLinearHom_root,
      frobeniusSpecialLinearHom_root]
    change (z / frobeniusSpecialLinearDenominator K E γ R M) /
      frobeniusSpecialLinearHom K E γ R M (matrixRow K E γ R N 1) =
        z / matrixRow K E γ R (N * M) 1
    rw [matrixRow_map]
    exact div_div_div_cancel_right₀ (frobeniusSpecialLinearDenominator_ne_zero K E γ R M) _ _
  have he := frobeniusKummerField_algHom_ext γ (q - 2) R n
    ((frobeniusSpecialLinearHom K E γ R M).comp (frobeniusSpecialLinearHom K E γ R N))
    (frobeniusSpecialLinearHom K E γ R (N * M)) hcoord hroot
  apply AlgEquiv.ext
  intro a
  exact congrArg (fun f : L →ₐ[E] L => f a) he

/-- The identity matrix gives the identity field automorphism. -/
theorem frobeniusSpecialLinearAut_one : frobeniusSpecialLinearAut K E γ R 1 = 1 := by
  have h := frobeniusSpecialLinearAut_mul K E γ R 1 1
  rw [one_mul] at h
  exact mul_left_cancel (h.trans (mul_one _).symm)

/-- Inverse-matrix substitution defines a determinant-one action on the actual radical field. -/
def frobeniusSpecialLinearAction : SpecialLinearGroup (Fin 2) K →* (L ≃ₐ[E] L) where
  toFun M := frobeniusSpecialLinearAut K E γ R M⁻¹
  map_one' := by rw [inv_one, frobeniusSpecialLinearAut_one]
  map_mul' M N := by rw [_root_.mul_inv_rev, frobeniusSpecialLinearAut_mul]

/-- The determinant-one action is faithful, including its central matrices. -/
theorem frobeniusSpecialLinearAction_injective :
    Function.Injective (frobeniusSpecialLinearAction K E γ R) := by
  intro M N h
  have hi := frobeniusSpecialLinearAut_injective K E γ R h
  exact inv_injective hi

/-- The same faithful action fixes the explicit invariant-generated intermediate field. -/
def frobeniusSpecialLinearRelativeAction :
    SpecialLinearGroup (Fin 2) K →* (L ≃ₐ[frobeniusSpecialLinearInvariantField K E γ R] L) where
  toFun M := frobeniusSpecialLinearRelativeAut K E γ R M⁻¹
  map_one' := by
    apply AlgEquiv.ext
    intro a
    exact congrArg (fun σ : L ≃ₐ[E] L => σ a)
      (show frobeniusSpecialLinearAut K E γ R (1 : SpecialLinearGroup (Fin 2) K)⁻¹ = 1 by
        rw [inv_one, frobeniusSpecialLinearAut_one])
  map_mul' M N := by
    apply AlgEquiv.ext
    intro a
    have h : frobeniusSpecialLinearAut K E γ R (M * N)⁻¹ =
        frobeniusSpecialLinearAut K E γ R M⁻¹ * frobeniusSpecialLinearAut K E γ R N⁻¹ := by
      rw [_root_.mul_inv_rev, frobeniusSpecialLinearAut_mul]
    exact congrArg (fun σ : L ≃ₐ[E] L => σ a) h

/-- The invariant-field action recovers every determinant-one matrix uniquely. -/
theorem frobeniusSpecialLinearRelativeAction_injective :
    Function.Injective (frobeniusSpecialLinearRelativeAction K E γ R) := by
  intro M N h
  have hi := frobeniusSpecialLinearRelativeAut_injective K E γ R h
  exact inv_injective hi

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
