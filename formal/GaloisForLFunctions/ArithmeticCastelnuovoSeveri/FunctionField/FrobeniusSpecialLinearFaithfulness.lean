import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.FrobeniusSpecialLinearInvariant
import Mathlib.Tactic.FinCases

/-!
# Faithfulness of determinant-one radical automorphisms

The radical image determines the linear denominator because the radical
is nonzero. The coordinate image then determines the numerator. A
transcendental coordinate separates both coefficient pairs, recovering
all four matrix entries, even when the projective matrix has a center.
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

/-- A linear expression in the actual transcendental coordinate determines both constant coefficients. -/
theorem frobeniusSpecialLinearField_linearCoordinate_injective :
    Function.Injective (fun a : E × E => algebraMap E L a.1 * x + algebraMap E L a.2) := by
  rintro ⟨a, b⟩ ⟨c, d⟩ h
  have hinj : Function.Injective (algebraMap E[X] L) := by
    rw [IsScalarTower.algebraMap_eq E[X] (FractionRing E[X]) L]
    exact (algebraMap (FractionRing E[X]) L).injective.comp (IsFractionRing.injective E[X] _)
  have hC (t : E) : algebraMap E[X] L (C t) = algebraMap E L t :=
    (IsScalarTower.algebraMap_apply E E[X] L t).symm
  have hp : (C a * X + C b : E[X]) = C c * X + C d := by
    apply hinj
    simp only [map_add, map_mul, hC]
    exact h
  apply Prod.ext
  · have he := congrArg (fun f : E[X] => f.coeff 1) hp
    simpa using he
  · have he := congrArg (fun f : E[X] => f.coeff 0) hp
    simpa using he

/-- Distinct determinant-one matrices give distinct actual field automorphisms. -/
theorem frobeniusSpecialLinearAut_injective :
    Function.Injective (frobeniusSpecialLinearAut K E γ R) := by
  intro M N h
  let D := frobeniusSpecialLinearDenominator K E γ R M
  let D' := frobeniusSpecialLinearDenominator K E γ R N
  have hD : D ≠ 0 := frobeniusSpecialLinearDenominator_ne_zero K E γ R M
  have hD' : D' ≠ 0 := frobeniusSpecialLinearDenominator_ne_zero K E γ R N
  have hz : z ≠ 0 := frobeniusKummerField_root_ne_zero γ (q - 2) R n
  have hroot := congrArg (fun σ : L ≃ₐ[E] L => σ z) h
  change frobeniusSpecialLinearHom K E γ R M z = frobeniusSpecialLinearHom K E γ R N z at hroot
  rw [frobeniusSpecialLinearHom_root, frobeniusSpecialLinearHom_root] at hroot
  have hden : D = D' := (mul_left_cancel₀ hz ((div_eq_div_iff hD hD').mp hroot)).symm
  have hbottom := frobeniusSpecialLinearField_linearCoordinate_injective K E γ R hden
  have h10 : M 1 0 = N 1 0 := (algebraMap K E).injective (congrArg Prod.fst hbottom)
  have h11 : M 1 1 = N 1 1 := (algebraMap K E).injective (congrArg Prod.snd hbottom)
  have hcoord := congrArg (fun σ : L ≃ₐ[E] L => σ x) h
  change frobeniusSpecialLinearHom K E γ R M x = frobeniusSpecialLinearHom K E γ R N x at hcoord
  rw [frobeniusSpecialLinearHom_coordinate, frobeniusSpecialLinearHom_coordinate] at hcoord
  change (algebraMap E L (algebraMap K E (M 0 0)) * x + algebraMap E L (algebraMap K E (M 0 1))) / D =
    (algebraMap E L (algebraMap K E (N 0 0)) * x + algebraMap E L (algebraMap K E (N 0 1))) / D' at hcoord
  rw [hden] at hcoord
  have hnum := congrArg (fun a : L => a * D') hcoord
  rw [div_mul_cancel₀ _ hD', div_mul_cancel₀ _ hD'] at hnum
  have htop := frobeniusSpecialLinearField_linearCoordinate_injective K E γ R hnum
  have h00 : M 0 0 = N 0 0 := (algebraMap K E).injective (congrArg Prod.fst htop)
  have h01 : M 0 1 = N 0 1 := (algebraMap K E).injective (congrArg Prod.snd htop)
  apply SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j
  · exact h00
  · exact h01
  · exact h10
  · exact h11

/-- Faithfulness persists after viewing the maps as automorphisms over the actual invariant field. -/
theorem frobeniusSpecialLinearRelativeAut_injective :
    Function.Injective (frobeniusSpecialLinearRelativeAut K E γ R) := by
  intro M N h
  apply frobeniusSpecialLinearAut_injective K E γ R
  apply AlgEquiv.ext
  intro a
  exact congrArg (fun σ : L ≃ₐ[frobeniusSpecialLinearInvariantField K E γ R] L => σ a) h

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
