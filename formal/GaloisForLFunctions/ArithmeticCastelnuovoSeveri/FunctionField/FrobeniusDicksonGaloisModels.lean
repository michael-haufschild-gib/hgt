import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.FrobeniusSpecialLinearGalois
import GaloisForLFunctions.ArithmeticHarmonicAnalysis.FiniteField.FrobeniusTracePolynomials

/-!
# Geometric-exponent Frobenius–Dickson Galois covers

For `n≥2`, the geometric exponent `R=1+q+⋯+q^(n-2)` makes the
radical degree equal to `q^n+1`. The determinant-one invariant therefore
gives an explicit rational Galois quotient of this family, over any
constant field containing the finite field of order `q`.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open Polynomial Matrix ArithmeticHarmonicAnalysis
variable (K E : Type*) [Field K] [Fintype K] [Field E] [Algebra K E]

/-- The covariance degree at a geometric branch exponent is a Frobenius power. -/
theorem frobeniusDickson_radical_index (r : ℕ) :
    ((Fintype.card K) ^ 2 - Fintype.card K) * kummerExponent (Fintype.card K) (r + 1) +
      Fintype.card K = (Fintype.card K) ^ (r + 2) := by
  let q := Fintype.card K
  have hq : 1 ≤ q := le_of_lt (Fintype.one_lt_card : 1 < q)
  have hgeom := kummerExponent_mul_add (q - 1) (r + 1)
  rw [Nat.sub_add_cancel hq] at hgeom
  have hk : q ^ 2 - q = q * (q - 1) := by
    rw [Nat.mul_sub_left_distrib, Nat.mul_one, pow_two]
  change (q ^ 2 - q) * kummerExponent q (r + 1) + q = q ^ (r + 2)
  rw [hk]
  calc
    _ = q * (kummerExponent q (r + 1) * (q - 1) + 1) := by ring
    _ = q * q ^ (r + 1) := by rw [hgeom]
    _ = q ^ (r + 2) := (pow_succ' q (r + 1)).symm

/-- The actual radical field with geometric branch exponent and degree `q^(r+2)+1`. -/
abbrev FrobeniusDicksonField (γ : Eˣ) (r : ℕ) :=
  FrobeniusSpecialLinearField K E γ (kummerExponent (Fintype.card K) (r + 1))

variable (γ : Eˣ) (r : ℕ)
local notation "q" => Fintype.card K
local notation "R" => kummerExponent q (r + 1)
local notation "L" => FrobeniusDicksonField K E γ r
local notation "x" => algebraMap E[X] L X
local notation "z" => AdjoinRoot.root
  (frobeniusKummerFieldPolynomial γ (q - 2) R ((q ^ 2 - q) * R + q))

/-- The constructed field satisfies the literal geometric-exponent curve equation. -/
theorem frobeniusDicksonField_root_equation :
    z ^ (q ^ (r + 2) + 1) =
      algebraMap E L γ * (x ^ q - x) * (1 + (x ^ q - x) ^ (q - 1)) ^ R := by
  have he := congrArg (fun j : ℕ => z ^ (j + 1)) (frobeniusDickson_radical_index K r)
  exact he.symm.trans (frobeniusSpecialLinearField_root_equation K E γ R)

/-- The explicit invariant generates a rational subfield of index `q(q²-1)`. -/
theorem frobeniusDicksonField_invariant_finrank :
    Module.finrank (frobeniusSpecialLinearInvariantField K E γ R) L = q * (q ^ 2 - 1) :=
  frobeniusSpecialLinearInvariant_finrank K E γ R

/-- The geometric-exponent field is Galois over its explicit invariant subfield. -/
theorem frobeniusDicksonField_invariant_isGalois :
    IsGalois (frobeniusSpecialLinearInvariantField K E γ R) L :=
  frobeniusSpecialLinearInvariant_isGalois K E γ R

/-- The full relative automorphism group of the geometric-exponent cover is `SL₂(K)`. -/
def frobeniusDicksonField_galoisEquiv : SpecialLinearGroup (Fin 2) K ≃*
    (L ≃ₐ[frobeniusSpecialLinearInvariantField K E γ R] L) :=
  frobeniusSpecialLinearGaloisEquiv K E γ R

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
