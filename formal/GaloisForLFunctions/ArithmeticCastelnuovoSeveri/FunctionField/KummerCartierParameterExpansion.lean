import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerCartierNormalization

/-!
# Cartier extraction in every parameter

The normalization on every function and the vanishing of lower
monomials give the same coefficient-extraction formula in every
parameter. No choice of a separating coordinate enters the formula.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open Polynomial
variable (p : ℕ) [Fact p.Prime] (s : ℕ) (c : (SquareConstantField p s)ˣ) (b R : ℕ)
local notation "K" => SquareConstantField p s
local notation "L" => SquareKummerField p s c b R
local notation "D" => KaehlerDifferential.D K L

/-- In any function, only the highest of the first `p` monomial differentials survives Cartier extraction. -/
theorem squareKummerCoordinateCartier_parameter_monomial (t : L) (i : Fin p) :
    squareKummerCoordinateCartier p s c b R (t ^ i.val • D t) =
      if i.val = p - 1 then D t else 0 := by
  by_cases hi : i.val = p - 1
  · rw [hi, if_pos rfl, squareKummerCoordinateCartier_normalization]
  · rw [if_neg hi]
    exact squareKummerCoordinateCartier_lower_monomial p s c b R t i.val
      (by have h := i.isLt; omega)

/-- The same Cartier operator extracts the top Frobenius coefficient in every parameter expansion. -/
theorem squareKummerCoordinateCartier_parameter_expansion (t : L) (a : Fin p → L)
    (j : Fin p) (hj : j.val = p - 1) :
    squareKummerCoordinateCartier p s c b R
      (∑ i : Fin p, a i ^ p • (t ^ i.val • D t)) = a j • D t := by
  classical
  rw [map_sum]
  calc
    _ = ∑ i : Fin p, if i = j then a j • D t else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      rw [squareKummerCoordinateCartier_frobenius_smul,
        squareKummerCoordinateCartier_parameter_monomial]
      by_cases hi : i = j
      · subst i
        rw [hj, if_pos rfl, if_pos rfl]
      · have hival : i.val ≠ p - 1 := fun h => hi (Fin.ext (h.trans hj.symm))
        rw [if_neg hival, smul_zero, if_neg hi]
    _ = _ := by simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
