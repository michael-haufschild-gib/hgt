import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.Codes.KummerEvaluationCodes
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.NormalizedKummerAlgebraPoints

/-!
# Evaluation codes from the maximal Kummer curves

The evaluation coordinates are all rational algebra points of the actual
affine normalization. Their number is `N=Q²+2Qg`. At pole allowance
`2g+a<N`, the code has dimension `g+a+1` and every nonzero word has
weight at least `N-(2g+a)`.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open ArithmeticHarmonicAnalysis
variable (p : ℕ) [Fact p.Prime] (d n r : ℕ)
local notation "K" => SquareConstantField p (kummerSquareIndex d n)
local notation "Q" => p ^ (kummerSquareIndex d n + 1)
local notation "g" => Module.finrank K (NormalizedKummerRegularDifferentials p d n r)
local notation "I" => NormalizedKummerAlgebraPoints p d n r
local notation "c" => (kummerTraceConstant p (kummerSquareIndex d n))⁻¹ ^
  kummerExponent (p ^ (d + 1)) (r + 1)

local instance : Fintype I := Fintype.ofFinite _

/-- Evaluation of bounded-pole functions at every rational affine point of the maximal Kummer curve. -/
def normalizedKummerEvaluationCode (m : ℕ) : Submodule K (I → K) :=
  squareKummerEvaluationCode p (kummerSquareIndex d n) c d (r + 1) m id

/-- These codes have the explicit maximal-curve evaluation length. -/
theorem normalizedKummerEvaluationCode_length :
    Fintype.card I = Q ^ 2 + 2 * Q * g := by
  rw [← Nat.card_eq_fintype_card]
  exact normalizedKummerAlgebraPoints_card p d n r

/-- Every pole allowance below the length has an exact character-cutoff dimension. -/
theorem normalizedKummerEvaluationCode_finrank_cutoffs
    (m : Fin (Q ^ 2 + 2 * Q * g)) :
    Module.finrank K (normalizedKummerEvaluationCode p d n r m.val) =
      ∑ i : Fin (Q + 1), kummerPoleCutoff p (kummerSquareIndex d n) d (r + 1) m.val i.val := by
  apply squareKummerEvaluationCode_finrank_cutoffs p (kummerSquareIndex d n) c d (r + 1)
    m.val id Function.injective_id
  rw [normalizedKummerEvaluationCode_length]
  exact m.isLt

/-- Riemann–Roch determines the dimension throughout its full valid interval. -/
theorem normalizedKummerEvaluationCode_riemannRoch
    (m : {m : Fin (Q ^ 2 + 2 * Q * g) // 2 * g ≤ m.val + 1}) :
    Module.finrank K (normalizedKummerEvaluationCode p d n r m.val.val) + g = m.val.val + 1 := by
  apply squareKummerEvaluationCode_riemannRoch p (kummerSquareIndex d n) c d (r + 1)
    m.val.val id Function.injective_id _ m.property
  rw [normalizedKummerEvaluationCode_length]
  exact m.val.isLt

/-- The entire indexed family has dimension `g+a+1`, with all geometric inputs discharged. -/
theorem normalizedKummerEvaluationCode_finrank
    (a : Fin (Q ^ 2 + 2 * Q * g - 2 * g)) :
    Module.finrank K (normalizedKummerEvaluationCode p d n r (2 * g + a.val)) =
      g + a.val + 1 := by
  have ha : a.val < Fintype.card I - 2 * g := by
    rw [normalizedKummerEvaluationCode_length]
    exact a.isLt
  exact squareKummerEvaluationCode_finrank_tail p (kummerSquareIndex d n) c d (r + 1)
    ⟨a.val, ha⟩ id Function.injective_id

/-- Every nonzero word satisfies the designed-distance bound at every pole allowance. -/
theorem normalizedKummerEvaluationCode_weight_bound (m : ℕ) :
    ∀ w ∈ normalizedKummerEvaluationCode p d n r m,
      w ≠ 0 → Q ^ 2 + 2 * Q * g - m ≤ Codes.weight w := by
  rw [← normalizedKummerEvaluationCode_length p d n r]
  exact squareKummerEvaluationCode_weight_bound p (kummerSquareIndex d n) c d (r + 1)
    m id Function.injective_id

/-- Explicit length, dimension, and distance for every member of the bounded-pole code family. -/
theorem normalizedKummerEvaluationCode_parameters
    (a : Fin (Q ^ 2 + 2 * Q * g - 2 * g)) :
    Fintype.card I = Q ^ 2 + 2 * Q * g ∧
    Module.finrank K (normalizedKummerEvaluationCode p d n r (2 * g + a.val)) =
      g + a.val + 1 ∧
    ∀ w ∈ normalizedKummerEvaluationCode p d n r (2 * g + a.val),
      w ≠ 0 → Q ^ 2 + 2 * Q * g - (2 * g + a.val) ≤ Codes.weight w :=
  ⟨normalizedKummerEvaluationCode_length p d n r,
    normalizedKummerEvaluationCode_finrank p d n r a,
    normalizedKummerEvaluationCode_weight_bound p d n r (2 * g + a.val)⟩

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
