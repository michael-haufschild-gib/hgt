import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.NormalizedKummerAlgebraPoints
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerIharaBound
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerIharaEquality
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerRationalParameterClassification

/-!
# The sharp length bound for maximal Kummer codes

The actual affine length `Q²+2Qg` lies between `Q²` and `Q³` by the
proved Ihara genus bound. Equality at the upper endpoint occurs exactly
at the smallest covering exponent with odd geometric branch length.
Equality at the lower endpoint occurs exactly at doubled branch periods,
which are also the rational members of the family.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
variable (p : ℕ) [Fact p.Prime] (d n r : ℕ)
local notation "K" => SquareConstantField p (kummerSquareIndex d n)
local notation "Q" => p ^ (kummerSquareIndex d n + 1)
local notation "g" => Module.finrank K (NormalizedKummerRegularDifferentials p d n r)
local notation "I" => NormalizedKummerAlgebraPoints p d n r

private theorem halfCard_pos : 0 < Q :=
  pow_pos (Fact.out : p.Prime).pos _

private theorem cube_partition : Q ^ 3 = Q ^ 2 + Q * (Q * (Q - 1)) := by
  have hQ : 1 ≤ Q := halfCard_pos p d n
  calc
    Q ^ 3 = Q ^ 2 * Q := pow_succ Q 2
    _ = Q ^ 2 * ((Q - 1) + 1) :=
      congrArg (fun x => Q ^ 2 * x) (Nat.sub_add_cancel hQ).symm
    _ = Q ^ 2 + Q * (Q * (Q - 1)) := by ring

private theorem length_eq_genus_iff :
    Nat.card I = Q ^ 3 ↔ 2 * g = Q * (Q - 1) := by
  have hN : Nat.card I = Q ^ 2 + Q * (2 * g) := by
    rw [normalizedKummerAlgebraPoints_card]
    ring
  rw [hN, cube_partition p d n]
  constructor
  · intro h
    exact Nat.eq_of_mul_eq_mul_left (halfCard_pos p d n) (Nat.add_left_cancel h)
  · intro h
    rw [h]

/-- All affine evaluation lengths lie in the sharp interval from `Q²` to `Q³`. -/
theorem normalizedKummer_code_length_bounds : Q ^ 2 ≤ Nat.card I ∧ Nat.card I ≤ Q ^ 3 := by
  constructor
  · rw [normalizedKummerAlgebraPoints_card]
    omega
  · have hg := primePowerKummer_genus_ihara_bound p d n (r + 1)
    change 2 * g ≤ Q * (Q - 1) at hg
    calc
      Nat.card I = Q ^ 2 + Q * (2 * g) := by
        rw [normalizedKummerAlgebraPoints_card]
        ring
      _ ≤ Q ^ 2 + Q * (Q * (Q - 1)) :=
        Nat.add_le_add_left (Nat.mul_le_mul_left Q hg) _
      _ = Q ^ 3 := (cube_partition p d n).symm

/-- The longest evaluation sets occur exactly at the smallest covering exponent and odd branch length. -/
theorem normalizedKummer_code_length_cube_iff :
    Nat.card I = Q ^ 3 ↔ n = 0 ∧ Odd (r + 1) :=
  (length_eq_genus_iff p d n r).trans
    (primePowerKummer_genus_ihara_equality_iff p d n (r + 1) _)

/-- The shortest evaluation sets occur exactly at the rational doubled-period parameters. -/
theorem normalizedKummer_code_length_square_iff :
    Nat.card I = Q ^ 2 ↔ 2 * (n + 1) ∣ r + 1 := by
  have hperiod : g = 0 ↔ 2 * (n + 1) ∣ r + 1 :=
    primePowerKummer_regularDifferential_finrank_zero_iff_period p d n (r + 1) _
  constructor
  · intro h
    rw [normalizedKummerAlgebraPoints_card] at h
    have hz : 2 * Q * g = 0 := by omega
    have hg : g = 0 := (mul_eq_zero.mp hz).resolve_left
      (mul_ne_zero (by omega : (2 : ℕ) ≠ 0) (Nat.ne_of_gt (halfCard_pos p d n)))
    exact hperiod.mp hg
  · intro h
    rw [normalizedKummerAlgebraPoints_card, hperiod.mpr h, mul_zero, add_zero]

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
