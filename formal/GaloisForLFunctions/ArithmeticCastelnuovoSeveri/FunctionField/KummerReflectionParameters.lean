import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerThreePointCyclic
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerReciprocalModel
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FiniteField.KummerNormFibers


/-!
# Arithmetic of complementary Kummer exponents

The exponents `q^a-1` and `q^(2m-a)-1` satisfy the reciprocal branch
identity. The multiplicative period of the square constant field also
identifies the coefficient after coordinate inversion.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open ArithmeticHarmonicAnalysis
variable (p : ℕ) [Fact p.Prime] (d n : ℕ)

/-- Complementary Frobenius exponents satisfy the positive reciprocal branch identity. -/
theorem primePowerKummer_reflection_exponent_relation (r : Fin (2 * n + 1)) :
    ((p ^ (d + 1)) ^ (r.val + 1) - 1 + 1) *
      ((p ^ (d + 1)) ^ (2 * n - r.val + 1) - 1 + 1) =
        1 + kummerExponent (p ^ (d + 1)) (n + 1) * primePowerKummerCyclicDegree p d n := by
  let q := p ^ (d + 1)
  let Q := p ^ (kummerSquareIndex d n + 1)
  have hq : 1 ≤ q := Nat.one_le_pow _ _ (Fact.out : p.Prime).pos
  have hQ : Q = q ^ (n + 1) := by
    dsimp only [Q, q]
    rw [kummerSquareIndex_succ, pow_mul]
  have hgeom : kummerExponent q (n + 1) * (q - 1) + 1 = Q := by
    have h := kummerExponent_mul_add (q - 1) (n + 1)
    rwa [Nat.sub_add_cancel hq, ← hQ] at h
  have hsum : (r.val + 1) + (2 * n - r.val + 1) = (n + 1) * 2 := by omega
  change (q ^ (r.val + 1) - 1 + 1) * (q ^ (2 * n - r.val + 1) - 1 + 1) =
    1 + kummerExponent q (n + 1) * ((Q + 1) * (q - 1))
  rw [Nat.sub_add_cancel (Nat.one_le_pow _ _ hq),
    Nat.sub_add_cancel (Nat.one_le_pow _ _ hq), ← pow_add, hsum, pow_mul, ← hQ, pow_two]
  have h : (1 + kummerExponent q (n + 1) * ((Q + 1) * (q - 1))) + Q = Q * Q + Q := by
    calc
      _ = (kummerExponent q (n + 1) * (q - 1) + 1) * (Q + 1) := by ring
      _ = Q * (Q + 1) := by rw [hgeom]
      _ = Q * Q + Q := by ring
  exact (Nat.add_right_cancel h).symm

/-- The same complementary exponent relation has period equal to the unit-group order. -/
theorem primePowerKummer_reflection_unit_period (r : Fin (2 * n + 1)) :
    ((p ^ (d + 1)) ^ (r.val + 1) - 1) *
      ((p ^ (d + 1)) ^ (2 * n - r.val + 1)) +
        ((p ^ (d + 1)) ^ (2 * n - r.val + 1) - 1) =
          Nat.card (SquareConstantField p (kummerSquareIndex d n))ˣ := by
  let q := p ^ (d + 1)
  have hq : 1 ≤ q := Nat.one_le_pow _ _ (Fact.out : p.Prime).pos
  have ha := Nat.sub_add_cancel (Nat.one_le_pow (r.val + 1) q hq)
  have hb := Nat.sub_add_cancel (Nat.one_le_pow (2 * n - r.val + 1) q hq)
  have hsum : (r.val + 1) + (2 * n - r.val + 1) = 2 * (n + 1) := by omega
  have hcard : Nat.card (SquareConstantField p (kummerSquareIndex d n)) =
      q ^ (r.val + 1) * q ^ (2 * n - r.val + 1) := by
    rw [squareConstantField_card, ← pow_add, hsum]
    dsimp only [q]
    rw [← pow_mul, kummerSquareIndex_succ]
    congr 1
    ring
  rw [Nat.card_units, hcard]
  change (q ^ (r.val + 1) - 1) * q ^ (2 * n - r.val + 1) +
    (q ^ (2 * n - r.val + 1) - 1) = _
  have h : (q ^ (r.val + 1) - 1) * q ^ (2 * n - r.val + 1) +
      (q ^ (2 * n - r.val + 1) - 1) + 1 =
        q ^ (r.val + 1) * q ^ (2 * n - r.val + 1) := by
    calc
      _ = (q ^ (r.val + 1) - 1) * q ^ (2 * n - r.val + 1) +
        (q ^ (2 * n - r.val + 1) - 1 + 1) := by ring
      _ = (q ^ (r.val + 1) - 1 + 1) * q ^ (2 * n - r.val + 1) := by rw [hb]; ring
      _ = _ := by rw [ha]
  omega

/-- The sign produced by reciprocal coordinates is trivial in the actual characteristic. -/
theorem primePowerKummer_reflection_sign (a : ℕ) :
    (-1 : (SquareConstantField p (kummerSquareIndex d n))ˣ) ^
      ((p ^ (d + 1)) ^ a - 1) = 1 := by
  apply Units.ext
  change (-1 : SquareConstantField p (kummerSquareIndex d n)) ^ ((p ^ (d + 1)) ^ a - 1) = 1
  have hq : 1 ≤ (p ^ (d + 1)) ^ a :=
    Nat.one_le_pow _ _ (Nat.one_le_pow _ _ (Fact.out : p.Prime).pos)
  have h := neg_one_pow_expChar_pow (SquareConstantField p (kummerSquareIndex d n)) p ((d + 1) * a)
  rw [pow_mul, ← Nat.sub_add_cancel hq, pow_succ] at h
  exact mul_right_cancel₀ (neg_ne_zero.mpr one_ne_zero) (h.trans (one_mul _).symm)

/-- Reciprocal inversion sends the power coefficient to the complementary power coefficient. -/
theorem primePowerKummer_reflection_coefficient
    (η : (SquareConstantField p (kummerSquareIndex d n))ˣ) (r : Fin (2 * n + 1)) :
    kummerReciprocalCoefficient (η⁻¹ ^ ((p ^ (d + 1)) ^ (r.val + 1) - 1))
      ((p ^ (d + 1)) ^ (2 * n - r.val + 1) - 1) =
        η⁻¹ ^ ((p ^ (d + 1)) ^ (2 * n - r.val + 1) - 1) := by
  let q := p ^ (d + 1)
  let S := q ^ (r.val + 1) - 1
  let T := q ^ (2 * n - r.val + 1) - 1
  have hT : T + 1 = q ^ (2 * n - r.val + 1) :=
    Nat.sub_add_cancel (Nat.one_le_pow _ _ (Nat.one_le_pow _ _ (Fact.out : p.Prime).pos))
  have hp : η ^ (S * (T + 1) + T) = 1 := by
    rw [hT]
    change η ^ ((q ^ (r.val + 1) - 1) * q ^ (2 * n - r.val + 1) +
      (q ^ (2 * n - r.val + 1) - 1)) = 1
    rw [primePowerKummer_reflection_unit_period p d n r]
    exact pow_card_eq_one'
  change (-1 : (SquareConstantField p (kummerSquareIndex d n))ˣ) ^ T /
    (η⁻¹ ^ S) ^ (T + 1) = η⁻¹ ^ T
  rw [primePowerKummer_reflection_sign p d n (2 * n - r.val + 1),
    one_div, ← pow_mul, inv_pow, inv_inv, inv_pow]
  apply eq_inv_iff_mul_eq_one.mpr
  rw [← pow_add]
  exact hp

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
