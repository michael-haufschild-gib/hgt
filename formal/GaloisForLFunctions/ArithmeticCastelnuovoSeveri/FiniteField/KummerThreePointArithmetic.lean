import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerThreePointCyclic
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerInfinityRamification

/-!
# Arithmetic of the three-point branch exponent

For `M=(Q+1)(q-1)` and `a=(q-1)(1+q+...+q^(r-1))`, the pole
degree `1+a=q^r` is coprime to `M`. The branch gcd is
`(q-1)gcd(Q+1,1+q+...+q^(r-1))`. These identities include `r=0`.
-/

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open ArithmeticHarmonicAnalysis
variable (p : ℕ) [Fact p.Prime] (d n r : ℕ)
local notation "s" => kummerSquareIndex d n
local notation "M" => primePowerKummerCyclicDegree p d n
local notation "q" => p ^ (d + 1)
local notation "R" => kummerExponent q r

/-- The full three-point cyclic degree is prime to the characteristic. -/
theorem primePowerKummerCyclicDegree_coprime : Nat.Coprime M p := by
  have hlarge : (p ^ (s + 1) + 1).Coprime (p ^ (s + 1)) :=
    Nat.coprime_self_add_left.mpr (Nat.coprime_one_left _)
  have hsmall : (q - 1).Coprime q :=
    (Nat.coprime_self_sub_left (Nat.one_le_pow _ _ (Fact.out : p.Prime).pos)).mpr
      (Nat.coprime_one_left _)
  exact Nat.coprime_mul_iff_left.mpr
    ⟨(Nat.coprime_pow_right_iff (Nat.succ_pos s) _ _).mp hlarge,
      (Nat.coprime_pow_right_iff (Nat.succ_pos d) _ _).mp hsmall⟩

/-- The three-point branch polynomial has prime-power pole degree. -/
theorem primePowerThreePointExponent_poleDegree : 1 + (q - 1) * R = q ^ r := by
  have hq : 2 ≤ q := Nat.one_lt_pow (Nat.succ_ne_zero d) (Fact.out : p.Prime).one_lt
  have he : q - 2 + 1 = q - 1 := by omega
  simpa only [he] using kummerInfinity_primePower_poleDegree p d r

/-- The actual three-point pole degree is coprime to the full covering degree. -/
theorem primePowerThreePointExponent_pole_coprime : Nat.Coprime M (1 + (q - 1) * R) := by
  rw [primePowerThreePointExponent_poleDegree, ← pow_mul]
  exact (primePowerKummerCyclicDegree_coprime p d n).pow_right _

omit [Fact p.Prime] in
/-- The three-point branch gcd is the original branch gcd multiplied by `q-1`. -/
theorem primePowerThreePointExponent_gcd :
    Nat.gcd M ((q - 1) * R) = (q - 1) * Nat.gcd (p ^ (s + 1) + 1) R := by
  change Nat.gcd ((p ^ (s + 1) + 1) * (q - 1)) ((q - 1) * R) = _
  rw [Nat.mul_comm (p ^ (s + 1) + 1) (q - 1), Nat.gcd_mul_left]

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
