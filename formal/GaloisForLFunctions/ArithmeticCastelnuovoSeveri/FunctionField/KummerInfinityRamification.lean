import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerInfinityNormalization
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerInfinityValuation
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.RadicalRamification
import GaloisForLFunctions.ArithmeticHarmonicAnalysis.FiniteField.FrobeniusTracePolynomials

import Mathlib.NumberTheory.RamificationInertia.Basic

/-!
# Total ramification at infinity of Kummer covers

The radical equation forces `N ∣ eD`, where `D` is the pole degree of
the branch function. When `D` and `N` are coprime, the degree bound gives
`e=N`. For the prime-power family, `D=q^r` and `N=Q+1` are automatically
coprime, so every actual place above infinity is totally ramified.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open Polynomial IsDedekindDomain
variable (p : ℕ) [Fact p.Prime] (s : ℕ) (c : (SquareConstantField p s)ˣ) (b R : ℕ)

theorem squareKummerInfinity_ramification_order_dvd
    (w : HeightOneSpectrum (SquareKummerInfinityNormalization p s c b R))
    [w.asIdeal.LiesOver (Ideal.span {(X : (SquareConstantField p s)[X])})] :
    p ^ (s + 1) + 1 ∣ (Ideal.span {(X : (SquareConstantField p s)[X])}).ramificationIdx'
      w.asIdeal * (1 + (b + 1) * R) := by
  let v := kummerInfinityBasePlace (K := SquareConstantField p s)
  letI : w.asIdeal.LiesOver v.asIdeal := by
    change w.asIdeal.LiesOver (Ideal.span {(X : (SquareConstantField p s)[X])})
    infer_instance
  have h := radical_ramification_log_dvd v w (p ^ (s + 1) + 1)
    (AdjoinRoot.root (kummerInfinityPolynomial c b R (p ^ (s + 1))))
    (kummerCoordinateInversion (SquareConstantField p s)
      (algebraMap (SquareConstantField p s)[X] (FractionRing (SquareConstantField p s)[X])
        (kummerBranch c b R)))
    (kummerInfinityField_root_pow c b R (p ^ (s + 1)))
  rw [kummerInfinityBasePlace_branch_log] at h
  change ((p ^ (s + 1) + 1 : ℕ) : ℤ) ∣
    ((Ideal.span {(X : (SquareConstantField p s)[X])}).ramificationIdx' w.asIdeal : ℤ) *
      ((1 + (b + 1) * R : ℕ) : ℤ) at h
  exact Int.natCast_dvd_natCast.mp (by simpa only [Nat.cast_mul] using h)

theorem squareKummerInfinity_ramification_pos
    (w : HeightOneSpectrum (SquareKummerInfinityNormalization p s c b R))
    [w.asIdeal.LiesOver (Ideal.span {(X : (SquareConstantField p s)[X])})] :
    0 < (Ideal.span {(X : (SquareConstantField p s)[X])}).ramificationIdx' w.asIdeal :=
  Nat.pos_of_ne_zero (Ideal.IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver
    w.asIdeal (kummerInfinityBasePlace (K := SquareConstantField p s)).ne_bot)

theorem squareKummerInfinity_ramification_le_degree
    (w : HeightOneSpectrum (SquareKummerInfinityNormalization p s c b R))
    [w.asIdeal.LiesOver (Ideal.span {(X : (SquareConstantField p s)[X])})] :
    (Ideal.span {(X : (SquareConstantField p s)[X])}).ramificationIdx' w.asIdeal ≤ p ^ (s + 1) + 1 := by
  let v := kummerInfinityBasePlace (K := SquareConstantField p s)
  letI : v.asIdeal.IsMaximal := v.isPrime.isMaximal v.ne_bot
  letI : w.asIdeal.LiesOver v.asIdeal := by
    change w.asIdeal.LiesOver (Ideal.span {(X : (SquareConstantField p s)[X])})
    infer_instance
  letI : NoZeroSMulDivisors (SquareConstantField p s)[X]
      (SquareKummerInfinityNormalization p s c b R) := ⟨fun {a x} h => by
    rw [Algebra.smul_def] at h
    rcases mul_eq_zero.mp h with ha | hx
    · exact Or.inl ((Module.isTorsionFree_iff_algebraMap_injective.mp inferInstance)
        (ha.trans (map_zero _).symm))
    · exact Or.inr hx⟩
  have h := Ideal.ramificationIdx_le_finrank (SquareKummerInfinityNormalization p s c b R)
    (FractionRing (SquareConstantField p s)[X]) (KummerInfinityField c b R (p ^ (s + 1)))
    (p := v.asIdeal) w.asIdeal
  exact h.trans_eq (kummerInfinityField_finrank c b R _)

theorem squareKummerInfinity_ramification_eq_degree
    (hcop : (p ^ (s + 1) + 1).Coprime (1 + (b + 1) * R))
    (w : HeightOneSpectrum (SquareKummerInfinityNormalization p s c b R))
    [w.asIdeal.LiesOver (Ideal.span {(X : (SquareConstantField p s)[X])})] :
    (Ideal.span {(X : (SquareConstantField p s)[X])}).ramificationIdx' w.asIdeal = p ^ (s + 1) + 1 := by
  apply Nat.le_antisymm (squareKummerInfinity_ramification_le_degree p s c b R w)
  exact Nat.le_of_dvd (squareKummerInfinity_ramification_pos p s c b R w)
    (hcop.dvd_of_dvd_mul_right (squareKummerInfinity_ramification_order_dvd p s c b R w))


open GaloisForLFunctions.ArithmeticHarmonicAnalysis

/-- The geometric Kummer exponent gives a prime-power pole degree. -/
theorem kummerInfinity_primePower_poleDegree (d r : ℕ) :
    1 + (p ^ (d + 1) - 2 + 1) * kummerExponent (p ^ (d + 1)) r =
      (p ^ (d + 1)) ^ r := by
  have hq : 2 ≤ p ^ (d + 1) :=
    Nat.one_lt_pow (Nat.succ_ne_zero d) (Fact.out : p.Prime).one_lt
  have h := kummerExponent_mul_add (p ^ (d + 1) - 2 + 1) r
  rw [show p ^ (d + 1) - 2 + 1 + 1 = p ^ (d + 1) by omega] at h
  calc
    _ = kummerExponent (p ^ (d + 1)) r * (p ^ (d + 1) - 2 + 1) + 1 := by ac_rfl
    _ = _ := h

/-- The covering degree is coprime to every prime-power pole degree. -/
theorem kummerInfinity_primePower_poleDegree_coprime (d r : ℕ) :
    (p ^ (s + 1) + 1).Coprime
      (1 + (p ^ (d + 1) - 2 + 1) * kummerExponent (p ^ (d + 1)) r) := by
  rw [kummerInfinity_primePower_poleDegree, ← pow_mul]
  have hpow : (p ^ (s + 1) + 1).Coprime (p ^ (s + 1)) :=
    Nat.coprime_self_add_left.mpr (Nat.coprime_one_left _)
  have hbase : (p ^ (s + 1) + 1).Coprime p :=
    (Nat.coprime_pow_right_iff (Nat.succ_pos s) _ _).mp hpow
  exact hbase.pow_right _

/-- Every actual prime at infinity is totally ramified for the prime-power family. -/
theorem squareKummerInfinity_primePower_ramification (d r : ℕ)
    (w : HeightOneSpectrum (SquareKummerInfinityNormalization p s c
      (p ^ (d + 1) - 2) (kummerExponent (p ^ (d + 1)) r)))
    [w.asIdeal.LiesOver (Ideal.span {(X : (SquareConstantField p s)[X])})] :
    (Ideal.span {(X : (SquareConstantField p s)[X])}).ramificationIdx' w.asIdeal = p ^ (s + 1) + 1 :=
  squareKummerInfinity_ramification_eq_degree p s c _ _
    (kummerInfinity_primePower_poleDegree_coprime p s d r) w

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
