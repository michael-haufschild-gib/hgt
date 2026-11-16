import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerThreePointExtensionInfinity
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerInfinityValuation
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.RadicalRamification
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.TotallyRamifiedFiber

/-!
# Infinity ramification over extended constants

The pole order of `c*x*(1-x)^a` is `1+a`. Its radical equation forces
`M` to divide this order times the actual ramification index. Coprime
pole and covering degrees therefore give one totally ramified rational
prime in the reciprocal normalization.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open Polynomial IsDedekindDomain
variable (p : ℕ) [Fact p.Prime] (d n : ℕ)
    (E : Type*) [Field E]
    [Algebra (SquareConstantField p (kummerSquareIndex d n)) E]
    (c : Eˣ) (a : ℕ)
local notation "M" => primePowerKummerCyclicDegree p d n
local notation "L" => PrimePowerThreePointExtensionInfinityField p d n E c a
local notation "B" => PrimePowerThreePointExtensionInfinityNormalization p d n E c a
local notation "F" => FractionRing E[X]

/-- The covering degree divides the ramified pole order of the three-point branch function. -/
theorem primePowerThreePointExtensionInfinity_ramification_order_dvd
    (w : HeightOneSpectrum B) [w.asIdeal.LiesOver (Ideal.span {(X : E[X])})] :
    M ∣ (Ideal.span {(X : E[X])}).ramificationIdx' w.asIdeal * (1 + a) := by
  let v := kummerInfinityBasePlace (K := E)
  letI : w.asIdeal.LiesOver v.asIdeal := by
    change w.asIdeal.LiesOver (Ideal.span {(X : E[X])})
    infer_instance
  have h := radical_ramification_log_dvd v w (M - 1 + 1)
    (AdjoinRoot.root (kummerInfinityPolynomial c 0 a (M - 1)))
    (kummerCoordinateInversion E (algebraMap E[X] F (kummerBranch c 0 a)))
    (kummerInfinityField_root_pow c 0 a (M - 1))
  rw [kummerInfinityBasePlace_branch_log, Nat.zero_add, Nat.one_mul] at h
  have hd : M - 1 + 1 ∣ v.asIdeal.ramificationIdx' w.asIdeal * (1 + a) :=
    Int.natCast_dvd_natCast.mp (by simpa only [Nat.cast_mul] using h)
  change M - 1 + 1 ∣ (Ideal.span {(X : E[X])}).ramificationIdx' w.asIdeal * (1 + a) at hd
  exact (congrArg (fun k : ℕ => k ∣
    (Ideal.span {(X : E[X])}).ramificationIdx' w.asIdeal * (1 + a))
    (primePowerThreePointExtension_index p d n)).mp hd

/-- Every actual infinity prime has positive ramification index. -/
theorem primePowerThreePointExtensionInfinity_ramification_pos
    (w : HeightOneSpectrum B) [w.asIdeal.LiesOver (Ideal.span {(X : E[X])})] :
    0 < (Ideal.span {(X : E[X])}).ramificationIdx' w.asIdeal :=
  Nat.pos_of_ne_zero (Ideal.IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver
    w.asIdeal (kummerInfinityBasePlace (K := E)).ne_bot)

/-- The actual infinity ramification is bounded by the unchanged covering degree. -/
theorem primePowerThreePointExtensionInfinity_ramification_le_degree
    (w : HeightOneSpectrum B) [w.asIdeal.LiesOver (Ideal.span {(X : E[X])})] :
    (Ideal.span {(X : E[X])}).ramificationIdx' w.asIdeal ≤ M := by
  let v := kummerInfinityBasePlace (K := E)
  letI : v.asIdeal.IsMaximal := v.isPrime.isMaximal v.ne_bot
  letI : w.asIdeal.LiesOver v.asIdeal := by
    change w.asIdeal.LiesOver (Ideal.span {(X : E[X])})
    infer_instance
  letI : NoZeroSMulDivisors E[X] B := ⟨fun {u z} h => by
    rw [Algebra.smul_def] at h
    rcases mul_eq_zero.mp h with hu | hz
    · exact Or.inl ((Module.isTorsionFree_iff_algebraMap_injective.mp inferInstance)
        (hu.trans (map_zero _).symm))
    · exact Or.inr hz⟩
  exact (Ideal.ramificationIdx_le_finrank B F L (p := v.asIdeal) w.asIdeal).trans_eq
    (primePowerThreePointExtensionInfinity_finrank p d n E c a)

/-- Coprime pole and covering degrees force total ramification at infinity. -/
theorem primePowerThreePointExtensionInfinity_ramification_eq_degree
    (hcop : Nat.Coprime M (1 + a))
    (w : HeightOneSpectrum B) [w.asIdeal.LiesOver (Ideal.span {(X : E[X])})] :
    (Ideal.span {(X : E[X])}).ramificationIdx' w.asIdeal = M := by
  apply Nat.le_antisymm (primePowerThreePointExtensionInfinity_ramification_le_degree p d n E c a w)
  exact Nat.le_of_dvd (primePowerThreePointExtensionInfinity_ramification_pos p d n E c a w)
    (hcop.dvd_of_dvd_mul_right
      (primePowerThreePointExtensionInfinity_ramification_order_dvd p d n E c a w))

/-- A coprime pole degree leaves exactly one rational prime in the reciprocal normalization. -/
theorem primePowerThreePointExtensionInfinity_singleton (hcop : Nat.Coprime M (1 + a)) :
    ∃ P : Ideal B, IsDedekindDomain.primesOverFinset (Ideal.span {(X : E[X])}) B = {P} ∧
      (Ideal.span {(X : E[X])}).inertiaDeg' P = 1 := by
  let v := kummerInfinityBasePlace (K := E)
  apply singleton_primesOver_of_full_ramification F L v
  intro P hP hover
  letI := hP
  letI : P.LiesOver (Ideal.span {(X : E[X])}) := hover
  let w : HeightOneSpectrum B := ⟨P, hP, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot P⟩
  exact (primePowerThreePointExtensionInfinity_ramification_eq_degree p d n E c a hcop w).trans
    (primePowerThreePointExtensionInfinity_finrank p d n E c a).symm

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
