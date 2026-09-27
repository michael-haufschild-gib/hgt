import GaloisForLFunctions.RHTower.CCMPrimeDeficitResidualPrimeForce
import GaloisForLFunctions.RHTower.MobiusCoprimeIncidence

/-!
# Completing the coefficient cutoff over a finite Euler product

Restricting Möbius to divisors of `P` changes its zeta transform into the
coprimality indicator. The resulting residual is exactly minus the
indicator of nontrivial integers coprime to `P`. Its prime force has the
same sign. Factorial moduli preserve every prescribed initial coefficient.
-/

noncomputable section
open scoped BigOperators

namespace RHTower

def ccmEulerMobius (P : ℕ) : ArithmeticFunction ℝ where
  toFun n := if n ∣ P then (ArithmeticFunction.moebius n : ℝ) else 0
  map_zero' := by simp

def ccmEulerRough (P : ℕ) : ArithmeticFunction ℝ where
  toFun n := if 1 < n ∧ n.Coprime P then 1 else 0
  map_zero' := by simp

def ccmEulerMobiusTail (P : ℕ) : ArithmeticFunction ℝ :=
  (ArithmeticFunction.moebius : ArithmeticFunction ℝ) - ccmEulerMobius P

private theorem eulerMobius_divisor_sum (P : ℕ) {n : ℕ} (hn : n ≠ 0) :
    (∑ d ∈ n.divisors, ccmEulerMobius P d) = if n.Coprime P then 1 else 0 := by
  change (∑ d ∈ n.divisors, if d ∣ P then (ArithmeticFunction.moebius d : ℝ) else 0) = _
  rw [← Finset.sum_filter]
  have hs : n.divisors.filter (fun d => d ∣ P) = (n.gcd P).divisors := by
    ext d
    simp only [Finset.mem_filter, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨hdn, _⟩, hdP⟩
      exact ⟨Nat.dvd_gcd hdn hdP, (Nat.gcd_pos_of_pos_left P (Nat.pos_of_ne_zero hn)).ne'⟩
    · rintro ⟨hd, _⟩
      exact ⟨⟨hd.trans (Nat.gcd_dvd_left n P), hn⟩, hd.trans (Nat.gcd_dvd_right n P)⟩
  rw [hs]
  exact_mod_cast mobiusCommonDivisorKernel_eq_coprimeIndicator n P

/-- The complete finite Euler product has a nonnegative zeta transform. -/
theorem ccmEulerMobius_mul_zeta (P : ℕ) :
    ccmEulerMobius P * (ArithmeticFunction.zeta : ArithmeticFunction ℝ) =
      1 + ccmEulerRough P := by
  ext n
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  rw [ArithmeticFunction.coe_mul_zeta_apply, eulerMobius_divisor_sum P hn]
  change (if n.Coprime P then (1 : ℝ) else 0) =
    (if n = 1 then 1 else 0) + (if 1 < n ∧ n.Coprime P then 1 else 0)
  by_cases hn1 : n = 1
  · simp [hn1]
  · have hn2 : 1 < n := by omega
    simp [hn1, hn2]

theorem ccmEulerMobiusTail_mul_zeta (P : ℕ) :
    ccmEulerMobiusTail P * (ArithmeticFunction.zeta : ArithmeticFunction ℝ) =
      -ccmEulerRough P := by
  rw [ccmEulerMobiusTail, sub_mul, ArithmeticFunction.coe_moebius_mul_coe_zeta,
    ccmEulerMobius_mul_zeta]
  abel

theorem logarithmicDivisorTransform_ccmEulerMobiusTail (P n : ℕ) :
    logarithmicDivisorTransform (ccmEulerMobiusTail P) n = -ccmEulerRough P n := by
  rw [logarithmicDivisorTransform, ← ArithmeticFunction.coe_mul_zeta_apply,
    ccmEulerMobiusTail_mul_zeta]
  rfl

theorem logarithmicLogDivisorTransform_ccmEulerMobiusTail (P n : ℕ) :
    logarithmicLogDivisorTransform (ccmEulerMobiusTail P) n =
      -(ccmEulerRough P * ArithmeticFunction.vonMangoldt : ArithmeticFunction ℝ) n := by
  have hl : logarithmicLogDivisorTransform (ccmEulerMobiusTail P) n =
      (ccmEulerMobiusTail P * ArithmeticFunction.log : ArithmeticFunction ℝ) n := by
    rw [logarithmicLogDivisorTransform, ArithmeticFunction.mul_apply]
    simp_rw [ArithmeticFunction.log_apply]
    exact (Nat.sum_divisorsAntidiagonal
      (fun d e => ccmEulerMobiusTail P d * Real.log e)).symm
  rw [hl, ← ArithmeticFunction.zeta_mul_vonMangoldt, ← mul_assoc,
    ccmEulerMobiusTail_mul_zeta]
  exact congrArg (fun f : ArithmeticFunction ℝ => f n)
    (_root_.neg_mul (ccmEulerRough P) ArithmeticFunction.vonMangoldt)

theorem ccmEulerRough_nonneg (P n : ℕ) : 0 ≤ ccmEulerRough P n := by
  change 0 ≤ if _ then (1 : ℝ) else 0
  split <;> norm_num

theorem ccmEulerRough_le_one (P n : ℕ) : ccmEulerRough P n ≤ 1 := by
  change (if _ then (1 : ℝ) else 0) ≤ 1
  split <;> norm_num

theorem ccmEulerRough_primeForce_nonneg (P n : ℕ) :
    0 ≤ (ccmEulerRough P * ArithmeticFunction.vonMangoldt : ArithmeticFunction ℝ) n := by
  rw [ArithmeticFunction.mul_apply]
  exact Finset.sum_nonneg fun _ _ => mul_nonneg (ccmEulerRough_nonneg _ _)
    ArithmeticFunction.vonMangoldt_nonneg

theorem logarithmicDivisorTransform_ccmEulerMobiusTail_nonpos (P n : ℕ) :
    logarithmicDivisorTransform (ccmEulerMobiusTail P) n ≤ 0 := by
  rw [logarithmicDivisorTransform_ccmEulerMobiusTail]
  exact neg_nonpos.mpr (ccmEulerRough_nonneg P n)

theorem logarithmicLogDivisorTransform_ccmEulerMobiusTail_nonpos (P n : ℕ) :
    logarithmicLogDivisorTransform (ccmEulerMobiusTail P) n ≤ 0 := by
  rw [logarithmicLogDivisorTransform_ccmEulerMobiusTail]
  exact neg_nonpos.mpr (ccmEulerRough_primeForce_nonneg P n)

/-- Factorial completion keeps the literal Möbius head, without computing a factorial. -/
theorem ccmEulerMobius_factorial_of_le {m n : ℕ} (hn : n ≤ m) :
    ccmEulerMobius m.factorial n = (ArithmeticFunction.moebius n : ℝ) := by
  rcases eq_or_ne n 0 with rfl | hn0
  · simp
  · exact if_pos (Nat.dvd_factorial (Nat.pos_of_ne_zero hn0) hn)

theorem ccmEulerRough_factorial_of_le {m n : ℕ} (hn : n ≤ m) :
    ccmEulerRough m.factorial n = 0 := by
  change (if 1 < n ∧ n.Coprime m.factorial then (1 : ℝ) else 0) = 0
  apply if_neg
  rintro ⟨hn1, hcop⟩
  have heq : n = 1 := Nat.eq_one_of_dvd_coprimes hcop dvd_rfl
    (Nat.dvd_factorial (by omega) hn)
  omega

end RHTower
