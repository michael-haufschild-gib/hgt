import GaloisForLFunctions.CountingHolography.Sections.OrdinaryPrimeSectionModuli
import GaloisForLFunctions.RHTower.Deninger.DeningerRationalPrimeFactorization
import GaloisForLFunctions.HTGeometry.Arithmetic.IntegralTests

/-!
# Reduced prime products of a signed divisor

Every ordinary prime occurs in one row. Its integral contact is therefore
already the valuation of the reduced fraction. Its positive and negative
parts give the actual numerator and denominator.
-/

noncomputable section
namespace GaloisForLFunctions.CountingHolography.Sections

open Finset _root_.RHTower HTGeometry.Arithmetic

private def primes {N : ℕ} (_a : Fin N → ℤ) := (Icc 2 (3*windowEnd N)).filter Nat.Prime
private def row {N : ℕ} (a : Fin N → ℤ) :=
  contactMultiplicity (packet a) (3*windowEnd N) (resolution a)

private theorem base_prime {N : ℕ} {a : Fin N → ℤ} {p : ℕ} (hp : p ∈ primes a) : contactBase p=p := by
  have h := (mem_filter.mp hp).2
  rw [contactBase,if_pos h.isPrimePow,h.minFac_eq]

/-- The signed valuation vector of the rational generator has one floor
at each ordinary prime in its window and vanishes elsewhere. -/
theorem ordinaryPrimeGenerator_exponent {N : ℕ} (a : Fin N → ℤ) (p : ℕ) :
    deningerRatExp (ordinaryPrimeGenerator a) p =
      if p ∈ (Icc 2 (3*windowEnd N)).filter Nat.Prime then
        ⌊contactMultiplicity (packet a) (3*windowEnd N) (resolution a) p⌋ else 0 := by
  change deningerRatExp (∏ k ∈ primes a, (contactBase k:ℚ)^⌊row a k⌋) p =
    if p ∈ primes a then ⌊row a p⌋ else 0
  rw [deningerRatExp_prod (fun k _ => zpow_ne_zero _ (Nat.cast_ne_zero.mpr (contactBase_pos k).ne')),
    Finsupp.finsetSum_apply]
  calc _ = ∑ k ∈ primes a, if k=p then ⌊row a k⌋ else 0 := by
          refine sum_congr rfl fun k hk => ?_
          have hp := (mem_filter.mp hk).2
          rw [base_prime hk,deningerRatExp_zpow (Nat.cast_ne_zero.mpr hp.ne_zero),
            deningerRatExp_natCast_prime hp,Finsupp.smul_apply,Finsupp.single_apply]
          by_cases h : k=p <;> simp [h]
    _ = _ := by simp

private theorem positive_factorization {N : ℕ} (a : Fin N → ℤ) (p : ℕ) :
    (ordinaryPrimeModulus a).factorization p = if p ∈ primes a then ⌊row a p⌋₊ else 0 := by
  change (∏ k ∈ primes a, (contactBase k)^⌊row a k⌋₊).factorization p = _
  rw [Nat.factorization_prod (fun k _ => pow_ne_zero _ (contactBase_pos k).ne'),Finsupp.finsetSum_apply]
  calc _ = ∑ k ∈ primes a, if k=p then ⌊row a k⌋₊ else 0 := by
          refine sum_congr rfl fun k hk => ?_
          rw [base_prime hk,Nat.factorization_pow,(mem_filter.mp hk).2.factorization,
            Finsupp.smul_apply,Finsupp.single_apply]
          by_cases h : k=p <;> simp [h]
    _ = _ := by simp

/-- The positive valuation product equals the numerator in lowest terms. -/
theorem ordinaryPrimeGenerator_num {N : ℕ} (a : Fin N → ℤ) :
    (ordinaryPrimeGenerator a).num.natAbs = ordinaryPrimeModulus a := by
  let q := ordinaryPrimeGenerator a
  have hq : 0 < q := prod_pos fun k _ => zpow_pos (Nat.cast_pos.mpr (contactBase_pos k)) _
  have hM : 0 < ordinaryPrimeModulus a := prod_pos fun k _ => pow_pos (contactBase_pos k) _
  apply Nat.factorization_inj (Int.natAbs_ne_zero.mpr ((Rat.num_pos.mpr hq).ne')) hM.ne'
  ext p
  by_cases hp : p.Prime
  · letI : Fact p.Prime := ⟨hp⟩
    have he := ordinaryPrimeGenerator_exponent a p
    change deningerRatExp q p = if p ∈ primes a then ⌊row a p⌋ else 0 at he
    have hd := den_valuation_eq_negative_part p q
    rw [← Nat.factorization_def q.den hp,← deningerRatExp_apply_of_prime hp,he] at hd
    rw [deningerRatExp_apply] at he
    rw [positive_factorization]
    by_cases h : p ∈ primes a
    · rw [if_pos h] at he hd ⊢
      rw [← Int.floor_toNat]
      omega
    · rw [if_neg h] at he hd ⊢
      omega
  · simp only [Nat.factorization_eq_zero_of_not_prime _ hp]

/-- The omitted negative valuations give precisely the logarithm of the
reduced denominator, with no common prime factors to cancel. -/
theorem log_ordinaryPrimeGenerator_den {N : ℕ} (a : Fin N → ℤ) :
    Real.log (ordinaryPrimeGenerator a).den =
      Real.log (ordinaryPrimeModulus a)-Real.log (ordinaryPrimeGenerator a : ℝ) := by
  let q := ordinaryPrimeGenerator a
  have hq : 0 < q := prod_pos fun k _ => zpow_pos (Nat.cast_pos.mpr (contactBase_pos k)) _
  have hn : (q.num:ℝ) ≠ 0 := Int.cast_ne_zero.mpr ((Rat.num_pos.mpr hq).ne')
  have hd : (q.den:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr q.den_nz
  rw [← ordinaryPrimeGenerator_num]
  change Real.log (q.den:ℝ) = Real.log (q.num.natAbs:ℝ)-Real.log (q:ℝ)
  have ha : (q.num.natAbs:ℝ) = |(q.num:ℝ)| := by
    rw [← Int.cast_abs, ← Int.natCast_natAbs, Int.cast_natCast]
  rw [ha,Real.log_abs,Rat.cast_def,Real.log_div hn hd]
  ring

#print axioms ordinaryPrimeGenerator_num
#print axioms log_ordinaryPrimeGenerator_den

end GaloisForLFunctions.CountingHolography.Sections
