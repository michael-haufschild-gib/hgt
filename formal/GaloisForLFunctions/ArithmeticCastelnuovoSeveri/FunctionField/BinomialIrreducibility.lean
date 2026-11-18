import Mathlib.FieldTheory.KummerExtension
import Mathlib.Tactic.Ring

/-!
# The binomial irreducibility criterion over fields containing a square root of minus one

Taking norms down a simple radical extension turns a prime-power obstruction
for its generator into one for the original radicand. A square root of minus
one absorbs the sign in the norm at even degree.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open Polynomial IntermediateField

private theorem sign_prime_root {K : Type*} [Field K] {q : ℕ} (hq : q.Prime)
    (hi : ∃ i : K, i^2 = -1) : ∃ t : K, t^q = -1 := by
  by_cases he : q = 2
  · simpa only [he] using hi
  · exact ⟨-1, (hq.odd_of_ne_two he).neg_one_pow⟩

/-- Capelli's criterion in every degree over fields where minus one is a square. -/
theorem binomial_irreducible_iff_over_sqrt_neg_one {K : Type*} [Field K]
    (hi : ∃ i : K, i^2 = -1) (a : K) {n : ℕ} (hn : n ≠ 0) :
    Irreducible (X^n - C a) ↔ ∀ q : ℕ, q.Prime → q ∣ n → ∀ b : K, b^q ≠ a := by
  refine ⟨fun h _ hq hd => pow_ne_of_irreducible_X_pow_sub_C h hd hq.ne_one, ?_⟩
  induction n using induction_on_primes with
  | zero => exact (hn rfl).elim
  | one => exact fun _ => by simpa only [pow_one] using irreducible_X_sub_C a
  | prime_mul q m hq ih =>
    intro h
    have hm : m ≠ 0 := fun he => hn (by rw [he, mul_zero])
    have hsmall := ih hm (fun l hl hd => h l hl (dvd_mul_of_dvd_right hd q))
    apply X_pow_mul_sub_C_irreducible hsmall
    intro E _ _ x hx
    apply X_pow_sub_C_irreducible_of_prime hq
    intro b hb
    have hxint : IsIntegral K x := by
      by_contra hni
      exact (monic_X_pow_sub_C a hm).ne_zero (hx.symm.trans (minpoly.eq_zero hni))
    have hnorm := Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly (adjoin.powerBasis hxint)
    rw [adjoin.powerBasis_gen hxint, adjoin.powerBasis_dim, minpoly_gen, hx, natDegree_X_pow_sub_C,
      coeff_sub, coeff_C_zero, coeff_X_pow, if_neg (Ne.symm hm), zero_sub] at hnorm
    obtain ⟨t,ht⟩ := sign_prime_root hq hi
    apply h q hq (dvd_mul_right _ _) (t^(m+1) * Algebra.norm K b)
    rw [mul_pow, ← pow_mul, Nat.mul_comm (m+1) q, pow_mul, ht, ← map_pow, hb, hnorm,
      pow_succ]
    calc
      (-1:K)^m * -1 * ((-1)^m * -a) = ((-1:K)*(-1))^m * a := by rw [mul_pow]; ring
      _ = a := by simp

#print axioms binomial_irreducible_iff_over_sqrt_neg_one

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
