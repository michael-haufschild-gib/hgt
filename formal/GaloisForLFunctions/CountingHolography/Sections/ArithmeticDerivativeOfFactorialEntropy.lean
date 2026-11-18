import GaloisForLFunctions.CountingHolography.Sections.TheDenominatorOfTheArithmeticLogarithmicDerivative
import GaloisForLFunctions.CountingHolography.Sections.PrimeCoordinatesOfBalancedFactorialValues

/-! # A single rational integrality test for factorial entropy

Allowing any finite horizon, the entropy coordinates are precisely those
with integral arithmetic logarithmic derivative. They can already be
realized by balanced factorial identities of price one.
-/

noncomputable section
namespace GaloisForLFunctions.CountingHolography.Sections

open Finset

/-- A prescribed entropy is available at price one if and only if its
arithmetic logarithmic derivative is an integer. -/
theorem factorial_entropy_iff_integral_prime_reciprocal (a : Nat.Primes →₀ ℤ) :
    (∃ L, (0,primeLogValue a) ∈ factorialJointImage L) ↔ (primeReciprocalReading a).den=1 := by
  rw [primeReciprocalReading_den_one_iff]
  constructor
  · rintro ⟨L,c,hc,hb,he⟩
    let M := max 10 L
    have hz : (primeLogValue 0,primeLogValue a) ∈ factorialJointImage M := by
      rw [map_zero]
      exact ⟨c,fun j hj => hc j ((le_max_right 10 L).trans_lt hj),hb,he⟩
    have h := (factorialJointImage_iff_prime_coordinates (le_max_left 10 L) 0 a).mp hz
    exact fun p => (h p).2.1
  · intro h
    let L := max 10 (a.support.sup Subtype.val+1)
    have hz {p : Nat.Primes} (hp : L ≤ p) : a p=0 := by
      by_contra hn
      have hle := Finset.le_sup (f := Subtype.val) (Finsupp.mem_support_iff.mpr hn)
      exact (Nat.lt_succ_of_le hle).not_ge ((le_max_right 10 _).trans hp)
    refine ⟨L,?_⟩
    rw [← map_zero primeLogValue]
    apply (factorialJointImage_iff_prime_coordinates (le_max_left 10 _) 0 a).mpr
    intro p
    exact ⟨fun hp => ⟨rfl,hz hp.le⟩,h p,fun hp => by rw [hz hp.ge,Finsupp.zero_apply,mul_zero]⟩

#print axioms factorial_entropy_iff_integral_prime_reciprocal

end GaloisForLFunctions.CountingHolography.Sections
