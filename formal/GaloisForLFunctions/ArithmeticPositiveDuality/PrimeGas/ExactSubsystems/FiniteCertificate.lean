import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.PrimeRay

/-! # Finite certificates for exact extraction at any prime -/

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems

/-- Both the period and the set of possible translate starts range over finite sets. -/
theorem extractable_iff_finite_certificate (q : Nat.Primes) (A : Finset ℕ) :
    extractable q A ↔ ∃ hA : A.Nonempty, ∃ L : ℕ+, L.val ≤ 2^(A.max' hA) ∧
      ∃ T ∈ (Finset.range L.val).powerset, tilesInterval A T L.val := by
  constructor
  · intro h
    have hA : A.Nonempty := by
      obtain ⟨B,hB⟩ := h
      obtain ⟨v,_⟩ := hB.2 1
      exact ⟨v.1.val,v.1.property⟩
    obtain ⟨L,hL,T,hT⟩ := (extractable_iff_interval q A hA).mp h
    refine ⟨hA,L,hL,T,Finset.mem_powerset.mpr ?_,hT⟩
    obtain ⟨a,ha⟩ := hA
    intro t ht
    have hl := (hT.2 (a+t)).mp ⟨(⟨a,ha⟩,⟨t,ht⟩),rfl⟩
    exact Finset.mem_range.mpr (by omega)
  · rintro ⟨hA,L,hL,T,_,hT⟩
    exact (extractable_iff_interval q A hA).mpr ⟨L,hL,T,hT⟩

theorem prime_independent (p q : Nat.Primes) (A : Finset ℕ) : extractable p A ↔ extractable q A := by
  rw [extractable_iff_finite_certificate,extractable_iff_finite_certificate]

#print axioms extractable_iff_finite_certificate
#print axioms prime_independent

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems
