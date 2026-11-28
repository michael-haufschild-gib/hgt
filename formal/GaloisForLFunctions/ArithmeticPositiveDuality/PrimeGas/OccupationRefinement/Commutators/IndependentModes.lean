import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.OccupationRefinement.Commutators.Canonical

/-! # Independent prime modes commute on all finite states -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.OccupationRefinement.Commutators

open CoassociativeSplitting

private theorem add_other (m : Occupation) {p q : Nat.Primes} (ne : p≠q) :
    (m+particle p) q = m q := by
  rw [Finsupp.add_apply, particle, Finsupp.single_eq_of_ne ne.symm, add_zero]

private theorem sub_other (m : Occupation) {p q : Nat.Primes} (ne : p≠q) :
    (m-particle p) q = m q := by
  rw [Finsupp.tsub_apply, particle, Finsupp.single_eq_of_ne ne.symm, Nat.sub_zero]

private theorem distinct_shifts (m : Occupation) {p q : Nat.Primes} (ne : p≠q) :
    m+particle q-particle p = m-particle p+particle q := by
  ext i
  by_cases h : i=p
  · subst i
    rw [sub_count, add_other _ ne.symm, add_other _ ne.symm, sub_count]
  · simp only [Finsupp.tsub_apply, Finsupp.add_apply, particle, Finsupp.single_eq_of_ne h, Nat.sub_zero]

theorem independent (K : Kernel) {p q : Nat.Primes} (ne : p≠q) :
    bracket (lower K p) (raise K q) = 0 ∧ bracket (lower K p) (lower K q) = 0 ∧
      bracket (raise K p) (raise K q) = 0 := by
  have mixed : (lower K p).comp (raise K q) = (raise K q).comp (lower K p) := by
    apply core_ext
    intro m
    simp only [LinearMap.comp_apply, raise_ket, lower_ket, map_smul, smul_smul,
      add_other _ ne.symm, sub_other _ ne, distinct_shifts _ ne]
    rw [mul_comm]
  have lows : (lower K p).comp (lower K q) = (lower K q).comp (lower K p) := by
    apply core_ext
    intro m
    have swap : m-particle q-particle p = m-particle p-particle q := by rw [tsub_tsub,tsub_tsub,add_comm]
    simp only [LinearMap.comp_apply, lower_ket, map_smul, smul_smul, sub_other _ ne.symm,
      sub_other _ ne, swap]
    rw [mul_comm]
  have highs : (raise K p).comp (raise K q) = (raise K q).comp (raise K p) := by
    apply core_ext
    intro m
    simp only [LinearMap.comp_apply, raise_ket, map_smul, smul_smul, add_other _ ne.symm, add_other _ ne]
    rw [add_right_comm, mul_comm]
  exact ⟨sub_eq_zero.mpr mixed,sub_eq_zero.mpr lows,sub_eq_zero.mpr highs⟩

#print axioms independent

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.OccupationRefinement.Commutators
