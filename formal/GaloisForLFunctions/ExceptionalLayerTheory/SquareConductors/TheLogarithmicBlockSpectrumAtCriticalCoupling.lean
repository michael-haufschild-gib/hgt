import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.TheVirialGapOfComplementaryFactors
import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.WalshConstraintsAtTheUnitaryMidpoint
import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.ParitySectorMomentsAtTheUnitaryMidpoint

/-!
# Logarithmic block-flip spectrum at the critical coupling

Give each prime-power block a flip rate proportional to its logarithm,
with total rate three. The Walsh frequency of a subset is then six
times the logarithm of its unitary divisor divided by log k. The
continuum virial zero at frequency three corresponds exactly to the
integer square-root cut, which a nontrivial unitary factorization misses.
-/

noncomputable section
open Finset
namespace GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval

private def flipRate (k p : ℕ) : ℝ := 3*Real.log (p^k.factorization p:ℕ)/Real.log k

/-- Generator of independent logarithmically weighted prime-block flips. -/
def logarithmicBlockLaplacian (k : ℕ) (f : Finset ℕ → ℝ) (S : Finset ℕ) : ℝ :=
  ∑ p ∈ k.primeFactors, flipRate k p*(f S-f (if p∈S then S.erase p else insert p S))

private theorem product_of_sides {k : ℕ} (hk : 0<k) {T : Finset ℕ} (hT : T⊆k.primeFactors) :
    primePowerSubset k T*primePowerSubset k (k.primeFactors \ T)=k := by
  unfold primePowerSubset
  rw [mul_comm,prod_sdiff hT]
  exact (Nat.prod_primeFactors_pow_factorization hk.ne').symm

private theorem block_pos {k : ℕ} {T : Finset ℕ} (hT : T⊆k.primeFactors) : 0<primePowerSubset k T :=
  prod_pos fun _ h => pow_pos (Nat.prime_of_mem_primeFactors (hT h)).pos _

private theorem total_rate {k : ℕ} {T : Finset ℕ} (hT : T⊆k.primeFactors) :
    ∑ p ∈ T,flipRate k p=3*Real.log (primePowerSubset k T)/Real.log k := by
  rw [primePowerSubset,Nat.cast_prod,Real.log_prod (fun p h =>
    (Nat.cast_pos.mpr (pow_pos (Nat.prime_of_mem_primeFactors (hT h)).pos _) : 0<(↑(p^k.factorization p):ℝ)).ne')]
  simp only [flipRate,mul_sum,sum_div]

private theorem character_at_insertion (T S : Finset ℕ) {p : ℕ} (fresh : p∉S) :
    blockCharacter T (insert p S)=(if p∈T then -1 else 1)*blockCharacter T S := by
  rw [blockCharacter_comm T (insert p S),blockCharacter_comm T S]
  exact prod_insert fresh

private theorem character_edge (T S : Finset ℕ) (p : ℕ) :
    (blockCharacter T S:ℝ)-(blockCharacter T (if p∈S then S.erase p else insert p S):ℝ)=
      if p∈T then 2*(blockCharacter T S:ℝ) else 0 := by
  by_cases present : p∈S
  · rw [if_pos present]
    have eq := character_at_insertion T (S.erase p) (notMem_erase p S)
    rw [insert_erase present] at eq
    by_cases active : p∈T
    · rw [if_pos active,neg_one_mul] at eq
      rw [if_pos active,eq,Int.cast_neg]
      ring
    · rw [if_neg active,one_mul] at eq
      rw [if_neg active,eq,sub_self]
  · rw [if_neg present,character_at_insertion T S present]
    by_cases active : p∈T <;> simp [active] <;> ring

/-- Each actual Walsh mode has twice its occupied logarithmic rate as
eigenvalue, including the empty and full prime supports. -/
theorem logarithmic_block_eigenvalue {k : ℕ} (hk : 1<k) {T : Finset ℕ}
    (hT : T⊆k.primeFactors) (S : Finset ℕ) :
    logarithmicBlockLaplacian k (fun A => (blockCharacter T A:ℝ)) S=
      factorFrequency (primePowerSubset k T) (primePowerSubset k (k.primeFactors \ T))*
        (blockCharacter T S:ℝ) := by
  unfold logarithmicBlockLaplacian
  simp only [character_edge,mul_ite,mul_zero,←sum_filter,filter_mem_eq_inter,inter_eq_right.mpr hT]
  rw [←sum_mul,total_rate hT,factorFrequency,←Nat.cast_mul,product_of_sides (by omega) hT]
  ring

/-- On every integer k>1 the complete critical quadratic form
dominates its Walsh mass after scaling by k (log k)². This applies in
particular to the signed coefficients of the small-unitary-divisor cut. -/
theorem logarithmic_block_virial_coercivity {k : ℕ} (hk : 1<k) (c : Finset ℕ → ℝ) :
    (1/2:ℝ)*(∑ T ∈ k.primeFactors.powerset,(c T)^2) ≤
      (k:ℝ)*Real.log k^2*∑ T ∈ k.primeFactors.powerset,
        blockVirialSymbol (1/9) (factorFrequency (primePowerSubset k T)
          (primePowerSubset k (k.primeFactors \ T)))*(c T)^2 := by
  rw [mul_sum,mul_sum]
  apply sum_le_sum
  intro T h
  have sub := mem_powerset.mp h
  have comp : k.primeFactors \ T⊆k.primeFactors := sdiff_subset
  have prod := product_of_sides (show 0<k by omega) sub
  have co := (primePowerSubset_coprime_iff sub comp).mpr
    (disjoint_left.mpr (fun _ hs ht => (mem_sdiff.mp ht).2 hs))
  have floor := unitary_factor_virial_floor co (block_pos sub) (block_pos comp) (prod.symm ▸ hk)
  rw [scaledFactorVirial,←Nat.cast_mul,prod] at floor
  exact (mul_le_mul_of_nonneg_right floor (sq_nonneg _)).trans_eq (mul_assoc ..)

#print axioms logarithmic_block_eigenvalue
#print axioms logarithmic_block_virial_coercivity
end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
