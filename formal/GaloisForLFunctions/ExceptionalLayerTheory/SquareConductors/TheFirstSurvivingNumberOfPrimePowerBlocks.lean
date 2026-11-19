import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.TheParityOfTheSmallUnitaryDivisors
import Mathlib.Algebra.Group.ForwardDiff

/-!
# The first surviving number of prime-power blocks

A finite difference in the number of available colors removes products with
few distinct primes. The smaller unitary divisors remove every dominant
prime-power block. The first surviving balanced products have constant price.
-/

noncomputable section
open Finset
namespace GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval

private def rankCoefficient (m j : ℕ) : ℤ :=
  (-1:ℤ)^m*((-1:ℤ)^(m-j)*m.choose j)

private def rankDifference (m t : ℕ) (x : ℤ) : ℤ :=
  ∑ j ∈ range (m+1),rankCoefficient m j*(x+j)^t

private theorem rank_difference_eq (m t : ℕ) (x : ℤ) :
    rankDifference m t x=(-1:ℤ)^m*((fwdDiff (1:ℤ))^[m] (fun z : ℤ => z^t)) x := by
  rw [fwdDiff_iter_eq_sum_shift,mul_sum]
  unfold rankDifference
  apply sum_congr rfl
  intro j _
  simp only [rankCoefficient,zsmul_eq_mul,nsmul_eq_mul,mul_one,mul_assoc]

private theorem rank_difference_low {m t : ℕ} (h : t < m) (x : ℤ) :
    rankDifference m t x=0 := by
  rw [rank_difference_eq,fwdDiff_iter_pow_eq_zero_of_lt h]
  exact mul_zero _

private theorem rank_difference_leading (m : ℕ) (x : ℤ) :
    rankDifference m m x=(-1:ℤ)^m*m.factorial := by
  rw [rank_difference_eq,fwdDiff_iter_eq_factorial]
  rfl

/-- Positive arities only. For a product with t+1 blocks, the number of
j-colorings with prescribed largest class is j^t. -/
def unitaryColorCenter (m t : ℕ) : ℤ :=
  -(∑ j ∈ range m,rankCoefficient m (j+1)*((j+1:ℕ):ℤ)^t)

private theorem color_center (m t : ℕ) :
    unitaryColorCenter m t=(0:ℤ)^t-rankDifference m t 0 := by
  have hzero : rankCoefficient m 0=1 := by
    simp only [rankCoefficient,Nat.sub_zero,Nat.choose_zero_right,Nat.cast_one,mul_one,←mul_pow]
    norm_num
  rw [unitaryColorCenter,rankDifference,sum_range_succ',hzero]
  simp only [Nat.cast_zero,zero_add,one_mul]
  ring

/-- Integer weight built from positive coloring counts and small divisors.
Every input can be enumerated without testing the primality of the product. -/
def reflectedBlockWeight (m k : ℕ) : ℤ :=
  unitaryColorCenter m (k.primeFactors.card-1)+
    ∑ S ∈ smallUnitarySubsets k,rankDifference m S.card (-1)

private theorem full_subset_difference (m : ℕ) (P : Finset ℕ) :
    (∑ S ∈ P.powerset,rankDifference m S.card (-1))=rankDifference m P.card 0 := by
  have hexp (z : ℤ) : (∑ S ∈ P.powerset,z^S.card)=(z+1)^P.card := by
    rw [sum_powerset_apply_card (fun t => z^t),add_pow]
    apply sum_congr rfl
    intro j _
    simp only [nsmul_eq_mul,one_pow,mul_one,mul_comm]
  unfold rankDifference
  rw [sum_comm]
  apply sum_congr rfl
  intro j _
  rw [←mul_sum,hexp]
  simp only [zero_add]
  congr 2
  ring

/-- A dominant block gives weight one on pure powers, zero on every
mixed product, for all orders of the finite difference. -/
theorem reflected_block_weight_dominant {k p : ℕ} (hk : 1 < k) (hp : p ∈ k.primeFactors)
    (hbig : k < (p^k.factorization p)^2) (m : ℕ) :
    reflectedBlockWeight m k=(0:ℤ)^(k.primeFactors.card-1) := by
  rw [reflectedBlockWeight,small_unitary_subsets_of_dominant hk hp hbig,full_subset_difference,
    card_erase_of_mem hp,color_center]
  ring

/-- At most m prime-power blocks leave only pure powers. -/
theorem reflected_block_weight_few {k m : ℕ} (hk : 1 < k) (h : k.primeFactors.card ≤ m) :
    reflectedBlockWeight m k=(0:ℤ)^(k.primeFactors.card-1) := by
  have hpos := card_pos.mpr (Nat.nonempty_primeFactors.mpr hk)
  rw [reflectedBlockWeight,color_center,rank_difference_low (by omega),sub_zero,
    sum_eq_zero (fun S hS => rank_difference_low ((small_unitary_subset_card hk hS).1.trans_le h) _),
    add_zero]

/-- At the first possible number of blocks, every balanced product has
the same signed factorial weight, for arbitrary prime multiplicities. -/
theorem reflected_block_weight_first_balanced {k m : ℕ} (hk : 1 < k) (hm : 0 < m)
    (h : k.primeFactors.card=m+1)
    (hbal : ∀ p ∈ k.primeFactors,(p^k.factorization p)^2 < k) :
    reflectedBlockWeight m k= -((-1:ℤ)^m*m.factorial) := by
  have hz : ∀ S ∈ smallUnitarySubsets k,rankDifference m S.card (-1)=0 := by
    intro S hS
    have hc := (small_unitary_subset_card hk hS).2 hbal
    exact rank_difference_low (by omega) _
  rw [reflectedBlockWeight,h,Nat.add_one_sub_one,color_center,rank_difference_leading,
    zero_pow hm.ne',zero_sub,sum_eq_zero hz,add_zero]

#print axioms reflected_block_weight_few
#print axioms reflected_block_weight_dominant
#print axioms reflected_block_weight_first_balanced

end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
