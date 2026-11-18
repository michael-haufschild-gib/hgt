import GaloisForLFunctions.RepresentationLifting.Probability.FittingDegreeDistribution
import GaloisForLFunctions.ArithmeticHarmonicAnalysis.Codes.CoordinateArrangementCounts
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.Card

/-!
# Fitting distributions under rank extension

Every old stratum acquires the same survival factor. It equals the fraction of
triangular arrays whose added rows are all nonzero and determines the total
variation distance.
-/

namespace GaloisForLFunctions.RepresentationLifting.OperatorKernels
open Finset ArithmeticHarmonicAnalysis.Codes
open scoped Classical
noncomputable section
variable (F : Type*) [Field F] [Fintype F]

/-- Probability that none of the extra triangular block rows is zero. -/
def rowSurvival (n k : ℕ) : ℚ :=
  ∏ i : Fin k, (1-1/(Nat.card F:ℚ)^(n+i.val+1))

omit [Field F] [Fintype F] in
private theorem rowSurvival_succ (n k : ℕ) : rowSurvival F n (k+1) =
    rowSurvival F n k*(1-1/(Nat.card F:ℚ)^(n+k+1)) := by
  unfold rowSurvival
  rw [Fin.prod_univ_castSucc]
  rfl

private theorem extension_step (d k : ℕ) :
    fittingDegreeDensity F (d+k+1) d =
      fittingDegreeDensity F (d+k) d * (1-1/(Nat.card F:ℚ)^(d+k+1)) := by
  rw [Nat.add_assoc,fittingDegreeDensity_eq_product,fittingDegreeDensity_eq_product,
    Fin.prod_univ_castSucc]
  dsimp only [Fin.val_castSucc,Fin.val_last]
  ring

/-- Increasing ambient rank thins every old Fitting stratum by the very
same factor. Conditional on the degree staying below the old rank, the
whole old law is unchanged. -/
theorem fittingDegree_extension (n k : ℕ) (d : Fin (n+1)) :
    fittingDegreeDensity F (n+k) d.val = fittingDegreeDensity F n d.val * rowSurvival F n k := by
  induction k with
  | zero => simp [rowSurvival]
  | succ k ih =>
    have h := extension_step F d.val (n+k-d.val)
    rw [show d.val+(n+k-d.val)=n+k by omega] at h
    rw [Nat.add_succ,h,ih,rowSurvival_succ,mul_assoc]

/-- Exact cumulative distribution of the generalized zero-eigenspace dimension. -/
theorem fittingDegree_cumulative (n k : ℕ) :
    (∑ d : Fin (n+1), fittingDegreeDensity F (n+k) d.val) = rowSurvival F n k := by
  simp_rw [fittingDegree_extension F n k]
  rw [← sum_mul,sum_fittingDegreeDensity,one_mul]

/-- The same cumulative law counts actual words in independently punctured
coordinate alphabets: at row j the alphabet consists of vectors of length n+j+1. -/
theorem fittingDegree_zeroRow_model (n k : ℕ) :
    let A (j : Fin k) := Fin (n+j.val+1) → F
    let D := fun j : Fin k => ({0} : Finset (A j))
    (∑ d : Fin (n+1), fittingDegreeDensity F (n+k) d.val) =
      ((arrangementWords D {∅}).card:ℚ)/(Fintype.card (∀ j, A j):ℚ) := by
  dsimp only
  rw [fittingDegree_cumulative,card_arrangementWords,Fintype.card_pi]
  simp only [sum_singleton,notMem_empty,if_false,card_singleton,Fintype.card_fun,Fintype.card_fin,
    Nat.cast_prod,← prod_div_distrib,rowSurvival,Nat.card_eq_fintype_card]
  refine prod_congr rfl fun i _ => ?_
  have hq : 0 < (Fintype.card F)^(n+i.val+1) := pow_pos Fintype.card_pos _
  rw [Nat.cast_sub hq,Nat.cast_one,Nat.cast_pow]
  field_simp [show (Fintype.card F:ℚ) ≠ 0 by exact_mod_cast Fintype.card_pos.ne']

omit [Fintype F] in
private theorem density_nonneg (n d : ℕ) : 0 ≤ fittingDegreeDensity F n d := by
  unfold fittingDegreeDensity
  positivity

private theorem rowSurvival_le_one (n k : ℕ) : rowSurvival F n k ≤ 1 := by
  have hq (j : ℕ) : (1:ℚ) ≤ (Nat.card F:ℚ)^j := by
    exact_mod_cast (show 1 ≤ (Nat.card F)^j from pow_pos (Nat.card_pos (α := F)) _)
  apply prod_le_one
  · intro i _
    apply sub_nonneg.mpr
    exact (div_le_iff₀ (zero_lt_one.trans_le (hq _))).mpr (by simpa using hq (n+i.val+1))
  · exact fun i _ => sub_le_self _ (by positivity)

private theorem tail_eq (n k : ℕ) :
    (∑ j ∈ range k, fittingDegreeDensity F (n+k) (n+1+j)) = 1-rowSurvival F n k := by
  have h := sum_fittingDegreeDensity F (n+k)
  rw [Fin.sum_univ_eq_sum_range,show n+k+1=n+1+k by omega,sum_range_add] at h
  have h₀ := fittingDegree_cumulative F n k
  rw [Fin.sum_univ_eq_sum_range] at h₀
  rw [h₀] at h
  linarith only [h]

/-- Exact total variation distance between any two finite-rank Fitting laws;
the missing old mass is precisely the probability of a new zero row. -/
theorem fittingDegree_totalVariation (n k : ℕ) :
    ((∑ d : Fin (n+1), |fittingDegreeDensity F n d.val-fittingDegreeDensity F (n+k) d.val|) +
      ∑ j ∈ range k, |fittingDegreeDensity F (n+k) (n+1+j)|)/2 =
        1-rowSurvival F n k := by
  have he (d : Fin (n+1)) :
      |fittingDegreeDensity F n d.val-fittingDegreeDensity F (n+k) d.val| =
        fittingDegreeDensity F n d.val*(1-rowSurvival F n k) := by
    rw [fittingDegree_extension F n k d,
      show fittingDegreeDensity F n d.val-fittingDegreeDensity F n d.val*rowSurvival F n k =
        fittingDegreeDensity F n d.val*(1-rowSurvival F n k) by ring]
    exact abs_of_nonneg (mul_nonneg (density_nonneg F _ _) (sub_nonneg.mpr (rowSurvival_le_one F n k)))
  simp_rw [he,abs_of_nonneg (density_nonneg F _ _)]
  rw [← sum_mul,sum_fittingDegreeDensity,one_mul,tail_eq]
  ring

omit [Field F] [Fintype F] in
/-- The first nontrivial rank extension already realizes a strictly positive
distance. The identity works in every finite field, even in rank zero. -/
theorem fittingDegree_one_step_distance (n : ℕ) :
    1-rowSurvival F n 1 = 1/(Nat.card F:ℚ)^(n+1) := by simp [rowSurvival]

#print axioms fittingDegree_extension
#print axioms fittingDegree_cumulative
#print axioms fittingDegree_zeroRow_model
#print axioms fittingDegree_totalVariation

end
end GaloisForLFunctions.RepresentationLifting.OperatorKernels
