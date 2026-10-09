import GaloisForLFunctions.RHTower.PaperCircleHeatInformation
import GaloisForLFunctions.HTGeometry.DiscreteMutualInformation

/-! # Native selection information of the actual heat channel

The corpus's existing request/word mutual-information functional evaluates exactly on
an actual native heat channel. Every finite summability premise is discharged here.
-/

open scoped BigOperators NNReal
open GaloisForLFunctions.HTGeometry.FourierLLogL
open GaloisForLFunctions.HTGeometry.FourierLLogL.Dyadic
open GaloisForLFunctions.HTGeometry
  (marginalFst marginalSnd entropySnd condEntropySnd mutualInfo
   entropySnd_eq_condEntropySnd_add_mutualInfo)

namespace RHTower
noncomputable section
variable {ι : Type*} [Fintype ι]

/-- Joint law of the initial native heat increment and its noisy observed sum. -/
def paperCircleHeatJoint (a : ι → CCMCircleBoundedSymbol) (M : ℕ) (s t : ℝ≥0)
    (x z : Grid M) : ℝ :=
  paperCircleGridHeat a M s x * paperCircleGridHeat a M t (z - x)

theorem paperCircleHeatJoint_nonneg (a : ι → CCMCircleBoundedSymbol) (M : ℕ)
    (s t : ℝ≥0) (x z : Grid M) : 0 ≤ paperCircleHeatJoint a M s t x z :=
  mul_nonneg (Law.nonneg _ _) (Law.nonneg _ _)

/-- The existing request marginal is exactly the initial native heat law. -/
theorem marginalFst_paperCircleHeatJoint (a : ι → CCMCircleBoundedSymbol) (M : ℕ)
    (s t : ℝ≥0) (x : Grid M) :
    marginalFst (paperCircleHeatJoint a M s t) x = paperCircleGridHeat a M s x := by
  unfold marginalFst paperCircleHeatJoint
  rw [tsum_fintype, ← Finset.mul_sum]
  have H := Fintype.sum_equiv (Equiv.addLeft x)
    (fun y => paperCircleGridHeat a M t y) (fun z => paperCircleGridHeat a M t (z - x))
    (fun y => by change _ = paperCircleGridHeat a M t (x + y - x); rw [add_sub_cancel_left])
  rw [← H, Law.total, mul_one]

/-- The existing word marginal is exactly the native heat law at the combined time. -/
theorem marginalSnd_paperCircleHeatJoint (a : ι → CCMCircleBoundedSymbol) (M : ℕ)
    (s t : ℝ≥0) (z : Grid M) :
    marginalSnd (paperCircleHeatJoint a M s t) z = paperCircleGridHeat a M (s + t) z :=
  (paperCircleGridHeat_convolution a M s t z).symm

theorem paperCircleHeatJoint_total (a : ι → CCMCircleBoundedSymbol) (M : ℕ) (s t : ℝ≥0) :
    ∑ x : Grid M, ∑ z : Grid M, paperCircleHeatJoint a M s t x z = 1 := by
  have H (x : Grid M) : ∑ z, paperCircleHeatJoint a M s t x z = paperCircleGridHeat a M s x := by
    simpa only [marginalFst, tsum_fintype] using marginalFst_paperCircleHeatJoint a M s t x
  simp_rw [H]
  exact Law.total _

/-- Corpus word entropy agrees with the actual heat entropy. -/
theorem entropySnd_paperCircleHeatJoint (a : ι → CCMCircleBoundedSymbol) (M : ℕ) (s t : ℝ≥0) :
    entropySnd (paperCircleHeatJoint a M s t) = paperCircleHeatEntropy a M (s + t) := by
  unfold entropySnd
  simp_rw [marginalSnd_paperCircleHeatJoint]
  rw [tsum_fintype]
  simp only [paperCircleHeatEntropy, Law.entropy, Law.crossE, Law.Ex, mul_neg]

private theorem weighted_log_product (p q : ℝ) :
    -(p * q * (Real.log (p * q) - Real.log p)) = p * (-(q * Real.log q)) := by
  by_cases hp : p = 0
  · simp [hp]
  by_cases hq : q = 0
  · simp [hq]
  rw [Real.log_mul hp hq]
  ring

/-- Conditional word entropy is exactly the entropy of the added heat noise. -/
theorem condEntropySnd_paperCircleHeatJoint (a : ι → CCMCircleBoundedSymbol) (M : ℕ)
    (s t : ℝ≥0) :
    condEntropySnd (paperCircleHeatJoint a M s t) = paperCircleHeatEntropy a M t := by
  unfold condEntropySnd
  simp_rw [marginalFst_paperCircleHeatJoint, paperCircleHeatJoint, weighted_log_product,
    tsum_fintype, ← Finset.mul_sum]
  have H (x : Grid M) :
      (∑ z, -(paperCircleGridHeat a M t (z - x) * Real.log (paperCircleGridHeat a M t (z - x)))) =
        paperCircleHeatEntropy a M t := by
    have h := Fintype.sum_equiv (Equiv.addLeft x)
      (fun y => -(paperCircleGridHeat a M t y * Real.log (paperCircleGridHeat a M t y)))
      (fun z => -(paperCircleGridHeat a M t (z - x) * Real.log (paperCircleGridHeat a M t (z - x))))
      (fun y => by
        change _ = -(paperCircleGridHeat a M t (x + y - x) *
          Real.log (paperCircleGridHeat a M t (x + y - x)))
        rw [add_sub_cancel_left])
    rw [← h]
    simp only [paperCircleHeatEntropy, Law.entropy, Law.crossE, Law.Ex, mul_neg]
  simp_rw [H]
  rw [← Finset.sum_mul, Law.total, one_mul]

/-- The existing native mutual-information functional is an exact heat-entropy increment. -/
theorem mutualInfo_paperCircleHeatJoint (a : ι → CCMCircleBoundedSymbol) (M : ℕ) (s t : ℝ≥0) :
    mutualInfo (paperCircleHeatJoint a M s t) =
      paperCircleHeatEntropy a M (s + t) - paperCircleHeatEntropy a M t := by
  have H := entropySnd_eq_condEntropySnd_add_mutualInfo (paperCircleHeatJoint a M s t)
    (fun _ => Summable.of_finite) (fun _ => Summable.of_finite) (fun _ => Summable.of_finite)
  rw [entropySnd_paperCircleHeatJoint, condEntropySnd_paperCircleHeatJoint] at H
  linarith

/-- The channel reveals between zero and all of the initial heat entropy. -/
theorem mutualInfo_paperCircleHeatJoint_bounds (a : ι → CCMCircleBoundedSymbol) (M : ℕ)
    (s t : ℝ≥0) :
    0 ≤ mutualInfo (paperCircleHeatJoint a M s t) ∧
      mutualInfo (paperCircleHeatJoint a M s t) ≤ paperCircleHeatEntropy a M s := by
  rw [mutualInfo_paperCircleHeatJoint]
  constructor
  · apply sub_nonneg.mpr
    simpa only [add_comm] using paperCircleHeatEntropy_le_add a M t s
  · linarith [paperCircleHeatEntropy_add_le a M s t]

theorem mutualInfo_paperCircleHeatJoint_zero_noise (a : ι → CCMCircleBoundedSymbol)
    (M : ℕ) (s : ℝ≥0) :
    mutualInfo (paperCircleHeatJoint a M s 0) = paperCircleHeatEntropy a M s := by
  rw [mutualInfo_paperCircleHeatJoint, add_zero, paperCircleHeatEntropy_zero, sub_zero]

theorem mutualInfo_paperCircleHeatJoint_zero_signal (a : ι → CCMCircleBoundedSymbol)
    (M : ℕ) (t : ℝ≥0) : mutualInfo (paperCircleHeatJoint a M 0 t) = 0 := by
  rw [mutualInfo_paperCircleHeatJoint, zero_add, sub_self]

end
end RHTower
