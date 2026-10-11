import GaloisForLFunctions.HTGeometry.PaperFourierLiteralConvergence
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Fourier reconstruction respects a normally summable copy row

A summable uniform envelope permits literal interchange of the copy sum with each Fourier
coefficient and each finite Fourier projection. This supplies the integration interface needed
when applying the proven paper theorem to a complete native spectral row.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section
open MeasureTheory
open scoped BigOperators

private theorem norm_fourierChar_eq_one (k : ℤ) (x : ℝ) : ‖fourierChar k x‖ = 1 := by
  simp [fourierChar, Complex.norm_exp, Complex.mul_re, Complex.mul_im]

/-- A normal copy sum commutes with every literal unit-interval Fourier coefficient. -/
theorem paperSummableFourierCopies_hasSum_coefficient {ι : Type*} [Countable ι]
    (f : ι → C(ℝ, ℂ)) (b : ι → ℝ) (hb : Summable b)
    (hbound : ∀ i x, ‖f i x‖ ≤ b i) (k : ℤ) :
    HasSum (fun i => l2Pair (fourierChar k) (f i))
      (l2Pair (fourierChar k) (fun x => ∑' i, f i x)) := by
  unfold l2Pair
  apply intervalIntegral.hasSum_integral_of_dominated_convergence (fun i _ => b i)
  · intro i
    exact ((continuous_fourierChar k).star.mul (f i).continuous).aestronglyMeasurable
  · intro i
    filter_upwards [] with x hx
    simpa only [starRingEnd_apply, norm_mul, norm_star, norm_fourierChar_eq_one, one_mul]
      using hbound i x
  · exact Filter.Eventually.of_forall (fun _ _ => hb)
  · exact intervalIntegrable_const
  · filter_upwards [] with x hx
    exact ((hb.of_norm_bounded (fun i => hbound i x)).hasSum).mul_left _

/-- Coefficient identity retaining the entire countable copy sum. -/
theorem paperSummableFourierCopies_coefficient {ι : Type*} [Countable ι]
    (f : ι → C(ℝ, ℂ)) (b : ι → ℝ) (hb : Summable b)
    (hbound : ∀ i x, ‖f i x‖ ≤ b i) (k : ℤ) :
    l2Pair (fourierChar k) (fun x => ∑' i, f i x) =
      ∑' i, l2Pair (fourierChar k) (f i) :=
  (paperSummableFourierCopies_hasSum_coefficient f b hb hbound k).tsum_eq.symm

/-- Each finite Fourier projection also commutes with the complete copy sum. -/
theorem paperSummableFourierCopies_hasSum_partialSum {ι : Type*} [Countable ι]
    (f : ι → C(ℝ, ℂ)) (b : ι → ℝ) (hb : Summable b)
    (hbound : ∀ i x, ‖f i x‖ ≤ b i) (N : ℕ) (x : ℝ) :
    HasSum (fun i => fourierPartialSum (f i) N x)
      (fourierPartialSum (fun y => ∑' i, f i y) N x) := by
  unfold fourierPartialSum
  exact hasSum_sum fun k _ =>
    (paperSummableFourierCopies_hasSum_coefficient f b hb hbound k).mul_right _

/-- Literal projection identity, with no finite-cluster truncation of the copy row. -/
theorem paperSummableFourierCopies_partialSum {ι : Type*} [Countable ι]
    (f : ι → C(ℝ, ℂ)) (b : ι → ℝ) (hb : Summable b)
    (hbound : ∀ i x, ‖f i x‖ ≤ b i) (N : ℕ) (x : ℝ) :
    fourierPartialSum (fun y => ∑' i, f i y) N x =
      ∑' i, fourierPartialSum (f i) N x :=
  (paperSummableFourierCopies_hasSum_partialSum f b hb hbound N x).tsum_eq.symm

end
end GaloisForLFunctions.HTGeometry
