import GaloisForLFunctions.BiScaleUncertainty.CoprimeShearAndMultiplicativeGraphUncertainty

/-!
# The exact defect of the trace-free coordinate aperture

The aperture deficit is the pairwise variance of the complementary coordinates,
with an explicit correction for nonzero trace. After centering, equality holds
exactly when all complementary coordinates coincide. Thus the trace-free bound
also records a rigidity law and the precise cost of a small nonzero trace in
Luchese's Hessian aperture mechanism (https://arxiv.org/abs/2611.17317).
-/

open Finset
open scoped BigOperators

namespace HTGeometry.TraceApertureDefect
noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Pairwise dispersion after removing the selected coordinate. -/
def complementaryVariance (x : ι → ℝ) (i : ι) : ℝ :=
  (∑ j ∈ univ.erase i, ∑ k ∈ univ.erase i, (x j - x k)^2) / 2

theorem complementaryVariance_nonneg (x : ι → ℝ) (i : ι) :
    0 ≤ complementaryVariance x i := by
  exact div_nonneg (sum_nonneg fun _ _ => sum_nonneg fun _ _ => sq_nonneg _) (by norm_num)

/-- The trace correction and every source of slack in the coordinate aperture are exact. -/
theorem trace_aperture_decomposition (x : ι → ℝ) (i : ι) :
    ((Fintype.card ι : ℝ) - 1) * ∑ j, (x j)^2 -
      (Fintype.card ι : ℝ) * (x i)^2 =
      complementaryVariance x i + (∑ j, x j)^2 - 2 * x i * ∑ j, x j := by
  have hs := sum_erase_add (univ : Finset ι) x (mem_univ i)
  have he := sum_erase_add (univ : Finset ι) (fun j => (x j)^2) (mem_univ i)
  have hc : ((univ.erase i).card : ℝ) + 1 = (Fintype.card ι : ℝ) := by
    exact_mod_cast card_erase_add_one (mem_univ i)
  have hd := GaloisForLFunctions.BiScaleUncertainty.lagrange_finset_sum_sq_sub_sq_sum
    (univ.erase i) x
  unfold complementaryVariance
  rw [← hs, ← he, ← hc]
  nlinarith only [hd]

/-- A nonzero trace has an explicit signed cost, with no trace-size assumption. -/
theorem coordinate_bound_with_trace (x : ι → ℝ) (i : ι) :
    (Fintype.card ι : ℝ) * (x i)^2 ≤
      ((Fintype.card ι : ℝ) - 1) * ∑ j, (x j)^2 +
        2 * x i * ∑ j, x j - (∑ j, x j)^2 := by
  linarith only [trace_aperture_decomposition x i, complementaryVariance_nonneg x i]

/-- Zero defect means precisely one common complementary value. -/
theorem complementaryVariance_eq_zero_iff (x : ι → ℝ) (i : ι) :
    complementaryVariance x i = 0 ↔ ∀ j, j ≠ i → ∀ k, k ≠ i → x j = x k := by
  unfold complementaryVariance
  rw [div_eq_zero_iff]
  simp only [OfNat.ofNat_ne_zero, or_false]
  rw [sum_eq_zero_iff_of_nonneg (fun _ _ => sum_nonneg fun _ _ => sq_nonneg _)]
  constructor
  · intro h j hj k hk
    have hz := (sum_eq_zero_iff_of_nonneg (fun k _ => sq_nonneg (x j - x k))).mp
      (h j (mem_erase.mpr ⟨hj, mem_univ j⟩)) k (mem_erase.mpr ⟨hk, mem_univ k⟩)
    exact sub_eq_zero.mp (sq_eq_zero_iff.mp hz)
  · intro h j hj
    apply sum_eq_zero
    intro k hk
    rw [h j (mem_erase.mp hj).1 k (mem_erase.mp hk).1, sub_self, zero_pow two_ne_zero]

/-- Division-free projection onto the trace-zero hyperplane. -/
def centeredSpectrum (x : ι → ℝ) (i : ι) : ℝ :=
  (Fintype.card ι : ℝ) * x i - ∑ j, x j

omit [DecidableEq ι] in
theorem centeredSpectrum_sum (x : ι → ℝ) : ∑ i, centeredSpectrum x i = 0 := by
  simp only [centeredSpectrum, sum_sub_distrib, ← mul_sum, sum_const,
    card_univ, nsmul_eq_mul, sub_self]

/-- Centering removes the trace correction, leaving the full nonnegative remainder. -/
theorem centered_aperture_decomposition (x : ι → ℝ) (i : ι) :
    ((Fintype.card ι : ℝ) - 1) * ∑ j, (centeredSpectrum x j)^2 -
      (Fintype.card ι : ℝ) * (centeredSpectrum x i)^2 =
      complementaryVariance (centeredSpectrum x) i := by
  simpa only [centeredSpectrum_sum, zero_pow two_ne_zero, mul_zero, add_zero, sub_zero] using
    trace_aperture_decomposition (centeredSpectrum x) i

/-- Equality in the centered aperture is equivalent to complementary spectral rigidity. -/
theorem centered_aperture_equality_iff (x : ι → ℝ) (i : ι) :
    (Fintype.card ι : ℝ) * (centeredSpectrum x i)^2 =
      ((Fintype.card ι : ℝ) - 1) * ∑ j, (centeredSpectrum x j)^2 ↔
      ∀ j, j ≠ i → ∀ k, k ≠ i → centeredSpectrum x j = centeredSpectrum x k := by
  rw [← complementaryVariance_eq_zero_iff]
  have h := centered_aperture_decomposition x i
  constructor <;> intro he <;> linarith only [h, he]

#print axioms trace_aperture_decomposition
#print axioms coordinate_bound_with_trace
#print axioms centered_aperture_equality_iff

end
end HTGeometry.TraceApertureDefect
