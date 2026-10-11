import GaloisForLFunctions.RHTower.WeilLogShiftGaussianCoupling
import Mathlib.Probability.Moments.Variance

/-! First-moment bounds for the actual Gaussian probability coupling. -/

open MeasureTheory ProbabilityTheory

noncomputable section
namespace RHTower

theorem finiteWeilCanonicalGaussianCoupling_gap_memLp (r k : ℕ) (a b : ℝ) :
    MemLp (fun z : ℝ × ℝ => |z.1 - z.2|) 2
      (finiteWeilCanonicalGaussianCoupling r k a b : Measure (ℝ × ℝ)) :=
  (memLp_two_iff_integrable_sq
    (continuous_fst.sub continuous_snd).abs.aestronglyMeasurable).mpr
    (finiteWeilCanonicalGaussianCoupling_quadratic_integrable r k a b)

theorem finiteWeilCanonicalGaussianCoupling_gap_integrable (r k : ℕ) (a b : ℝ) :
    Integrable (fun z : ℝ × ℝ => |z.1 - z.2|)
      (finiteWeilCanonicalGaussianCoupling r k a b : Measure (ℝ × ℝ)) :=
  (finiteWeilCanonicalGaussianCoupling_gap_memLp r k a b).integrable (by norm_num)

def finiteWeilCanonicalGaussianMeanGap (r k : ℕ) (a b : ℝ) : ℝ :=
  ∫ z, |z.1 - z.2| ∂(finiteWeilCanonicalGaussianCoupling r k a b : Measure (ℝ × ℝ))

theorem finiteWeilCanonicalGaussianMeanGap_nonneg (r k : ℕ) (a b : ℝ) :
    0 ≤ finiteWeilCanonicalGaussianMeanGap r k a b :=
  integral_nonneg fun z => abs_nonneg (z.1 - z.2)

theorem finiteWeilCanonicalGaussianMeanGap_sq_le_cost (r k : ℕ) (a b : ℝ) :
    finiteWeilCanonicalGaussianMeanGap r k a b ^ 2 ≤
      finiteWeilCanonicalGaussianQuadraticCost r k a b := by
  have h := variance_nonneg (fun z : ℝ × ℝ => |z.1 - z.2|)
    (finiteWeilCanonicalGaussianCoupling r k a b : Measure (ℝ × ℝ))
  rw [variance_eq_sub (finiteWeilCanonicalGaussianCoupling_gap_memLp r k a b)] at h
  change 0 ≤ finiteWeilCanonicalGaussianQuadraticCost r k a b -
    finiteWeilCanonicalGaussianMeanGap r k a b ^ 2 at h
  exact sub_nonneg.mp h

theorem finiteWeilCanonicalGaussianMeanGap_le_sqrt_cost (r k : ℕ) (a b : ℝ) :
    finiteWeilCanonicalGaussianMeanGap r k a b ≤
      Real.sqrt (finiteWeilCanonicalGaussianQuadraticCost r k a b) :=
  (Real.le_sqrt (finiteWeilCanonicalGaussianMeanGap_nonneg r k a b)
    (finiteWeilCanonicalGaussianQuadraticCost_nonneg r k a b)).mpr
    (finiteWeilCanonicalGaussianMeanGap_sq_le_cost r k a b)

end RHTower
