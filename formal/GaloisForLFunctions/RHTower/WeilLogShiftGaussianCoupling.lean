import GaloisForLFunctions.RHTower.WeilLogShiftProjectedSecondMoment
import GaloisForLFunctions.RHTower.WeilLogShiftGaussianQuantile
import GaloisForLFunctions.HTGeometry.KantorovichRubinsteinDuality

/-! Actual probability couplings between every projected finite law and its Gaussian target. -/

open MeasureTheory ProbabilityTheory GaloisForLFunctions.HTGeometry

noncomputable section
namespace RHTower

def finiteWeilCanonicalGaussianCoupling (r k : ℕ) (a b : ℝ) : ProbabilityMeasure (ℝ × ℝ) :=
  ⟨monotoneCoupling (finiteWeilCanonicalProjectedProbabilityLaw r k a b : Measure ℝ)
    (finiteWeilProjectedGaussian a b : Measure ℝ),
    (show IsCoupling (finiteWeilCanonicalProjectedProbabilityLaw r k a b : Measure ℝ)
        (finiteWeilProjectedGaussian a b : Measure ℝ)
        (monotoneCoupling (finiteWeilCanonicalProjectedProbabilityLaw r k a b : Measure ℝ)
          (finiteWeilProjectedGaussian a b : Measure ℝ)) from
      ⟨map_fst_monotoneCoupling _ _, map_snd_monotoneCoupling _ _⟩).isProbabilityMeasure⟩

theorem finiteWeilCanonicalGaussianCoupling_isCoupling (r k : ℕ) (a b : ℝ) :
    IsCoupling (finiteWeilCanonicalProjectedProbabilityLaw r k a b : Measure ℝ)
      (finiteWeilProjectedGaussian a b : Measure ℝ)
      (finiteWeilCanonicalGaussianCoupling r k a b : Measure (ℝ × ℝ)) :=
  ⟨map_fst_monotoneCoupling _ _, map_snd_monotoneCoupling _ _⟩

theorem finiteWeilCanonicalGaussianCoupling_quadratic_integrable (r k : ℕ) (a b : ℝ) :
    Integrable (fun z : ℝ × ℝ => |z.1 - z.2| ^ 2)
      (finiteWeilCanonicalGaussianCoupling r k a b : Measure (ℝ × ℝ)) :=
  integrable_sq_sub_monotoneCoupling _ _
    (finiteWeilCanonicalProjectedProbabilityLaw_integrable r k a b _)
    (finiteWeilProjectedGaussian_integrable_sq a b)

def finiteWeilCanonicalGaussianQuadraticCost (r k : ℕ) (a b : ℝ) : ℝ :=
  ∫ z, |z.1 - z.2| ^ 2 ∂(finiteWeilCanonicalGaussianCoupling r k a b : Measure (ℝ × ℝ))

theorem finiteWeilCanonicalGaussianQuadraticCost_nonneg (r k : ℕ) (a b : ℝ) :
    0 ≤ finiteWeilCanonicalGaussianQuadraticCost r k a b :=
  integral_nonneg fun z => sq_nonneg |z.1 - z.2|

theorem finiteWeilCanonicalGaussianQuadraticCost_antidiagonal (r k : ℕ) (a : ℝ) :
    finiteWeilCanonicalGaussianQuadraticCost r k a (-a) =
      ∫ x, x ^ 2 ∂(finiteWeilCanonicalProjectedProbabilityLaw r k a (-a) : Measure ℝ) := by
  have htarget : (finiteWeilProjectedGaussian a (-a) : Measure ℝ) = Measure.dirac (0 : ℝ) := by
    simp [finiteWeilProjectedGaussian, gaussianReal_zero_var]
  change (∫ z, |z.1 - z.2| ^ 2 ∂(monotoneCoupling
    (finiteWeilCanonicalProjectedProbabilityLaw r k a (-a) : Measure ℝ)
    (finiteWeilProjectedGaussian a (-a) : Measure ℝ))) = _
  rw [htarget]
  exact finiteWeil_monotoneCoupling_dirac_sq _

end RHTower
