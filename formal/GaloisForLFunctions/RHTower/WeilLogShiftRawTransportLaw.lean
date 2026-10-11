import GaloisForLFunctions.RHTower.WeilLogShiftObservableCoupling
import GaloisForLFunctions.RHTower.WeilLogShiftRawResidualDecay

/-! The centered index and scaled correction have an explicit finite transport plan. -/

open MeasureTheory GaloisForLFunctions.HTGeometry
open scoped BigOperators

noncomputable section
namespace RHTower

def finiteWeilCanonicalRawIndexValue (r k : ℕ) (i : Fin (r + 1)) : ℝ :=
  ((i : ℕ) : ℝ) - finiteWeilCanonicalEdgeIndexMean r k

def finiteWeilCanonicalRawCorrectionValue (r k : ℕ) (i : Fin (r + 1)) : ℝ :=
  ((r + 1 : ℕ) : ℝ) *
    (finiteWeilCanonicalEdgeLogCorrection r k i - finiteWeilCanonicalLogTransportCorrection r k)

def finiteWeilCanonicalRawIndexLaw (r k : ℕ) : ProbabilityMeasure ℝ :=
  finiteWeilCanonicalObservableLaw r k (finiteWeilCanonicalRawIndexValue r k)

def finiteWeilCanonicalRawCorrectionLaw (r k : ℕ) : ProbabilityMeasure ℝ :=
  finiteWeilCanonicalObservableLaw r k (finiteWeilCanonicalRawCorrectionValue r k)

def finiteWeilCanonicalRawCoupling (r k : ℕ) : ProbabilityMeasure (ℝ × ℝ) :=
  finiteWeilCanonicalObservableCoupling r k
    (finiteWeilCanonicalRawIndexValue r k) (finiteWeilCanonicalRawCorrectionValue r k)

theorem finiteWeilCanonicalRawCoupling_isCoupling (r k : ℕ) :
    IsCoupling (finiteWeilCanonicalRawIndexLaw r k : Measure ℝ)
      (finiteWeilCanonicalRawCorrectionLaw r k : Measure ℝ)
      (finiteWeilCanonicalRawCoupling r k : Measure (ℝ × ℝ)) :=
  finiteWeilCanonicalObservableCoupling_isCoupling r k _ _

theorem finiteWeilCanonicalRawCoupling_cost (r k : ℕ) :
    (∫ p, dist p.1 p.2 ∂(finiteWeilCanonicalRawCoupling r k : Measure (ℝ × ℝ))) =
      finiteWeilCanonicalRawFluctuationGap r k := by
  rw [finiteWeilCanonicalRawCoupling, finiteWeilCanonicalObservableCoupling_cost]
  unfold finiteWeilCanonicalRawFluctuationGap
  apply Finset.sum_congr rfl
  intro i _
  rw [Real.dist_eq]
  exact congrArg (fun z : ℝ => finiteWeilCanonicalEdgeMass r k i * z)
    (abs_sub_comm (finiteWeilCanonicalRawIndexValue r k i) (finiteWeilCanonicalRawCorrectionValue r k i))

def finiteWeilCanonicalRawWasserstein (r k : ℕ) : ℝ :=
  wassersteinOne (finiteWeilCanonicalRawIndexLaw r k : Measure ℝ)
    (finiteWeilCanonicalRawCorrectionLaw r k : Measure ℝ)

theorem finiteWeilCanonicalRawWasserstein_nonneg (r k : ℕ) :
    0 ≤ finiteWeilCanonicalRawWasserstein r k := by
  letI : Nonempty {π : Measure (ℝ × ℝ) //
      IsCoupling (finiteWeilCanonicalRawIndexLaw r k : Measure ℝ)
        (finiteWeilCanonicalRawCorrectionLaw r k : Measure ℝ) π} :=
    ⟨⟨(finiteWeilCanonicalRawCoupling r k : Measure (ℝ × ℝ)),
      finiteWeilCanonicalRawCoupling_isCoupling r k⟩⟩
  unfold finiteWeilCanonicalRawWasserstein wassersteinOne
  exact le_ciInf fun π => integral_dist_nonneg π.val

theorem finiteWeilCanonicalRawWasserstein_le_gap (r k : ℕ) :
    finiteWeilCanonicalRawWasserstein r k ≤ finiteWeilCanonicalRawFluctuationGap r k := by
  calc
    _ ≤ ∫ p, dist p.1 p.2 ∂(finiteWeilCanonicalRawCoupling r k : Measure (ℝ × ℝ)) :=
      wassersteinOne_le_integral (finiteWeilCanonicalRawCoupling_isCoupling r k)
    _ = _ := finiteWeilCanonicalRawCoupling_cost r k

end RHTower
