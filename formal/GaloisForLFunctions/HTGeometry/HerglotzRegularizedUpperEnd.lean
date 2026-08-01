import GaloisForLFunctions.HTGeometry.HerglotzFiniteAtomicChamber
import GaloisForLFunctions.HTGeometry.HerglotzUpperEndCarrier

/-!
# Regularized Herglotz transforms at the upper end

An arbitrary Herglotz measure satisfying the Nevanlinna integrability condition need not be
finite.  Multiplication by the Nevanlinna weight produces a finite measure whose Cauchy transform
gives the non-affine part of the regularized transform.  This module places the literal regularized
integral, not only its Cauchy-transform gauge, in the upper-end analytic and meromorphic carriers.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions MeasureTheory Filter Set Polynomial
open scoped ENNReal

noncomputable section

/-- The zero-gauge Nevanlinna-weighted measure is finite under the exact Herglotz integrability
hypothesis. -/
theorem isFiniteMeasure_nevanlinnaWeightedMeasure_zero
    (ν : Measure ℝ) (hH0 : Integrable nevanlinnaWeight ν) :
    IsFiniteMeasure (nevanlinnaWeightedMeasure ν (fun _ => 0)) := by
  have hdens : Measurable
      (fun t : ℝ => Real.toNNReal (nevanlinnaWeight t * Real.exp (0 : ℝ))) := by
    apply Measurable.real_toNNReal
    unfold nevanlinnaWeight
    fun_prop
  have hint : Integrable (fun t => nevanlinnaWeight t * Real.exp (0 : ℝ)) ν := by
    simpa using hH0
  have hnn : 0 ≤ᵐ[ν] fun t => nevanlinnaWeight t * Real.exp (0 : ℝ) := by
    filter_upwards with t
    exact mul_nonneg (nevanlinnaWeight_pos t).le (Real.exp_pos _).le
  have hlint : ∫⁻ t,
      (Real.toNNReal (nevanlinnaWeight t * Real.exp (0 : ℝ)) : ℝ≥0∞) ∂ν ≠ ∞ := by
    have heq : ∫⁻ t,
        (Real.toNNReal (nevanlinnaWeight t * Real.exp (0 : ℝ)) : ℝ≥0∞) ∂ν =
        ENNReal.ofReal (∫ t, nevanlinnaWeight t * Real.exp (0 : ℝ) ∂ν) :=
      (ofReal_integral_eq_lintegral_ofReal hint hnn).symm
    rw [heq]
    exact ENNReal.ofReal_ne_top
  rw [nevanlinnaWeightedMeasure]
  exact isFiniteMeasure_withDensity hlint

/-- Literal regularized Herglotz integral as an upper-end analytic germ.  Its analytic
representative is the exact affine Cauchy-transform gauge supplied by
`regularizedHerglotzTransform_eq`. -/
def regularizedH0UpperEndAnalytic (nu : Measure ℝ)
    (hH0 : Integrable nevanlinnaWeight nu) : upperEndAnalyticSubring := by
  letI := isDomain_upperEndAnalyticSubring
  letI : IsFiniteMeasure (nevanlinnaWeightedMeasure nu (fun _ => 0)) :=
    isFiniteMeasure_nevanlinnaWeightedMeasure_zero nu hH0
  exact
    ⟨(((fun z => ∫ t, regularizedHerglotzKernel t z ∂nu) : ℂ → ℂ) :
        Germ upperEndFilter ℂ),
      (fun z => z * (((nevanlinnaWeightedMeasure nu (fun _ => 0)).real univ : ℝ) : ℂ) +
        (1 + z ^ 2) * cauchyTransform (nevanlinnaWeightedMeasure nu (fun _ => 0)) z),
      0, by
        apply AnalyticOnNhd.add
        · exact analyticOnNhd_id.mul analyticOnNhd_const
        · exact (analyticOnNhd_const.add (analyticOnNhd_id.pow 2)).mul
            (analyticOnNhd_cauchyTransform_upperTail_zero
              (nevanlinnaWeightedMeasure nu (fun _ => 0))),
      by
        apply Filter.Germ.coe_eq.mpr
        filter_upwards [upperEndFilter_basis.mem_iff.mpr
          ⟨0, trivial, Set.Subset.rfl⟩] with z hz
        have hzi : z.im ≠ 0 := ne_of_gt hz
        simpa [cauchyTransform] using
          (regularizedHerglotzTransform_eq nu (fun _ => 0) measurable_const hzi).symm⟩

/-- Literal regularized Herglotz integral as an upper-end meromorphic element. -/
def regularizedH0UpperEndMero (nu : Measure ℝ)
    (hH0 : Integrable nevanlinnaWeight nu) : upperEndMeroField := by
  letI := isDomain_upperEndAnalyticSubring
  exact algebraMap upperEndAnalyticSubring upperEndMeroField
    (regularizedH0UpperEndAnalytic nu hH0)

@[simp]
theorem regularizedH0UpperEndAnalytic_coe
    (nu : Measure ℝ) (hH0 : Integrable nevanlinnaWeight nu) :
    ((regularizedH0UpperEndAnalytic nu hH0 : upperEndAnalyticSubring) :
      Germ upperEndFilter ℂ) =
      (((fun z => ∫ t, regularizedHerglotzKernel t z ∂nu) : ℂ → ℂ) :
        Germ upperEndFilter ℂ) := rfl

end

end GaloisForLFunctions.HTGeometry
