import GaloisForLFunctions.HTGeometry.AnalyticCircleSeamCompletion
import GaloisForLFunctions.HTGeometry.DiskSmirnovHardyOneFactorization
import GaloisForLFunctions.HTGeometry.HardyProductWeightedArcGluing
import GaloisForLFunctions.HTGeometry.SmirnovKernelOuterRegularization
import GaloisForLFunctions.RHTower.KapustinOneSidedToeplitzCircleLocalAnalytic

/-!
# Outer gluing for the one-sided Kapustin Toeplitz symbol

The canonical outer regularization of a nonzero `N⁺` kernel has an integrable circle boundary.
Its phase-reflection identity is transported to the circle and glued across every finite Cayley
point.  Squaring removes the sign ambiguity between local analytic square-root branches.
-/

open Complex Filter MeasureTheory Metric Set Topology

namespace RHTower

open GaloisForLFunctions.HTGeometry

noncomputable section

/-- Circle seam identity induced by an outer phase-reflection factorization of the one-sided
Kapustin symbol. -/
theorem kapustinOneSidedToeplitzCircle_seam_of_outer_phaseReflection
    (d : ℂ) (Q : DiskSmirnovBoundary) (hd : ‖d‖ = 1)
    (hQ : ∃ z ∈ ball (0 : ℂ) 1, Q.numerator.fn z ≠ 0)
    (hphase : kapustinOneSidedToeplitzSymbol =ᵐ[volume]
      fun x => d * Q.phaseReflectionSymbol x) :
    (fun z : Circle =>
      (starRingEnd ℂ) d * kapustinOneSidedToeplitzCircleSymbol z *
        Q.circleBoundary z) =ᵐ[circleLebesgue]
      fun z => (starRingEnd ℂ) (Q.circleBoundary z) := by
  have hleft : AEMeasurable (fun z : Circle =>
      (starRingEnd ℂ) d * kapustinOneSidedToeplitzCircleSymbol z *
        Q.circleBoundary z) circleLebesgue := by
    have hcoeffMeas : Measurable (fun z : Circle =>
        (starRingEnd ℂ) d * kapustinOneSidedToeplitzCircleSymbol z) :=
      measurable_const.mul measurable_kapustinOneSidedToeplitzCircleSymbol
    have hcoeff : AEStronglyMeasurable (fun z : Circle =>
        (starRingEnd ℂ) d * kapustinOneSidedToeplitzCircleSymbol z)
        circleLebesgue := hcoeffMeas.aestronglyMeasurable
    exact (hcoeff.mul Q.aestronglyMeasurable_circleBoundary).aemeasurable
  have hright : AEMeasurable (fun z : Circle =>
      (starRingEnd ℂ) (Q.circleBoundary z)) circleLebesgue :=
    (Complex.continuous_conj.comp_aestronglyMeasurable
      Q.aestronglyMeasurable_circleBoundary).aemeasurable
  apply circle_eventuallyEq_of_line_eventuallyEq_ae hleft hright
  filter_upwards [hphase, Q.boundary_eq_circleBoundary_cayley_ae,
    Q.boundary_ne_zero_ae hQ] with x hxPhase hxCircle hxNe
  rw [kapustinOneSidedToeplitzCircleSymbol_circleCayley, ← hxCircle, hxPhase,
    DiskSmirnovBoundary.phaseReflectionSymbol, if_neg hxNe]
  have hunit : (starRingEnd ℂ) d * d = 1 := by
    rw [Complex.conj_mul', hd]
    norm_num
  rw [← mul_assoc, hunit, one_mul]
  field_simp [hxNe]

end

end RHTower
