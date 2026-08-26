import GaloisForLFunctions.HTGeometry.HerglotzConjugateWeakType
import GaloisForLFunctions.HTGeometry.SmirnovKernelOuterRegularization

open Complex Filter MeasureTheory Metric Set Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Normalized zero-free logarithm of an outer Smirnov numerator. -/
def DiskSmirnovBoundary.outerNumeratorLog
    (Q : DiskSmirnovBoundary) (hQ : IsOuterDiskMultiplier Q.numerator) :
    BoundedZeroFreeLog Q.numerator :=
  BoundedZeroFreeLog.ofZeroFree Q.numerator (fun z hz =>
    hQ.ne_zero_on_disk (by simpa [Metric.mem_ball, dist_zero_right] using hz))

/-- Normalized zero-free logarithm of a Smirnov denominator. -/
def DiskSmirnovBoundary.outerDenominatorLog
    (Q : DiskSmirnovBoundary) : BoundedZeroFreeLog Q.denominator :=
  BoundedZeroFreeLog.ofZeroFree Q.denominator (fun z hz =>
    Q.denominator_outer.ne_zero_on_disk
      (by simpa [Metric.mem_ball, dist_zero_right] using hz))

/-- Canonical real-line phase of an outer Smirnov quotient. -/
def DiskSmirnovBoundary.outerBoundaryPhase
    (Q : DiskSmirnovBoundary) (hQ : IsOuterDiskMultiplier Q.numerator)
    (x : ℝ) : ℝ :=
  (Q.outerNumeratorLog hQ).boundaryLinePhase x -
    Q.outerDenominatorLog.boundaryLinePhase x

/-- The literal phase reflection of an outer Smirnov quotient is the exponential of its
canonical boundary phase. -/
theorem DiskSmirnovBoundary.phaseReflectionSymbol_eq_exp_outerBoundaryPhase_ae
    (Q : DiskSmirnovBoundary) (hQ : IsOuterDiskMultiplier Q.numerator) :
    Q.phaseReflectionSymbol =ᵐ[volume] fun x =>
      Complex.exp (-2 * I * ((Q.outerBoundaryPhase hQ x : ℝ) : ℂ)) := by
  filter_upwards [(Q.outerNumeratorLog hQ).phaseReflection_eq_exp_ae,
    Q.outerDenominatorLog.phaseReflection_eq_exp_ae,
    diskMultiplierLineBoundary_ne_zero_ae Q.numerator hQ.exists_nonzero,
    Q.denominator_ne_zero_ae] with x hn hd hnum hden
  rw [DiskSmirnovBoundary.phaseReflectionSymbol,
    DiskSmirnovBoundary.boundary, if_neg (div_ne_zero hnum hden)]
  rw [diskMultiplierPhaseReflectionSymbol, if_neg hnum] at hn
  rw [diskMultiplierPhaseReflectionSymbol, if_neg hden] at hd
  have hexp :
      Complex.exp (-2 * I * ((Q.outerBoundaryPhase hQ x : ℝ) : ℂ)) =
        Complex.exp (-2 * I *
          (((Q.outerNumeratorLog hQ).boundaryLinePhase x : ℝ) : ℂ)) /
        Complex.exp (-2 * I *
          ((Q.outerDenominatorLog.boundaryLinePhase x : ℝ) : ℂ)) := by
    rw [← Complex.exp_sub]
    congr 1
    simp only [DiskSmirnovBoundary.outerBoundaryPhase]
    push_cast
    ring
  rw [hexp, ← hn, ← hd, map_div₀]
  field_simp

/-- Canonical phase of every outer Smirnov quotient has finite weak-`L¹` Poisson tails. -/
theorem DiskSmirnovBoundary.outerBoundaryPhase_weakL1BigO
    (Q : DiskSmirnovBoundary) (hQ : IsOuterDiskMultiplier Q.numerator) :
    PoissonWeakL1BigO (Q.outerBoundaryPhase hQ) :=
  (Q.outerNumeratorLog hQ).boundaryLinePhase_weakL1BigO.sub
    Q.outerDenominatorLog.boundaryLinePhase_weakL1BigO

end

end GaloisForLFunctions.HTGeometry
