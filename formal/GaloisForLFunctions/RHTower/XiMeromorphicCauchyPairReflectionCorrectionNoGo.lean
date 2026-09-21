import GaloisForLFunctions.RHTower.XiMeromorphicCauchyPairSourceLanding

/-!
# EGC reflection-only shifted-pole correction no-go

The EGC rational Cauchy pair has two prescribed shifted-pole residues whenever
an outer contour crosses its observation poles.  Pairing a divisor point with
its functional-equation reflection does not cancel that correction: reflection
conjugates its real channel.  Therefore a cofinal EGC covariance proof needs
an independent source-side decay or real-part cancellation law.
-/

namespace RHTower

noncomputable section

/-- Sum of the two prescribed shifted-pole residues in the EGC Cauchy-pair
three-pole decomposition. -/
def meromorphicCauchyPairShiftResidueCorrection
    (eps : ℝ) (w rho : ℂ) : ℂ :=
  -(eps : ℂ) / (2 * (rho - w - (eps : ℂ))) +
    (eps : ℂ) / (2 * (rho - w + (eps : ℂ)))

/-- Functional-equation reflection alone cannot cancel the EGC shifted-pole
correction.  This does not assert a value at an Xi zero; it rules out proving
the required outer covariance from reflection pairing without an additional
source-side real-part law. -/
theorem not_forall_meromorphicCauchyPair_reflectionCorrection_zero :
    ¬ ∀ (eps : ℝ) (w rho : ℂ),
      rho - w - (eps : ℂ) ≠ 0 →
      rho - w + (eps : ℂ) ≠ 0 →
      (1 - (starRingEnd ℂ) rho) - w - (eps : ℂ) ≠ 0 →
      (1 - (starRingEnd ℂ) rho) - w + (eps : ℂ) ≠ 0 →
      meromorphicCauchyPairShiftResidueCorrection eps w rho +
        meromorphicCauchyPairShiftResidueCorrection eps w
          (1 - (starRingEnd ℂ) rho) = 0 := by
  intro h
  have htest := h 1 (1 / 2 : ℂ) (5 : ℂ)
    (by norm_num) (by norm_num)
    (by norm_num [starRingEnd_apply]) (by norm_num [starRingEnd_apply])
  norm_num [meromorphicCauchyPairShiftResidueCorrection, starRingEnd_apply] at htest

end

end RHTower
