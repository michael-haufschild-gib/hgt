import GaloisForLFunctions.RHTower.ThetaCuspRatioKineticSecondSource
namespace HTGeometry.ThetaRatioKineticContraction
noncomputable section
set_option autoImplicit false
open MvPolynomial ThetaRatioSource ThetaRatioSquare ThetaRatioInfinity
open HTGeometry.EvenCompactBernstein

theorem reducedKineticCoefficient_drift_expansion (h v : ℝ) (j : ℕ) :
    reducedKineticCoefficient h v j=
      ∑ b ∈ Finset.range 10,(kineticDriftCell (h:ℂ) completeKineticSlope j (b+1)).re*v^b := by
  have he := congrArg Complex.re (reducedKineticDriftCoefficient_expansion (h:ℂ) (v:ℂ) j)
  simpa only [reducedKineticCoefficient,Complex.re_sum,Complex.mul_re,
    ←Complex.ofReal_pow,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero] using he

def reducedKineticControlDriftCell (h Z : ℝ) (i b : ℕ) : ℝ :=
  ∑ j ∈ Finset.range 20,(kineticDriftCell (h:ℂ) completeKineticSlope j (b+1)).re*
    Z^j*degreeElevationCoefficient 19 j i

theorem reducedKineticControl_drift_expansion (h v Z : ℝ) (i : ℕ) :
    reducedKineticControl h v Z i=
      ∑ b ∈ Finset.range 10,reducedKineticControlDriftCell h Z i b*v^b := by
  unfold reducedKineticControl kineticControl reducedKineticControlDriftCell
  simp_rw [reducedKineticCoefficient_drift_expansion]
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro j _
  ring

end
end HTGeometry.ThetaRatioKineticContraction

