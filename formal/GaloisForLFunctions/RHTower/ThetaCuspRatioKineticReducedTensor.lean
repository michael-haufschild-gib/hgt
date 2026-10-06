import GaloisForLFunctions.RHTower.ThetaCuspRatioKineticDriftBlocks2
import GaloisForLFunctions.RHTower.ThetaCuspRatioKineticDriftBlocks4
import GaloisForLFunctions.RHTower.ThetaCuspRatioKineticDriftBlocks6
import GaloisForLFunctions.RHTower.ThetaCuspRatioKineticDriftBlocks8
import GaloisForLFunctions.RHTower.ThetaCuspRatioKineticDriftBlocks10
import GaloisForLFunctions.RHTower.ThetaCuspRatioKineticReducedDrift
namespace HTGeometry.ThetaRatioKineticContraction
noncomputable section
set_option autoImplicit false
open MvPolynomial ThetaRatioSource ThetaRatioSquare ThetaRatioInfinity

theorem completeKineticSlope_drift_bound : KineticDriftBound completeKineticSlope 10 := by
  rw [completeKineticSlope_cofactors]
  exact kineticDriftBound_add
    (kineticDriftBound_add
      (kineticDriftBound_add
        (kineticDriftBound_add
          (kineticDriftBound_mul kineticCof2_drift_bound kineticBlock2_drift_bound)
          (kineticDriftBound_mul kineticCof4_drift_bound kineticBlock4_drift_bound))
        (kineticDriftBound_mul kineticCof6_drift_bound kineticBlock6_drift_bound))
      (kineticDriftBound_mul kineticCof8_drift_bound kineticBlock8_drift_bound))
    (kineticDriftBound_mul kineticCof10_drift_bound kineticBlock10_drift_bound)

theorem reducedKineticDriftCoefficient_degree (h : ℂ) (j : ℕ) :
    (reducedKineticDriftCoefficient h j).natDegree≤9 := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro b hb
  rw [reducedKineticDriftCoefficient_coeff]
  exact completeKineticSlope_drift_bound h j (b+1) (by omega)

theorem reducedKineticDriftCoefficient_expansion (h v : ℂ) (j : ℕ) :
    (reducedKineticDriftCoefficient h j).eval v=
      ∑ b ∈ Finset.range 10,kineticDriftCell h completeKineticSlope j (b+1)*v^b := by
  rw [Polynomial.eval_eq_sum_range'
    (show (reducedKineticDriftCoefficient h j).natDegree<10 by
      have := reducedKineticDriftCoefficient_degree h j
      omega)]
  simp only [reducedKineticDriftCoefficient_coeff,kineticDriftCell]

theorem completeKineticSlope_reduced_tensor (h v z : ℂ) :
    eval (basePoint h v z) clearSlope=
      v*∑ j ∈ Finset.range 20,
        (∑ b ∈ Finset.range 10,kineticDriftCell h completeKineticSlope j (b+1)*v^b)*z^j := by
  rw [completeKineticSlope_reduced_expansion]
  simp_rw [reducedKineticDriftCoefficient_expansion]

end
end HTGeometry.ThetaRatioKineticContraction
