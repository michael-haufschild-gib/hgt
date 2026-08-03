import GaloisForLFunctions.RHTower.MobiusCriticalFisherCountableCommonHardyReporter
import GaloisForLFunctions.RHTower.DeningerMeyerReflectedGaussianCountertransportXiCapacity

/-!
# Countable reporter selection criterion for Gaussian countertransport

The completed squarefree source gives a uniformly budgeted countable Hardy
reporter for every contraction.  The reflected Gaussian countertransport
gives a completed Xi field whose uniform boundedness is equivalent to RH.
This file isolates the exact missing compatibility: any source-derived
uniform domination of the countertransport field by contraction reporters
forces RH.

No such domination is assumed elsewhere or constructed here.
-/

open Complex Filter Set Topology
open scoped ENNReal NNReal Topology

namespace RHTower

noncomputable section

open DeningerMeyerGaussianGreen

/-- **Countable-reporter selection criterion.**  Fix any finite Euler
parameter `sigma > 1`.  If every reflected Gaussian Xi countertransport
field is dominated, with one uniform constant, by a countable common Hardy
reporter produced from a contraction of the completed squarefree source,
then RH follows. -/
theorem riemannHypothesis_of_countertransportXiField_sq_norm_le_countableReporter
    (sigma : ℝ) (hsigma : 1 < sigma)
    (D : ℝ →
      (lp (fun _ : ℕ => ℂ) 2 →L[ℂ] lp (fun _ : ℕ => ℂ) 2))
    (hD : ∀ c, ‖D c‖ ≤ 1)
    (K : ℝ) (hK : 0 ≤ K)
    (hdom : ∀ c : ℝ,
      ‖deningerMeyerReflectedGaussianCountertransportXiField c‖ ^ 2 ≤
        K *
          ‖squarefreeMobiusCriticalFisherCountableCommonHardyReporter
            sigma hsigma (D c) (hD c)‖ ^ 2) :
    RiemannHypothesis := by
  apply
    deningerMeyerReflectedGaussianCountertransportXiFieldsBounded_iff_rh.mp
  let B := squarefreeMobiusCriticalFisherCountableReporterBudget sigma
  refine ⟨K * B + 1, fun c => ?_⟩
  have hreport :=
    norm_sq_squarefreeMobiusCriticalFisherCountableCommonHardyReporter_le
      sigma hsigma (D c) (hD c)
  have hB : 0 ≤ B := by
    dsimp only [B]
    exact (sq_nonneg
      ‖squarefreeMobiusCriticalFisherCountableCommonHardyReporter
        sigma hsigma (D c) (hD c)‖).trans hreport
  have hfieldSq :
      ‖deningerMeyerReflectedGaussianCountertransportXiField c‖ ^ 2 ≤
        K * B := by
    exact (hdom c).trans
      (mul_le_mul_of_nonneg_left hreport hK)
  nlinarith
    [norm_nonneg
      (deningerMeyerReflectedGaussianCountertransportXiField c),
     sq_nonneg
      (‖deningerMeyerReflectedGaussianCountertransportXiField c‖ - 1)]

end

end RHTower
