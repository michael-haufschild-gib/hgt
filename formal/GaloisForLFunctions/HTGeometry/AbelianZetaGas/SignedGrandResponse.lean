import GaloisForLFunctions.HTGeometry.AbelianZetaGas.GrandResponse
import GaloisForLFunctions.HTGeometry.AbelianZetaGas.ParityMass

/-!
# Signed grand response

This file identifies the parity-twisted two-observable response with the quotient of the doubled
grand-response ladder by the tilted and base ladders.  The same depth-tail argument gives its
meromorphic continuation throughout the positive dilation chamber.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The complex signed response in the order-dilation variable. -/
def signedGrandResponse (σ : ℝ) (v u : ℂ) : ℂ :=
  grandResponse (2 * σ) (2 * v) (2 * u) /
    (grandResponse σ v u * grandResponse σ 0 0)

/-- **Signed grand response `(GAS4.2)`, zeta-product form.** -/
theorem signedGrandResponse_eq_zetaProduct (σ : ℝ) (v u : ℂ) :
    signedGrandResponse σ v u =
      (∏' j : ℕ, riemannZeta
        (2 * (((j + 1 : ℕ) : ℂ) * ((σ : ℝ) + u) + v))) /
      ((∏' j : ℕ, riemannZeta
          (((j + 1 : ℕ) : ℂ) * ((σ : ℝ) + u) + v)) *
        ∏' j : ℕ, riemannZeta (((j + 1 : ℕ) : ℂ) * (σ : ℝ))) := by
  unfold signedGrandResponse grandResponse depthFactor
  congr 1
  · refine tprod_congr fun j => ?_
    congr 1
    push_cast
    ring
  · congr 1
    · refine tprod_congr fun j => ?_
      congr 1
      simp

/-- A convergent zeta partition is the zero-dilation grand response at its parameter point. -/
theorem AbelianZetaConvergentParameters.zetaPartition_eq_grandResponse_zero
    (θ : AbelianZetaConvergentParameters) :
    θ.zetaPartition = grandResponse θ.sigma (θ.tau : ℂ) 0 := by
  unfold AbelianZetaConvergentParameters.zetaPartition grandResponse depthFactor
  refine tprod_congr fun j => ?_
  congr 1
  push_cast
  ring

/-- A real dilation can equivalently be absorbed into the base temperature. -/
theorem grandResponse_realShift (σ u : ℝ) (v : ℂ) :
    grandResponse σ v (u : ℂ) = grandResponse (σ + u) v 0 := by
  unfold grandResponse depthFactor
  refine tprod_congr fun j => ?_
  congr 1
  push_cast
  ring

/-- The complex signed response at a real convergent target is exactly the doubled partition
quotient appearing in the parity expectation. -/
theorem signedGrandResponse_temperature_target
    (σ : EulerSigma) (θ' : AbelianZetaConvergentParameters) :
    signedGrandResponse σ.val (θ'.tau : ℂ) (θ'.sigma - σ.val : ℝ) =
      θ'.double.zetaPartition /
        (θ'.zetaPartition * (temperatureConv σ).zetaPartition) := by
  have hnumShift :
      grandResponse (2 * σ.val) (2 * (θ'.tau : ℂ))
          (2 * ((θ'.sigma - σ.val : ℝ) : ℂ)) =
        grandResponse (2 * σ.val + 2 * (θ'.sigma - σ.val))
          (2 * (θ'.tau : ℂ)) 0 := by
    convert grandResponse_realShift (2 * σ.val) (2 * (θ'.sigma - σ.val))
      (2 * (θ'.tau : ℂ)) using 1
    push_cast
    ring
  have hnum :
      grandResponse (2 * σ.val) (2 * (θ'.tau : ℂ))
          (2 * ((θ'.sigma - σ.val : ℝ) : ℂ)) = θ'.double.zetaPartition := by
    rw [hnumShift, θ'.double.zetaPartition_eq_grandResponse_zero]
    congr 3
    · simp only [AbelianZetaConvergentParameters.double_sigma]
      ring
    · simp only [AbelianZetaConvergentParameters.double_tau]
      push_cast
      rfl
  have htarget :
      grandResponse σ.val (θ'.tau : ℂ) (θ'.sigma - σ.val : ℝ) =
        θ'.zetaPartition := by
    rw [grandResponse_realShift, θ'.zetaPartition_eq_grandResponse_zero]
    congr 3
    ring
  have hbase : grandResponse σ.val 0 0 = (temperatureConv σ).zetaPartition := by
    simpa using ((temperatureConv σ).zetaPartition_eq_grandResponse_zero).symm
  unfold signedGrandResponse
  rw [hnum, htarget, hbase]

/-- **Signed grand response `(GAS4.2)`, expectation form.**  The native parity-twisted moment at
every real target in the exact convergence chamber equals the corresponding complex signed grand
response. -/
theorem integral_classLaw_parity_mul_gasTilt_eq_signedGrandResponse
    (σ : EulerSigma) (θ' : AbelianZetaConvergentParameters) :
    (∫ A, A.parity * ((temperatureConv σ).gasTilt θ' A : ℂ)
      ∂classLaw (temperatureConv σ).toAbelianZetaParameters) =
      signedGrandResponse σ.val (θ'.tau : ℂ) (θ'.sigma - σ.val : ℝ) := by
  rw [integral_classLaw_parity_mul_gasTilt,
    signedGrandResponse_temperature_target]

/-- The signed response is meromorphic on `Re (σ + u) > 0`, by the common depth-tail argument. -/
theorem meromorphicAt_signedGrandResponse (σ : ℝ) (v : ℂ) {a₀ : ℝ} (ha₀ : 0 < a₀) {u : ℂ}
    (hu : a₀ < σ + u.re) : MeromorphicAt (signedGrandResponse σ v) u := by
  have hdoubleBase : 0 < 2 * a₀ := by linarith
  have hdoubleChamber : 2 * a₀ < 2 * σ + (2 * u).re := by
    simp only [Complex.mul_re]
    norm_num
    linarith
  have hnumAt : MeromorphicAt (grandResponse (2 * σ) (2 * v)) (2 * u) :=
    meromorphicAt_grandResponse (2 * σ) (2 * v) hdoubleBase hdoubleChamber
  have hscale : AnalyticAt ℂ (fun w : ℂ => 2 * w) u := by fun_prop
  have hnum : MeromorphicAt (fun w : ℂ => grandResponse (2 * σ) (2 * v) (2 * w)) u :=
    hnumAt.comp_analyticAt hscale
  have htilted : MeromorphicAt (grandResponse σ v) u :=
    meromorphicAt_grandResponse σ v ha₀ hu
  have hbase : MeromorphicAt (fun _ : ℂ => grandResponse σ 0 0) u :=
    analyticAt_const.meromorphicAt
  exact hnum.fun_div (htilted.fun_mul hbase)

end

end GaloisForLFunctions.HTGeometry
