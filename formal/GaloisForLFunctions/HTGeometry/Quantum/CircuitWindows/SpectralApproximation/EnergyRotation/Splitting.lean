import GaloisForLFunctions.HTGeometry.Quantum.CircuitSynthesis.LocalErrors.Commutator
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! # Integrated commutator error for comparing two unitary flows -/
open NormedSpace MeasureTheory
namespace GaloisForLFunctions.HTGeometry.EnergyRotation
noncomputable section
variable {A : Type*} [CStarAlgebra A]
open private reverseFlow_deriv flow_unitary from GaloisForLFunctions.HTGeometry.Quantum.CircuitSynthesis.LocalErrors.Commutator

/-- The commutator defect grows at most linearly along the interpolating
flow. Integrating that defect gives half the squared duration. -/
theorem split_error (x y : A) (hx : x∈skewAdjoint A) (hy : y∈skewAdjoint A)
    (t : ℝ) (ht : 0≤t) :
    ‖exp (t • x)*exp (t • y)-exp (t • (x+y))‖ ≤ t^2/2*‖x*y-y*x‖ := by
  letI : NormedAlgebra ℚ A := .restrictScalars ℚ ℂ A
  let f (s : ℝ) := exp ((t-s) • (x+y))*exp (s • x)*exp (s • y)
  let g (s : ℝ) := exp ((t-s) • (x+y))*(exp (s • x)*y-y*exp (s • x))*exp (s • y)
  have hd (s : ℝ) : HasDerivAt f (g s) s := by
    have h := ((reverseFlow_deriv (x+y) t s).fun_mul
      (hasDerivAt_exp_smul_const' x s)).fun_mul (hasDerivAt_exp_smul_const' y s)
    convert h using 1
    dsimp only [g]
    noncomm_ring
  have hg : Continuous g := by dsimp only [g]; fun_prop
  have hft := intervalIntegral.integral_deriv_eq_sub' (a:=0) (b:=t) f (funext fun s => (hd s).deriv)
    (fun s _ => (hd s).differentiableAt) hg.continuousOn
  have hbound (s : ℝ) (hs : s∈Set.Ioc 0 t) : ‖g s‖≤s*‖x*y-y*x‖ := by
    dsimp only [g]
    rw [CStarRing.norm_mul_mem_unitary _ (flow_unitary y hy s),
      CStarRing.norm_mem_unitary_mul _ (flow_unitary _ ((skewAdjoint A).add_mem hx hy) (t-s)),mul_comm s]
    exact norm_exp_mul_sub_mul_exp_le_commutator x y hx s hs.1.le
  have h := intervalIntegral.norm_integral_le_of_norm_le (f:=g) (μ:=volume) ht
    (Filter.Eventually.of_forall hbound)
    ((continuous_id.mul continuous_const).intervalIntegrable 0 t)
  rw [hft,intervalIntegral.integral_mul_const,integral_id] at h
  simpa [f] using h

#print axioms split_error
end
end GaloisForLFunctions.HTGeometry.EnergyRotation
