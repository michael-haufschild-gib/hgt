import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.RepeatedGates.DoubleBracket
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.RepeatedGates.TaylorFloor
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.EigenlineSignals.AnalyticSignal
import Mathlib.Analysis.SpecialFunctions.Exponential

/-! # A nonzero Heisenberg coefficient gives a short-time signal -/
open Filter Matrix NormedSpace Topology
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.RepeatedGates
noncomputable section
private abbrev Reg (N : ℕ) := Matrix (Fin N→Bool) (Fin N→Bool) ℂ

/-- Pull a local output back to the input and commute it with the input probe. -/
def signal {N : ℕ} (H A B : Reg N) (t : ℝ) :=
  bracket (unitaryEvolution H (-t)*A*unitaryEvolution H t) B

private theorem signal_deriv {N : ℕ} (H A B : Reg N) (t : ℝ) :
    HasDerivAt (signal H A B) (signal H (bracket A ((-Complex.I) • H)) B t) t := by
  letI : NormedAlgebra ℚ (Reg N) := .restrictScalars ℚ ℂ _
  let G := (-Complex.I) • H
  have h := ((hasDerivAt_exp_smul_const (-G) t).mul_const A).fun_mul (hasDerivAt_exp_smul_const' G t)
  have he : HasDerivAt (fun s : ℝ => exp (s • (-G))*A*exp (s • G))
      (exp (t • (-G))*bracket A G*exp (t • G)) t := by
    have prod (L R : Reg N) : L*bracket A G*R=L*(-G)*A*R+L*A*(G*R) := by
      unfold bracket
      noncomm_ring
    rw [prod]
    exact h
  have hd := (he.mul_const B).sub (he.const_mul B)
  change HasDerivAt (fun s : ℝ => (exp ((-s) • G)*A*exp (s • G))*B-
    B*(exp ((-s) • G)*A*exp (s • G))) _ t
  simpa only [Pi.sub_def,signal,bracket,unitaryEvolution,G,neg_smul,smul_neg] using hd

private theorem signal_zero {N : ℕ} (H A B : Reg N) : signal H A B 0=bracket A B := by
  simp [signal,unitaryEvolution]

private theorem signal_smooth {N : ℕ} (H A B : Reg N) : ContDiff ℝ 2 (signal H A B) := by
  apply contDiff_iff_contDiffAt.mpr
  intro t
  have h := (((EigenlineSignals.analytic_evolution H (-t)).comp analyticAt_id.neg).mul
    (analyticAt_const (v:=A))).mul (EigenlineSignals.analytic_evolution H t)
  exact ((h.mul (analyticAt_const (v:=B))).sub ((analyticAt_const (v:=B)).mul h)).contDiffAt

/-- A nonzero second-order coefficient bounds the signal in both time
directions, including when a first-order term is also present. -/
theorem quadratic_signal_floor {N : ℕ} (H A B : Reg N) (hc : Commute A B)
    (hP : signal₂ A B H ≠ 0) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ t : ℝ in 𝓝 0, c*t^2 ≤ ‖signal H A B t‖ := by
  let G := (-Complex.I) • H
  have hd (X : Reg N) : deriv (signal H X B)=signal H (bracket X G) B :=
    funext fun s => (signal_deriv H X B s).deriv
  have h₂ : iteratedDeriv 2 (signal H A B) 0=signal₂ A B G := by
    rw [iteratedDeriv_succ,iteratedDeriv_one,hd,hd,signal_zero]; rfl
  have ex (X K : Reg N) (z : ℂ) : bracket X (z • K)=z • bracket X K := by
    simp only [bracket,Matrix.mul_smul,Matrix.smul_mul,smul_sub]
  have ey (X K : Reg N) (z : ℂ) : bracket (z • X) K=z • bracket X K := by
    simp only [bracket,Matrix.mul_smul,Matrix.smul_mul,smul_sub]
  apply second_deriv_floor (signal_smooth H A B) (by rw [signal_zero,bracket,hc.eq,sub_self])
  have he : signal₂ A B G=((-Complex.I)*(-Complex.I)) • signal₂ A B H := by
    simp only [signal₂,G,ex,ey,smul_smul]
  rw [h₂,he]
  exact smul_ne_zero (mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero) (neg_ne_zero.mpr Complex.I_ne_zero)) hP

end
end GaloisForLFunctions.HTGeometry.RepeatedGates
