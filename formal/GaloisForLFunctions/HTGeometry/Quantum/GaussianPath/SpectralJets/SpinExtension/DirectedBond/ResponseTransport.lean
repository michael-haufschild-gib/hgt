import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.SpinExtension.DirectedBond.TiltResponses
import Mathlib.Analysis.Calculus.Deriv.CompMul

/-! # Mixed derivatives of an endpoint field projected onto a spin sector -/
namespace GaloisForLFunctions.HTGeometry.SpectralJets.SpinExtension.DirectedBond
noncomputable section

/-- Rescaling the terminal control multiplies its derivative by the corresponding power. -/
theorem jet_rescale (m : Bool) (f : ℂ→ℂ) (k : ℂ) :
    jet m (fun J => f (k*J)) 0 = k^order m*jet m f 0 := by
  have h (g : ℂ→ℂ) : deriv (fun J => g (k*J)) = fun J => k*deriv g (k*J) :=
    funext fun J => deriv_comp_mul_left k g J
  cases m with
  | false => simp only [jet,h,mul_zero,order,pow_one]
  | true =>
    simp only [jet,h,deriv_const_mul_field,mul_zero,order]
    ring

/-- Old derivatives may be taken before projection. The remaining bond and tilt
derivatives separate the two sectors according to the parity of the bond order. -/
theorem projected_response (j m : Bool) (s : ℂ) (f : ℂ→ℂ) :
    jet j (fun t => jet m (fun J => f ((s*alignment t)*J)) 0) 0 =
      (s^order m*jet j (fun t => alignment t^order m) 0)*jet m f 0 := by
  have h (t : ℂ) : jet m (fun J => f ((s*alignment t)*J)) 0 =
      (s^order m*jet m f 0)*alignment t^order m := by
    rw [jet_rescale,mul_pow]
    ring
  simp only [h,jet_const_mul]
  ring

#print axioms projected_response
end
end GaloisForLFunctions.HTGeometry.SpectralJets.SpinExtension.DirectedBond
