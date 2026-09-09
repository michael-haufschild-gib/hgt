import GaloisForLFunctions.HTGeometry.WuSchwartzEnergy
import GaloisForLFunctions.RHTower.ThetaCuspSchwartzFourierXi

/-!
# Characteristic energy integration for the native theta and Xi sources

Wu's Lemma 2.3 in arXiv:2609.08421 applies to the actual all-integer theta
source and its existing Fourier identification with `XiC`. Every derivative
and polynomial moment is admitted by the already proved Schwartz structure.
These are real-axis energy bounds; no assertion about the location of zeros
is used or obtained.
-/
namespace RHTower.Wu
open GaloisForLFunctions.HTGeometry.Wu
noncomputable section

/-- All weighted derivatives of the native theta-cusp source satisfy the inverse-rate energy bound. -/
theorem theta_source_jet_energy_le (k n : ℕ) (d t : ℝ) :
    energy d t (fun s => (s ^ k : ℝ) •
      iteratedDeriv n (fun x : ℝ => (thetaCuspFullSource x : ℂ)) s) ≤
      (SchwartzMap.seminorm ℝ k n thetaCuspSchwartz) ^ 2 / (2 * Real.exp d) :=
  schwartz_jet_energy_le thetaCuspSchwartz k n d t

/-- The native source normalized for the Xi Fourier transform has the same closed estimate. -/
theorem xi_source_jet_energy_le (k n : ℕ) (d t : ℝ) :
    energy d t (fun s => (s ^ k : ℝ) • iteratedDeriv n (xiThetaSchwartzSource : ℝ → ℂ) s) ≤
      (SchwartzMap.seminorm ℝ k n xiThetaSchwartzSource) ^ 2 / (2 * Real.exp d) :=
  schwartz_jet_energy_le xiThetaSchwartzSource k n d t

/-- Transfer through the actual Fourier identity gives all real-axis Xi derivative and moment bounds. -/
theorem xi_real_jet_energy_le (k n : ℕ) (d t : ℝ) :
    energy d t (fun s => (s ^ k : ℝ) • iteratedDeriv n (fun x : ℝ => XiC (x : ℂ)) s) ≤
      (SchwartzMap.seminorm ℝ k n (SchwartzMap.fourierTransformCLM ℂ xiThetaSchwartzSource)) ^ 2 /
        (2 * Real.exp d) := by
  have he : (SchwartzMap.fourierTransformCLM ℂ xiThetaSchwartzSource : ℝ → ℂ) =
      fun x : ℝ => XiC (x : ℂ) := funext fourier_xiThetaSchwartzSource
  simpa only [he] using fourier_schwartz_jet_energy_le xiThetaSchwartzSource k n d t

end
end RHTower.Wu
