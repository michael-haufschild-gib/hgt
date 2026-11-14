import GaloisForLFunctions.GaloisTheoryOfZeros.Probability.CoxResidualClassification
import GaloisForLFunctions.RHTower.HardyZThetaTrace

/-!
# Gamma–Cox detection for completed zeta and Hardy Z

Complex modulus reduces completed-zeta zeros to a real residual. On the critical
line, real Xi and Hardy Z have the same limiting classification despite their
different finite-concentration scales. Counts concern prescribed candidates only.
-/

open Filter Topology
open scoped Classical
open RHTower
namespace GaloisForLFunctions.GaloisTheoryOfZeros
open GammaCox
noncomputable section

/-- Completed-zeta zeros are detected throughout the complex plane. -/
theorem cox_xi_zero (s : ℂ) :
    Tendsto (fun K => detection K ‖xi s‖) atTop (𝓝 (if xi s = 0 then 1 else 0)) := by
  simpa only [norm_eq_zero] using tendsto_detection ‖xi s‖

/-- Functional-equation reflection preserves finite detection probabilities exactly. -/
theorem cox_xi_reflection (K : ℝ) (s : ℂ) :
    detection K ‖xi (1 - s)‖ = detection K ‖xi s‖ := by rw [xi_one_sub]

/-- Real Xi detection has exactly Hardy Z's zero indicator as its limit. -/
theorem cox_Xi_hardyZ (t : ℝ) :
    Tendsto (fun K => detection K (Xi t)) atTop (𝓝 (if hardyZ t = 0 then 1 else 0)) := by
  simpa only [Xi_eq_zero_iff_hardyZ] using tendsto_detection (Xi t)

/-- Xi and Hardy Z may differ at finite concentration, but their detection gap vanishes. -/
theorem cox_Xi_hardyZ_gap (t : ℝ) :
    Tendsto (fun K => detection K (Xi t) - detection K (hardyZ t)) atTop (𝓝 0) := by
  simpa only [sub_self] using (cox_Xi_hardyZ t).sub (tendsto_detection (hardyZ t))

/-- A finite list of complex candidates is classified simultaneously. -/
theorem cox_xi_family {ι : Type*} [Fintype ι] (s : ι → ℂ) :
    Tendsto (fun K => (binaryLaw K (fun i => ‖xi (s i)‖)).real
      {b | b ≠ fun i => decide (xi (s i) = 0)}) atTop (𝓝 0) := by
  exact tendsto_classification_error (fun i => ‖xi (s i)‖)
    (fun i => xi (s i) = 0) fun i => by
    simp only [norm_eq_zero]

/-- Critical-line Xi tests consistently recover the Hardy-Z zero pattern. -/
theorem cox_critical_family {ι : Type*} [Fintype ι] (t : ι → ℝ) :
    Tendsto (fun K => (binaryLaw K (fun i => Xi (t i))).real
      {b | b ≠ fun i => decide (hardyZ (t i) = 0)}) atTop (𝓝 0) := by
  exact tendsto_classification_error (fun i => Xi (t i))
    (fun i => hardyZ (t i) = 0) fun i => by
    simp only [Xi_eq_zero_iff_hardyZ]

end
end GaloisForLFunctions.GaloisTheoryOfZeros

#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.cox_xi_zero
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.cox_xi_reflection
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.cox_Xi_hardyZ
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.cox_Xi_hardyZ_gap
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.cox_xi_family
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.cox_critical_family
