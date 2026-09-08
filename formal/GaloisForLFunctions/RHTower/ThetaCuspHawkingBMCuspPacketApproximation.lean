import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMCuspPacketNativeNorms
import Mathlib.Analysis.SpecificLimits.Basic

/-!
Explicit unit vectors with vanishing residual in the original modular operator domain.
-/

open MeasureTheory Set Filter Topology
open scoped ContDiff ComplexConjugate
namespace RHTower.D4BMModularCore
noncomputable section

private theorem cuspPacketVector_norm_pos (tau : ℝ) {L : ℝ} (hL : 0 < L) :
    0 < ‖((cuspPacketTest tau L hL).operatorVector : Space)‖ := by
  have hp := mul_pos hL cuspWindowMoment_zero_pos
  rw [← cuspPacketVector_norm_sq tau hL] at hp
  nlinarith [norm_nonneg ((cuspPacketTest tau L hL).operatorVector : Space)]

/-- Explicitly normalized vector in the original modular operator domain. -/
def cuspUnitPacket (tau L : ℝ) (hL : 0 < L) : energyOperator.domain :=
  ((‖((cuspPacketTest tau L hL).operatorVector : Space)‖⁻¹:ℝ):ℂ) •
    (cuspPacketTest tau L hL).operatorVector

/-- Normalization is exact in the original Hilbert norm. -/
theorem cuspUnitPacket_norm (tau : ℝ) {L : ℝ} (hL : 0 < L) :
    ‖(cuspUnitPacket tau L hL : Space)‖ = 1 := by
  rw [cuspUnitPacket,Submodule.coe_smul,norm_smul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr (cuspPacketVector_norm_pos tau hL)),
    inv_mul_cancel₀ (cuspPacketVector_norm_pos tau hL).ne']

/-- Exact normalized residual; its two positive derivative costs have orders two and four. -/
theorem cuspUnitPacket_residual_norm_sq (tau : ℝ) {L : ℝ} (hL : 0 < L) :
    ‖energyOperator (cuspUnitPacket tau L hL)-
      ((5/4:ℂ)+(tau:ℂ)^2) • (cuspUnitPacket tau L hL : Space)‖^2 =
      (4*tau^2*cuspWindowMoment 1/cuspWindowMoment 0)*L⁻¹^2+
        (cuspWindowMoment 2/cuspWindowMoment 0)*L⁻¹^4 := by
  rw [cuspUnitPacket,energyOperator.map_smul,Submodule.coe_smul,smul_comm
    ((5/4:ℂ)+(tau:ℂ)^2),← smul_sub,norm_smul,mul_pow,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr (cuspPacketVector_norm_pos tau hL)),inv_pow,
    cuspPacketVector_norm_sq tau hL,cuspPacketVector_residual_norm_sq tau hL]
  field_simp

/-- A concrete sequence of admitted cusp packets, with no approximate-spectrum assumption. -/
def cuspApproximateVector (tau : ℝ) (n : ℕ) : energyOperator.domain :=
  cuspUnitPacket tau (n+1) (by positivity)

theorem cuspApproximateVector_norm (tau : ℝ) (n : ℕ) :
    ‖(cuspApproximateVector tau n : Space)‖ = 1 :=
  cuspUnitPacket_norm tau (by positivity)

/-- The actual modular residual tends to zero along the constructed unit sequence. -/
theorem cuspApproximateVector_residual_tendsto (tau : ℝ) :
    Tendsto (fun n : ℕ => ‖energyOperator (cuspApproximateVector tau n)-
      ((5/4:ℂ)+(tau:ℂ)^2) • (cuspApproximateVector tau n : Space)‖) atTop (𝓝 0) := by
  have hi : Tendsto (fun n : ℕ => ((n:ℝ)+1)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)
  have hs : Tendsto (fun n : ℕ => ‖energyOperator (cuspApproximateVector tau n)-
      ((5/4:ℂ)+(tau:ℂ)^2) • (cuspApproximateVector tau n : Space)‖^2) atTop (𝓝 0) := by
    simp_rw [cuspApproximateVector,cuspUnitPacket_residual_norm_sq]
    simpa only [zero_pow (by norm_num : 2 ≠ 0),zero_pow (by norm_num : 4 ≠ 0),
      mul_zero,add_zero] using
      ((hi.pow 2).const_mul (4*tau^2*cuspWindowMoment 1/cuspWindowMoment 0)).add
        ((hi.pow 4).const_mul (cuspWindowMoment 2/cuspWindowMoment 0))
  simpa only [Real.sqrt_sq (norm_nonneg _),Real.sqrt_zero] using hs.sqrt

end
end RHTower.D4BMModularCore
