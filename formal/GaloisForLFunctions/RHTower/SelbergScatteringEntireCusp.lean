import GaloisForLFunctions.RHTower.SelbergScatteringEntireOperator
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMCuspPacketApproximation
import GaloisForLFunctions.HTGeometry.CfcResidualTransport

/-!
# Actual cusp packets in the entire-transform operator domain

The original modular unit cusp packets are transported first through the bounded
inverse energy coordinate and then through the reciprocal entire symbol by its
continuous divided difference. Normalizing their transformed covariance images
gives explicit unit vectors in the actual entire-operator domain. Their residual
at `cosh(8π tau)` tends to zero, before any Xi divisor is selected. At an arbitrary
complex target their residual tends to the exact distance from that real value.
This proves source occurrence on the real cusp ray; it does not identify the full
complex Xi scattering value with that real target.
-/

open Filter Topology
open GaloisForLFunctions.HTGeometry RHTower.D4BMModularCore

namespace RHTower.SelbergScatteringEntireTransform

theorem differentiableAt_entireCovarianceSymbol {x : ℝ} (hx : 0 < x) :
    DifferentiableAt ℝ entireCovarianceSymbol x := by
  have hf : Differentiable ℝ (fun y : ℝ => (casimirTransform y).re) :=
    Complex.reCLM.differentiable.comp
      ((differentiable_casimirTransform.restrictScalars ℝ).comp Complex.ofRealCLM.differentiable)
  have hi : DifferentiableAt ℝ (fun y : ℝ => y⁻¹ - 1) x :=
    (differentiableAt_id.inv (ne_of_gt hx)).sub_const 1
  have hden : (casimirTransform (x⁻¹ - 1 : ℝ)).re + 2 ≠ 0 := by
    have := (casimirTransform_real_range (x⁻¹ - 1)).2
    linarith
  have h := ((hf.differentiableAt.comp x hi).add_const 2).inv hden
  apply h.congr_of_eventuallyEq
  filter_upwards [lt_mem_nhds hx] with y hy
  simp only [entireCovarianceSymbol, if_pos hy]
  rfl

end RHTower.SelbergScatteringEntireTransform

namespace RHTower.SelbergScatteringEntireCusp
open RHTower.SelbergScatteringEntireTransform RHTower.SelbergScatteringEntireOperator
noncomputable section

local instance : IsometricContinuousFunctionalCalculus ℝ (Space →L[ℂ] Space) IsSelfAdjoint :=
  IsSelfAdjoint.instIsometricContinuousFunctionalCalculus

/-- Original native cusp energy, including the energy operator's shift by one. -/
def cuspEnergy (tau : ℝ) : ℝ := 5 / 4 + tau ^ (2 : ℕ)

theorem cuspEnergy_pos (tau : ℝ) : 0 < cuspEnergy tau := by
  dsimp [cuspEnergy]
  positivity

/-- Real transformed value produced by the original cusp frequency. -/
def cuspEntireValue (tau : ℝ) : ℝ := Real.cosh (8 * Real.pi * tau)

theorem cuspEntireValue_eq_transform (tau : ℝ) :
    (casimirTransform (cuspEnergy tau - 1 : ℝ)).re = cuspEntireValue tau := by
  have he : ((cuspEnergy tau - 1 : ℝ) : ℂ) = 1 / 4 + (tau : ℂ) ^ (2 : ℕ) := by
    dsimp [cuspEnergy]
    push_cast
    ring
  rw [he, casimirTransform_sq]
  simp only [cuspEntireValue, ← Complex.ofReal_mul, ← Complex.ofReal_ofNat,
    ← Complex.ofReal_cosh, Complex.ofReal_re]

theorem symbol_cusp_inverse (tau : ℝ) :
    (entireCovarianceSymbol (cuspEnergy tau)⁻¹)⁻¹ - 2 = cuspEntireValue tau := by
  rw [entireCovarianceSymbol_inverse _ (inv_pos.mpr (cuspEnergy_pos tau)), inv_inv,
    cuspEntireValue_eq_transform]

theorem nativeCovariance_apply_energy (u : energyOperator.domain) :
    nativeCovariance (energyOperator u) = (u : Space) :=
  closedDenseInverse_C_apply nativeCovariance nativeCovariance_injective u

/-- Exact residual identity in the bounded inverse coordinate of the original operator. -/
theorem nativeCovariance_residual (tau : ℝ) (u : energyOperator.domain) :
    nativeCovariance (u : Space) - (((cuspEnergy tau)⁻¹ : ℝ) : ℂ) • (u : Space) =
      -(((cuspEnergy tau)⁻¹ : ℝ) : ℂ) • nativeCovariance
        (energyOperator u - (cuspEnergy tau : ℂ) • (u : Space)) := by
  rw [map_sub, map_smul, nativeCovariance_apply_energy, smul_sub, neg_smul, neg_smul]
  have hc : (((cuspEnergy tau)⁻¹ : ℝ) : ℂ) •
      ((cuspEnergy tau : ℂ) • nativeCovariance (u : Space)) = nativeCovariance (u : Space) := by
    rw [smul_smul, ← Complex.ofReal_mul, inv_mul_cancel₀ (cuspEnergy_pos tau).ne',
      Complex.ofReal_one, one_smul]
  rw [hc]
  module

theorem nativeCovariance_cusp_residual_tendsto (tau : ℝ) :
    Tendsto (fun n : ℕ => ‖nativeCovariance (cuspApproximateVector tau n : Space) -
      (((cuspEnergy tau)⁻¹ : ℝ) : ℂ) • (cuspApproximateVector tau n : Space)‖)
      atTop (𝓝 0) := by
  have hA : Tendsto (fun n : ℕ => ‖energyOperator (cuspApproximateVector tau n) -
      (cuspEnergy tau : ℂ) • (cuspApproximateVector tau n : Space)‖) atTop (𝓝 0) := by
    simpa only [cuspEnergy, Complex.ofReal_add, Complex.ofReal_div, Complex.ofReal_ofNat,
      Complex.ofReal_pow] using cuspApproximateVector_residual_tendsto tau
  have hb : Tendsto (fun n : ℕ => ‖nativeCovariance
      (energyOperator (cuspApproximateVector tau n) -
        (cuspEnergy tau : ℂ) • (cuspApproximateVector tau n : Space))‖) atTop (𝓝 0) :=
    squeeze_zero (fun _ => norm_nonneg _) (fun _ => nativeCovariance.le_opNorm _)
      (by simpa using hA.const_mul ‖nativeCovariance‖)
  have h := hb.const_mul ‖-(((cuspEnergy tau)⁻¹ : ℝ) : ℂ)‖
  simpa only [← norm_smul, ← nativeCovariance_residual, mul_zero] using h

/-- The constructed cusp packets have vanishing residual for the bounded transformed covariance. -/
theorem entireCovariance_cusp_residual_tendsto (tau : ℝ) :
    Tendsto (fun n : ℕ => ‖entireCovariance (cuspApproximateVector tau n : Space) -
      (entireCovarianceSymbol (cuspEnergy tau)⁻¹ : ℂ) •
        (cuspApproximateVector tau n : Space)‖) atTop (𝓝 0) :=
  cfc_residual_tendsto_zero nativeCovariance nativeCovariance_selfAdjoint
    entireCovarianceSymbol (cuspEnergy tau)⁻¹ continuous_entireCovarianceSymbol.continuousOn
    (differentiableAt_entireCovarianceSymbol (inv_pos.mpr (cuspEnergy_pos tau)))
    (fun n => (cuspApproximateVector tau n : Space))
    (nativeCovariance_cusp_residual_tendsto tau)

/-- No original unit packet is erased by the transformed covariance. -/
theorem entireCovariance_cusp_norm_pos (tau : ℝ) (n : ℕ) :
    0 < ‖entireCovariance (cuspApproximateVector tau n : Space)‖ := by
  apply norm_pos_iff.mpr
  intro hz
  have hu : (cuspApproximateVector tau n : Space) = 0 :=
    entireCovariance_injective (by simpa only [map_zero] using hz)
  have hnorm := cuspApproximateVector_norm tau n
  rw [hu, norm_zero] at hnorm
  exact zero_ne_one hnorm

theorem entireCovariance_cusp_norm_tendsto (tau : ℝ) :
    Tendsto (fun n : ℕ => ‖entireCovariance (cuspApproximateVector tau n : Space)‖)
      atTop (𝓝 (entireCovarianceSymbol (cuspEnergy tau)⁻¹)) := by
  let c := entireCovarianceSymbol (cuspEnergy tau)⁻¹
  have hc : 0 < c := entireCovarianceSymbol_pos (inv_pos.mpr (cuspEnergy_pos tau))
  have hsize (n : ℕ) : ‖(c : ℂ) • (cuspApproximateVector tau n : Space)‖ = c := by
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc,
      cuspApproximateVector_norm, mul_one]
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [Metric.tendsto_nhds.mp (entireCovariance_cusp_residual_tendsto tau) ε hε]
    with n hn
  calc
    dist ‖entireCovariance (cuspApproximateVector tau n : Space)‖ c =
        |‖entireCovariance (cuspApproximateVector tau n : Space)‖ -
          ‖(c : ℂ) • (cuspApproximateVector tau n : Space)‖| := by rw [hsize, Real.dist_eq]
    _ ≤ ‖entireCovariance (cuspApproximateVector tau n : Space) -
        (c : ℂ) • (cuspApproximateVector tau n : Space)‖ := abs_norm_sub_norm_le _ _
    _ < ε := by simpa only [dist_zero_right, norm_norm] using hn

/-- Explicit unit packet in the actual entire-transform graph domain, before selecting any zero. -/
def entireCuspPacket (tau : ℝ) (n : ℕ) : entireOperator.domain :=
  ((‖entireCovariance (cuspApproximateVector tau n : Space)‖⁻¹ : ℝ) : ℂ) •
    ⟨entireCovariance (cuspApproximateVector tau n : Space),
      entireCovariance_mem_domain (cuspApproximateVector tau n : Space)⟩

theorem entireCuspPacket_norm (tau : ℝ) (n : ℕ) :
    ‖(entireCuspPacket tau n : Space)‖ = 1 := by
  rw [entireCuspPacket, Submodule.coe_smul, norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr (entireCovariance_cusp_norm_pos tau n)),
    inv_mul_cancel₀ (entireCovariance_cusp_norm_pos tau n).ne']

/-- Normalization retains the full residual numerator and its exact native norm denominator. -/
theorem entireCuspPacket_residual_norm (tau : ℝ) (n : ℕ) :
    ‖entireOperator (entireCuspPacket tau n) -
      (cuspEntireValue tau : ℂ) • (entireCuspPacket tau n : Space)‖ =
      ‖entireCovariance (cuspApproximateVector tau n : Space)‖⁻¹ *
        ‖(cuspApproximateVector tau n : Space) -
          ((cuspEntireValue tau + 2 : ℝ) : ℂ) •
            entireCovariance (cuspApproximateVector tau n : Space)‖ := by
  rw [entireCuspPacket, entireOperator.map_smul, Submodule.coe_smul,
    smul_comm (cuspEntireValue tau : ℂ), ← smul_sub, norm_smul,
    Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr (entireCovariance_cusp_norm_pos tau n)), entireOperator_apply_covariance]
  congr 2
  push_cast
  module

private theorem cusp_residual_numerator_tendsto (tau : ℝ) :
    Tendsto (fun n : ℕ => ‖(cuspApproximateVector tau n : Space) -
      ((cuspEntireValue tau + 2 : ℝ) : ℂ) •
        entireCovariance (cuspApproximateVector tau n : Space)‖) atTop (𝓝 0) := by
  let c := entireCovarianceSymbol (cuspEnergy tau)⁻¹
  have hc : 0 < c := entireCovarianceSymbol_pos (inv_pos.mpr (cuspEnergy_pos tau))
  have hvalue : cuspEntireValue tau + 2 = c⁻¹ := by
    have := symbol_cusp_inverse tau
    change c⁻¹ - 2 = cuspEntireValue tau at this
    linarith
  have hid (n : ℕ) : (cuspApproximateVector tau n : Space) -
      ((cuspEntireValue tau + 2 : ℝ) : ℂ) •
        entireCovariance (cuspApproximateVector tau n : Space) =
      -((c : ℂ)⁻¹) • (entireCovariance (cuspApproximateVector tau n : Space) -
        (c : ℂ) • (cuspApproximateVector tau n : Space)) := by
    rw [hvalue, Complex.ofReal_inv, smul_sub, neg_smul, neg_smul, smul_smul,
      inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr hc.ne'), one_smul]
    module
  simp_rw [hid, norm_smul]
  simpa only [mul_zero] using (entireCovariance_cusp_residual_tendsto tau).const_mul ‖-(c : ℂ)⁻¹‖

/-- Actual unit vectors realize every transformed real cusp frequency as approximate spectrum. -/
theorem entireCuspPacket_residual_tendsto (tau : ℝ) :
    Tendsto (fun n : ℕ => ‖entireOperator (entireCuspPacket tau n) -
      (cuspEntireValue tau : ℂ) • (entireCuspPacket tau n : Space)‖) atTop (𝓝 0) := by
  simp_rw [entireCuspPacket_residual_norm]
  have hc := entireCovarianceSymbol_pos (inv_pos.mpr (cuspEnergy_pos tau))
  have hi := (entireCovariance_cusp_norm_tendsto tau).inv₀ hc.ne'
  simpa only [mul_zero] using hi.mul (cusp_residual_numerator_tendsto tau)

/-- At any complex target the same unit packets have the exact limiting scalar-distance defect. -/
theorem entireCuspPacket_residual_at_tendsto (tau : ℝ) (mu : ℂ) :
    Tendsto (fun n : ℕ => ‖entireOperator (entireCuspPacket tau n) -
      mu • (entireCuspPacket tau n : Space)‖) atTop (𝓝 ‖(cuspEntireValue tau : ℂ) - mu‖) := by
  have hsize (n : ℕ) :
      ‖((cuspEntireValue tau : ℂ) - mu) • (entireCuspPacket tau n : Space)‖ =
        ‖(cuspEntireValue tau : ℂ) - mu‖ := by rw [norm_smul, entireCuspPacket_norm, mul_one]
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [Metric.tendsto_nhds.mp (entireCuspPacket_residual_tendsto tau) ε hε]
    with n hn
  have hdiff : (entireOperator (entireCuspPacket tau n) - mu • (entireCuspPacket tau n : Space)) -
      ((cuspEntireValue tau : ℂ) - mu) • (entireCuspPacket tau n : Space) =
        entireOperator (entireCuspPacket tau n) -
          (cuspEntireValue tau : ℂ) • (entireCuspPacket tau n : Space) := by module
  calc
    dist ‖entireOperator (entireCuspPacket tau n) - mu • (entireCuspPacket tau n : Space)‖
        ‖(cuspEntireValue tau : ℂ) - mu‖ =
        |‖entireOperator (entireCuspPacket tau n) - mu • (entireCuspPacket tau n : Space)‖ -
          ‖((cuspEntireValue tau : ℂ) - mu) • (entireCuspPacket tau n : Space)‖| := by
      rw [hsize, Real.dist_eq]
    _ ≤ ‖entireOperator (entireCuspPacket tau n) - mu • (entireCuspPacket tau n : Space) -
        ((cuspEntireValue tau : ℂ) - mu) • (entireCuspPacket tau n : Space)‖ :=
      abs_norm_sub_norm_le _ _
    _ < ε := by rw [hdiff]; simpa only [dist_zero_right, norm_norm] using hn

end
end RHTower.SelbergScatteringEntireCusp
