import GaloisForLFunctions.ThetaCuspSections.GibbsResponse
import GaloisForLFunctions.RHTower.ThetaCarrierHassePacket

/-!
# Relative entropy between arbitrary real Xi tilts

The Gibbs tangent gap is the relative entropy between the actual theta
probabilities, for all real parameters. The Hasse recovery kernel preserves
the whole two-parameter formula. Comparing the costs to two fixed targets
recovers the signed source tilt through the real Xi logarithmic derivative.
-/

open MeasureTheory InformationTheory ProbabilityTheory RHTower
open GaloisForLFunctions.HTGeometry

namespace ThetaCuspSections

noncomputable section

private theorem base_exp (a : ℝ) :
    Integrable (fun x : ℝ => Real.exp (a*x)) thetaBaseMeasure := by
  apply integrable_thetaBaseMeasure
  simpa using integrable_thetaTiltIntegrand_global a 0

theorem thetaTiltProb_probability (a : ℝ) : IsProbabilityMeasure (thetaTiltProb a) :=
  isProbabilityMeasure_tilted (base_exp a)

private theorem tilt_add (a b : ℝ) :
    (thetaTiltProb b).tilted (fun x : ℝ => (a-b)*x) = thetaTiltProb a := by
  rw [thetaTiltProb, thetaTiltProb, tilted_tilted (base_exp b)]
  apply tilted_congr
  filter_upwards with x
  simp only [Pi.add_apply]
  ring

theorem thetaTilts_ac (a b : ℝ) : thetaTiltProb a ≪ thetaTiltProb b := by
  rw [← tilt_add a b]
  exact tilted_absolutelyContinuous _ _

private theorem tilt_exp_integrable (a b : ℝ) :
    Integrable (fun x : ℝ => Real.exp ((a-b)*x)) (thetaTiltProb b) := by
  rw [thetaTiltProb, integrable_tilted_iff (base_exp b)]
  apply (base_exp a).congr
  filter_upwards with x
  rw [smul_eq_mul, ← Real.exp_add]
  congr 1
  ring

private theorem tilt_mgf (a b : ℝ) :
    (∫ x : ℝ, Real.exp ((a-b)*x) ∂thetaTiltProb b) = thetaTiltMoment a 0 / thetaTiltMoment b 0 := by
  rw [thetaTiltProb, integral_exp_tilted, integral_exp_mul_thetaBase]
  congr 1
  rw [← integral_exp_mul_thetaBase a]
  apply integral_congr_ae
  filter_upwards with x
  simp only [Pi.add_apply]
  congr 1
  ring

/-- The whole log likelihood ratio is affine, with normalizer fixed by centered Xi. -/
theorem thetaTilts_llr (a b : ℝ) :
    llr (thetaTiltProb a) (thetaTiltProb b) =ᵐ[thetaTiltProb b]
      fun x => (a-b)*x - (thetaTiltLogPartition a - thetaTiltLogPartition b) := by
  letI := thetaTiltProb_probability b
  have h := log_rnDeriv_tilted_left_self (tilt_exp_integrable a b)
  rw [tilt_add, tilt_mgf, Real.log_div (thetaTiltMoment_zero_pos_global a).ne'
    (thetaTiltMoment_zero_pos_global b).ne'] at h
  exact h

private theorem tilt_id_integrable (a : ℝ) : Integrable (fun x : ℝ => x) (thetaTiltProb a) := by
  rw [thetaTiltProb, integrable_tilted_iff (base_exp a)]
  apply integrable_thetaBaseMeasure
  simpa only [smul_eq_mul, pow_one, mul_comm (Real.exp _) _] using
    integrable_thetaTiltIntegrand_global a 1

private theorem tilt_mean (a : ℝ) : (∫ x : ℝ, x ∂thetaTiltProb a) = thetaTiltMean a := by
  rw [thetaTiltProb, integral_tilted, integral_thetaBaseMeasure, integral_exp_mul_thetaBase,
    thetaTiltMean, thetaTiltMoment, ← integral_div]
  apply integral_congr_ae
  filter_upwards with x
  simp only [smul_eq_mul, pow_one]
  ring

/-- Actual KL divergence is finite and equals the directed log-partition tangent gap. -/
theorem thetaTilts_klDiv (a b : ℝ) :
    klDiv (thetaTiltProb a) (thetaTiltProb b) = ENNReal.ofReal (tiltGap a b) := by
  letI := thetaTiltProb_probability a
  letI := thetaTiltProb_probability b
  have hac := thetaTilts_ac a b
  have hll := hac.ae_le (thetaTilts_llr a b)
  have hf := (tilt_id_integrable a).const_mul (a-b)
  have hc : Integrable (fun _ : ℝ => thetaTiltLogPartition a - thetaTiltLogPartition b)
      (thetaTiltProb a) := integrable_const _
  rw [klDiv_of_ac_of_integrable hac ((hf.sub hc).congr hll.symm), integral_congr_ae hll,
    integral_sub hf hc, integral_const_mul, tilt_mean]
  simp [tiltGap]
  <;> congr 1 <;> ring

/-- The decorated theta carrier has the same exact cost at every pair of real tilts. -/
theorem thetaCarrier_klDiv (a b : ℝ) :
    klDiv (thetaCarrierPacket a) (thetaCarrierPacket b) = ENNReal.ofReal (tiltGap a b) := by
  letI := thetaTiltProb_probability a
  letI := thetaTiltProb_probability b
  exact (klDiv_splitFormation (thetaTiltProb a) (thetaTiltProb b) thetaHasseProfile.kernel).trans
    (thetaTilts_klDiv a b)

private theorem cost (a b : ℝ) :
    (klDiv (thetaCarrierPacket a) (thetaCarrierPacket b)).toReal = tiltGap a b := by
  rw [thetaCarrier_klDiv, ENNReal.toReal_ofReal (tiltGap_nonneg _ _)]

/-- Comparing two target costs cancels the source entropy and reads the signed Xi response. -/
theorem thetaCarrier_cost_difference (a b c : ℝ) :
    (klDiv (thetaCarrierPacket a) (thetaCarrierPacket b)).toReal -
      (klDiv (thetaCarrierPacket a) (thetaCarrierPacket c)).toReal =
    thetaTiltLogPartition b - thetaTiltLogPartition c + (c-b)*xiRealLogDeriv a := by
  rw [cost, cost, tiltGap, tiltGap, thetaTiltMean_eq_xiRealLogDeriv]
  ring

/-- Two distinct reference packets determine the signed tilt from one difference of costs. -/
theorem thetaCarrier_cost_identifies (a a' b c : ℝ) :
    (klDiv (thetaCarrierPacket a) (thetaCarrierPacket b)).toReal -
        (klDiv (thetaCarrierPacket a) (thetaCarrierPacket c)).toReal =
      (klDiv (thetaCarrierPacket a') (thetaCarrierPacket b)).toReal -
        (klDiv (thetaCarrierPacket a') (thetaCarrierPacket c)).toReal ↔ b = c ∨ a = a' := by
  simp only [thetaCarrier_cost_difference, add_right_inj, mul_eq_mul_left_iff,
    sub_eq_zero, strictMono_xiRealLogDeriv.injective.eq_iff]
  aesop

#print axioms thetaTilts_klDiv
#print axioms thetaCarrier_klDiv
#print axioms thetaCarrier_cost_identifies

end

end ThetaCuspSections
