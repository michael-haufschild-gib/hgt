import GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolarCorrelationBudget
import GaloisForLFunctions.BiScaleUncertainty.FiniteSourceEnergyScalarization

/-!
# Signed scalar collar compensation for the actual prime–polar packet

Every real multiple of the constructed collar is an admitted compact source.
Its exact signed covariance determines the remainder energy; Chebyshev control
of its packet gives an explicit quadratic family of source-only upper bounds.
-/

open MeasureTheory Set
open scoped BigOperators CompactlySupported

namespace GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar
open RHTower.ArchimedeanAnomaly RHTower.ArchimedeanExactForm RHTower.WeilMarkovPole
open ChebyshevGauge
noncomputable section
set_option autoImplicit false

theorem signedSource_smul_apply (f : C_c(ℝ, ℝ)) (t : ℝ) (N : ℕ) (u : ℝ) :
    signedSource (t • f) N u = t * signedSource f N u := by
  change (∑ n ∈ Finset.Icc 1 (N+2), primeWeight n * (t • f) (u + Real.log n)) -
      (∫ x in Icc 0 (cutoff N), polarDensity x * (t • f) (u+x)) =
    t * ((∑ n ∈ Finset.Icc 1 (N+2), primeWeight n * f (u + Real.log n)) -
      ∫ x in Icc 0 (cutoff N), polarDensity x * f (u+x))
  simp only [CompactlySupportedContinuousMap.smul_apply, smul_eq_mul,
    show ∀ x y : ℝ, x * (t*y) = t * (x*y) from fun x y => by ring,
    ← Finset.mul_sum, integral_const_mul]
  ring

theorem packetEnergy_smul (f : C_c(ℝ, ℝ)) (t : ℝ) (N : ℕ) :
    packetEnergy (t • f) N = t ^ 2 * packetEnergy f N := by
  have he : (signedSource (t • f) N : ℝ → ℝ) = fun u => t * signedSource f N u :=
    funext (signedSource_smul_apply f t N)
  unfold packetEnergy
  rw [he, autocorr_source_const_mul]

/-- Exact remainder energy retains the sign of the collar covariance. -/
theorem autocorr_sub_smul_collar_zero (f : C_c(ℝ, ℝ)) (a b t : ℝ) :
    autocorr ((f - t • collarSource f a b : C_c(ℝ, ℝ)) : ℝ → ℝ) 0 =
      autocorr f 0 - 2*t*correlationAverage f a b 0 + t^2*collarEnergy f a b := by
  let g := collarSource f a b
  have hf : Integrable (fun u => f u ^ 2) := integrable_sq f.continuous f.hasCompactSupport
  have hg : Integrable (fun u => g u ^ 2) := integrable_sq g.continuous g.hasCompactSupport
  have hm : Integrable (fun u => g u * f u) :=
    (g.continuous.mul f.continuous).integrable_of_hasCompactSupport g.hasCompactSupport.mul_right
  have htm : Integrable (fun u => (2*t)*(g u*f u)) := hm.const_mul (2*t)
  have hsub : Integrable (fun u => f u^2-(2*t)*(g u*f u)) := hf.sub htm
  have htg : Integrable (fun u => t^2*g u^2) := hg.const_mul (t^2)
  have he : (fun u => (f - t • g) u ^ 2) = fun u =>
      f u ^ 2 - (2*t)*(g u*f u) + t^2*g u^2 := by
    funext u
    simp only [CompactlySupportedContinuousMap.sub_apply,
      CompactlySupportedContinuousMap.smul_apply, smul_eq_mul]
    ring
  rw [← integral_sq_eq_autocorr_zero]
  change (∫ u, (f-t • g) u ^ 2) = _
  rw [he, integral_add hsub htg,
    integral_sub hf htm, integral_const_mul, integral_const_mul,
    integral_sq_eq_autocorr_zero, integral_sq_eq_autocorr_zero]
  change autocorr f 0 - 2*t*(∫ u, collarSource f a b u*f u) + t^2*collarEnergy f a b = _
  rw [integral_collarSource_mul_source]

theorem collar_covariance_sq_le (f : C_c(ℝ, ℝ)) (a b : ℝ) :
    correlationAverage f a b 0 ^ 2 ≤ collarEnergy f a b * autocorr f 0 := by
  have hs := HTGeometry.sq_integral_mul_le
    (f := (collarSource f a b : ℝ → ℝ)) (g := (f : ℝ → ℝ))
    (collarSource f a b).continuous.aestronglyMeasurable f.continuous.aestronglyMeasurable
    (integrable_sq (collarSource f a b).continuous (collarSource f a b).hasCompactSupport)
    (integrable_sq f.continuous f.hasCompactSupport)
  rwa [integral_collarSource_mul_source, integral_sq_eq_autocorr_zero,
    integral_sq_eq_autocorr_zero] at hs

/-- Correlation-based bound on the packet of the collar itself. -/
def collarPacketBound (f : C_c(ℝ, ℝ)) (a b : ℝ) (N : ℕ) : ℝ :=
  3 * (10+normalizedLogError (cutoff N)^2) * collarEnergy f a b +
    3 * collarGaugeBudget f a b * (∫ x in Icc 0 (cutoff N), normalizedLogError x ^ 2)

theorem collar_packetEnergy_le_correlation (f : C_c(ℝ, ℝ)) (a b : ℝ) (N : ℕ) :
    packetEnergy (collarSource f a b) N ≤ collarPacketBound f a b N := by
  apply (collar_packetEnergy_le_gauge f a b N).trans
  apply add_le_add le_rfl
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (collarGaugeL1_sq_le_budget f a b) (by norm_num))
    (integral_nonneg fun _ => sq_nonneg _)

theorem collarPacketBound_nonneg (f : C_c(ℝ, ℝ)) (a b : ℝ) (N : ℕ) :
    0 ≤ collarPacketBound f a b N :=
  (packetEnergy_nonneg _ _).trans (collar_packetEnergy_le_correlation f a b N)

theorem thirty_mul_collarEnergy_le_bound (f : C_c(ℝ, ℝ)) (a b : ℝ) (N : ℕ) :
    30 * collarEnergy f a b ≤ collarPacketBound f a b N := by
  have hb := collarEnergy_nonneg f a b
  have hs := mul_nonneg (sq_nonneg (normalizedLogError (cutoff N))) hb
  have hi : 0 ≤ 3 * collarGaugeBudget f a b *
      (∫ x in Icc 0 (cutoff N), normalizedLogError x ^ 2) :=
    mul_nonneg (mul_nonneg (by norm_num) (collarGaugeBudget_nonneg f a b))
      (integral_nonneg fun _ => sq_nonneg _)
  unfold collarPacketBound
  nlinarith only [hs, hi]

/-- The signed scalar trial family, before any coefficient is optimized. -/
def collarTrialBound (f : C_c(ℝ, ℝ)) (a b c : ℝ) (N : ℕ) (t : ℝ) : ℝ :=
  (1+Real.exp c)*t^2*collarPacketBound f a b N +
    (1+1/Real.exp c)*mass N^2 *
      (autocorr f 0 - 2*t*correlationAverage f a b 0 + t^2*collarEnergy f a b)

/-- Every signed coefficient yields an unconditional actual-source certificate. -/
theorem packetEnergy_le_collarTrialBound (f : C_c(ℝ, ℝ)) (a b c t : ℝ) (N : ℕ) :
    packetEnergy f N ≤ collarTrialBound f a b c N t := by
  have hs := packetEnergy_le_weighted_split f (t • collarSource f a b) N c
  rw [packetEnergy_smul] at hs
  have hr := packetEnergy_le_mass_sq (f-t • collarSource f a b) N
  rw [autocorr_sub_smul_collar_zero] at hr
  have hu := mul_le_mul_of_nonneg_left (collar_packetEnergy_le_correlation f a b N)
    (sq_nonneg t)
  apply hs.trans
  unfold collarTrialBound
  calc
    _ ≤ (1+Real.exp c)*(t^2*collarPacketBound f a b N) +
        (1+1/Real.exp c)*(mass N^2 *
          (autocorr f 0 - 2*t*correlationAverage f a b 0 + t^2*collarEnergy f a b)) :=
      add_le_add (mul_le_mul_of_nonneg_left hu (by positivity))
        (mul_le_mul_of_nonneg_left hr (by positivity))
    _ = _ := by ring

end
end GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar
