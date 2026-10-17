import GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolarCoherentSchur
import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-!
# Constructed differentiability and exact roughness of collar sources

Every compact continuous source has a compact C¹ collar average. Its derivative
is an explicit finite difference of the original source. The gauge derivative
is therefore an actual compact continuous source, with an admitted L¹ norm.
The original source's remainder has exactly the coherent collar chord energy.
-/

open MeasureTheory Set
open scoped CompactlySupported

namespace GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar
open RHTower.ArchimedeanAnomaly RHTower.ArchimedeanExactForm RHTower.WeilMarkovPole
noncomputable section
set_option autoImplicit false

/-- The actual collar source is a moving interval integral of the original source. -/
theorem collarSource_eq_annularAverage (f : C_c(ℝ, ℝ)) (a b : ℝ) :
    (collarSource f a b : ℝ → ℝ) =
      annularAverage f.toContinuousMap (-(Real.exp a + Real.exp b)) (Real.exp b) := by
  funext u
  change (∫ y in Icc (Real.exp a) (Real.exp a + Real.exp b), f (u-y)) / Real.exp b =
    (∫ x in u + (-(Real.exp a + Real.exp b))..
      u + (-(Real.exp a + Real.exp b)) + Real.exp b, f x) / Real.exp b
  rw [integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (le_add_of_nonneg_right (Real.exp_pos b).le),
    intervalIntegral.integral_comp_sub_left]
  congr 2
  ring

/-- No derivative of the original source occurs in the collar slope. -/
def collarSourceSlope (f : C_c(ℝ, ℝ)) (a b u : ℝ) : ℝ :=
  (f (u - Real.exp a) - f (u - Real.exp a - Real.exp b)) / Real.exp b

theorem hasDerivAt_collarSource (f : C_c(ℝ, ℝ)) (a b u : ℝ) :
    HasDerivAt (collarSource f a b : ℝ → ℝ) (collarSourceSlope f a b u) u := by
  rw [collarSource_eq_annularAverage]
  have h₁ : u + -(Real.exp a + Real.exp b) + Real.exp b = u - Real.exp a := by ring
  have h₂ : u + -(Real.exp a + Real.exp b) = u - Real.exp a - Real.exp b := by ring
  have hd := hasDerivAt_annularAverage f.toContinuousMap
    (-(Real.exp a + Real.exp b)) (Real.exp b) u
  change HasDerivAt _
    ((f (u + -(Real.exp a + Real.exp b) + Real.exp b) -
      f (u + -(Real.exp a + Real.exp b))) / Real.exp b) u at hd
  rw [h₁, h₂] at hd
  exact hd

theorem deriv_collarSource (f : C_c(ℝ, ℝ)) (a b : ℝ) :
    deriv (collarSource f a b : ℝ → ℝ) = collarSourceSlope f a b :=
  funext fun u => (hasDerivAt_collarSource f a b u).deriv

theorem continuous_collarSourceSlope (f : C_c(ℝ, ℝ)) (a b : ℝ) :
    Continuous (collarSourceSlope f a b) :=
  ((f.continuous.comp (continuous_id.sub continuous_const)).sub
    (f.continuous.comp ((continuous_id.sub continuous_const).sub continuous_const))).div_const _

/-- C¹ regularity is derived from the actual original source's continuity. -/
theorem contDiff_collarSource (f : C_c(ℝ, ℝ)) (a b : ℝ) :
    ContDiff ℝ 1 (collarSource f a b : ℝ → ℝ) := by
  apply contDiff_one_iff_deriv.mpr
  refine ⟨fun u => (hasDerivAt_collarSource f a b u).differentiableAt, ?_⟩
  rw [deriv_collarSource]
  exact continuous_collarSourceSlope f a b

theorem hasCompactSupport_collarSourceSlope (f : C_c(ℝ, ℝ)) (a b : ℝ) :
    HasCompactSupport (collarSourceSlope f a b) := by
  have hs : HasCompactSupport (fun u => f (u - Real.exp a) - f (u - Real.exp a - Real.exp b)) := by
    have ht := (hasCompactSupport_comp_add f.hasCompactSupport (-Real.exp a)).sub
        (hasCompactSupport_comp_add f.hasCompactSupport (-Real.exp a + -Real.exp b))
    change HasCompactSupport (fun u =>
      f (u + -Real.exp a) - f (u + (-Real.exp a + -Real.exp b))) at ht
    simpa only [sub_eq_add_neg, add_assoc] using ht
  have hm : HasCompactSupport (fun u =>
      (f (u - Real.exp a) - f (u - Real.exp a - Real.exp b)) * (Real.exp b)⁻¹) := hs.mul_right
  change HasCompactSupport (fun u =>
    (f (u - Real.exp a) - f (u - Real.exp a - Real.exp b)) / Real.exp b)
  simpa only [div_eq_mul_inv] using hm

/-- The collar's hyperbolic gauge derivative, constructed without differentiating f. -/
def collarGaugeSource (f : C_c(ℝ, ℝ)) (a b : ℝ) : C_c(ℝ, ℝ) :=
  ⟨⟨fun u => collarSourceSlope f a b u - collarSource f a b u / 2,
    (continuous_collarSourceSlope f a b).sub ((collarSource f a b).continuous.div_const 2)⟩, by
    have hg : HasCompactSupport (fun u => collarSource f a b u / 2) := by
      have hm : HasCompactSupport (fun u => collarSource f a b u * (2 : ℝ)⁻¹) :=
        (collarSource f a b).hasCompactSupport.mul_right
      simpa only [div_eq_mul_inv] using hm
    exact (hasCompactSupport_collarSourceSlope f a b).sub hg⟩

/-- Admitted L¹ gauge cost of the explicitly constructed collar source. -/
def collarGaugeL1 (f : C_c(ℝ, ℝ)) (a b : ℝ) : ℝ :=
  ∫ u, |collarGaugeSource f a b u|

theorem integrable_abs_collarGaugeSource (f : C_c(ℝ, ℝ)) (a b : ℝ) :
    Integrable (fun u => |collarGaugeSource f a b u|) :=
  ((collarGaugeSource f a b).continuous.integrable_of_hasCompactSupport
    (collarGaugeSource f a b).hasCompactSupport).abs

theorem collarGaugeL1_nonneg (f : C_c(ℝ, ℝ)) (a b : ℝ) : 0 ≤ collarGaugeL1 f a b :=
  integral_nonneg fun _ => abs_nonneg _

/-- The unsmoothed remainder is an actual compact continuous source. -/
def collarRemainderSource (f : C_c(ℝ, ℝ)) (a b : ℝ) : C_c(ℝ, ℝ) :=
  f - collarSource f a b

/-- Exact roughness energy, retaining the signed source–collar covariance. -/
theorem autocorr_collarRemainderSource_zero (f : C_c(ℝ, ℝ)) (a b : ℝ) :
    autocorr (collarRemainderSource f a b) 0 = collarChordEnergy f a b := by
  have hf := integrable_sq (g := (f : ℝ → ℝ)) f.continuous f.hasCompactSupport
  have hg := integrable_sq (g := (collarSource f a b : ℝ → ℝ))
    (collarSource f a b).continuous (collarSource f a b).hasCompactSupport
  have hc : Integrable (fun u => f u * collarSource f a b u) :=
    (f.continuous.mul (collarSource f a b).continuous).integrable_of_hasCompactSupport
      f.hasCompactSupport.mul_right
  have he : (fun u => collarRemainderSource f a b u ^ 2) =
      fun u => f u ^ 2 - 2 * (f u * collarSource f a b u) + collarSource f a b u ^ 2 := by
    funext u
    change (f u - collarSource f a b u) ^ 2 = _
    ring
  have hC : (∫ u, f u * collarSource f a b u) = correlationAverage f a b 0 := by
    simp_rw [mul_comm (f _) (collarSource f a b _)]
    exact integral_collarSource_mul_source f a b
  have hsub : Integrable (fun u => f u ^ 2 - 2 * (f u * collarSource f a b u)) :=
    hf.sub (hc.const_mul 2)
  rw [← integral_sq_eq_autocorr_zero (collarRemainderSource f a b), he,
    integral_add hsub hg,
    integral_sub hf (hc.const_mul 2), integral_const_mul, hC,
    integral_sq_eq_autocorr_zero, integral_sq_eq_autocorr_zero]
  dsimp [collarChordEnergy, collarEnergy]
  ring

end
end GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar
