import GaloisForLFunctions.BiScaleUncertainty.HorizontalGammaDifference
import GaloisForLFunctions.RHTower.PaperEGCArithmeticRay
import GaloisForLFunctions.RHTower.XiShiftPrimeExposure
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Exact EGC source-ray baseline

On the original prescribed ray, the complete correction has a nonzero algebraic
Gamma floor. The exact arithmetic remainder has a smaller, exponential scale.
This classifies the ray asymptotic; it does not settle outer contour orientation.
-/

open Complex Filter
open scoped Topology

namespace RHTower

noncomputable section
open GaloisForLFunctions.BiScaleUncertainty

private theorem ray_abscissa_tendsto :
    Tendsto (fun m : ℕ => (m : ℝ) + 3 / 2) atTop atTop :=
  (tendsto_natCast_atTop_atTop (R := ℝ)).atTop_add tendsto_const_nhds

private theorem ray_scale_div_two_cpow_tendsto :
    Tendsto (fun m : ℕ => (((m : ℝ) + 1 : ℝ) : ℂ) /
      (2 : ℂ) ^ (((m : ℝ) + 3 / 2 : ℝ) : ℂ)) atTop (𝓝 0) := by
  have hreal : Tendsto (fun m : ℕ => ((m : ℝ) + 1) * (1 / 2 : ℝ) ^ m)
      atTop (𝓝 0) := by
    have h := (tendsto_self_mul_const_pow_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1)).add
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num : (1 / 2 : ℝ) < 1))
    simpa only [add_mul, one_mul, add_zero] using h
  have h := (Complex.continuous_ofReal.continuousAt.tendsto.comp hreal).div_const
    ((2 : ℂ) ^ (3 / 2 : ℂ))
  convert h using 1
  · funext m
    simp only [Function.comp_apply]
    push_cast
    rw [Complex.cpow_add _ _ (by norm_num : (2 : ℂ) ≠ 0), Complex.cpow_natCast]
    simp only [div_eq_mul_inv, mul_inv, inv_pow, one_mul]
    ring
  · simp

/-- The complete arithmetic row is negligible at the algebraic Gamma scale. -/
theorem tendsto_natScale_paperEGCRayArithmetic (eps x : ℝ) :
    Tendsto (fun m : ℕ => (((m : ℝ) + 1 : ℝ) : ℂ) *
      paperEGCRayArithmetic eps x ((m : ℝ) + 3 / 2)) atTop (𝓝 0) := by
  have h := ray_scale_div_two_cpow_tendsto.mul
    ((tendsto_paperEGCRayArithmetic_first_prime eps x).comp ray_abscissa_tendsto)
  convert h using 1
  · funext m
    have hn : (2 : ℂ) ^ (((m : ℝ) + 3 / 2 : ℝ) : ℂ) ≠ 0 := by
      simp
    dsimp only [Function.comp_apply]
    field_simp
  · simp

private theorem arch_ray_closed (m : ℕ) (u : ℝ) :
    logDeriv archFactor ((((m : ℝ) + 3 / 2 : ℝ) : ℂ) + (u : ℂ) * Complex.I) =
      1 / ((((m : ℝ) + 3 / 2 : ℝ) : ℂ) + (u : ℂ) * Complex.I) +
      1 / (((((m : ℝ) + 3 / 2 : ℝ) : ℂ) + (u : ℂ) * Complex.I) - 1) +
      (-((Real.log Real.pi : ℝ) : ℂ) / 2 +
        Complex.digamma (((((m : ℝ) + 3 / 2 : ℝ) : ℂ) + (u : ℂ) * Complex.I) / 2) / 2) := by
  have hs : 1 < ((((m : ℝ) + 3 / 2 : ℝ) : ℂ) + (u : ℂ) * Complex.I).re := by
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_self, add_zero]
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith
  have h0 : ((((m : ℝ) + 3 / 2 : ℝ) : ℂ) + (u : ℂ) * Complex.I) ≠ 0 := by
    intro h; rw [h] at hs; norm_num at hs
  have h1 : ((((m : ℝ) + 3 / 2 : ℝ) : ℂ) + (u : ℂ) * Complex.I) ≠ 1 := by
    intro h; rw [h] at hs; norm_num at hs
  rw [logDeriv_archFactor_closed (lt_trans zero_lt_one hs) h0 h1]
  simp only [GaloisForLFunctions.gammaRealLogConnection, neg_div]

/-- Exact first-order baseline, including both rational poles and the Gamma connection. -/
theorem tendsto_natScale_paperEGCRayArch (eps x : ℝ) :
    Tendsto (fun m : ℕ => (((m : ℝ) + 1 : ℝ) : ℂ) *
      paperEGCRayArch eps x ((m : ℝ) + 3 / 2)) atTop
      (𝓝 (-((eps : ℂ) ^ 2) / 2)) := by
  let ap : ℂ := 1 / 4 + ((x + eps : ℝ) : ℂ) * Complex.I / 2
  let am : ℂ := 1 / 4 + ((x - eps : ℝ) : ℂ) * Complex.I / 2
  have hap : 0 < ap.re := by norm_num [ap]
  have ham : 0 < am.re := by norm_num [am]
  have h0 := (tendsto_natScale_div_shift
    ((1 / 2 : ℂ) + ((x + eps : ℝ) : ℂ) * Complex.I)).sub
    (tendsto_natScale_div_shift ((1 / 2 : ℂ) + ((x - eps : ℝ) : ℂ) * Complex.I))
  have h1 := (tendsto_natScale_div_shift
    ((-1 / 2 : ℂ) + ((x + eps : ℝ) : ℂ) * Complex.I)).sub
    (tendsto_natScale_div_shift ((-1 / 2 : ℂ) + ((x - eps : ℝ) : ℂ) * Complex.I))
  have hg := (tendsto_natScale_digamma_pair ap am hap ham).div_const 2
  have h := ((h0.add h1).add hg).const_mul (Complex.I * (eps : ℂ) / 2)
  convert h using 1
  · funext m
    dsimp only [paperEGCRayArch, ap, am]
    rw [arch_ray_closed m (x + eps), arch_ray_closed m (x - eps)]
    push_cast
    ring_nf
  · dsimp only [ap, am]
    push_cast
    ring_nf
    simp
    ring

/-- Sharp decay of the complete correction along the original source ray. -/
theorem tendsto_paperEGCCompleteCorrection_source_ray_scaled
    (eps x : PaperEGCSmallParameter) :
    Tendsto (fun m : ℕ => (((m : ℝ) + 1 : ℝ) : ℂ) *
      paperEGCCompleteCorrection eps x (-((m : ℝ) + 1)))
      atTop (𝓝 (-(((eps : ℝ) : ℂ) ^ 2) / 2)) := by
  have h := (tendsto_natScale_paperEGCRayArch eps x).add
    (tendsto_natScale_paperEGCRayArithmetic eps x)
  simpa only [add_zero] using h.congr (fun m => by
    have hs : 1 < (m : ℝ) + 3 / 2 := by have := Nat.cast_nonneg (α := ℝ) m; linarith
    rw [← mul_add, ← paperEGCCompleteCorrection_source_ray_split eps x hs]
    congr 2
    ring)

/-- The original source-only diagonal extractor has the same nonzero Gamma floor. -/
theorem tendsto_paperEGCSourceExtractor_scaled (n : ℕ) (x : PaperEGCSmallParameter) :
    Tendsto (fun m : ℕ => (((m : ℝ) + 1 : ℝ) : ℂ) *
      centeredPrimeArchRealShiftDiagonalExtractor (paperEGCSourceRayPoint x m) n)
      atTop (𝓝 (-(((paperEGCScale n : ℝ) : ℂ) ^ 2) / 2)) := by
  simpa only [paperEGCCompleteCorrection_eq_sourceExtractor] using
    tendsto_paperEGCCompleteCorrection_source_ray_scaled (paperEGCScale n) x

/-- Faster than reciprocal-scale decay of the unrenormalized ray is impossible.
The exponentially decaying coefficient-faithful remainder is the positive replacement. -/
theorem not_tendsto_paperEGCSourceExtractor_scaled_zero (n : ℕ) (x : PaperEGCSmallParameter) :
    ¬ Tendsto (fun m : ℕ => (((m : ℝ) + 1 : ℝ) : ℂ) *
      centeredPrimeArchRealShiftDiagonalExtractor (paperEGCSourceRayPoint x m) n)
      atTop (𝓝 0) := by
  intro hz
  have heq := tendsto_nhds_unique (tendsto_paperEGCSourceExtractor_scaled n x) hz
  have hn : (((paperEGCScale n : ℝ) : ℂ)) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (paperEGCScale_pos n).ne'
  exact (div_ne_zero (neg_ne_zero.mpr (pow_ne_zero 2 hn)) (by norm_num)) heq

end
end RHTower
