import GaloisForLFunctions.HTGeometry.HyperbolicLevyKhintchine
import GaloisForLFunctions.HTGeometry.JuliaDefectSpectralEquilibrium

/-!
# Lévy--Khintchine law for the Julia compression profile

This module proves the hyperbolic integral identity for the Julia compression square from the
unconditional `log cosh` Lévy--Khintchine formula.  No probabilistic representation is assumed.
-/

open MeasureTheory

namespace HTGeometry

noncomputable section

theorem neg_log_juliaCompressionSquareProfile (y : ℝ) :
    -Real.log (juliaCompressionSquareProfile y) =
      (1 / 2 : ℝ) * Real.log (Real.cosh (2 * y)) -
        2 * Real.log (Real.cosh (y / 2)) := by
  rw [juliaCompressionSquareProfile_eq_cosh_ratio]
  have hhalf : Real.cosh (y / 2) ≠ 0 := (Real.cosh_pos _).ne'
  have htwo : Real.sqrt (Real.cosh (2 * y)) ≠ 0 :=
    (Real.sqrt_pos.mpr (Real.cosh_pos _)).ne'
  rw [Real.log_div (pow_ne_zero 2 hhalf) htwo, Real.log_pow,
    Real.log_sqrt (Real.cosh_pos _).le]
  ring

/-- **Exact Julia Lévy--Khintchine identity (JSE2).** -/
theorem neg_log_juliaCompressionSquareProfile_eq_integral (y : ℝ) :
    -Real.log (juliaCompressionSquareProfile y) =
      ∫ t : ℝ in Set.Ioi 0,
        (1 - Real.cos (t * y)) * juliaCompressionLevyDensity t := by
  have h2 := log_cosh_eq_hyperbolicLevyIntegral
    (a := (2 : ℝ)) (by norm_num : (0 : ℝ) < 2) y
  have hh := log_cosh_eq_hyperbolicLevyIntegral
    (a := (1 / 2 : ℝ)) (by norm_num : (0 : ℝ) < 1 / 2) y
  have hi2 := integrableOn_hyperbolicLevyIntegrand
    (a := (2 : ℝ)) (y := y) (by norm_num : (0 : ℝ) < 2)
  have hih := integrableOn_hyperbolicLevyIntegrand
    (a := (1 / 2 : ℝ)) (y := y) (by norm_num : (0 : ℝ) < 1 / 2)
  rw [neg_log_juliaCompressionSquareProfile, h2, hh,
    ← MeasureTheory.integral_const_mul, ← MeasureTheory.integral_const_mul,
    ← MeasureTheory.integral_sub (hi2.const_mul (1 / 2)) (hih.const_mul 2)]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi ?_
  intro t ht
  have ht0 : t ≠ 0 := ht.ne'
  have hs4 : Real.sinh (Real.pi * t / 4) ≠ 0 :=
    (Real.sinh_pos_iff.mpr (by positivity)).ne'
  have hs1 : Real.sinh (Real.pi * t) ≠ 0 :=
    (Real.sinh_pos_iff.mpr (by positivity)).ne'
  unfold hyperbolicLevyIntegrand juliaCompressionLevyDensity
  field_simp [ht0, hs4, hs1]
  ring

end

end HTGeometry
