import GaloisForLFunctions.RHTower.ProlateRadialNormalization
import GaloisForLFunctions.RHTower.CCMRadialProlateProfileMeasure

/-!
# Exact bridge from endpoint-normalized prolate modes to the Dunster transform

The two radial constructions use apparently different amplitudes.  This file proves their exact
identity.  Consequently the comparison-equation unknown is literally the radial profile divided
by Dunster's Liouville--Green amplitude; no normalization constant or asymptotic replacement is
hidden in the passage.
-/

noncomputable section

namespace GaloisForLFunctions.RHTower

/-- The normal-form weight times Dunster's displayed amplitude is exactly the comparison
amplitude. -/
theorem nfWeight_mul_xiAmplitude_eq_lgAmplitude {s x : ℝ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hx : 1 < x) :
    nfWeight x * xiAmplitude s x = lgAmplitude s x := by
  have hd : (0 : ℝ) < x ^ 2 - 1 := by nlinarith
  have hn : (0 : ℝ) < x ^ 2 - s := by nlinarith
  have hphase := xiEndpointPhase_pos hs0 hs1 hx
  have hspeed := xiSpeed_pos hs1 hx
  have hnf : 0 < nfWeight x := by
    rw [nfWeight]
    positivity
  have hamp := xiAmplitude_pos hs0 hs1 hx
  have hlg := lgAmplitude_pos hs0 hs1 hx
  have hnf_sq : nfWeight x ^ 2 = x ^ 2 - 1 := by
    rw [nfWeight]
    exact Real.sq_sqrt hd.le
  have hamp_sq : xiAmplitude s x ^ 2 =
      xiEndpointPhase s x / Real.sqrt ((x ^ 2 - 1) * (x ^ 2 - s)) := by
    rw [xiAmplitude, div_pow]
    rw [Real.sq_sqrt hphase.le]
    rw [Real.sq_sqrt (Real.sqrt_pos.mpr (mul_pos hd hn)).le]
  have hlg_sq : lgAmplitude s x ^ 2 = xiEndpointPhase s x / xiSpeed s x := by
    rw [lgAmplitude, Real.sq_sqrt (lgWeight_pos hs0 hs1 hx).le, lgWeight]
  have hroot : xiSpeed s x * (x ^ 2 - 1) =
      Real.sqrt ((x ^ 2 - 1) * (x ^ 2 - s)) := by
    rw [xiSpeed_mul_sub_one hs1 hx, Real.sqrt_mul hd.le]
    ring
  apply (sq_eq_sq₀ (mul_nonneg hnf.le hamp.le) hlg.le).mp
  rw [mul_pow, hnf_sq, hamp_sq, hlg_sq]
  field_simp [hspeed.ne', (Real.sqrt_pos.mpr (mul_pos hd hn)).ne']
  nlinarith

/-- The pole-uniform comparison unknown is exactly `R / A_s`. -/
theorem comparisonSol_prolateNormalForm_eq_div_xiAmplitude
    {s x : ℝ} {R : ℝ → ℝ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hx : 1 < x) :
    comparisonSol (prolateNormalFormSol R) s x = R x / xiAmplitude s x := by
  rw [comparisonSol, prolateNormalFormSol]
  have hamp := xiAmplitude_pos hs0 hs1 hx
  have hnf : 0 < nfWeight x := by
    rw [nfWeight]
    have : (0 : ℝ) < x ^ 2 - 1 := by nlinarith
    positivity
  rw [← nfWeight_mul_xiAmplitude_eq_lgAmplitude hs0 hs1 hx]
  field_simp [hamp.ne', hnf.ne']

end GaloisForLFunctions.RHTower

end
