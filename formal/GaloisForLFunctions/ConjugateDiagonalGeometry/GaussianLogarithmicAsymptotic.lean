import GaloisForLFunctions.ConjugateDiagonalGeometry.LogarithmicBoundaryNormalization
import GaloisForLFunctions.HTGeometry.DigammaHalfPlaneAsymptotic
import GaloisForLFunctions.RHTower.RiemannGaussian.GaussianXiLogDerivativeGrowth

/-!
# The logarithmic main term of the translated Gaussian zero sum

The quarter-line digamma density differs from the logarithm of height by a
bounded quantity. Gaussian convolution preserves its leading coefficient;
the absolutely convergent prime series contributes only a bounded remainder.
-/

open Filter Topology MeasureTheory Complex Set

noncomputable section

namespace GaloisForLFunctions.ConjugateDiagonalGeometry

open RiemannGaussian

/-- The real archimedean density has bounded error on the logarithmic scale,
uniformly at positive and negative heights. -/
theorem abs_riemannArchimedeanDensity_sub_log_le {t : ℝ} (ht : 4 ≤ |t|) :
    |riemannArchimedeanDensity t - Real.log |t|| ≤ 3 := by
  let z : ℂ := 1 / 4 + I * (t / 2)
  have ht0 : 0 < |t| := by linarith only [ht]
  have hzre : 0 < z.re := by norm_num [z]
  have him : |t| / 2 ≤ ‖z‖ := by
    simpa [z, abs_div] using Complex.abs_im_le_norm z
  have hz2 : 2 ≤ ‖z‖ := by linarith only [him, ht]
  have hz0 : 0 < ‖z‖ := by linarith only [hz2]
  have hnorm : ‖z‖ ≤ |t| := by
    calc ‖z‖ ≤ ‖(1 / 4 : ℂ)‖ + ‖I * (t / 2 : ℂ)‖ := norm_add_le _ _
      _ = 1 / 4 + |t| / 2 := by norm_num [norm_mul, norm_div]
      _ ≤ |t| := by linarith only [ht]
  have hloglo := Real.log_le_log (by positivity : 0 < |t| / 2) him
  rw [Real.log_div ht0.ne' (by norm_num)] at hloglo
  have hloghi := Real.log_le_log hz0 hnorm
  have hlog2 : Real.log 2 ≤ 1 := by
    simpa using Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
  have hgap : |Real.log ‖z‖ - Real.log |t|| ≤ 1 :=
    abs_le.mpr ⟨by linarith only [hloglo, hlog2], by linarith only [hloghi]⟩
  have hrem := (Complex.abs_re_le_norm (Complex.digamma z - Complex.log z)).trans
    (HTGeometry.norm_digamma_sub_log_le_of_re_pos hzre hz2)
  rw [Complex.sub_re, Complex.log_re] at hrem
  have hquot : 3 / ‖z‖ ≤ 3 / 2 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hz2
  calc |riemannArchimedeanDensity t - Real.log |t||
      = |((Complex.digamma z).re - Real.log ‖z‖) +
          (Real.log ‖z‖ - Real.log |t|)| := by
            congr 1
            change (Complex.digamma z).re - _ = _
            ring
    _ ≤ |(Complex.digamma z).re - Real.log ‖z‖| +
          |Real.log ‖z‖ - Real.log |t|| := abs_add_le _ _
    _ ≤ 3 := by linarith only [hrem, hquot, hgap]

/-- The archimedean density has logarithmic coefficient one at both ends. -/
theorem tendsto_riemannArchimedeanDensity_log_normalized :
    Tendsto (fun t => (riemannArchimedeanDensity t : ℂ) / (Real.log |t| : ℂ))
      (Filter.comap abs atTop) (𝓝 1) := by
  apply tendsto_log_normalized_of_epsilon_bound
  intro ε hε
  refine ⟨max 8 (Real.exp (3 / ε)), le_max_left _ _, ?_⟩
  intro t ht
  have ht8 : 8 ≤ |t| := (le_max_left _ _).trans ht
  have hlog : 3 / ε ≤ Real.log |t| := by
    have hh := Real.log_le_log (Real.exp_pos (3 / ε))
      ((le_max_right _ _).trans ht)
    simpa only [Real.log_exp] using hh
  have hh := mul_le_mul_of_nonneg_left hlog hε.le
  rw [mul_div_cancel₀ _ hε.ne'] at hh
  simpa only [mul_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] using
    (abs_riemannArchimedeanDensity_sub_log_le (by linarith only [ht8])).trans hh

/-- The archimedean density admits a global logarithmic majorant, including
the compact interval around the origin. -/
theorem exists_riemannArchimedeanDensity_log_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ,
      ‖(riemannArchimedeanDensity t : ℂ)‖ ≤ C * Real.log (2 + |t|) := by
  apply exists_global_logarithmic_bound_of_eventual
    (Complex.continuous_ofReal.comp continuous_riemannArchimedeanDensity)
    (K := 4) (by norm_num)
  refine ⟨8, le_rfl, ?_⟩
  intro t ht
  have hl : 1 ≤ Real.log |t| := by
    have he : Real.exp 1 ≤ |t| := by
      have he := Real.exp_one_lt_d9
      linarith only [he, ht]
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) he
  have hb := abs_riemannArchimedeanDensity_sub_log_le
    (by linarith only [ht] : 4 ≤ |t|)
  have ha : |riemannArchimedeanDensity t| ≤ 3 + Real.log |t| := by
    calc |riemannArchimedeanDensity t|
        = |(riemannArchimedeanDensity t - Real.log |t|) + Real.log |t|| := by ring_nf
      _ ≤ |riemannArchimedeanDensity t - Real.log |t|| + |Real.log |t|| := abs_add_le _ _
      _ ≤ 3 + Real.log |t| := by
        rw [abs_of_nonneg (by linarith only [hl] : 0 ≤ Real.log |t|)]
        exact add_le_add_right hb _
  rw [Complex.norm_real, Real.norm_eq_abs]
  linarith only [ha, hl]

end GaloisForLFunctions.ConjugateDiagonalGeometry

#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.tendsto_riemannArchimedeanDensity_log_normalized
