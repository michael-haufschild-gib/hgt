import GaloisForLFunctions.ConjugateDiagonalGeometry.TheResidueUnitLogDerivativeHasItsBoundaryAsymptotics
import GaloisForLFunctions.ConjugateDiagonalGeometry.LogarithmicBoundaryNormalization
import GaloisForLFunctions.SquareRootThreshold.SechStripKernel

/-!
# The logarithmic main term of the sech boundary integral

The residue-unit logarithmic derivative is continuous on each fixed line
outside the quasi-Riemann strip. Its all-height asymptotics pass through the
shifted sech kernel by dominated convergence.
-/

open Complex Filter Topology MeasureTheory Set

noncomputable section

namespace GaloisForLFunctions.ConjugateDiagonalGeometry

open _root_.RHTower
open GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
open GaloisForLFunctions.SquareRootThreshold

private theorem residueUnit_boundary_ne_zero {σ : ℝ} (hσ1 : σ ≠ 1)
    (hz : ∀ t : ℝ, riemannZeta ((σ : ℂ) + (t : ℂ)*I) ≠ 0) (t : ℝ) :
    zetaResidueUnit ((σ : ℂ) + (t : ℂ)*I) ≠ 0 := by
  have hs : (σ : ℂ) + (t : ℂ)*I ≠ 1 := by
    intro he
    apply hσ1
    simpa using congrArg Complex.re he
  rw [(zetaResidueUnit_eventuallyEq hs).eq_of_nhds]
  exact mul_ne_zero (sub_ne_zero.mpr hs) (hz t)

private theorem continuous_boundary_logDeriv {σ : ℝ}
    (hz : ∀ t : ℝ, zetaResidueUnit ((σ : ℂ) + (t : ℂ)*I) ≠ 0) :
    Continuous (fun t : ℝ => logDeriv zetaResidueUnit ((σ : ℂ) + (t : ℂ)*I)) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  have han := analyticAt_zetaResidueUnit ((σ : ℂ) + (t : ℂ)*I)
  exact (han.deriv.continuousAt.div han.continuousAt (hz t)).comp (by fun_prop)

/-- The right boundary contains no zeros of the residue unit. -/
theorem residueUnit_right_boundary_ne_zero {σ : ℝ}
    (hσ : (7:ℝ)/8 < σ) (hσ1 : σ < 1) :
    ∀ t : ℝ, zetaResidueUnit ((σ : ℂ) + (t : ℂ)*I) ≠ 0 := by
  exact residueUnit_boundary_ne_zero hσ1.ne (fun t =>
    riemannZeta_ne_zero_of_seven_eighths_lt_re (by simpa using hσ))

/-- Reflection places the left boundary outside the zero strip at every height. -/
theorem residueUnit_left_boundary_ne_zero {σ : ℝ}
    (hσ0 : 0 < σ) (hσ : σ < (1:ℝ)/8) :
    ∀ t : ℝ, zetaResidueUnit ((σ : ℂ) + (t : ℂ)*I) ≠ 0 := by
  apply residueUnit_boundary_ne_zero (by linarith only [hσ])
  intro t
  exact riemannZeta_ne_zero_of_re_lt_one_eighth (by simpa using hσ0) (by simpa using hσ)

/-- The right logarithmic derivative is continuous through bounded heights. -/
theorem continuous_residueUnit_right_boundary {σ : ℝ}
    (hσ : (7:ℝ)/8 < σ) (hσ1 : σ < 1) :
    Continuous (fun t : ℝ => logDeriv zetaResidueUnit ((σ : ℂ) + (t : ℂ)*I)) :=
  continuous_boundary_logDeriv (residueUnit_right_boundary_ne_zero hσ hσ1)

/-- The reflected logarithmic derivative is continuous through bounded heights. -/
theorem continuous_residueUnit_left_boundary {σ : ℝ}
    (hσ0 : 0 < σ) (hσ : σ < (1:ℝ)/8) :
    Continuous (fun t : ℝ => logDeriv zetaResidueUnit ((σ : ℂ) + (t : ℂ)*I)) :=
  continuous_boundary_logDeriv (residueUnit_left_boundary_ne_zero hσ0 hσ)

theorem tendsto_residueUnit_right_boundary_log_normalized {σ : ℝ}
    (hσ : (7:ℝ)/8 < σ) (hσ1 : σ < 1) :
    Tendsto (fun t : ℝ => logDeriv zetaResidueUnit ((σ : ℂ) + (t : ℂ)*I) /
      (Real.log |t| : ℂ)) (Filter.comap abs atTop) (𝓝 0) := by
  apply tendsto_log_normalized_of_epsilon_bound
  intro ε hε
  simpa only [mul_zero,sub_zero] using
    exists_logDeriv_residueUnit_right_le_epsilon_log hσ hσ1 hε

theorem tendsto_residueUnit_left_boundary_log_normalized {σ : ℝ}
    (hσ0 : 0 < σ) (hσ : σ < (1:ℝ)/8) :
    Tendsto (fun t : ℝ => logDeriv zetaResidueUnit ((σ : ℂ) + (t : ℂ)*I) /
      (Real.log |t| : ℂ)) (Filter.comap abs atTop) (𝓝 (-1)) := by
  apply tendsto_log_normalized_of_epsilon_bound
  intro ε hε
  simpa only [mul_neg_one,sub_neg_eq_add] using
    exists_logDeriv_residueUnit_left_add_log_le_epsilon_log hσ0 hσ hε

theorem exists_residueUnit_right_boundary_log_bound {σ : ℝ}
    (hσ : (7:ℝ)/8 < σ) (hσ1 : σ < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ,
      ‖logDeriv zetaResidueUnit ((σ : ℂ) + (t : ℂ)*I)‖ ≤ C*Real.log (2+|t|) := by
  apply exists_global_logarithmic_bound_of_eventual
    (continuous_residueUnit_right_boundary hσ hσ1) (show (0:ℝ) ≤ 1 by norm_num)
  simpa only [one_mul] using
    exists_logDeriv_residueUnit_right_le_epsilon_log hσ hσ1 zero_lt_one

theorem exists_residueUnit_left_boundary_log_bound {σ : ℝ}
    (hσ0 : 0 < σ) (hσ : σ < (1:ℝ)/8) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ,
      ‖logDeriv zetaResidueUnit ((σ : ℂ) + (t : ℂ)*I)‖ ≤ C*Real.log (2+|t|) := by
  apply exists_global_logarithmic_bound_of_eventual
    (continuous_residueUnit_left_boundary hσ0 hσ) (show (0:ℝ) ≤ 2 by norm_num)
  obtain ⟨T,hT,hb⟩ := exists_logDeriv_residueUnit_left_add_log_le_epsilon_log
    hσ0 hσ zero_lt_one
  refine ⟨T,hT,fun t ht => ?_⟩
  have hl : 0 ≤ Real.log |t| := Real.log_nonneg (by linarith only [hT,ht])
  have hh := norm_sub_le
    (logDeriv zetaResidueUnit ((σ : ℂ) + (t : ℂ)*I) + (Real.log |t| : ℂ))
    (Real.log |t| : ℂ)
  rw [add_sub_cancel_right,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hl] at hh
  have he := hb t ht
  linarith only [hh,he]

private theorem continuous_sech_vertical {a b : ℝ} (ha : 0 < a) (hb : |b| < a) :
    Continuous (fun u : ℝ => sechStripWeight a 0 (1/2+(b : ℂ)+(u : ℂ)*I)) := by
  apply continuous_iff_continuousAt.mpr
  intro u
  exact ((analyticOnNhd_sechStripWeight ha 0 _ (by simpa using hb)).continuousAt).comp
    (by fun_prop)

/-- The right logarithmic derivative has zero normalized sech convolution. -/
theorem tendsto_sech_residueUnit_right_boundary {a b σ : ℝ}
    (ha : 0 < a) (hb : |b| < a) (hσ : (7:ℝ)/8 < σ) (hσ1 : σ < 1) :
    Tendsto (fun T : ℝ => (∫ u : ℝ,
      sechStripWeight a 0 (1/2+(b : ℂ)+(u : ℂ)*I) *
        logDeriv zetaResidueUnit ((σ : ℂ)+((T+u : ℝ) : ℂ)*I)) /
      (Real.log |T| : ℂ)) (Filter.comap abs atTop) (𝓝 0) := by
  obtain ⟨C,hC,hgrowth⟩ := exists_residueUnit_right_boundary_log_bound hσ hσ1
  simpa only [mul_zero] using tendsto_integral_mul_log_normalized
    (T := id) Filter.tendsto_comap (continuous_residueUnit_right_boundary hσ hσ1)
    (tendsto_residueUnit_right_boundary_log_normalized hσ hσ1) hC hgrowth
    (continuous_sech_vertical ha hb).aestronglyMeasurable
    (integrable_norm_sechStripWeight_vertical_weight ha hb)

/-- The left boundary contributes minus the full shifted-kernel mass. -/
theorem tendsto_sech_residueUnit_left_boundary {a b σ : ℝ}
    (ha : 0 < a) (hb : |b| < a) (hσ0 : 0 < σ) (hσ : σ < (1:ℝ)/8) :
    Tendsto (fun T : ℝ => (∫ u : ℝ,
      sechStripWeight a 0 (1/2+(b : ℂ)+(u : ℂ)*I) *
        logDeriv zetaResidueUnit ((σ : ℂ)+((T+u : ℝ) : ℂ)*I)) /
      (Real.log |T| : ℂ)) (Filter.comap abs atTop)
      (𝓝 (-(∫ u : ℝ, sechStripWeight a 0 (1/2+(b : ℂ)+(u : ℂ)*I)))) := by
  obtain ⟨C,hC,hgrowth⟩ := exists_residueUnit_left_boundary_log_bound hσ0 hσ
  simpa only [mul_neg_one] using tendsto_integral_mul_log_normalized
    (T := id) Filter.tendsto_comap (continuous_residueUnit_left_boundary hσ0 hσ)
    (tendsto_residueUnit_left_boundary_log_normalized hσ0 hσ) hC hgrowth
    (continuous_sech_vertical ha hb).aestronglyMeasurable
    (integrable_norm_sechStripWeight_vertical_weight ha hb)

/-- The shifted sech kernel is Bochner integrable on every line in its strip. -/
theorem integrable_sech_vertical {a b : ℝ} (ha : 0 < a) (hb : |b| < a) :
    Integrable (fun u : ℝ => sechStripWeight a 0 (1/2+(b : ℂ)+(u : ℂ)*I)) := by
  apply (integrable_norm_sechStripWeight_vertical_weight ha hb).mono'
    (continuous_sech_vertical ha hb).aestronglyMeasurable
  apply Eventually.of_forall
  intro u
  have hu : 0 ≤ |u| / Real.log 2 := div_nonneg (abs_nonneg u)
    (Real.log_nonneg (by norm_num))
  nlinarith only [norm_nonneg (sechStripWeight a 0 (1/2+(b : ℂ)+(u : ℂ)*I)),
    mul_nonneg (norm_nonneg (sechStripWeight a 0 (1/2+(b : ℂ)+(u : ℂ)*I))) hu]

/-- The difference of the two full vertical boundary integrals, without the
factor `i` contributed by the contour parametrization. -/
def sechResidueUnitBoundary (a b T : ℝ) : ℂ :=
  (∫ u : ℝ, sechStripWeight a 0 (1/2+(b : ℂ)+(u : ℂ)*I) *
    logDeriv zetaResidueUnit (((1/2+b : ℝ) : ℂ)+((T+u : ℝ) : ℂ)*I)) -
  (∫ u : ℝ, sechStripWeight a 0 (1/2+((-b : ℝ) : ℂ)+(u : ℂ)*I) *
    logDeriv zetaResidueUnit (((1/2-b : ℝ) : ℂ)+((T+u : ℝ) : ℂ)*I))

/-- The full vertical sech boundary term has main coefficient `a/π`, uniformly
at both signs of the height. -/
theorem tendsto_sechResidueUnitBoundary_log_normalized {a b : ℝ}
    (hb : (3:ℝ)/8 < b) (hbhalf : b < 1/2) (hba : b < a) :
    Tendsto (fun T : ℝ => (sechResidueUnitBoundary a b T).re /
      (2*Real.pi*Real.log |T|)) (Filter.comap abs atTop) (𝓝 (a/Real.pi)) := by
  have hb0 : 0 < b := by linarith only [hb]
  have ha : 0 < a := hb0.trans hba
  have hab : |b| < a := by rwa [abs_of_pos hb0]
  have han : |-b| < a := by simpa only [abs_neg] using hab
  have hr := tendsto_sech_residueUnit_right_boundary ha hab
    (σ := 1/2+b) (by linarith only [hb]) (by linarith only [hbhalf])
  have hl := tendsto_sech_residueUnit_left_boundary ha han
    (σ := 1/2-b) (by linarith only [hbhalf]) (by linarith only [hb])
  have hlim := hr.sub hl
  simp only [zero_sub,neg_neg,← sub_div] at hlim
  change Tendsto (fun T : ℝ => sechResidueUnitBoundary a b T / (Real.log |T| : ℂ))
    (Filter.comap abs atTop)
    (𝓝 (∫ u : ℝ, sechStripWeight a 0 (1/2+((-b : ℝ) : ℂ)+(u : ℂ)*I))) at hlim
  have hre := Complex.continuous_re.continuousAt.tendsto.comp hlim
  have hint := integrable_sech_vertical ha han
  have hmass : (∫ u : ℝ, sechStripWeight a 0
      (1/2+((-b : ℝ) : ℂ)+(u : ℂ)*I)).re = 2*a := by
    have hh := integral_re hint
    simp only [RCLike.re_eq_complex_re] at hh
    rw [← hh]
    exact integral_re_sechStripWeight_vertical ha han
  rw [hmass] at hre
  have hdiv := hre.div_const (2*Real.pi)
  convert hdiv using 1
  · funext T
    dsimp only [Function.comp_def]
    rw [Complex.div_ofReal_re,div_div,mul_comm (Real.log |T|) (2*Real.pi)]
  · congr 1
    field_simp [Real.pi_ne_zero]


end GaloisForLFunctions.ConjugateDiagonalGeometry

#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.tendsto_sech_residueUnit_right_boundary
#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.tendsto_sech_residueUnit_left_boundary
#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.tendsto_sechResidueUnitBoundary_log_normalized
