import GaloisForLFunctions.RHTower.SelbergOneSidedSecants
import GaloisForLFunctions.RHTower.SelbergMaassWeakCurvature

/-!
# Uniform actual cusp-current decay over every positive regulator

Original amplitude dominates both the regularized radius displacement and
its spectral forcing. Uniform source cusp decay and quantitative secants
therefore control the averaged and literal centered Stokes currents with
one height cutoff for all positive regulators. No derivative tail estimate
or regulator-dependent cutoff is supplied as a hypothesis.
-/

open Set Filter Topology MeasureTheory UpperHalfPlane
open scoped ContDiff
namespace GaloisForLFunctions.RHTower.SelbergMaassUniformCusp
open SelbergMaassMean SelbergMaassCongruenceTrace SelbergMaassTraceEnergy
  SelbergMaassTraceRegularized SelbergMaassRegularizedArea SelbergMaassRegularizedCusp
  SelbergMaassWeakCurvature SelbergScalarHorizontalAverage SelbergSquareRootRegularizationError
noncomputable section
variable (N : ℕ) {lam : ℝ}
  (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam)

/-- Every regularized radius lies between its regulator and regulator plus original amplitude. -/
theorem radius_bounds_amplitude (e : Ioi (0 : ℝ)) (z : ℂ) :
    (e : ℝ) ≤ radius N f e z ∧ radius N f e z ≤ e + amplitude N f z := by
  have hd := density_nonneg N f (ofComplex z)
  constructor
  · have h := Real.sqrt_le_sqrt (show (e : ℝ)^2 ≤ density N f (ofComplex z) + (e : ℝ)^2 by linarith)
    simpa only [Real.sqrt_sq e.2.le, radius] using h
  · simpa only [radius, amplitude, add_comm] using regularized_le_sqrt_add hd e.2.le

/-- The forcing lower bound uses the original amplitude, independently of every positive regulator. -/
theorem radius_laplacian_lower_amplitude (e : Ioi (0 : ℝ)) (z : ℍ) :
    -|lam| * amplitude N f z / z.im ^ 2 ≤ realLaplacian (radius N f e) z := by
  have hr : density N f z / radius N f e (z : ℂ) ≤ amplitude N f z := by
    simpa only [radius, amplitude, ofComplex_apply] using
      weighted_sqrt_le (density_nonneg N f z) e.2
  have hm : massWeight N f e (z : ℂ) ≤ amplitude N f z / z.im ^ 2 := by
    calc
      massWeight N f e (z : ℂ) = (density N f z / radius N f e (z : ℂ)) / z.im ^ 2 := by
        simp only [massWeight, ofComplex_apply, UpperHalfPlane.coe_im]
        ring
      _ ≤ _ := div_le_div_of_nonneg_right hr (sq_nonneg _)
  have hn : 0 ≤ massWeight N f e (z : ℂ) :=
    div_nonneg (density_nonneg N f _) (mul_nonneg (sq_nonneg _) (radius_pos N f e _).le)
  have hl : lam * massWeight N f e (z : ℂ) ≤ |lam| * (amplitude N f z / z.im ^ 2) :=
    (mul_le_mul_of_nonneg_right (le_abs_self lam) hn).trans
      (mul_le_mul_of_nonneg_left hm (abs_nonneg lam))
  have hid := curvatureWeight_eq N f e z.im_pos
  have hp := curvatureWeight_nonneg N f e z
  have h : -(|lam| * (amplitude N f z / z.im ^ 2)) ≤ realLaplacian (radius N f e) z := by linarith
  convert h using 1
  ring

/-- Original cusp decay makes the original amplitude uniformly small beyond an actual height. -/
theorem exists_amplitude_cusp_bound {delta : ℝ} (hd : 0 < delta) :
    ∃ A : ℝ, 0 < A ∧ ∀ z : ℍ, A ≤ z.im → amplitude N f z ≤ delta := by
  have hdec : IsZeroAtImInfty (fun z : ℍ => Real.sqrt (density N f z)) := by
    simpa only [IsZeroAtImInfty, ZeroAtFilter, Real.sqrt_zero] using (density_decay N f).sqrt
  rw [isZeroAtImInfty_iff] at hdec
  obtain ⟨A, hA⟩ := hdec delta hd
  refine ⟨max A 1, lt_of_lt_of_le zero_lt_one (le_max_right A 1), ?_⟩
  intro z hz
  have h := hA z ((le_max_left A 1).trans hz)
  simpa only [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), amplitude, ofComplex_apply] using h

private theorem constant_integrable (c : ℝ) : IntegrableOn (fun _ : ℝ => c) (Ioc (0 : ℝ) 1) :=
  integrableOn_const (hs := measure_Ioc_lt_top.ne)

private theorem integral_constant (c : ℝ) : (∫ _x : ℝ in Ioc (0 : ℝ) 1, c) = c := by
  rw [setIntegral_const, Real.volume_real_Ioc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  simp only [sub_zero, one_smul]

/-- Horizontal means inherit original amplitude bounds with no regulator-dependent cutoff. -/
theorem average_radius_bounds (e : Ioi (0 : ℝ)) {A delta y : ℝ}
    (hA : 0 < A) (hb : ∀ z : ℍ, A ≤ z.im → amplitude N f z ≤ delta) (hy : A ≤ y) :
    (e : ℝ) ≤ average (radius N f e) y ∧ average (radius N f e) y ≤ e + delta := by
  have hy0 := hA.trans_le hy
  have hi : IntegrableOn (fun x : ℝ => radius N f e (point x y)) (Ioc (0 : ℝ) 1) :=
    ((slice_continuous (radius_contDiffOn N f e).continuousOn hy0).integrableOn_Icc).mono_set
    (Ioc_subset_Icc_self : Ioc (0 : ℝ) 1 ⊆ Icc 0 1)
  have hp (x : ℝ) : 0 < (point x y).im := by simpa [point] using hy0
  have hbound (x : ℝ) := hb ⟨point x y, hp x⟩ (by simpa [UpperHalfPlane.im, point] using hy)
  have hlo := setIntegral_mono_on (constant_integrable (e : ℝ)) hi measurableSet_Ioc
    (fun x _ => (radius_bounds_amplitude N f e (point x y)).1)
  have hup := setIntegral_mono_on hi (constant_integrable ((e : ℝ) + delta)) measurableSet_Ioc
    (fun x _ => (radius_bounds_amplitude N f e (point x y)).2.trans (by linarith [hbound x]))
  rw [integral_constant] at hlo hup
  exact ⟨hlo, hup⟩

/-- Uniform original-amplitude control gives the same inverse-square forcing constant for every regulator. -/
theorem average_laplacian_uniform_lower (e : Ioi (0 : ℝ)) {A y : ℝ}
    (hA : 0 < A) (hb : ∀ z : ℍ, A ≤ z.im → amplitude N f z ≤ 1) (hy : A ≤ y) :
    -|lam| / y ^ 2 ≤ average (realLaplacian (radius N f e)) y := by
  have hy0 := hA.trans_le hy
  have hi : IntegrableOn (fun x : ℝ => realLaplacian (radius N f e) (point x y)) (Ioc (0 : ℝ) 1) :=
    ((slice_continuous (radius_laplacian_continuousOn N f e) hy0).integrableOn_Icc).mono_set
    (Ioc_subset_Icc_self : Ioc (0 : ℝ) 1 ⊆ Icc 0 1)
  have h := setIntegral_mono_on (constant_integrable (-|lam| / y ^ 2)) hi measurableSet_Ioc (fun x _ => ?_)
  · rw [integral_constant] at h
    exact h
  · have hp : 0 < (point x y).im := by simpa [point] using hy0
    let z : ℍ := ⟨point x y, hp⟩
    have hz : A ≤ z.im := by simpa [z, UpperHalfPlane.im, point] using hy
    have hm := mul_le_mul_of_nonneg_left (hb z hz) (abs_nonneg lam)
    have hl := radius_laplacian_lower_amplitude N f e z
    have hyz : z.im = y := by simp [z, UpperHalfPlane.im, point]
    rw [hyz] at hl
    apply le_trans _ hl
    apply div_le_div_of_nonneg_right _ (sq_nonneg _)
    linarith

/-- One source height controls both mean displacement and mean curvature for all positive regulators. -/
theorem exists_uniform_mean_bounds {delta : ℝ} (hd : 0 < delta) :
    ∃ A : ℝ, 0 < A ∧ ∀ e : Ioi (0 : ℝ), ∀ y : ℝ, A ≤ y →
      ((e : ℝ) ≤ average (radius N f e) y ∧ average (radius N f e) y ≤ e + delta) ∧
      -|lam| / y ^ 2 ≤ average (realLaplacian (radius N f e)) y := by
  obtain ⟨A, hA, hb⟩ := exists_amplitude_cusp_bound N f (lt_min hd zero_lt_one)
  refine ⟨A, hA, fun e y hy => ⟨?_, ?_⟩⟩
  · exact average_radius_bounds N f e hA (fun z hz => (hb z hz).trans (min_le_left _ _)) hy
  · exact average_laplacian_uniform_lower N f e hA (fun z hz => (hb z hz).trans (min_le_right _ _)) hy

/-- Original averaged currents decay uniformly over all positive regulators. -/
theorem average_current_uniform_decay {eps : ℝ} (heps : 0 < eps) :
    ∃ Y : ℝ, 0 < Y ∧ ∀ e : Ioi (0 : ℝ), ∀ y : ℝ, Y ≤ y →
      |average (dir Complex.I (radius N f e)) y| < eps := by
  obtain ⟨A, hA, hb⟩ := exists_uniform_mean_bounds N f (half_pos heps)
  have hdiv : Tendsto (fun y : ℝ => |lam| / (y - 1)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (by
      simpa only [sub_eq_add_neg, id_eq] using tendsto_atTop_add_const_right atTop (-1) tendsto_id)
  obtain ⟨B, hB⟩ := eventually_atTop.mp (hdiv.eventually_lt_const (half_pos heps))
  refine ⟨max (A + 1) B, lt_of_lt_of_le (by linarith : 0 < A + 1) (le_max_left _ _), ?_⟩
  intro e y hy
  have hAy : A + 1 ≤ y := (le_max_left _ _).trans hy
  have hbound := SelbergOneSidedSecants.abs_derivative_le_of_range hA (abs_nonneg lam)
    (fun s hs => average_radius_hasDerivAt N f e (hA.trans_le hs))
    (fun s hs => average_current_hasDerivAt N f e (hA.trans_le hs))
    (fun s hs => (hb e s hs).2) (fun s hs => (hb e s hs).1) hAy
  have hsmall := hB y ((le_max_right _ _).trans hy)
  linarith

/-- The literal centered Stokes top current decays uniformly over every positive regulator. -/
theorem top_current_uniform_decay {eps : ℝ} (heps : 0 < eps) :
    ∃ Y : ℝ, 0 < Y ∧ ∀ e : Ioi (0 : ℝ), ∀ y : ℝ, Y ≤ y →
      |∫ x in (-(1 / 2 : ℝ))..(1 / 2), regularizedCurrent N f e Complex.I x y| < eps := by
  obtain ⟨Y, hY, hb⟩ := average_current_uniform_decay N f heps
  refine ⟨Y, hY, fun e y hy => ?_⟩
  rw [top_eq_average_current N f e (hY.trans_le hy)]
  exact hb e y hy

end
end GaloisForLFunctions.RHTower.SelbergMaassUniformCusp
