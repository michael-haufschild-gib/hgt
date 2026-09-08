import GaloisForLFunctions.RHTower.SelbergMaassRegularizedArea
import GaloisForLFunctions.RHTower.SelbergScalarHorizontalAverage
import GaloisForLFunctions.RHTower.SelbergOneSidedCurvatureDecay

/-!
# Actual regularized cusp-current decay

The source radius converges uniformly to its positive regulator at the cusp.
Actual horizontal averaging identifies both derivatives and yields the lower
curvature bound with the absolute eigenvalue. An inverse-square corrected
derivative and secants prove the top current tends to zero. No derivative decay,
quantitative cusp rate, or top boundary condition is assumed.
-/

open Set Filter Topology MeasureTheory UpperHalfPlane
open scoped ContDiff
namespace GaloisForLFunctions.RHTower.SelbergMaassRegularizedCusp
open SelbergMaassMean SelbergMaassCongruenceTrace SelbergMaassTraceEnergy
  SelbergMaassTraceBoundary SelbergMaassTraceRegularized SelbergMaassRegularizedArea
  SelbergScalarHorizontalAverage
noncomputable section

variable (N : ℕ) {lam : ℝ}
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam)
    (e : Ioi (0 : ℝ))

/-- The regularized source inherits its literal unit horizontal period. -/
theorem radius_slice_periodic {y : ℝ} (hy : 0 < y) :
    Function.Periodic (fun x => radius N f e (point x y)) 1 := by
  intro x
  unfold radius
  exact congrArg (fun t : ℝ => Real.sqrt (t + (e : ℝ) ^ 2)) (density_slice_periodic N f hy x)

/-- Original uniform density decay forces the regularized radius to its regulator. -/
theorem radius_cusp_limit :
    Tendsto (fun z : ℍ => radius N f e (z : ℂ)) atImInfty (𝓝 (e : ℝ)) := by
  have hd : Tendsto (density N f) atImInfty (𝓝 0) := density_decay N f
  have h := (hd.add_const ((e : ℝ) ^ 2)).sqrt
  simpa only [zero_add, Real.sqrt_sq e.2.le, radius, ofComplex_apply] using h

/-- The actual unit horizontal radius average converges to the regulator. -/
theorem average_radius_limit :
    Tendsto (average (radius N f e)) atTop (𝓝 (e : ℝ)) := by
  have hc : IsZeroAtImInfty (fun z : ℍ => radius N f e (z : ℂ) - e) := by
    simpa only [IsZeroAtImInfty, ZeroAtFilter, sub_self] using (radius_cusp_limit N f e).sub_const (e : ℝ)
  rw [isZeroAtImInfty_iff] at hc
  refine Metric.tendsto_atTop.mpr ?_
  intro ε hε
  obtain ⟨A, hA⟩ := hc (ε / 2) (half_pos hε)
  refine ⟨max A 1, fun y hy => ?_⟩
  have hAy := (le_max_left A 1).trans hy
  have hypos : 0 < y := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) ((le_max_right A 1).trans hy)
  have hb : ∀ x ∈ Ioc (0 : ℝ) 1, ‖radius N f e (point x y) - e‖ ≤ ε / 2 := by
    intro x _
    have hp : 0 < (point x y).im := by simpa [point] using hypos
    exact hA ⟨point x y, hp⟩ (by simpa [UpperHalfPlane.im, point] using hAy)
  have hb' := norm_setIntegral_le_of_norm_le_const (μ := volume) measure_Ioc_lt_top hb
  have hi : IntegrableOn (fun x => radius N f e (point x y)) (Ioc (0 : ℝ) 1) :=
    ((SelbergScalarHorizontalAverage.slice_continuous (radius_contDiffOn N f e).continuousOn hypos).integrableOn_Icc).mono_set Ioc_subset_Icc_self
  rw [integral_sub hi (integrableOn_const (μ := volume) (s := Ioc (0 : ℝ) 1) (C := (e : ℝ)) (hs := measure_Ioc_lt_top.ne)),
    setIntegral_const, Real.volume_real_Ioc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hb'
  simp only [sub_zero, one_smul, mul_one] at hb'
  exact (show dist (average (radius N f e) y) (e : ℝ) ≤ ε / 2 by
    simpa only [dist_eq_norm, SelbergScalarHorizontalAverage.average] using hb').trans_lt (by linarith)

/-- The source curvature equation gives an inverse-square lower bound for every real eigenvalue. -/
theorem radius_laplacian_lower (z : ℍ) :
    -|lam| * radius N f e (z : ℂ) / z.im ^ 2 ≤ realLaplacian (radius N f e) (z : ℂ) := by
  have hr := radius_pos N f e (z : ℂ)
  have hs := radius_sq N f e (z : ℂ)
  simp only [ofComplex_apply] at hs
  have hid := radius_laplacian_identity N f e z
  have hrem := remainder_nonneg N f e z
  have hD := density_nonneg N f z
  have hy := sq_pos_of_pos z.im_pos
  apply (mul_le_mul_iff_right₀ hr).mp
  rw [hid]
  apply (mul_le_mul_iff_right₀ hy).mp
  field_simp
  have hm : lam * density N f z ≤ radius N f e (z : ℂ) ^ 2 * |lam| := by
    calc
      lam * density N f z ≤ |lam| * density N f z := mul_le_mul_of_nonneg_right (le_abs_self lam) hD
      _ ≤ |lam| * radius N f e (z : ℂ) ^ 2 := mul_le_mul_of_nonneg_left (by linarith [sq_nonneg (e : ℝ)]) (abs_nonneg lam)
      _ = radius N f e (z : ℂ) ^ 2 * |lam| := mul_comm _ _
  nlinarith only [hm, mul_nonneg hrem hy.le]

/-- The actual radius mean differentiates to its vertical-current mean. -/
theorem average_radius_hasDerivAt {y : ℝ} (hy : 0 < y) :
    HasDerivAt (average (radius N f e)) (average (dir Complex.I (radius N f e)) y) y :=
  average_hasDerivAt ((radius_contDiffOn N f e).of_le (by norm_num)) hy

/-- The actual mean current differentiates to the mean planar Laplacian. -/
theorem average_current_hasDerivAt {y : ℝ} (hy : 0 < y) :
    HasDerivAt (average (dir Complex.I (radius N f e)))
      (average (realLaplacian (radius N f e)) y) y := by
  have h := SelbergScalarHorizontalAverage.average_current_hasDerivAt (radius_contDiffOn N f e) hy
  rwa [average_vertical_second_eq_laplacian (radius_contDiffOn N f e) hy (radius_slice_periodic N f e hy)] at h

/-- Periodicity and source positivity give the mean inverse-square forcing bound. -/
theorem average_laplacian_lower {y : ℝ} (hy : 0 < y) :
    -|lam| * average (radius N f e) y / y ^ 2 ≤ average (realLaplacian (radius N f e)) y := by
  have hc := SelbergScalarHorizontalAverage.slice_continuous (radius_contDiffOn N f e).continuousOn hy
  have hi : IntegrableOn (fun x => radius N f e (point x y)) (Ioc (0 : ℝ) 1) :=
    hc.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hdi (v : ℂ) : IntegrableOn (fun x => dir v (dir v (radius N f e)) (point x y)) (Ioc (0 : ℝ) 1) :=
    (SelbergScalarHorizontalAverage.slice_continuous (dir_contDiffOn
      (dir_contDiffOn (radius_contDiffOn N f e) (m := 1) (by norm_num) v)
      (m := 0) (by norm_num) v).continuousOn hy).integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have h := setIntegral_mono_on ((hi.const_mul (-|lam|)).div_const (y ^ 2))
    ((hdi 1).add (hdi Complex.I)) measurableSet_Ioc (fun x _ => ?_)
  · simpa only [integral_div, integral_const_mul, SelbergScalarHorizontalAverage.average, realLaplacian, Pi.add_apply] using h
  · have hp : 0 < (point x y).im := by simpa [point] using hy
    simpa only [UpperHalfPlane.im, point, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
      Complex.ofReal_re, Complex.I_im, Complex.I_re, mul_one, mul_zero, zero_add, add_zero,
      realLaplacian, Pi.add_apply] using radius_laplacian_lower N f e ⟨point x y, hp⟩

/-- Actual cusp convergence and one-sided curvature force the mean current to zero. -/
theorem average_current_limit :
    Tendsto (average (dir Complex.I (radius N f e))) atTop (𝓝 0) := by
  have hlim := average_radius_limit N f e
  have hb : ∀ᶠ y in atTop, average (radius N f e) y ≤ (e : ℝ) + 1 :=
    (hlim.eventually_lt_const (by linarith : (e : ℝ) < e + 1)).mono (fun _ h => h.le)
  obtain ⟨A, hA⟩ := eventually_atTop.mp hb
  apply SelbergOneSidedCurvatureDecay.derivative_tendsto_zero
    (A := max A 1) (C := |lam| * ((e : ℝ) + 1)) (a2 := average (realLaplacian (radius N f e)))
    (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (le_max_right A 1))
    (mul_nonneg (abs_nonneg _) (le_of_lt (add_pos e.2 (by norm_num))))
    (fun y hy => average_radius_hasDerivAt N f e (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) ((le_max_right A 1).trans hy)))
    (fun y hy => average_current_hasDerivAt N f e (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) ((le_max_right A 1).trans hy)))
    _ hlim
  intro y hy
  have hypos : 0 < y := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) ((le_max_right A 1).trans hy)
  apply le_trans ?_ (average_laplacian_lower N f e hypos)
  apply div_le_div_of_nonneg_right ?_ (sq_nonneg y)
  have h := mul_le_mul_of_nonneg_left (hA y ((le_max_left A 1).trans hy)) (abs_nonneg lam)
  nlinarith

/-- Every actual regularized coordinate current has unit horizontal period. -/
theorem regularizedCurrent_slice_periodic (v : ℂ) {y : ℝ} (hy : 0 < y) :
    Function.Periodic (fun x => regularizedCurrent N f e v x y) 1 := by
  intro x
  change regularizedCurrent N f e v (x + 1) y = regularizedCurrent N f e v x y
  simp only [regularizedCurrent_eq N f e _ _ hy]
  exact congrArg₂ (fun a b : ℝ => a / (2 * b))
    (current_slice_periodic N f v hy x) (radius_slice_periodic N f e hy x)

/-- The centered Stokes boundary integral equals the unit current average. -/
theorem top_eq_average_current {y : ℝ} (hy : 0 < y) :
    (∫ x in (-(1 / 2 : ℝ))..(1 / 2), regularizedCurrent N f e Complex.I x y) =
      average (dir Complex.I (radius N f e)) y := by
  rw [average_eq_interval]
  have h := (regularizedCurrent_slice_periodic N f e Complex.I hy).intervalIntegral_add_eq (-(1 / 2)) 0
  norm_num only [show -(1 / 2 : ℝ) + 1 = 1 / 2 by ring, zero_add] at h
  exact h

/-- The literal centered top boundary current tends to zero at infinite height. -/
theorem top_current_limit :
    Tendsto (fun y => ∫ x in (-(1 / 2 : ℝ))..(1 / 2), regularizedCurrent N f e Complex.I x y)
      atTop (𝓝 0) := by
  apply (average_current_limit N f e).congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with y hy
  exact (top_eq_average_current N f e hy).symm

end
end GaloisForLFunctions.RHTower.SelbergMaassRegularizedCusp
