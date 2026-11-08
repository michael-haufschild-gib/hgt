import GaloisForLFunctions.ExactEventTheory.IntegrableDefectsHaveDecayingBoundary
import GaloisForLFunctions.ArithmeticPositiveDuality.ApproximateFunctionalEquationNearCounting

/-!
# Variable-width tent pairings of a defective functional equation

Pairing the Laplace identity with a tent of width `h` gives an exact cosine series
and the integral of the boundary defect. Scaling the Poisson kernel reduces the
atomic side to the unit-tent approximate identity. The inverse-square moment
dominates both sides before passing to the boundary.
-/

open Complex MeasureTheory Filter Topology Set Function
open GaloisForLFunctions.ArithmeticPositiveDuality RHTower.HamburgerStability

noncomputable section
namespace GaloisForLFunctions.ExactEventTheory

/-- The Poisson-side kernel for a tent of width `h` centred at `h*n`. -/
def tentSeriesKernel (h n ε s u : ℝ) : ℝ := shiftedTentSeriesKernel n ε s (u / h)

/-- The dual cosine kernel for the same tent. -/
def tentDualKernel (h n ε s u : ℝ) : ℝ := h * shiftedTentDualKernel n ε s (h * u)

/-- The nonnegative Fourier weight of a tent, without its width factor. -/
def tentFourierWeight (h u : ℝ) : ℝ :=
  (Real.sin (Real.pi * (h * u)) / (Real.pi * (h * u))) ^ 2

/-- The pole term after the radial and height variables are scaled together. -/
def tentPolarKernel (h β n ε s : ℝ) : ℝ :=
  shiftedTentPolarKernel (β : ℂ) n ε s + (h - 1) * β * (1 - |s|)

/-- The defect term on the vertical segment above the tent. -/
def tentDefectKernel (g : ℝ → ℂ) (h n ε s : ℝ) : ℝ :=
  h * (1 - |s|) * (defectLaplace g
    ((h : ℂ) * ((ε : ℂ) + ((n + s : ℝ) : ℂ) * I))).re

/-- Boundary error paired with a tent of width `h` centred at `h*n`. -/
def tentBoundaryError (g : ℝ → ℂ) (h n : ℝ) : ℝ :=
  ∫ s in (-1 : ℝ)..1, h * (1 - |s|) * (defectBoundary g (h * (n + s))).re

theorem tentSeriesKernel_eq {h : ℝ} (hh : 0 < h) (n ε s u : ℝ) :
    tentSeriesKernel h n ε s u = h * (1 - |s|) *
      (((h : ℂ) * ((ε : ℂ) + ((n + s : ℝ) : ℂ) * I)) /
        ((Real.pi : ℂ) * ((u : ℂ) ^ 2 +
          ((h : ℂ) * ((ε : ℂ) + ((n + s : ℝ) : ℂ) * I)) ^ 2))).re := by
  have hh0 : (h : ℂ) ≠ 0 := by exact_mod_cast hh.ne'
  let z : ℂ := (ε : ℂ) + ((n + s : ℝ) : ℂ) * I
  have hd : ((u : ℂ) / h) ^ 2 + z ^ 2 =
      ((u : ℂ) ^ 2 + ((h : ℂ) * z) ^ 2) / (h : ℂ) ^ 2 := by
    field_simp
  have he : z / ((Real.pi : ℂ) * (((u : ℂ) / h) ^ 2 + z ^ 2)) =
      (h : ℂ) * (((h : ℂ) * z) / ((Real.pi : ℂ) * ((u : ℂ) ^ 2 + ((h : ℂ) * z) ^ 2))) := by
    rw [hd, ← mul_div_assoc]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
    ring
  unfold tentSeriesKernel shiftedTentSeriesKernel
  rw [Complex.ofReal_div]
  change (1 - |s|) * (z / ((Real.pi : ℂ) * (((u : ℂ) / h) ^ 2 + z ^ 2))).re = _
  rw [he, Complex.re_ofReal_mul]
  ring

theorem tentDualKernel_eq (h n ε s u : ℝ) :
    tentDualKernel h n ε s u = h * (1 - |s|) *
      (cexp (-(2 * Real.pi * (u : ℂ) *
        ((h : ℂ) * ((ε : ℂ) + ((n + s : ℝ) : ℂ) * I))))).re := by
  have he : -(2 * (Real.pi : ℂ) * ((h * u : ℝ) : ℂ) *
      ((ε : ℂ) + ((n + s : ℝ) : ℂ) * I)) =
      -(2 * Real.pi * (u : ℂ) * ((h : ℂ) * ((ε : ℂ) + ((n + s : ℝ) : ℂ) * I))) := by
    push_cast
    ring
  simp only [tentDualKernel, shiftedTentDualKernel, he]
  ring

theorem tentPolarKernel_eq {h : ℝ} (hh : 0 < h) (β n ε s : ℝ) :
    tentPolarKernel h β n ε s = h * (1 - |s|) *
      (-(β : ℂ) / ((Real.pi : ℂ) * ((h : ℂ) *
        ((ε : ℂ) + ((n + s : ℝ) : ℂ) * I))) + β).re := by
  have hh0 : (h : ℂ) ≠ 0 := by exact_mod_cast hh.ne'
  let z : ℂ := (ε : ℂ) + ((n + s : ℝ) : ℂ) * I
  have he : (h : ℂ) * (-(β : ℂ) / ((Real.pi : ℂ) * ((h : ℂ) * z)) + β) =
      -(β : ℂ) / ((Real.pi : ℂ) * z) + (h : ℂ) * β := by
    rw [mul_add, show (Real.pi : ℂ) * ((h : ℂ) * z) = (h : ℂ) * (Real.pi * z) by ring,
      ← mul_div_assoc, mul_div_mul_left _ _ hh0]
  have her := congrArg Complex.re he
  simp only [Complex.re_ofReal_mul, Complex.add_re, Complex.ofReal_re] at her
  unfold tentPolarKernel shiftedTentPolarKernel
  change (1 - |s|) * (-(β : ℂ) / ((Real.pi : ℂ) * z) + β).re +
    (h - 1) * β * (1 - |s|) =
      h * (1 - |s|) * (-(β : ℂ) / ((Real.pi : ℂ) * ((h : ℂ) * z)) + β).re
  simp only [Complex.add_re, Complex.ofReal_re]
  linear_combination -(1 - |s|) * her

theorem integrable_tentSeriesKernel {ν : Measure ℝ} [SFinite ν]
    (hsupp : ν (Iio 1) = 0) (hmom : Integrable (fun u : ℝ => 1 / u ^ 2) ν)
    {h n ε : ℝ} (hh : 0 < h) (hh1 : h ≤ 1) (hn : 1 ≤ n)
    (hε : 0 < ε) (hε1 : ε ≤ 1) :
    Integrable (uncurry (tentSeriesKernel h n ε))
      ((volume.restrict (uIoc (-1 : ℝ) 1)).prod ν) := by
  refine integrable_prod_uIoc_of_inv_sq_bound hmom
    (f := tentSeriesKernel h n ε)
    (C := (4 * (n + 1) ^ 2 / (Real.pi * ε)) * h ^ 2) (by
      unfold tentSeriesKernel shiftedTentSeriesKernel uncurry
      fun_prop) ?_
  intro s hs
  rw [uIoc_of_le (by norm_num)] at hs
  filter_upwards [ae_one_le_of_measure_Iio_one_eq_zero hsupp] with u hu
  have huh : 1 ≤ u / h := (le_div_iff₀ hh).mpr (by linarith only [hu, hh1])
  have hb := abs_shiftedTentSeriesKernel_le hn hε hε1 (abs_le.mpr ⟨hs.1.le, hs.2⟩) huh
  rw [Real.norm_eq_abs, tentSeriesKernel]
  convert hb using 1
  field_simp

theorem integrable_tentDualKernel {ν : Measure ℝ} [SFinite ν]
    (hsupp : ν (Iio 1) = 0) (hmom : Integrable (fun u : ℝ => 1 / u ^ 2) ν)
    {h ε : ℝ} (hh : 0 < h) (hε : 0 < ε) (n : ℝ) :
    Integrable (uncurry (tentDualKernel h n ε))
      ((volume.restrict (uIoc (-1 : ℝ) 1)).prod ν) := by
  refine integrable_prod_uIoc_of_inv_sq_bound hmom
    (f := tentDualKernel h n ε) (C := 1 / (2 * Real.pi ^ 2 * ε ^ 2 * h))
    (by unfold tentDualKernel shiftedTentDualKernel uncurry; fun_prop) ?_
  intro s hs
  rw [uIoc_of_le (by norm_num)] at hs
  filter_upwards [ae_one_le_of_measure_Iio_one_eq_zero hsupp] with u hu
  have hu0 : 0 < u := zero_lt_one.trans_le hu
  have hb := mul_le_mul_of_nonneg_left
    (abs_shiftedTentDualKernel_le (n := n) hε (abs_le.mpr ⟨hs.1.le, hs.2⟩)
      (mul_pos hh hu0)) hh.le
  rw [Real.norm_eq_abs, tentDualKernel, abs_mul, abs_of_pos hh]
  calc h * |shiftedTentDualKernel n ε s (h * u)| ≤
      h * ((1 / (2 * Real.pi ^ 2 * ε ^ 2)) * (1 / (h * u) ^ 2)) := hb
    _ = _ := by field_simp

theorem continuous_tentPolarKernel (h β n : ℝ) {ε : ℝ} (hε : 0 < ε) :
    Continuous (tentPolarKernel h β n ε) :=
  (continuous_shiftedTentPolarKernel (β : ℂ) n hε).add (by fun_prop)

theorem continuous_tentDefectKernel {g : ℝ → ℂ} (hg : Integrable g)
    {h ε : ℝ} (hh : 0 < h) (hε : 0 < ε) (n : ℝ) :
    Continuous (tentDefectKernel g h n ε) := by
  have hc := (continuous_defectLaplace_vertical hg (mul_pos hh hε)).comp
    (by fun_prop : Continuous fun s : ℝ => h * (n + s))
  have he (s : ℝ) : (h : ℂ) * ((ε : ℂ) + ((n + s : ℝ) : ℂ) * I) =
      ((h * ε : ℝ) : ℂ) + ((h * (n + s) : ℝ) : ℂ) * I := by
    push_cast
    ring
  change Continuous fun s : ℝ => h * (1 - |s|) *
    (defectLaplace g ((h : ℂ) * ((ε : ℂ) + ((n + s : ℝ) : ℂ) * I))).re
  simp only [he]
  exact (by fun_prop : Continuous fun s : ℝ => h * (1 - |s|)).mul (Complex.continuous_re.comp hc)

theorem integral_tentSeriesKernel_eq_of_theta_defect {ν : Measure ℝ}
    (hsupp : ν (Iio 1) = 0) (hmom : Integrable (fun u : ℝ => 1 / u ^ 2) ν)
    {β : ℝ} {g : ℝ → ℂ} {Cg : ℝ} {N : ℕ} (hgm : Measurable g)
    (hgb : ∀ t, ‖g t‖ ≤ Cg * (1 + |t|) ^ N)
    (hθ : ∀ x : ℝ, 0 < x → measureTheta ν x =
      (x : ℂ) ^ (-(1 / 2 : ℂ)) * measureTheta ν x⁻¹ + -(β : ℂ) +
        (β : ℂ) * (x : ℂ) ^ (-(1 / 2 : ℂ)) + defectKernel g x)
    {h ε : ℝ} (hh : 0 < h) (hε : 0 < ε) (n s : ℝ) :
    ∫ u, tentSeriesKernel h n ε s u ∂ν =
      (∫ u, tentDualKernel h n ε s u ∂ν) + tentPolarKernel h β n ε s +
        tentDefectKernel g h n ε s := by
  let z : ℂ := (h : ℂ) * ((ε : ℂ) + ((n + s : ℝ) : ℂ) * I)
  have hz : 0 < z.re := by simpa [z] using mul_pos hh hε
  have hser : ∫ u, tentSeriesKernel h n ε s u ∂ν = h * (1 - |s|) * (measureSeries ν z).re := by
    have hre : (∫ u : ℝ, (z / ((Real.pi : ℂ) * ((u : ℂ) ^ 2 + z ^ 2))).re ∂ν) =
        (measureSeries ν z).re := integral_re (integrable_measureSeries_integrand hsupp hmom hz)
    rw [← hre, ← integral_const_mul]
    exact integral_congr_ae (Eventually.of_forall fun u => tentSeriesKernel_eq hh n ε s u)
  have hdual : ∫ u, tentDualKernel h n ε s u ∂ν = h * (1 - |s|) * (measureDual ν z).re := by
    have hre : (∫ u : ℝ, (cexp (-(2 * Real.pi * (u : ℂ) * z))).re ∂ν) =
        (measureDual ν z).re := integral_re (integrable_measureDual_integrand hsupp hmom hz)
    rw [← hre, ← integral_const_mul]
    exact integral_congr_ae (Eventually.of_forall fun u => tentDualKernel_eq h n ε s u)
  rw [hser, hdual, tentPolarKernel_eq hh, tentDefectKernel,
    measureSeries_eq_of_theta_defect hsupp hmom hgm hgb hθ hz]
  simp only [Complex.add_re]
  ring

/-- The scaled Laplace identity may be integrated and its two measure integrals swapped. -/
theorem tent_pairing_identity {ν : Measure ℝ}
    (hsupp : ν (Iio 1) = 0) (hmom : Integrable (fun u : ℝ => 1 / u ^ 2) ν)
    {β : ℝ} {g : ℝ → ℂ} {Cg : ℝ} {N : ℕ} (hgm : Measurable g)
    (hgb : ∀ t, ‖g t‖ ≤ Cg * (1 + |t|) ^ N) (hgi : Integrable g)
    (hθ : ∀ x : ℝ, 0 < x → measureTheta ν x =
      (x : ℂ) ^ (-(1 / 2 : ℂ)) * measureTheta ν x⁻¹ + -(β : ℂ) +
        (β : ℂ) * (x : ℂ) ^ (-(1 / 2 : ℂ)) + defectKernel g x)
    {h n ε : ℝ} (hh : 0 < h) (hh1 : h ≤ 1) (hn : 1 ≤ n)
    (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∫ u, (∫ s in (-1 : ℝ)..1, tentSeriesKernel h n ε s u) ∂ν =
      (∫ u, (∫ s in (-1 : ℝ)..1, tentDualKernel h n ε s u) ∂ν) +
        (∫ s in (-1 : ℝ)..1, tentPolarKernel h β n ε s) +
          ∫ s in (-1 : ℝ)..1, tentDefectKernel g h n ε s := by
  haveI : SigmaFinite ν := sigmaFinite_of_measure_Iio_one_eq_zero hsupp hmom
  have hS := integrable_tentSeriesKernel hsupp hmom hh hh1 hn hε hε1
  have hD := integrable_tentDualKernel hsupp hmom hh hε n
  have hDi : IntervalIntegrable (fun s : ℝ => ∫ u, tentDualKernel h n ε s u ∂ν) volume (-1) 1 :=
    intervalIntegrable_iff.mpr hD.integral_prod_left
  have hPi : IntervalIntegrable (tentPolarKernel h β n ε) volume (-1) 1 :=
    (continuous_tentPolarKernel h β n hε).intervalIntegrable (-1) 1
  have hJi : IntervalIntegrable (tentDefectKernel g h n ε) volume (-1) 1 :=
    (continuous_tentDefectKernel hgi hh hε n).intervalIntegrable (-1) 1
  have he : (∫ s in (-1 : ℝ)..1, ∫ u, tentSeriesKernel h n ε s u ∂ν) =
      (∫ s in (-1 : ℝ)..1, ∫ u, tentDualKernel h n ε s u ∂ν) +
        (∫ s in (-1 : ℝ)..1, tentPolarKernel h β n ε s) +
          ∫ s in (-1 : ℝ)..1, tentDefectKernel g h n ε s := by
    rw [intervalIntegral.integral_congr (fun s _ =>
      integral_tentSeriesKernel_eq_of_theta_defect hsupp hmom hgm hgb hθ hh hε n s),
      intervalIntegral.integral_add (hDi.add hPi) hJi,
      intervalIntegral.integral_add hDi hPi]
  rwa [intervalIntegral_integral_swap hS, intervalIntegral_integral_swap hD] at he

theorem integrable_intervalIntegral_tentSeriesKernel {ν : Measure ℝ} [SFinite ν]
    (hsupp : ν (Iio 1) = 0) (hmom : Integrable (fun u : ℝ => 1 / u ^ 2) ν)
    {h n ε : ℝ} (hh : 0 < h) (hh1 : h ≤ 1) (hn : 1 ≤ n)
    (hε : 0 < ε) (hε1 : ε ≤ 1) :
    Integrable (fun u : ℝ => ∫ s in (-1 : ℝ)..1, tentSeriesKernel h n ε s u) ν := by
  refine (integrable_tentSeriesKernel hsupp hmom hh hh1 hn hε hε1).integral_prod_right.congr
    (Eventually.of_forall fun u => ?_)
  change (∫ s in uIoc (-1 : ℝ) 1, tentSeriesKernel h n ε s u) =
    ∫ s in (-1 : ℝ)..1, tentSeriesKernel h n ε s u
  rw [uIoc_of_le (by norm_num : (-1 : ℝ) ≤ 1),
    intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1)]

theorem integrable_intervalIntegral_tentDualKernel {ν : Measure ℝ} [SFinite ν]
    (hsupp : ν (Iio 1) = 0) (hmom : Integrable (fun u : ℝ => 1 / u ^ 2) ν)
    {h ε : ℝ} (hh : 0 < h) (hε : 0 < ε) (n : ℝ) :
    Integrable (fun u : ℝ => ∫ s in (-1 : ℝ)..1, tentDualKernel h n ε s u) ν := by
  refine (integrable_tentDualKernel hsupp hmom hh hε n).integral_prod_right.congr
    (Eventually.of_forall fun u => ?_)
  change (∫ s in uIoc (-1 : ℝ) 1, tentDualKernel h n ε s u) =
    ∫ s in (-1 : ℝ)..1, tentDualKernel h n ε s u
  rw [uIoc_of_le (by norm_num : (-1 : ℝ) ≤ 1),
    intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1)]

/-- Poisson smoothing recovers the mass of the tent of width `h`. -/
theorem tendsto_integral_tentSeriesKernel {ν : Measure ℝ}
    (hsupp : ν (Iio 1) = 0) (hmom : Integrable (fun u : ℝ => 1 / u ^ 2) ν)
    {h n : ℝ} (hh : 0 < h) (hh1 : h ≤ 1) (hn : 1 ≤ n) :
    Tendsto (fun ε : ℝ => ∫ u, (∫ s in (-1 : ℝ)..1, tentSeriesKernel h n ε s u) ∂ν)
      (𝓝[>] 0) (𝓝 ((1 / 2) * ∫ u, unitTent n (u / h) ∂ν)) := by
  haveI : SigmaFinite ν := sigmaFinite_of_measure_Iio_one_eq_zero hsupp hmom
  have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε ∈ Ioo 0 1 := Ioo_mem_nhdsGT one_pos
  rw [← integral_const_mul]
  refine tendsto_integral_filter_of_dominated_convergence
    (fun u => ((n + 2) ^ 2 * h ^ 2) * (1 / u ^ 2))
    (hev.mono fun ε hε =>
      (integrable_intervalIntegral_tentSeriesKernel hsupp hmom hh hh1 hn hε.1 hε.2.le).1)
    (hev.mono fun ε hε => ?_) (hmom.const_mul _) ?_
  · filter_upwards [ae_one_le_of_measure_Iio_one_eq_zero hsupp] with u hu
    have huh : 1 ≤ u / h := (le_div_iff₀ hh).mpr (by linarith only [hu, hh1])
    simp only [tentSeriesKernel]
    rw [Real.norm_eq_abs, abs_of_nonneg (intervalIntegral.integral_nonneg (by norm_num)
      fun s hs => shiftedTentSeriesKernel_nonneg hε.1 n (abs_le.mpr hs) (u / h))]
    have hb := intervalIntegral_shiftedTentSeriesKernel_le hn hε.1 hε.2.le huh
    change (∫ s in (-1 : ℝ)..1, shiftedTentSeriesKernel n ε s (u / h)) ≤ _
    convert hb using 1
    field_simp
  · filter_upwards [ae_one_le_of_measure_Iio_one_eq_zero hsupp] with u hu
    have huh : 1 ≤ u / h := (le_div_iff₀ hh).mpr (by linarith only [hu, hh1])
    have h0 : unitTent 0 (-(u / h) - n) = 0 :=
      unitTent_eq_zero (by rw [sub_zero, abs_of_neg (by linarith)]; linarith)
    have hlim := ((tendsto_windowPoisson (u / h - n)).add
      (tendsto_windowPoisson (-(u / h) - n))).const_mul (1 / 2 : ℝ)
    rw [h0, add_zero, unitTent_zero_sub] at hlim
    exact hlim.congr' (eventually_nhdsWithin_of_forall fun ε hε =>
      (intervalIntegral_shiftedTentSeriesKernel hε n (u / h)).symm)

theorem intervalIntegral_tentDualKernel {h u : ℝ} (hh : 0 < h) (hu : 0 < u) (n ε : ℝ) :
    ∫ s in (-1 : ℝ)..1, tentDualKernel h n ε s u =
      h * (Real.exp (-2 * Real.pi * (h * u) * ε) *
        (Real.cos (2 * Real.pi * (h * u) * n) * tentFourierWeight h u)) := by
  simp only [tentDualKernel, tentFourierWeight, intervalIntegral.integral_const_mul,
    intervalIntegral_shiftedTentDualKernel (mul_pos hh hu).ne']

theorem abs_intervalIntegral_tentDualKernel_le {h u ε : ℝ}
    (hh : 0 < h) (hu : 0 < u) (hε : 0 < ε) (n : ℝ) :
    |∫ s in (-1 : ℝ)..1, tentDualKernel h n ε s u| ≤
      (1 / (Real.pi ^ 2 * h)) * (1 / u ^ 2) := by
  rw [intervalIntegral_tentDualKernel hh hu, abs_mul, abs_of_pos hh,
    abs_mul, abs_of_pos (Real.exp_pos _), abs_mul,
    abs_of_nonneg (show 0 ≤ tentFourierWeight h u from sq_nonneg _)]
  have he : Real.exp (-2 * Real.pi * (h * u) * ε) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by
      have hp : 0 ≤ 2 * Real.pi * (h * u) * ε := by positivity
      linarith only [hp])
  have hc := Real.abs_cos_le_one (2 * Real.pi * (h * u) * n)
  have hs : tentFourierWeight h u ≤
      1 / (Real.pi * (h * u)) ^ 2 := by
    rw [tentFourierWeight, div_pow]
    exact div_le_div_of_nonneg_right (Real.sin_sq_le_one _) (sq_nonneg _)
  calc h * (Real.exp (-2 * Real.pi * (h * u) * ε) *
      (|Real.cos (2 * Real.pi * (h * u) * n)| * tentFourierWeight h u)) ≤
        h * (1 * (1 * (1 / (Real.pi * (h * u)) ^ 2))) := by
          apply mul_le_mul_of_nonneg_left _ hh.le
          exact mul_le_mul he
            (mul_le_mul hc hs (sq_nonneg _) zero_le_one)
            (mul_nonneg (abs_nonneg _) (sq_nonneg _)) zero_le_one
    _ = _ := by field_simp

/-- The dual side converges to its absolutely integrable sinc-squared cosine pairing. -/
theorem tendsto_integral_tentDualKernel {ν : Measure ℝ}
    (hsupp : ν (Iio 1) = 0) (hmom : Integrable (fun u : ℝ => 1 / u ^ 2) ν)
    {h : ℝ} (hh : 0 < h) (n : ℝ) :
    Tendsto (fun ε : ℝ => ∫ u, (∫ s in (-1 : ℝ)..1, tentDualKernel h n ε s u) ∂ν)
      (𝓝[>] 0) (𝓝 (h * ∫ u, Real.cos (2 * Real.pi * (h * u) * n) *
        tentFourierWeight h u ∂ν)) := by
  haveI : SigmaFinite ν := sigmaFinite_of_measure_Iio_one_eq_zero hsupp hmom
  rw [← integral_const_mul]
  refine tendsto_integral_filter_of_dominated_convergence
    (fun u => (1 / (Real.pi ^ 2 * h)) * (1 / u ^ 2)) ?_ ?_ (hmom.const_mul _) ?_
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    exact (integrable_intervalIntegral_tentDualKernel hsupp hmom hh hε n).1
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    filter_upwards [ae_one_le_of_measure_Iio_one_eq_zero hsupp] with u hu
    exact abs_intervalIntegral_tentDualKernel_le hh (zero_lt_one.trans_le hu) hε n
  · filter_upwards [ae_one_le_of_measure_Iio_one_eq_zero hsupp] with u hu
    have hc : Continuous fun ε : ℝ => h * (Real.exp (-2 * Real.pi * (h * u) * ε) *
        (Real.cos (2 * Real.pi * (h * u) * n) * tentFourierWeight h u)) := by fun_prop
    have ht := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
    simp only [mul_zero, Real.exp_zero, one_mul] at ht
    exact ht.congr' (Eventually.of_forall fun ε =>
      (intervalIntegral_tentDualKernel hh (zero_lt_one.trans_le hu) n ε).symm)

theorem intervalIntegral_tentPolarKernel (h β n : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∫ s in (-1 : ℝ)..1, tentPolarKernel h β n ε s = h * β - β * windowPoisson ε (-n) := by
  have hc : Continuous fun s : ℝ => (h - 1) * β * (1 - |s|) := by fun_prop
  simp only [tentPolarKernel]
  rw [intervalIntegral.integral_add
    ((continuous_shiftedTentPolarKernel (β : ℂ) n hε).intervalIntegrable _ _) (hc.intervalIntegrable _ _),
    intervalIntegral_shiftedTentPolarKernel _ hε, intervalIntegral.integral_const_mul,
    fejer_triangle_integral_one]
  simp only [Complex.ofReal_re, Complex.ofReal_im, zero_div, zero_mul, sub_zero, mul_one]
  ring

theorem tendsto_integral_tentPolarKernel (h β : ℝ) {n : ℝ} (hn : 1 ≤ n) :
    Tendsto (fun ε : ℝ => ∫ s in (-1 : ℝ)..1, tentPolarKernel h β n ε s)
      (𝓝[>] 0) (𝓝 (h * β)) := by
  have ht := tendsto_windowPoisson (-n)
  rw [unitTent_eq_zero (by rw [sub_zero, abs_neg, abs_of_pos (by linarith)]; exact hn)] at ht
  have hl := (tendsto_const_nhds : Tendsto (fun _ : ℝ => h * β)
    (𝓝[>] 0) (𝓝 (h * β))).sub (ht.const_mul β)
  simp only [mul_zero, sub_zero] at hl
  exact hl.congr' (eventually_nhdsWithin_of_forall fun ε hε =>
    (intervalIntegral_tentPolarKernel h β n hε).symm)

theorem norm_tentDefectKernel_le {g : ℝ → ℂ} (hg : Integrable g)
    {h n ε s : ℝ} (hh : 0 < h) (hn : 1 < n) (hε : 0 < ε) (hs : |s| ≤ 1) :
    ‖tentDefectKernel g h n ε s‖ ≤
      h * (3 / (2 * Real.pi) * ∫ t, ‖g t‖) * (h * (n - 1)) ^ (-(1 / 2 : ℝ)) := by
  let z : ℂ := (h : ℂ) * ((ε : ℂ) + ((n + s : ℝ) : ℂ) * I)
  have hz : 0 < z.re := by simpa [z] using mul_pos hh hε
  have hz0 : z ≠ 0 := fun he => by simp [he] at hz
  have ha : 0 < h * (n - 1) := mul_pos hh (sub_pos.mpr hn)
  have hi : h * (n - 1) ≤ ‖z‖ := by
    have him : z.im = h * (n + s) := by simp [z]
    calc h * (n - 1) ≤ h * (n + s) :=
        mul_le_mul_of_nonneg_left (by linarith only [(abs_le.mp hs).1]) hh.le
      _ = z.im := him.symm
      _ ≤ |z.im| := le_abs_self _
      _ ≤ ‖z‖ := Complex.abs_im_le_norm z
  have hb : ‖defectLaplace g z‖ ≤
      (3 / (2 * Real.pi) * ∫ t, ‖g t‖) * (h * (n - 1)) ^ (-(1 / 2 : ℝ)) := by
    rw [← closedDefectLaplace_eq hz]
    exact (norm_closedDefectLaplace_le hg hz.le hz0).trans
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos ha hi (by norm_num))
        (mul_nonneg (by positivity) (integral_nonneg fun _ => norm_nonneg _)))
  have hw : 0 ≤ h * (1 - |s|) := mul_nonneg hh.le (sub_nonneg.mpr hs)
  have hw1 : h * (1 - |s|) ≤ h := by nlinarith only [mul_nonneg hh.le (abs_nonneg s)]
  rw [tentDefectKernel, Real.norm_eq_abs, abs_mul, abs_of_nonneg hw]
  calc h * (1 - |s|) * |(defectLaplace g z).re| ≤ h * ‖defectLaplace g z‖ :=
      mul_le_mul hw1 (Complex.abs_re_le_norm _) (abs_nonneg _) hh.le
    _ ≤ h * ((3 / (2 * Real.pi) * ∫ t, ‖g t‖) * (h * (n - 1)) ^ (-(1 / 2 : ℝ))) :=
      mul_le_mul_of_nonneg_left hb hh.le
    _ = _ := by ring

/-- The defect window converges to the integral of its genuine right-hand boundary values. -/
theorem tendsto_integral_tentDefectKernel {g : ℝ → ℂ} (hg : Integrable g)
    {h n : ℝ} (hh : 0 < h) (hn : 1 < n) :
    Tendsto (fun ε : ℝ => ∫ s in (-1 : ℝ)..1, tentDefectKernel g h n ε s)
      (𝓝[>] 0) (𝓝 (∫ s in (-1 : ℝ)..1,
        h * (1 - |s|) * (defectBoundary g (h * (n + s))).re)) := by
  have ht : Tendsto (fun ε : ℝ => h * ε) (𝓝[>] 0) (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_, ?_⟩
    · simpa only [id_eq, mul_zero] using
        ((tendsto_id : Tendsto (fun x : ℝ => x) (𝓝 0) (𝓝 0)).const_mul h).mono_left
        (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
    · exact eventually_nhdsWithin_of_forall fun ε hε => mul_pos hh hε
  apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (fun _ : ℝ => h * (3 / (2 * Real.pi) * ∫ t, ‖g t‖) * (h * (n - 1)) ^ (-(1 / 2 : ℝ)))
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    exact (continuous_tentDefectKernel hg hh hε n).aestronglyMeasurable
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    exact Eventually.of_forall fun s hs => by
      rw [uIoc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] at hs
      exact norm_tentDefectKernel_le hg hh hn hε (abs_le.mpr ⟨hs.1.le, hs.2⟩)
  · exact intervalIntegrable_const
  · apply Eventually.of_forall
    intro s hs
    rw [uIoc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] at hs
    have hy : h * (n + s) ≠ 0 := (mul_pos hh (by linarith only [hn, hs.1])).ne'
    have hl := (Complex.continuous_re.tendsto _).comp ((tendsto_defectLaplace_boundary hg hy).comp ht)
    have hl' := hl.const_mul (h * (1 - |s|))
    apply hl'.congr'
    apply Eventually.of_forall
    intro ε
    dsimp only [Function.comp_apply]
    have he : (h : ℂ) * ((ε : ℂ) + ((n + s : ℝ) : ℂ) * I) =
        ((h * ε : ℝ) : ℂ) + ((h * (n + s) : ℝ) : ℂ) * I := by push_cast; ring
    simp only [tentDefectKernel, he]

/-- Exact boundary pairing for every tent of width at most one lying in the positive half-line. -/
theorem tent_boundary_identity_of_theta_defect {ν : Measure ℝ}
    (hsupp : ν (Iio 1) = 0) (hmom : Integrable (fun u : ℝ => 1 / u ^ 2) ν)
    {β : ℝ} {g : ℝ → ℂ} {Cg : ℝ} {N : ℕ} (hgm : Measurable g)
    (hgb : ∀ t, ‖g t‖ ≤ Cg * (1 + |t|) ^ N) (hgi : Integrable g)
    (hθ : ∀ x : ℝ, 0 < x → measureTheta ν x =
      (x : ℂ) ^ (-(1 / 2 : ℂ)) * measureTheta ν x⁻¹ + -(β : ℂ) +
        (β : ℂ) * (x : ℂ) ^ (-(1 / 2 : ℂ)) + defectKernel g x)
    {h n : ℝ} (hh : 0 < h) (hh1 : h ≤ 1) (hn : 1 < n) :
    (1 / 2) * (∫ u, unitTent n (u / h) ∂ν) =
      h * (∫ u, Real.cos (2 * Real.pi * (h * u) * n) *
        tentFourierWeight h u ∂ν) + h * β +
          ∫ s in (-1 : ℝ)..1, h * (1 - |s|) * (defectBoundary g (h * (n + s))).re := by
  have hleft := tendsto_integral_tentSeriesKernel hsupp hmom hh hh1 hn.le
  have hright := ((tendsto_integral_tentDualKernel hsupp hmom hh n).add
    (tendsto_integral_tentPolarKernel h β hn.le)).add
      (tendsto_integral_tentDefectKernel hgi hh hn)
  apply tendsto_nhds_unique hleft
  apply hright.congr'
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with ε hε
  exact (tent_pairing_identity hsupp hmom hgm hgb hgi hθ hh hh1 hn.le hε.1 hε.2.le).symm

/-- The boundary error is uniformly small for tents far from the origin. -/
theorem norm_tentBoundaryError_le {g : ℝ → ℂ} (hg : Integrable g)
    {h n : ℝ} (hh : 0 < h) (hn : 1 < n) :
    ‖tentBoundaryError g h n‖ ≤
      (2 * h * (3 / (2 * Real.pi) * ∫ t, ‖g t‖)) *
        (h * (n - 1)) ^ (-(1 / 2 : ℝ)) := by
  let C : ℝ := 3 / (2 * Real.pi) * ∫ t, ‖g t‖
  have hC : 0 ≤ C := mul_nonneg (by positivity) (integral_nonneg fun _ => norm_nonneg _)
  have hb : ∀ s ∈ uIoc (-1 : ℝ) 1,
      ‖h * (1 - |s|) * (defectBoundary g (h * (n + s))).re‖ ≤
        h * C * (h * (n - 1)) ^ (-(1 / 2 : ℝ)) := by
    intro s hs
    rw [uIoc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] at hs
    have hs1 : |s| ≤ 1 := abs_le.mpr ⟨hs.1.le, hs.2⟩
    have ha : 0 < h * (n - 1) := mul_pos hh (sub_pos.mpr hn)
    have hy : h * (n - 1) ≤ |h * (n + s)| :=
      (mul_le_mul_of_nonneg_left (by linarith only [hs.1]) hh.le).trans (le_abs_self _)
    have hj : ‖defectBoundary g (h * (n + s))‖ ≤
        C * (h * (n - 1)) ^ (-(1 / 2 : ℝ)) :=
      (norm_defectBoundary_le hg _).trans
        (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos ha hy (by norm_num)) hC)
    have hw : 0 ≤ h * (1 - |s|) := mul_nonneg hh.le (sub_nonneg.mpr hs1)
    have hw1 : h * (1 - |s|) ≤ h := by nlinarith only [mul_nonneg hh.le (abs_nonneg s)]
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hw]
    calc h * (1 - |s|) * |(defectBoundary g (h * (n + s))).re| ≤
        h * ‖defectBoundary g (h * (n + s))‖ :=
          mul_le_mul hw1 (Complex.abs_re_le_norm _) (abs_nonneg _) hh.le
      _ ≤ h * (C * (h * (n - 1)) ^ (-(1 / 2 : ℝ))) :=
          mul_le_mul_of_nonneg_left hj hh.le
      _ = _ := by ring
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const hb
  norm_num only [show |(1 : ℝ) - -1| = 2 by norm_num] at hi
  exact hi.trans_eq (by dsimp only [C]; ring)

/-- Fixed-width tent errors vanish as their centres tend to positive infinity. -/
theorem tendsto_tentBoundaryError_atTop {g : ℝ → ℂ} (hg : Integrable g)
    {h : ℝ} (hh : 0 < h) :
    Tendsto (tentBoundaryError g h) atTop (𝓝 0) := by
  have ht : Tendsto (fun n : ℝ => h * (n - 1)) atTop atTop := by
    refine tendsto_atTop.mpr fun b => eventually_atTop.mpr ⟨b / h + 1, fun n hn => ?_⟩
    have hb : b / h ≤ n - 1 := by linarith only [hn]
    have hb' := (div_le_iff₀ hh).mp hb
    simpa only [mul_comm] using hb'
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  refine squeeze_zero' (Eventually.of_forall fun n => norm_nonneg _)
    (eventually_atTop.mpr ⟨2, fun n hn => norm_tentBoundaryError_le hg hh (by linarith only [hn])⟩) ?_
  simpa using
    ((tendsto_rpow_neg_atTop (by norm_num : 0 < (1 / 2 : ℝ))).comp ht).const_mul
      (2 * h * (3 / (2 * Real.pi) * ∫ t, ‖g t‖))

end GaloisForLFunctions.ExactEventTheory

#print axioms GaloisForLFunctions.ExactEventTheory.tent_boundary_identity_of_theta_defect
#print axioms GaloisForLFunctions.ExactEventTheory.tendsto_tentBoundaryError_atTop
