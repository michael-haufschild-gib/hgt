import GaloisForLFunctions.RHTower.ThetaQuantileFourierModes
import GaloisForLFunctions.RHTower.ThetaCdfFixedShiftAction
import GaloisForLFunctions.RHTower.HedenmalmQuantileSliceMoment
import GaloisForLFunctions.RHTower.HedenmalmThetaSourceCompressedInverseDeterminant
import GaloisForLFunctions.RHTower.HedenmalmThetaSourceDeterminantIdentity
import GaloisForLFunctions.RHTower.XiHadamardFactorization

/-!
# The CDF-action matrix of the theta source inverse

`B = i M_q V` on `L²(0,1)`, `q` the quantile speed of the theta density and
`Vf(t) = ∫₀ᵗ f − t ∫₀¹ f`.  On the Fourier modes `e_n(t) = e^{2πint}`:

* `B e = 0` for the constant mode, and `B e_n = q (e_n − 1)/(2πn)` for `n ≠ 0`;
* the integrals `∫₀¹ q(t)(1 − e_k(t)) dt` converge and equal the CDF action `Φ_k`
  (reflection `q(1 − t) = q(t)` kills the sine part);
* hence `⟨e_m, B e_n⟩ = (Φ_m − Φ_{n−m})/(2πn)` for `n ≠ 0`;
* the compression `D = P B P` to the mean-zero space has the same matrix on nonzero modes, and
  for `μ ≠ 0` the generalized eigenspaces of `B` and `D` correspond (`P` and `B` intertwine them
  injectively); so the nonzero eigenvalues of `D` are `−1/z`, `Ξ_C(z) = 0`, with algebraic
  multiplicity the order of the zero.
-/

open MeasureTheory Set Filter Topology
open scoped InnerProductSpace

namespace RHTower

noncomputable section

open HedenmalmThetaSource HedenmalmQuantile HedenmalmHilbertSchmidt GaloisForLFunctions.HTGeometry

/-- The quantile speed `q = M/k(Q)` of the theta density. -/
abbrev thetaQuantileSpeed (t : ℝ) : ℝ := quantileSpeed thetaSource t

theorem thetaQuantileSpeed_pos (t : ℝ) : 0 < thetaQuantileSpeed t := quantileSpeed_pos thetaSource t

/-! ## Endpoint cancellation -/

/-- `|1 − e^{2πi a s}| ≤ 2π|a| min(s, 1−s)` for `s ∈ [0,1]`. -/
theorem norm_one_sub_fourierMode_le (a : ℤ) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    ‖1 - fourierMode a s‖ ≤ 2 * Real.pi * |(a : ℝ)| * min s (1 - s) := by
  have h1 : ‖1 - fourierMode a s‖ ≤ 2 * Real.pi * |(a : ℝ)| * s := by
    have hθ : (2 * Real.pi * Complex.I * a * s : ℂ) = Complex.I * ((2 * Real.pi * a * s : ℝ) : ℂ) := by
      push_cast; ring
    rw [fourierMode, hθ, norm_sub_rev]
    refine Real.norm_exp_I_mul_ofReal_sub_one_le.trans (le_of_eq ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_of_pos Real.pi_pos, abs_of_nonneg hs.1]
    norm_num
  have h2 : ‖1 - fourierMode a s‖ ≤ 2 * Real.pi * |(a : ℝ)| * (1 - s) := by
    have hper : fourierMode a s = Complex.exp (Complex.I * ((2 * Real.pi * a * (s - 1) : ℝ) : ℂ)) := by
      have : Complex.exp (2 * Real.pi * Complex.I * a) = 1 := by
        rw [show (2 * Real.pi * Complex.I * a : ℂ) = (a : ℂ) * (2 * Real.pi * Complex.I) by ring]
        exact Complex.exp_int_mul_two_pi_mul_I a
      calc fourierMode a s = Complex.exp (Complex.I * ((2 * Real.pi * a * (s - 1) : ℝ) : ℂ)) *
              Complex.exp (2 * Real.pi * Complex.I * a) := by
            rw [fourierMode, ← Complex.exp_add]; push_cast; ring_nf
        _ = _ := by rw [this, mul_one]
    rw [hper, norm_sub_rev]
    refine Real.norm_exp_I_mul_ofReal_sub_one_le.trans (le_of_eq ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_of_pos Real.pi_pos,
      abs_of_nonpos (by linarith [hs.2] : s - 1 ≤ 0)]
    ring
  rcases min_choice s (1 - s) with h | h <;> rw [h]
  · exact h1
  · exact h2

/-- `q(t) min(t, 1−t)` is integrable on `(0,1)`: it is the CDF tail weight in quantile
coordinates. -/
theorem integrableOn_thetaQuantileSpeed_mul_min :
    IntegrableOn (fun t => thetaQuantileSpeed t * min t (1 - t)) (Ioo (0 : ℝ) 1) := by
  set g : ℝ → ℝ := fun x => thetaSource.mass / thetaSource.k x * cdfTailWeight x
  have hgc : Continuous g :=
    (continuous_const.div thetaSource.continuous_k fun x => (thetaSource.pos_k x).ne').mul
      (thetaSource.continuous_cdfFun.min (continuous_const.sub thetaSource.continuous_cdfFun))
  have h := (thetaSource.integrableOn_comp_quantileFun_iff hgc.aestronglyMeasurable).2 (by
    refine integrable_cdfTailWeight.congr (Eventually.of_forall fun x => ?_)
    simp only [g, smul_eq_mul, PositiveDensitySource.normalized]
    have hk := thetaSource.pos_k x
    have hM := thetaSource.mass_pos
    field_simp)
  refine h.congr_fun (fun u hu => ?_) measurableSet_Ioo
  simp only [g, cdfTailWeight, thetaSource.cdfFun_quantile hu, thetaQuantileSpeed, quantileSpeed]

theorem aestronglyMeasurable_thetaQuantileSpeed :
    AEStronglyMeasurable thetaQuantileSpeed (volume.restrict (Ioo (0 : ℝ) 1)) :=
  ((measurable_const.div ((thetaSource.continuous_k.measurable).comp
    thetaSource.measurable_quantileFun)).aestronglyMeasurable)

/-- `q(1 − e_k)` is integrable on `(0,1)`. -/
theorem integrableOn_thetaQuantileSpeed_mul_one_sub_fourierMode (k : ℤ) :
    IntegrableOn (fun t => (thetaQuantileSpeed t : ℂ) * (1 - fourierMode k t)) (Ioo (0 : ℝ) 1) := by
  refine ((integrableOn_thetaQuantileSpeed_mul_min.const_mul (2 * Real.pi * |(k : ℝ)|))).mono' ?_ ?_
  · exact (Complex.continuous_ofReal.comp_aestronglyMeasurable aestronglyMeasurable_thetaQuantileSpeed).mul
      (continuous_const.sub (continuous_fourierMode k)).aestronglyMeasurable
  · refine (ae_restrict_iff' measurableSet_Ioo).2 (Eventually.of_forall fun t ht => ?_)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (thetaQuantileSpeed_pos t)]
    calc thetaQuantileSpeed t * ‖1 - fourierMode k t‖ ≤
        thetaQuantileSpeed t * (2 * Real.pi * |(k : ℝ)| * min t (1 - t)) :=
          mul_le_mul_of_nonneg_left (norm_one_sub_fourierMode_le k (Ioo_subset_Icc_self ht))
            (thetaQuantileSpeed_pos t).le
      _ = 2 * Real.pi * |(k : ℝ)| * (thetaQuantileSpeed t * min t (1 - t)) := by ring

/-- The sine part vanishes by reflection: `∫₀¹ q(t) sin(2πkt) dt = 0`. -/
theorem integral_thetaQuantileSpeed_mul_sin (k : ℤ) :
    ∫ t in Ioo (0 : ℝ) 1, thetaQuantileSpeed t * Real.sin (2 * Real.pi * k * t) = 0 := by
  set f : ℝ → ℝ := fun t => thetaQuantileSpeed t * Real.sin (2 * Real.pi * k * t)
  have hIoo : ∫ t in Ioo (0 : ℝ) 1, f t = ∫ t in (0 : ℝ)..1, f t := by
    rw [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]
  have hrefl : ∫ t in (0 : ℝ)..1, f t = ∫ t in (0 : ℝ)..1, f (1 - t) := by
    rw [intervalIntegral.integral_comp_sub_left f 1]; norm_num
  have hneg : ∫ t in (0 : ℝ)..1, f (1 - t) = -∫ t in (0 : ℝ)..1, f t := by
    rw [← intervalIntegral.integral_neg]
    refine intervalIntegral.integral_congr_ae ?_
    have hnull : ∀ᵐ t ∂(volume : Measure ℝ), t ≠ 1 := by
      simp [ae_iff, measure_singleton]
    filter_upwards [hnull] with t ht1 ht
    rw [uIoc_of_le zero_le_one] at ht
    have htI : t ∈ Ioo (0 : ℝ) 1 := ⟨ht.1, lt_of_le_of_ne ht.2 ht1⟩
    simp only [f, thetaQuantileSpeed]
    rw [quantileSpeed_one_sub htI]
    have : Real.sin (2 * Real.pi * k * (1 - t)) = -Real.sin (2 * Real.pi * k * t) := by
      rw [show 2 * Real.pi * k * (1 - t) = -(2 * Real.pi * k * t - (k : ℝ) * (2 * Real.pi)) by ring,
        Real.sin_neg, Real.sin_sub_int_mul_two_pi]
    rw [this]; ring
  rw [hIoo]
  linarith [hrefl.trans hneg]

theorem fourierMode_eq_cos_add_sin (k : ℤ) (t : ℝ) :
    fourierMode k t = (Real.cos (2 * Real.pi * k * t) : ℂ) + (Real.sin (2 * Real.pi * k * t) : ℂ) * Complex.I := by
  rw [fourierMode, show (2 * Real.pi * Complex.I * k * t : ℂ) = ((2 * Real.pi * k * t : ℝ) : ℂ) *
    Complex.I by push_cast; ring, Complex.exp_mul_I]
  push_cast; ring

theorem abs_one_sub_cos_le (k : ℤ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    |1 - Real.cos (2 * Real.pi * k * t)| ≤ 2 * Real.pi * |(k : ℝ)| * min t (1 - t) := by
  have h := (Complex.abs_re_le_norm (1 - fourierMode k t)).trans (norm_one_sub_fourierMode_le k ht)
  rwa [fourierMode_eq_cos_add_sin, Complex.sub_re, Complex.one_re, Complex.add_re, Complex.ofReal_re,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul,
    sub_zero, add_zero] at h

theorem abs_sin_le_min (k : ℤ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    |Real.sin (2 * Real.pi * k * t)| ≤ 2 * Real.pi * |(k : ℝ)| * min t (1 - t) := by
  have h := (Complex.abs_im_le_norm (1 - fourierMode k t)).trans (norm_one_sub_fourierMode_le k ht)
  rwa [fourierMode_eq_cos_add_sin, Complex.sub_im, Complex.one_im, Complex.add_im, Complex.ofReal_im,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_one, zero_mul,
    add_zero, zero_add, zero_sub, abs_neg] at h

theorem integrableOn_thetaQuantileSpeed_mul_one_sub_cos (k : ℤ) :
    IntegrableOn (fun t => thetaQuantileSpeed t * (1 - Real.cos (2 * Real.pi * k * t))) (Ioo (0 : ℝ) 1) := by
  refine ((integrableOn_thetaQuantileSpeed_mul_min.const_mul (2 * Real.pi * |(k : ℝ)|))).mono' ?_ ?_
  · exact aestronglyMeasurable_thetaQuantileSpeed.mul (by fun_prop : Continuous fun t : ℝ =>
      1 - Real.cos (2 * Real.pi * k * t)).aestronglyMeasurable
  · refine (ae_restrict_iff' measurableSet_Ioo).2 (Eventually.of_forall fun t ht => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (thetaQuantileSpeed_pos t)]
    calc thetaQuantileSpeed t * |1 - Real.cos (2 * Real.pi * k * t)| ≤
        thetaQuantileSpeed t * (2 * Real.pi * |(k : ℝ)| * min t (1 - t)) :=
          mul_le_mul_of_nonneg_left (abs_one_sub_cos_le k (Ioo_subset_Icc_self ht))
            (thetaQuantileSpeed_pos t).le
      _ = 2 * Real.pi * |(k : ℝ)| * (thetaQuantileSpeed t * min t (1 - t)) := by ring

theorem integrableOn_thetaQuantileSpeed_mul_sin (k : ℤ) :
    IntegrableOn (fun t => thetaQuantileSpeed t * Real.sin (2 * Real.pi * k * t)) (Ioo (0 : ℝ) 1) := by
  refine ((integrableOn_thetaQuantileSpeed_mul_min.const_mul (2 * Real.pi * |(k : ℝ)|))).mono' ?_ ?_
  · exact aestronglyMeasurable_thetaQuantileSpeed.mul (by fun_prop : Continuous fun t : ℝ =>
      Real.sin (2 * Real.pi * k * t)).aestronglyMeasurable
  · refine (ae_restrict_iff' measurableSet_Ioo).2 (Eventually.of_forall fun t ht => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (thetaQuantileSpeed_pos t)]
    calc thetaQuantileSpeed t * |Real.sin (2 * Real.pi * k * t)| ≤
        thetaQuantileSpeed t * (2 * Real.pi * |(k : ℝ)| * min t (1 - t)) :=
          mul_le_mul_of_nonneg_left (abs_sin_le_min k (Ioo_subset_Icc_self ht))
            (thetaQuantileSpeed_pos t).le
      _ = 2 * Real.pi * |(k : ℝ)| * (thetaQuantileSpeed t * min t (1 - t)) := by ring

/-- **The complex action**: `∫₀¹ q(t)(1 − e_k(t)) dt = Φ_k`. -/
theorem integral_thetaQuantileSpeed_mul_one_sub_fourierMode (k : ℤ) :
    ∫ t in Ioo (0 : ℝ) 1, (thetaQuantileSpeed t : ℂ) * (1 - fourierMode k t) = cdfAction k := by
  have hsplit : ∀ t, (thetaQuantileSpeed t : ℂ) * (1 - fourierMode k t) =
      ((thetaQuantileSpeed t * (1 - Real.cos (2 * Real.pi * k * t)) : ℝ) : ℂ) -
        Complex.I * ((thetaQuantileSpeed t * Real.sin (2 * Real.pi * k * t) : ℝ) : ℂ) := by
    intro t
    rw [fourierMode, show (2 * Real.pi * Complex.I * k * t : ℂ) = ((2 * Real.pi * k * t : ℝ) : ℂ) *
      Complex.I by push_cast; ring, Complex.exp_mul_I]
    push_cast
    ring
  simp_rw [hsplit]
  have hA : Integrable (fun t => ((thetaQuantileSpeed t * (1 - Real.cos (2 * Real.pi * k * t)) : ℝ) : ℂ))
      (volume.restrict (Ioo (0 : ℝ) 1)) := (integrableOn_thetaQuantileSpeed_mul_one_sub_cos k).ofReal
  have hB : Integrable (fun t => Complex.I * ((thetaQuantileSpeed t * Real.sin (2 * Real.pi * k * t) : ℝ) : ℂ))
      (volume.restrict (Ioo (0 : ℝ) 1)) :=
    ((integrableOn_thetaQuantileSpeed_mul_sin k).ofReal).const_mul Complex.I
  rw [integral_sub hA hB, integral_const_mul, integral_complex_ofReal, integral_complex_ofReal,
    integral_thetaQuantileSpeed_mul_sin, ← cdfAction_eq_quantileSpeed]
  simp

/-! ## The pinned Volterra primitive of a Fourier mode -/

theorem integral_unitInterval_Iic_eq {f : ℝ → ℂ} {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    ∫ u, (Iic t).indicator f u ∂unitIntervalMeasure = ∫ u in (0 : ℝ)..t, f u := by
  rw [integral_indicator measurableSet_Iic, unitIntervalMeasure, Measure.restrict_restrict measurableSet_Iic,
    show Iic t ∩ Icc (0 : ℝ) 1 = Icc 0 t by
      ext u; simp only [mem_inter_iff, mem_Iic, mem_Icc]; constructor
      · rintro ⟨h1, h2, _⟩; exact ⟨h2, h1⟩
      · rintro ⟨h1, h2⟩; exact ⟨h2, h1, h2.trans ht.2⟩,
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le ht.1]

theorem integral_unitInterval_eq {f : ℝ → ℂ} :
    ∫ u, f u ∂unitIntervalMeasure = ∫ u in (0 : ℝ)..1, f u := by
  rw [unitIntervalMeasure, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one]

theorem integral_fourierMode_interval {n : ℤ} (hn : n ≠ 0) (t : ℝ) :
    ∫ u in (0 : ℝ)..t, fourierMode n u = (fourierMode n t - 1) / (2 * Real.pi * Complex.I * n) := by
  have hc : (2 * Real.pi * Complex.I * n : ℂ) ≠ 0 := by
    have : (n : ℂ) ≠ 0 := by exact_mod_cast hn
    have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    simp [hpi, this, Complex.I_ne_zero]
  have h := integral_exp_mul_complex (a := 0) (b := t) hc
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero] at h
  exact h

theorem pinnedPrefix_unitFourierBasis {n : ℤ} (hn : n ≠ 0) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    pinnedPrefix (unitFourierBasis n) t = (fourierMode n t - 1) / (2 * Real.pi * Complex.I * n) := by
  rw [pinnedPrefix, integral_congr_ae (Filter.EventuallyEq.indicator (coeFn_unitFourierBasis n)),
    integral_unitInterval_Iic_eq ht, integral_fourierMode_interval hn]

theorem pinnedMean_unitFourierBasis {n : ℤ} (hn : n ≠ 0) : pinnedMean (unitFourierBasis n) = 0 := by
  rw [pinnedMean, integral_congr_ae (coeFn_unitFourierBasis n), integral_unitInterval_eq,
    integral_fourierMode_interval hn, fourierMode_one, sub_self, zero_div]

theorem pinnedVolterraFun_unitFourierBasis {n : ℤ} (hn : n ≠ 0) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    pinnedVolterraFun (unitFourierBasis n) t = (fourierMode n t - 1) / (2 * Real.pi * Complex.I * n) := by
  rw [pinnedVolterraFun, pinnedPrefix_unitFourierBasis hn ht, pinnedMean_unitFourierBasis hn, mul_zero,
    sub_zero]

theorem pinnedVolterraFun_unitFourierBasis_zero {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    pinnedVolterraFun (unitFourierBasis 0) t = 0 := by
  have h0 : (unitFourierBasis 0 : ℝ → ℂ) =ᵐ[unitIntervalMeasure] fun _ => 1 := by
    filter_upwards [coeFn_unitFourierBasis 0] with u hu
    rw [hu, fourierMode_zero]
  rw [pinnedVolterraFun, pinnedPrefix, pinnedMean, integral_congr_ae (Filter.EventuallyEq.indicator h0),
    integral_congr_ae h0, integral_unitInterval_Iic_eq ht, integral_unitInterval_eq]
  simp

/-! ## The source inverse on Fourier modes -/

theorem ae_mem_Icc_unitInterval : ∀ᵐ t ∂unitIntervalMeasure, t ∈ Icc (0 : ℝ) 1 := by
  rw [unitIntervalMeasure]; exact ae_restrict_mem measurableSet_Icc

theorem thetaKernelOperator_ae (f : Lp ℂ 2 unitIntervalMeasure) :
    (thetaKernelOperator f : ℝ → ℂ) =ᵐ[unitIntervalMeasure]
      fun t => Complex.I * (thetaQuantileSpeed t : ℂ) * pinnedVolterraFun f t := by
  filter_upwards [pinnedKernelOperator_ae thetaSource hasFiniteKernelEnergy_thetaSource f] with t ht
  rw [thetaKernelOperator_eq_thetaCompactSourceInverse, thetaCompactSourceInverse, ht, pinnedKernelField_apply_eq_pinnedVolterraFun]

/-- `B e = 0`: the source inverse kills the constant mode. -/
theorem thetaKernelOperator_unitFourierBasis_zero : thetaKernelOperator (unitFourierBasis 0) = 0 := by
  apply Lp.ext
  filter_upwards [thetaKernelOperator_ae (unitFourierBasis 0), ae_mem_Icc_unitInterval,
    Lp.coeFn_zero ℂ 2 unitIntervalMeasure] with t h1 h2 h3
  rw [h1, h3, pinnedVolterraFun_unitFourierBasis_zero h2, mul_zero, Pi.zero_apply]

/-- `B e_n = q (e_n − 1)/(2πn)` for `n ≠ 0`. -/
theorem thetaKernelOperator_unitFourierBasis_ae {n : ℤ} (hn : n ≠ 0) :
    (thetaKernelOperator (unitFourierBasis n) : ℝ → ℂ) =ᵐ[unitIntervalMeasure]
      fun t => (thetaQuantileSpeed t : ℂ) * (fourierMode n t - 1) / (2 * Real.pi * n) := by
  filter_upwards [thetaKernelOperator_ae (unitFourierBasis n), ae_mem_Icc_unitInterval] with t h1 h2
  rw [h1, pinnedVolterraFun_unitFourierBasis hn h2]
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp

/-- **The CDF-action matrix**: `⟨e_m, B e_n⟩ = (Φ_m − Φ_{n−m})/(2πn)` for `n ≠ 0`. -/
theorem inner_unitFourierBasis_thetaKernelOperator (m : ℤ) {n : ℤ} (hn : n ≠ 0) :
    ⟪unitFourierBasis m, thetaKernelOperator (unitFourierBasis n)⟫_ℂ =
      ((cdfAction m - cdfAction (n - m)) / (2 * Real.pi * n) : ℝ) := by
  rw [MeasureTheory.L2.inner_def]
  have hpt : (fun t => ⟪(unitFourierBasis m : ℝ → ℂ) t, (thetaKernelOperator (unitFourierBasis n) : ℝ → ℂ) t⟫_ℂ)
      =ᵐ[unitIntervalMeasure] fun t => ((2 * Real.pi * n : ℝ) : ℂ)⁻¹ *
        ((thetaQuantileSpeed t : ℂ) * (1 - fourierMode (-m) t) -
          (thetaQuantileSpeed t : ℂ) * (1 - fourierMode (n - m) t)) := by
    filter_upwards [coeFn_unitFourierBasis m, thetaKernelOperator_unitFourierBasis_ae hn] with t h1 h2
    rw [h1, h2, RCLike.inner_apply, conj_fourierMode]
    have hsplit : fourierMode (n - m) t = fourierMode (-m) t * fourierMode n t := by
      rw [show n - m = -m + n by ring, fourierMode_add]
    rw [hsplit]
    have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn
    have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    push_cast
    field_simp
    ring
  rw [integral_congr_ae hpt, integral_const_mul, unitIntervalMeasure_eq,
    integral_sub (integrableOn_thetaQuantileSpeed_mul_one_sub_fourierMode (-m))
      (integrableOn_thetaQuantileSpeed_mul_one_sub_fourierMode (n - m)),
    integral_thetaQuantileSpeed_mul_one_sub_fourierMode, integral_thetaQuantileSpeed_mul_one_sub_fourierMode,
    cdfAction_neg]
  push_cast
  field_simp

/-! ## The mean-zero compression `D = P B P` -/

local notation "ThetaL2" => Lp ℂ 2 unitIntervalMeasure

/-- The constant mode `e = e_0`. -/
abbrev constMode : ThetaL2 := unitFourierBasis 0

/-- The mean-zero subspace `e⊥`. -/
abbrev meanZeroSpace : Submodule ℂ ThetaL2 := (ℂ ∙ constMode)ᗮ

/-- The mean-zero projection `P`. -/
def meanZeroProj : ThetaL2 →L[ℂ] ThetaL2 := meanZeroSpace.starProjection

/-- The divisor-bearing compression `D = P B P` of the theta source inverse. -/
def thetaQuotientOperator : ThetaL2 →L[ℂ] ThetaL2 :=
  meanZeroProj ∘L thetaKernelOperator ∘L meanZeroProj

theorem unitFourierBasis_mem_meanZeroSpace {n : ℤ} (hn : n ≠ 0) : unitFourierBasis n ∈ meanZeroSpace :=
  Submodule.mem_orthogonal_singleton_iff_inner_right.2
    (unitFourierBasis.orthonormal.2 (Ne.symm hn : (0 : ℤ) ≠ n))

theorem meanZeroProj_unitFourierBasis {n : ℤ} (hn : n ≠ 0) : meanZeroProj (unitFourierBasis n) = unitFourierBasis n :=
  Submodule.starProjection_eq_self_iff.2 (unitFourierBasis_mem_meanZeroSpace hn)

theorem meanZeroProj_apply (x : ThetaL2) :
    meanZeroProj x = x - ⟪constMode, x⟫_ℂ • constMode := by
  rw [meanZeroProj, Submodule.starProjection_orthogonal_val, Submodule.starProjection_singleton,
    unitFourierBasis.orthonormal.1 0]
  simp

theorem thetaKernelOperator_meanZeroProj (x : ThetaL2) :
    thetaKernelOperator (meanZeroProj x) = thetaKernelOperator x := by
  rw [meanZeroProj_apply, map_sub, map_smul, thetaKernelOperator_unitFourierBasis_zero, smul_zero,
    sub_zero]

theorem thetaQuotientOperator_apply (x : ThetaL2) :
    thetaQuotientOperator x = meanZeroProj (thetaKernelOperator x) := by
  rw [thetaQuotientOperator, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    thetaKernelOperator_meanZeroProj]

theorem thetaQuotientOperator_constMode : thetaQuotientOperator constMode = 0 := by
  rw [thetaQuotientOperator_apply, thetaKernelOperator_unitFourierBasis_zero, map_zero]

theorem isCompactOperator_thetaQuotientOperator : IsCompactOperator thetaQuotientOperator :=
  (isCompactOperator_thetaKernelOperator.comp_clm meanZeroProj).clm_comp meanZeroProj

/-- The matrix of `D` on nonzero modes is the CDF-action matrix. -/
theorem inner_unitFourierBasis_thetaQuotientOperator {m n : ℤ} (hm : m ≠ 0) (hn : n ≠ 0) :
    ⟪unitFourierBasis m, thetaQuotientOperator (unitFourierBasis n)⟫_ℂ =
      ((cdfAction m - cdfAction (n - m)) / (2 * Real.pi * n) : ℝ) := by
  rw [thetaQuotientOperator_apply, meanZeroProj, ← Submodule.inner_starProjection_left_eq_right,
    ← meanZeroProj, meanZeroProj_unitFourierBasis hm, inner_unitFourierBasis_thetaKernelOperator m hn]

/-! ## Generalized eigenspaces of `B` and `D` -/

open Module

/-- A generalized eigenvector killed by `f` vanishes when `μ ≠ 0`. -/
theorem eq_zero_of_mem_maxGenEigenspace_of_apply_eq_zero {M : Type*} [AddCommGroup M] [Module ℂ M]
    {f : Module.End ℂ M} {μ : ℂ} (hμ : μ ≠ 0) {x : M} (hx : x ∈ f.maxGenEigenspace μ) (hfx : f x = 0) :
    x = 0 := by
  obtain ⟨k, hk⟩ := (Module.End.mem_maxGenEigenspace _ _ _).1 hx
  have hpow : ∀ j, ((f - μ • 1) ^ j) x = (-μ) ^ j • x := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      rw [pow_succ', Module.End.mul_apply, ih, map_smul, LinearMap.sub_apply, hfx, LinearMap.smul_apply,
        Module.End.one_apply, zero_sub, smul_neg, ← neg_smul, smul_smul, pow_succ', neg_mul]
      simp [mul_comm]
  rw [hpow k] at hk
  exact (smul_eq_zero.1 hk).resolve_left (pow_ne_zero _ (neg_ne_zero.2 hμ))

/-- Intertwined generalized eigenspaces: if `a f = g a`, then `a` maps `G(f, μ)` into `G(g, μ)`. -/
theorem map_mem_maxGenEigenspace_of_comm {M : Type*} [AddCommGroup M] [Module ℂ M]
    {f g a : Module.End ℂ M} (hcomm : a * f = g * a) {μ : ℂ} {x : M} (hx : x ∈ f.maxGenEigenspace μ) :
    a x ∈ g.maxGenEigenspace μ := by
  obtain ⟨k, hk⟩ := (Module.End.mem_maxGenEigenspace _ _ _).1 hx
  refine (Module.End.mem_maxGenEigenspace _ _ _).2 ⟨k, ?_⟩
  have h1 : a * (f - μ • 1) = (g - μ • 1) * a := by
    rw [mul_sub, sub_mul, hcomm, mul_smul_comm, smul_mul_assoc, mul_one, one_mul]
  have hk' : ∀ j, a * (f - μ • 1) ^ j = (g - μ • 1) ^ j * a := by
    intro j
    induction j with
    | zero => simp
    | succ j ih => rw [pow_succ, ← mul_assoc, ih, mul_assoc, h1, ← mul_assoc, ← pow_succ]
  rw [← Module.End.mul_apply, ← hk' k, Module.End.mul_apply, hk, map_zero]

abbrev thetaB : Module.End ℂ ThetaL2 := ((thetaKernelOperator : ThetaL2 →L[ℂ] ThetaL2) : ThetaL2 →ₗ[ℂ] ThetaL2)
abbrev thetaD : Module.End ℂ ThetaL2 := ((thetaQuotientOperator : ThetaL2 →L[ℂ] ThetaL2) : ThetaL2 →ₗ[ℂ] ThetaL2)
abbrev thetaP : Module.End ℂ ThetaL2 := ((meanZeroProj : ThetaL2 →L[ℂ] ThetaL2) : ThetaL2 →ₗ[ℂ] ThetaL2)

theorem thetaP_mul_thetaB : thetaP * thetaB = thetaD * thetaP := by
  apply LinearMap.ext; intro x
  change meanZeroProj (thetaKernelOperator x) = thetaQuotientOperator (meanZeroProj x)
  rw [thetaQuotientOperator_apply, thetaKernelOperator_meanZeroProj]

theorem thetaB_mul_thetaD : thetaB * thetaD = thetaB * thetaB := by
  apply LinearMap.ext; intro x
  change thetaKernelOperator (thetaQuotientOperator x) = thetaKernelOperator (thetaKernelOperator x)
  rw [thetaQuotientOperator_apply, thetaKernelOperator_meanZeroProj]

/-- The generalized eigenspaces of `B` and `D` at `μ ≠ 0` have equal dimension, and `G(D, μ)` is
finite-dimensional whenever `G(B, μ)` is. -/
theorem finrank_maxGenEigenspace_thetaD_eq {μ : ℂ} (hμ : μ ≠ 0)
    [FiniteDimensional ℂ (thetaB.maxGenEigenspace μ)] :
    FiniteDimensional ℂ (thetaD.maxGenEigenspace μ) ∧
      finrank ℂ (thetaD.maxGenEigenspace μ) = finrank ℂ (thetaB.maxGenEigenspace μ) := by
  -- `B` maps `G(D, μ)` injectively into `G(B, μ)`
  set φ : thetaD.maxGenEigenspace μ →ₗ[ℂ] thetaB.maxGenEigenspace μ :=
    { toFun := fun w => ⟨thetaB w, map_mem_maxGenEigenspace_of_comm thetaB_mul_thetaD w.2⟩
      map_add' := fun a b => by ext; simp
      map_smul' := fun c a => by ext; simp }
  have hφ : Function.Injective φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro w hw
    have hBw : thetaB w = 0 := congrArg Subtype.val hw
    have hDw : thetaD w = 0 := by
      change thetaQuotientOperator w = 0
      rw [thetaQuotientOperator_apply]
      change meanZeroProj (thetaB w) = 0
      rw [hBw, map_zero]
    exact Subtype.ext (eq_zero_of_mem_maxGenEigenspace_of_apply_eq_zero hμ w.2 hDw)
  haveI : FiniteDimensional ℂ (thetaD.maxGenEigenspace μ) := Module.Finite.of_injective φ hφ
  -- `P` maps `G(B, μ)` injectively into `G(D, μ)`
  set ψ : thetaB.maxGenEigenspace μ →ₗ[ℂ] thetaD.maxGenEigenspace μ :=
    { toFun := fun v => ⟨thetaP v, map_mem_maxGenEigenspace_of_comm thetaP_mul_thetaB v.2⟩
      map_add' := fun a b => by ext; simp
      map_smul' := fun c a => by ext; simp }
  have hψ : Function.Injective ψ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v hv
    have hPv : meanZeroProj v = 0 := congrArg Subtype.val hv
    have hBv : thetaB v = 0 := by
      change thetaKernelOperator v = 0
      rw [← thetaKernelOperator_meanZeroProj, hPv, map_zero]
    exact Subtype.ext (eq_zero_of_mem_maxGenEigenspace_of_apply_eq_zero hμ v.2 hBv)
  exact ⟨inferInstance, le_antisymm (LinearMap.finrank_le_finrank_of_injective hφ)
    (LinearMap.finrank_le_finrank_of_injective hψ)⟩

theorem XiC_analyticOrderAt_ne_top (z : ℂ) : analyticOrderAt XiC z ≠ ⊤ := by
  have han : AnalyticOnNhd ℂ XiC Set.univ :=
    Complex.analyticOnNhd_univ_iff_differentiable.mpr XiC_differentiable
  apply han.analyticOrderAt_ne_top_of_isPreconnected isPreconnected_univ
    (x := 0) (y := z) (Set.mem_univ _) (Set.mem_univ _)
  rw [analyticOrderAt_eq_zero.mpr (Or.inr XiC_zero_ne)]
  exact ENat.zero_ne_top

theorem analyticOrderAt_thetaSourceEntireDet2_eq_XiC (z : ℂ) :
    analyticOrderAt thetaSourceEntireDet2 z = analyticOrderAt XiC z := by
  have h : thetaSourceEntireDet2 = (fun _ => (XiC 0)⁻¹) * XiC := by
    funext w; rw [thetaSourceEntireDet2_eq_XiC_normalized, div_eq_inv_mul, Pi.mul_apply]
  have hXi : AnalyticAt ℂ XiC z :=
    (Complex.analyticOnNhd_univ_iff_differentiable.mpr XiC_differentiable) z (Set.mem_univ _)
  have h0 : analyticOrderAt (fun _ : ℂ => (XiC 0)⁻¹) z = 0 :=
    analyticOrderAt_eq_zero.2 (Or.inr (inv_ne_zero XiC_zero_ne))
  rw [h, analyticOrderAt_mul analyticAt_const hXi, h0, zero_add]

/-- **Eigenvalues of `D` with algebraic multiplicity.**  For a zero `z` of `Ξ_C`, `−1/z` is an
eigenvalue of `D` whose generalized eigenspace is finite-dimensional of dimension the order of
the zero. -/
theorem finrank_maxGenEigenspace_thetaD_of_XiC_eq_zero {z : ℂ} (hz : XiC z = 0) :
    FiniteDimensional ℂ (thetaD.maxGenEigenspace (-z⁻¹)) ∧
      (finrank ℂ (thetaD.maxGenEigenspace (-z⁻¹)) : ℕ∞) = analyticOrderAt XiC z := by
  have hz0 : z ≠ 0 := fun h => XiC_zero_ne (h ▸ hz)
  have hdet : thetaSourceEntireDet2 z = 0 := (thetaSourceEntireDet2_eq_zero_iff_XiC_eq_zero z).2 hz
  have hB := analyticOrderAt_thetaSourceEntireDet2_eq_algebraicMultiplicity hdet
  rw [analyticOrderAt_thetaSourceEntireDet2_eq_XiC] at hB
  have hpos : 0 < finrank ℂ (thetaB.maxGenEigenspace (-z⁻¹)) := by
    have h1 : analyticOrderAt XiC z ≠ 0 := by
      rw [Ne, analyticOrderAt_eq_zero]; push Not
      exact ⟨(Complex.analyticOnNhd_univ_iff_differentiable.mpr XiC_differentiable) z (Set.mem_univ _), hz⟩
    have : (finrank ℂ (thetaB.maxGenEigenspace (-z⁻¹)) : ℕ∞) ≠ 0 := by rw [← hB]; exact h1
    exact Nat.pos_of_ne_zero (by exact_mod_cast this)
  haveI : FiniteDimensional ℂ (thetaB.maxGenEigenspace (-z⁻¹)) := Module.finite_of_finrank_pos hpos
  obtain ⟨hfin, heq⟩ := finrank_maxGenEigenspace_thetaD_eq (neg_ne_zero.2 (inv_ne_zero hz0))
  exact ⟨hfin, by rw [heq, ← hB]⟩

/-- Every nonzero generalized eigenvalue of `D` is `−1/z` for a zero `z` of `Ξ_C`. -/
theorem exists_XiC_zero_of_maxGenEigenspace_thetaD_ne_bot {μ : ℂ} (hμ : μ ≠ 0)
    (h : thetaD.maxGenEigenspace μ ≠ ⊥) : ∃ z : ℂ, XiC z = 0 ∧ μ = -z⁻¹ := by
  obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h
  have hBw : thetaB w ∈ thetaB.maxGenEigenspace μ :=
    map_mem_maxGenEigenspace_of_comm thetaB_mul_thetaD hw
  have hBw0 : thetaB w ≠ 0 := by
    intro hBw0
    apply hw0
    refine eq_zero_of_mem_maxGenEigenspace_of_apply_eq_zero hμ hw ?_
    change thetaQuotientOperator w = 0
    rw [thetaQuotientOperator_apply]
    change meanZeroProj (thetaB w) = 0
    rw [hBw0, map_zero]
  obtain ⟨k, hk⟩ := (Module.End.mem_maxGenEigenspace _ _ _).1 hBw
  have hgen : thetaB.HasGenEigenvalue μ k :=
    (Submodule.ne_bot_iff _).2 ⟨thetaB w, Module.End.mem_genEigenspace_nat.2 (LinearMap.mem_ker.2 hk),
      hBw0⟩
  have heig := Module.End.hasEigenvalue_of_hasGenEigenvalue hgen
  have hspec := (isCompactOperator_thetaKernelOperator.hasEigenvalue_iff_mem_spectrum hμ).1 heig
  exact (thetaKernelOperator_mem_spectrum_iff_exists_XiC_zero hμ).1 hspec

end

end RHTower
