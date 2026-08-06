import GaloisForLFunctions.RHTower.BurnolSoninEvaluationAperture
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.Fourier.PoissonSummation
import GaloisForLFunctions.HTGeometry.BarnesMellinRepresentation

/-!
# Gaussian smoothing and the archimedean Mellin--Fourier exchange

The completed Mellin evaluator factors through the Gaussian smoothing family

`G f u = ∫_ℝ f t exp (-π u t²) dt`,

because the Gamma integral resolves the power weight:

`π^(-w/2) Γ(w/2) t^(-w) = ∫_0^∞ u^(w/2-1) exp (-π u t²) du`.

Under the Fourier transform the smoothing family obeys the exact inversion law

`G (𝓕 f) u = u^(-1/2) G f (1/u)`,

which is the multiplication formula against the self-dual Gaussian.  Together these two facts are
the analytic content of the archimedean functional equation relating the completed Mellin transform
of `f` at `w` to that of `𝓕 f` at `1 - w`.
-/

open Complex Real MeasureTheory Set Filter Topology
open scoped FourierTransform RealInnerProductSpace

noncomputable section

namespace RHTower

/-- Gaussian smoothing of a function on the line at scale `u`. -/
def gaussianSmoothing (f : ℝ → ℂ) (u : ℝ) : ℂ :=
  ∫ t : ℝ, f t * Complex.exp (-(Real.pi : ℂ) * (u : ℂ) * (t : ℂ) ^ 2)

theorem integrable_gaussianKernel {u : ℝ} (hu : 0 < u) :
    Integrable fun t : ℝ => Complex.exp (-(Real.pi : ℂ) * (u : ℂ) * (t : ℂ) ^ 2) := by
  have hb : 0 < ((Real.pi : ℂ) * (u : ℂ)).re := by
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
    have := Real.pi_pos
    nlinarith
  have := integrable_cexp_neg_mul_sq hb
  refine this.congr ?_
  filter_upwards with t
  congr 1
  ring

theorem fourier_gaussianKernel {u : ℝ} (hu : 0 < u) :
    (𝓕 fun t : ℝ => Complex.exp (-(Real.pi : ℂ) * (u : ℂ) * (t : ℂ) ^ 2)) =
      fun t : ℝ => 1 / (u : ℂ) ^ (1 / 2 : ℂ) *
        Complex.exp (-(Real.pi : ℂ) / (u : ℂ) * (t : ℂ) ^ 2) := by
  have hb : 0 < ((u : ℂ)).re := by simpa using hu
  exact fourier_gaussian_pi hb

/-- **Multiplication formula against the Gaussian.**  Gaussian smoothing of the Fourier transform
is the reciprocal-scale smoothing of the function itself. -/
theorem gaussianSmoothing_fourier {f : ℝ → ℂ} (hf : Integrable f) {u : ℝ} (hu : 0 < u) :
    gaussianSmoothing (𝓕 f) u =
      1 / (u : ℂ) ^ (1 / 2 : ℂ) * gaussianSmoothing f u⁻¹ := by
  have hg : Integrable fun t : ℝ => Complex.exp (-(Real.pi : ℂ) * (u : ℂ) * (t : ℂ) ^ 2) :=
    integrable_gaussianKernel hu
  have hflip := (VectorFourier.integral_fourierIntegral_smul_eq_flip (L := innerₗ ℝ)
    Real.continuous_fourierChar continuous_inner hf hg)
  have hkey : (∫ ξ : ℝ, (𝓕 f) ξ * Complex.exp (-(Real.pi : ℂ) * (u : ℂ) * (ξ : ℂ) ^ 2)) =
      ∫ x : ℝ, f x *
        (𝓕 fun t : ℝ => Complex.exp (-(Real.pi : ℂ) * (u : ℂ) * (t : ℂ) ^ 2)) x := by
    simpa [smul_eq_mul] using! hflip
  rw [gaussianSmoothing, hkey, fourier_gaussianKernel hu, gaussianSmoothing,
    ← integral_const_mul]
  refine integral_congr_ae ?_
  filter_upwards with x
  have huinv : ((u⁻¹ : ℝ) : ℂ) = ((u : ℂ))⁻¹ := by push_cast; ring
  rw [huinv]
  have hne : (u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hu)
  have hexp : -(Real.pi : ℂ) / (u : ℂ) * (x : ℂ) ^ 2 =
      -(Real.pi : ℂ) * ((u : ℂ))⁻¹ * (x : ℂ) ^ 2 := by
    field_simp
  rw [hexp]
  ring


/-! ## The Gamma resolution of the power weight -/

private theorem re_div_two (w : ℂ) : (w / 2).re = w.re / 2 := by
  simp

/-- **Gamma resolution of the completed power weight.**  The completed Mellin weight is the Gamma
integral of the Gaussian family. -/
theorem integral_Ioi_gaussianPower {w : ℂ} (hw : 0 < w.re) {t : ℝ} (ht : 0 < t) :
    (∫ u in Ioi (0 : ℝ), (u : ℂ) ^ (w / 2 - 1) *
        Complex.exp (-(Real.pi : ℂ) * (u : ℂ) * (t : ℂ) ^ 2)) =
      mellinCompletionFactor w * (t : ℂ) ^ (-w) := by
  have hr : 0 < Real.pi * t ^ 2 := by positivity
  have ha : 0 < (w / 2).re := by
    rw [re_div_two]
    linarith
  have hcalc := integral_cpow_mul_exp_neg_mul_Ioi (a := w / 2) ha hr
  have hcongr : (∫ u in Ioi (0 : ℝ), (u : ℂ) ^ (w / 2 - 1) *
      Complex.exp (-(Real.pi : ℂ) * (u : ℂ) * (t : ℂ) ^ 2)) =
      ∫ u in Ioi (0 : ℝ), (u : ℂ) ^ (w / 2 - 1) *
        Complex.exp (-(((Real.pi * t ^ 2 : ℝ) : ℂ) * (u : ℂ))) := by
    refine setIntegral_congr_fun measurableSet_Ioi ?_
    intro u _
    have hexp : -(Real.pi : ℂ) * (u : ℂ) * (t : ℂ) ^ 2 =
        -(((Real.pi * t ^ 2 : ℝ) : ℂ) * (u : ℂ)) := by
      push_cast
      ring
    dsimp only
    rw [hexp]
  rw [hcongr, hcalc, mellinCompletionFactor]
  have hpine : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt Real.pi_pos)
  have htne : ((t : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt ht)
  have hbase : ((1 / (Real.pi * t ^ 2 : ℝ) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (by positivity)
  have hlog : Real.log (1 / (Real.pi * t ^ 2)) =
      -(Real.log Real.pi) + -(2 * Real.log t) := by
    rw [one_div, Real.log_inv, Real.log_mul (ne_of_gt Real.pi_pos) (by positivity),
      Real.log_pow]
    push_cast
    ring
  have hstep : ((1 / (Real.pi * t ^ 2 : ℝ) : ℝ) : ℂ) ^ (w / 2) =
      (Real.pi : ℂ) ^ (-w / 2) * ((t : ℝ) : ℂ) ^ (-w) := by
    rw [Complex.cpow_def_of_ne_zero hbase, Complex.cpow_def_of_ne_zero hpine,
      Complex.cpow_def_of_ne_zero htne, ← Complex.exp_add,
      ← Complex.ofReal_log (by positivity), ← Complex.ofReal_log Real.pi_pos.le,
      ← Complex.ofReal_log ht.le, hlog]
    congr 1
    push_cast
    ring
  rw [show ((1 : ℂ) / ((Real.pi * t ^ 2 : ℝ) : ℂ)) =
      ((1 / (Real.pi * t ^ 2 : ℝ) : ℝ) : ℂ) from by push_cast; ring, hstep]
  ring


/-! ## Even carriers -/

theorem gaussianKernel_ofReal (u t : ℝ) :
    Complex.exp (-(Real.pi : ℂ) * (u : ℂ) * (t : ℂ) ^ 2) =
      ((Real.exp (-(Real.pi * u * t ^ 2)) : ℝ) : ℂ) := by
  rw [show (-(Real.pi : ℂ) * (u : ℂ) * (t : ℂ) ^ 2)
      = ((-(Real.pi * u * t ^ 2) : ℝ) : ℂ) from by push_cast; ring,
    ← Complex.ofReal_exp]

theorem norm_gaussianKernel_le_one {u : ℝ} (hu : 0 ≤ u) (t : ℝ) :
    ‖Complex.exp (-(Real.pi : ℂ) * (u : ℂ) * (t : ℂ) ^ 2)‖ ≤ 1 := by
  rw [gaussianKernel_ofReal, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]
  refine Real.exp_le_one_iff.mpr ?_
  have : 0 ≤ Real.pi * u * t ^ 2 := by positivity
  linarith

theorem integrable_mul_gaussianKernel {f : ℝ → ℂ} (hf : Integrable f) {u : ℝ} (hu : 0 ≤ u) :
    Integrable fun t : ℝ => f t * Complex.exp (-(Real.pi : ℂ) * (u : ℂ) * (t : ℂ) ^ 2) := by
  refine hf.norm.mono' ?_ ?_
  · exact hf.aestronglyMeasurable.mul
      (Complex.continuous_exp.comp (by fun_prop)).aestronglyMeasurable
  · filter_upwards with t
    rw [norm_mul]
    calc ‖f t‖ * ‖Complex.exp (-(Real.pi : ℂ) * (u : ℂ) * (t : ℂ) ^ 2)‖
        ≤ ‖f t‖ * 1 := by
          exact mul_le_mul_of_nonneg_left (norm_gaussianKernel_le_one hu t) (norm_nonneg _)
      _ = ‖f t‖ := mul_one _

/-- On an even carrier the Gaussian smoothing is twice its half-line smoothing. -/
theorem gaussianSmoothing_of_even {f : ℝ → ℂ} (hf : Integrable f)
    (heven : ∀ t : ℝ, f (-t) = f t) {u : ℝ} (hu : 0 ≤ u) :
    gaussianSmoothing f u =
      2 * ∫ t in Ioi (0 : ℝ), f t * Complex.exp (-(Real.pi : ℂ) * (u : ℂ) * (t : ℂ) ^ 2) := by
  set h : ℝ → ℂ :=
    fun t => f t * Complex.exp (-(Real.pi : ℂ) * (u : ℂ) * (t : ℂ) ^ 2) with hh
  have hheven : ∀ t : ℝ, h (-t) = h t := by
    intro t
    simp only [hh, heven t]
    congr 2
    push_cast
    ring
  have hint : Integrable h := integrable_mul_gaussianKernel hf hu
  have hsplit := integral_add_compl (measurableSet_Iio (a := (0 : ℝ))) hint
  rw [compl_Iio, integral_Ici_eq_integral_Ioi] at hsplit
  have hrefl : (∫ x in Iio (0 : ℝ), h x) = ∫ x in Ioi (0 : ℝ), h x := by
    have hpre : (Neg.neg : ℝ → ℝ) ⁻¹' (Ioi (0 : ℝ)) = Iio 0 := by
      ext x
      simp
    have hmp := (Measure.measurePreserving_neg (volume : Measure ℝ)).setIntegral_preimage_emb
      measurableEmbedding_neg h (Ioi (0 : ℝ))
    rw [hpre] at hmp
    rw [← hmp]
    exact setIntegral_congr_fun measurableSet_Iio fun x _ => (hheven x).symm
  rw [hrefl] at hsplit
  rw [gaussianSmoothing, ← hsplit]
  ring


/-! ## The reciprocal change of variables -/

theorem ofReal_cpow_pos {v : ℝ} (hv : 0 < v) (z : ℂ) :
    ((v : ℝ) : ℂ) ^ z = Complex.exp ((Real.log v : ℂ) * z) := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (ne_of_gt hv)),
    ← Complex.ofReal_log hv.le]

theorem ofReal_inv_sq_eq_exp {v : ℝ} (hv : 0 < v) :
    (((v ^ 2)⁻¹ : ℝ) : ℂ) = Complex.exp ((Real.log v : ℂ) * (-2)) := by
  have hreal : Real.exp (Real.log v * (-2)) = (v ^ 2)⁻¹ := by
    rw [show Real.log v * (-2) = -(2 * Real.log v) by ring, Real.exp_neg,
      show (2 : ℝ) * Real.log v = ((2 : ℕ) : ℝ) * Real.log v by norm_num,
      Real.exp_nat_mul, Real.exp_log hv]
  rw [show ((Real.log v : ℂ) * (-2)) = ((Real.log v * (-2) : ℝ) : ℂ) by push_cast; ring,
    ← Complex.ofReal_exp, hreal]

theorem image_inv_Ioi : (fun v : ℝ => v⁻¹) '' Ioi 0 = Ioi 0 := by
  ext u
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact mem_Ioi.mpr (inv_pos.mpr (mem_Ioi.mp hv))
  · intro hu
    exact ⟨u⁻¹, mem_Ioi.mpr (inv_pos.mpr (mem_Ioi.mp hu)), inv_inv u⟩

theorem injOn_inv_Ioi : Set.InjOn (fun v : ℝ => v⁻¹) (Ioi 0) :=
  fun _ _ _ _ h => inv_injective h

/-- **Reciprocal change of variables on the positive ray.** -/
theorem integral_Ioi_comp_inv {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (g : ℝ → F) :
    (∫ u in Ioi (0 : ℝ), g u) = ∫ v in Ioi (0 : ℝ), (v ^ 2)⁻¹ • g v⁻¹ := by
  have hderiv : ∀ v ∈ Ioi (0 : ℝ),
      HasDerivWithinAt (fun s : ℝ => s⁻¹) (-(v ^ 2)⁻¹) (Ioi 0) v := by
    intro v hv
    exact (hasDerivAt_inv (ne_of_gt (mem_Ioi.mp hv))).hasDerivWithinAt
  have h := MeasureTheory.integral_image_eq_integral_abs_deriv_smul
    measurableSet_Ioi hderiv injOn_inv_Ioi g
  rw [image_inv_Ioi] at h
  rw [h]
  refine setIntegral_congr_fun measurableSet_Ioi ?_
  intro v hv
  have hvpos : (0 : ℝ) < v := mem_Ioi.mp hv
  have habs : |-(v ^ 2)⁻¹| = (v ^ 2)⁻¹ := by
    rw [abs_neg, abs_of_pos (by positivity)]
  dsimp only
  rw [habs]

/-- **Inversion of the completed Mellin weight.**  The reciprocal substitution exchanges the
completed exponent `w` with `1 - w`. -/
theorem integral_Ioi_cpow_mul_inv (w : ℂ) (H : ℝ → ℂ) :
    (∫ u in Ioi (0 : ℝ),
        (u : ℂ) ^ (w / 2 - 1) * (1 / (u : ℂ) ^ (1 / 2 : ℂ)) * H u⁻¹) =
      ∫ v in Ioi (0 : ℝ), (v : ℂ) ^ ((1 - w) / 2 - 1) * H v := by
  rw [integral_Ioi_comp_inv
    (fun u : ℝ => (u : ℂ) ^ (w / 2 - 1) * (1 / (u : ℂ) ^ (1 / 2 : ℂ)) * H u⁻¹)]
  refine setIntegral_congr_fun measurableSet_Ioi ?_
  intro v hv
  have hvpos : (0 : ℝ) < v := mem_Ioi.mp hv
  have hvinv : (0 : ℝ) < v⁻¹ := inv_pos.mpr hvpos
  have hscalar : (((v ^ 2)⁻¹ : ℝ) : ℂ) *
      ((((v⁻¹ : ℝ)) : ℂ) ^ (w / 2 - 1) * (1 / (((v⁻¹ : ℝ)) : ℂ) ^ (1 / 2 : ℂ))) =
      ((v : ℝ) : ℂ) ^ ((1 - w) / 2 - 1) := by
    rw [ofReal_inv_sq_eq_exp hvpos, ofReal_cpow_pos hvinv, ofReal_cpow_pos hvinv,
      ofReal_cpow_pos hvpos, Real.log_inv, one_div, ← Complex.exp_neg,
      ← Complex.exp_add, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  dsimp only
  rw [inv_inv, Complex.real_smul, ← mul_assoc, hscalar]


/-! ## Integrability of the Gamma kernel -/

theorem integrableOn_rpow_mul_exp_neg_mul_Ioi {a r : ℝ} (ha : 0 < a) (hr : 0 < r) :
    IntegrableOn (fun u : ℝ => u ^ (a - 1) * Real.exp (-(r * u))) (Ioi 0) :=
  GaloisForLFunctions.HTGeometry.integrableOn_rpow_mul_exp_neg_mul_Ioi (by linarith) hr

theorem continuousOn_cpow_ofReal (z : ℂ) :
    ContinuousOn (fun u : ℝ => (u : ℂ) ^ z) (Ioi (0 : ℝ)) := by
  refine ContinuousOn.congr ?_ (fun u hu => ofReal_cpow_pos (mem_Ioi.mp hu) z)
  refine Complex.continuous_exp.comp_continuousOn ?_
  refine ContinuousOn.mul ?_ continuousOn_const
  refine Complex.continuous_ofReal.comp_continuousOn ?_
  exact Real.continuousOn_log.mono (fun u hu => ne_of_gt (mem_Ioi.mp hu))

theorem integrableOn_cpow_mul_gaussianKernel {a : ℂ} (ha : 0 < a.re) {t : ℝ} (ht : 0 < t) :
    IntegrableOn (fun u : ℝ => (u : ℂ) ^ (a - 1) *
      Complex.exp (-(Real.pi : ℂ) * (u : ℂ) * (t : ℂ) ^ 2)) (Ioi 0) := by
  have hr : 0 < Real.pi * t ^ 2 := by positivity
  refine Integrable.mono' (integrableOn_rpow_mul_exp_neg_mul_Ioi
    (by simpa using ha : 0 < a.re) hr) ?_ ?_
  · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    refine (continuousOn_cpow_ofReal (a - 1)).mul ?_
    exact (Complex.continuous_exp.comp (by fun_prop)).continuousOn
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hu0 : (0 : ℝ) < u := hu
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hu0, gaussianKernel_ofReal,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    have hre : (a - 1).re = a.re - 1 := by simp
    rw [hre]
    have harg : -(Real.pi * u * t ^ 2) = -(Real.pi * t ^ 2 * u) := by ring
    rw [harg]

/-- The real Gamma resolution of the completed power weight. -/
theorem integral_Ioi_rpow_gaussianPower {σ : ℝ} (hσ : 0 < σ) {t : ℝ} (ht : 0 < t) :
    (∫ u in Ioi (0 : ℝ), u ^ (σ / 2 - 1) * Real.exp (-(Real.pi * t ^ 2 * u))) =
      Real.Gamma (σ / 2) * (Real.pi ^ (-σ / 2) * t ^ (-σ)) := by
  have hr : 0 < Real.pi * t ^ 2 := by positivity
  have h := integral_rpow_mul_exp_neg_mul_Ioi (a := σ / 2) (r := Real.pi * t ^ 2)
    (by linarith) hr
  rw [h]
  have hbase : (1 / (Real.pi * t ^ 2)) ^ (σ / 2) =
      Real.pi ^ (-σ / 2) * t ^ (-σ) := by
    rw [one_div, ← Real.rpow_neg_one (Real.pi * t ^ 2), ← Real.rpow_mul hr.le,
      Real.mul_rpow Real.pi_pos.le (by positivity),
      show (t : ℝ) ^ (2 : ℕ) = t ^ (2 : ℝ) from (Real.rpow_natCast t 2).symm,
      ← Real.rpow_mul ht.le]
    congr 1
    · congr 1
      ring
    · congr 1
      ring
  rw [hbase]
  ring


/-! ## The Fubini interchange -/

/-- **The completed Mellin transform factors through Gaussian smoothing.**  Resolving the power
weight by the Gamma integral and interchanging the two positive rays expresses the completed Mellin
evaluation as the Mellin transform of the Gaussian smoothing family. -/
theorem mellinCompletion_eq_integral_gaussianSmoothing
    {w : ℂ} (hw : 0 < w.re) {f : ℝ → ℂ}
    (hmeas : AEStronglyMeasurable f (volume.restrict (Ioi (0 : ℝ))))
    (hint : IntegrableOn (fun t : ℝ => ‖f t‖ * t ^ (-w.re)) (Ioi 0)) :
    mellinCompletionFactor w * (∫ t in Ioi (0 : ℝ), f t * (t : ℂ) ^ (-w)) =
      ∫ u in Ioi (0 : ℝ), (u : ℂ) ^ (w / 2 - 1) *
        ∫ t in Ioi (0 : ℝ), f t *
          Complex.exp (-(Real.pi : ℂ) * (u : ℂ) * (t : ℂ) ^ 2) := by
  have hw2 : 0 < (w / 2).re := by
    rw [re_div_two]
    linarith
  set F : ℝ → ℝ → ℂ := fun t u =>
    f t * ((u : ℂ) ^ (w / 2 - 1) *
      Complex.exp (-(Real.pi : ℂ) * (u : ℂ) * (t : ℂ) ^ 2)) with hFdef
  have hker : ContinuousOn
      (fun p : ℝ × ℝ => (p.2 : ℂ) ^ (w / 2 - 1) *
        Complex.exp (-(Real.pi : ℂ) * (p.2 : ℂ) * (p.1 : ℂ) ^ 2))
      (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)) := by
    refine ContinuousOn.mul ?_ ?_
    · exact (continuousOn_cpow_ofReal (w / 2 - 1)).comp continuous_snd.continuousOn
        fun p hp => hp.2
    · exact (Complex.continuous_exp.comp (by fun_prop)).continuousOn
  have hAE : AEStronglyMeasurable (Function.uncurry F)
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) := by
    have h1 : AEStronglyMeasurable (fun p : ℝ × ℝ => f p.1)
        ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) :=
      hmeas.comp_fst
    have h2 : AEStronglyMeasurable
        (fun p : ℝ × ℝ => (p.2 : ℂ) ^ (w / 2 - 1) *
          Complex.exp (-(Real.pi : ℂ) * (p.2 : ℂ) * (p.1 : ℂ) ^ 2))
        ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) := by
      rw [Measure.prod_restrict]
      exact hker.aestronglyMeasurable (measurableSet_Ioi.prod measurableSet_Ioi)
    exact h1.mul h2
  have hslice : ∀ᵐ t ∂(volume.restrict (Ioi (0 : ℝ))),
      Integrable (fun u => F t u) (volume.restrict (Ioi (0 : ℝ))) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact (integrableOn_cpow_mul_gaussianKernel hw2 (mem_Ioi.mp ht)).const_mul (f t)
  have hnormF : ∀ t ∈ Ioi (0 : ℝ), ∀ u ∈ Ioi (0 : ℝ),
      ‖F t u‖ = ‖f t‖ * (u ^ (w.re / 2 - 1) * Real.exp (-(Real.pi * t ^ 2 * u))) := by
    intro t _ u hu
    have hu0 : (0 : ℝ) < u := hu
    rw [hFdef]
    dsimp only
    rw [norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hu0,
      gaussianKernel_ofReal, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
    have hre : (w / 2 - 1).re = w.re / 2 - 1 := by
      rw [Complex.sub_re, re_div_two]
      norm_num
    rw [hre, show -(Real.pi * u * t ^ 2) = -(Real.pi * t ^ 2 * u) from by ring]
  have hnormint : ∀ t ∈ Ioi (0 : ℝ),
      (∫ u, ‖F t u‖ ∂(volume.restrict (Ioi (0 : ℝ)))) =
        Real.Gamma (w.re / 2) * Real.pi ^ (-w.re / 2) * (‖f t‖ * t ^ (-w.re)) := by
    intro t ht
    have ht0 : (0 : ℝ) < t := ht
    rw [setIntegral_congr_fun measurableSet_Ioi (fun u hu => hnormF t ht u hu),
      integral_const_mul, integral_Ioi_rpow_gaussianPower (by linarith) ht0]
    ring
  have hbound : Integrable (fun t => ∫ u, ‖F t u‖ ∂(volume.restrict (Ioi (0 : ℝ))))
      (volume.restrict (Ioi (0 : ℝ))) := by
    have hc : IntegrableOn (fun t : ℝ =>
        Real.Gamma (w.re / 2) * Real.pi ^ (-w.re / 2) * (‖f t‖ * t ^ (-w.re))) (Ioi 0) :=
      hint.const_mul _
    refine hc.congr_fun ?_ measurableSet_Ioi
    intro t ht
    exact (hnormint t ht).symm
  have hprod : Integrable (Function.uncurry F)
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) :=
    (integrable_prod_iff hAE).mpr ⟨hslice, hbound⟩
  have hswap := integral_integral_swap hprod
  have hL : (∫ t in Ioi (0 : ℝ), ∫ u in Ioi (0 : ℝ), F t u) =
      mellinCompletionFactor w * ∫ t in Ioi (0 : ℝ), f t * (t : ℂ) ^ (-w) := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi ?_
    intro t ht
    have ht0 : (0 : ℝ) < t := ht
    dsimp only [hFdef]
    rw [integral_const_mul, integral_Ioi_gaussianPower hw ht0]
    ring
  have hR : (∫ u in Ioi (0 : ℝ), ∫ t in Ioi (0 : ℝ), F t u) =
      ∫ u in Ioi (0 : ℝ), (u : ℂ) ^ (w / 2 - 1) *
        ∫ t in Ioi (0 : ℝ), f t *
          Complex.exp (-(Real.pi : ℂ) * (u : ℂ) * (t : ℂ) ^ 2) := by
    refine setIntegral_congr_fun measurableSet_Ioi ?_
    intro u _
    dsimp only
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi ?_
    intro t _
    dsimp only [hFdef]
    ring
  rw [← hL, hswap, hR]


/-! ## The archimedean functional equation -/

theorem ofReal_inv_cpow {v : ℝ} (hv : 0 < v) (z : ℂ) :
    (((v⁻¹ : ℝ)) : ℂ) ^ z = ((v : ℝ) : ℂ) ^ (-z) := by
  rw [ofReal_cpow_pos (inv_pos.mpr hv), ofReal_cpow_pos hv, Real.log_inv]
  congr 1
  push_cast
  ring

/-- The Fourier transform of an even function is even. -/
theorem fourier_even_of_even {f : ℝ → ℂ} (heven : ∀ t : ℝ, f (-t) = f t) (ξ : ℝ) :
    (𝓕 f) (-ξ) = (𝓕 f) ξ := by
  have h := (Measure.measurePreserving_neg (volume : Measure ℝ)).integral_comp
    measurableEmbedding_neg (fun v : ℝ => Real.fourierChar (-(inner ℝ v ξ)) • f v)
  rw [Real.fourier_eq, Real.fourier_eq, ← h]
  refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
  show (Real.fourierChar (-(inner ℝ v (-ξ))) • f v) =
    Real.fourierChar (-(inner ℝ (-v) ξ)) • f (-v)
  rw [heven v, inner_neg_left, inner_neg_right]

/-- **The archimedean functional equation.**  For an even integrable function with integrable
Fourier transform, the completed Mellin evaluation at `w` agrees with that of the Fourier transform
at `1 - w`. -/
theorem soninMellinEvaluation_fourier
    {w : ℂ} (hlo : 0 < w.re) (hhi : w.re < 1) {f : ℝ → ℂ}
    (hf : Integrable f) (hFf : Integrable (𝓕 f)) (heven : ∀ t : ℝ, f (-t) = f t)
    (hint : IntegrableOn (fun t : ℝ => ‖f t‖ * t ^ (-w.re)) (Ioi 0))
    (hFint : IntegrableOn (fun t : ℝ => ‖(𝓕 f) t‖ * t ^ (-(1 - w).re)) (Ioi 0)) :
    soninMellinEvaluation w f = soninMellinEvaluation (1 - w) (𝓕 f) := by
  have hw1 : 0 < (1 - w).re := by
    rw [Complex.sub_re, Complex.one_re]
    linarith
  have hmeas : AEStronglyMeasurable f (volume.restrict (Ioi (0 : ℝ))) :=
    hf.aestronglyMeasurable.restrict
  have hFmeas : AEStronglyMeasurable (𝓕 f) (volume.restrict (Ioi (0 : ℝ))) :=
    hFf.aestronglyMeasurable.restrict
  have hFeven : ∀ t : ℝ, (𝓕 f) (-t) = (𝓕 f) t := fourier_even_of_even heven
  have hhalf : ∀ u : ℝ, 0 < u →
      (∫ t in Ioi (0 : ℝ), f t *
          Complex.exp (-(Real.pi : ℂ) * (u : ℂ) * (t : ℂ) ^ 2)) =
        1 / (u : ℂ) ^ (1 / 2 : ℂ) *
          ∫ t in Ioi (0 : ℝ), (𝓕 f) t *
            Complex.exp (-(Real.pi : ℂ) * ((u⁻¹ : ℝ) : ℂ) * (t : ℂ) ^ 2) := by
    intro u hu
    have huinv : (0 : ℝ) < u⁻¹ := inv_pos.mpr hu
    have h1 := gaussianSmoothing_of_even hf heven hu.le
    have h2 := gaussianSmoothing_of_even hFf hFeven huinv.le
    have h3 := gaussianSmoothing_fourier hf huinv
    rw [inv_inv] at h3
    -- h3 : gaussianSmoothing (𝓕 f) u⁻¹ = 1/((u⁻¹ : ℝ) : ℂ)^(1/2) * gaussianSmoothing f u
    have hfac : ((1 : ℂ) / (((u⁻¹ : ℝ)) : ℂ) ^ (1 / 2 : ℂ))⁻¹ =
        1 / ((u : ℝ) : ℂ) ^ (1 / 2 : ℂ) := by
      rw [ofReal_inv_cpow hu, Complex.cpow_neg]
      simp
    have hne : (((u⁻¹ : ℝ)) : ℂ) ^ (1 / 2 : ℂ) ≠ 0 := by
      rw [ofReal_cpow_pos huinv]
      exact Complex.exp_ne_zero _
    have hsolve : gaussianSmoothing f u =
        1 / ((u : ℝ) : ℂ) ^ (1 / 2 : ℂ) * gaussianSmoothing (𝓕 f) u⁻¹ := by
      rw [h3, ← hfac, inv_mul_cancel_left₀ (one_div_ne_zero hne)]
    rw [h1, h2] at hsolve
    linear_combination hsolve / 2
  have hA : soninMellinEvaluation w f =
      ∫ u in Ioi (0 : ℝ), (u : ℂ) ^ (w / 2 - 1) *
        ∫ t in Ioi (0 : ℝ), f t *
          Complex.exp (-(Real.pi : ℂ) * (u : ℂ) * (t : ℂ) ^ 2) := by
    rw [soninMellinEvaluation]
    simp only [soninMellinKernel]
    exact mellinCompletion_eq_integral_gaussianSmoothing hlo hmeas hint
  have hB : soninMellinEvaluation (1 - w) (𝓕 f) =
      ∫ v in Ioi (0 : ℝ), (v : ℂ) ^ ((1 - w) / 2 - 1) *
        ∫ t in Ioi (0 : ℝ), (𝓕 f) t *
          Complex.exp (-(Real.pi : ℂ) * (v : ℂ) * (t : ℂ) ^ 2) := by
    rw [soninMellinEvaluation]
    simp only [soninMellinKernel]
    exact mellinCompletion_eq_integral_gaussianSmoothing hw1 hFmeas hFint
  have hsub := integral_Ioi_cpow_mul_inv w
    (fun v : ℝ => ∫ t in Ioi (0 : ℝ), (𝓕 f) t *
      Complex.exp (-(Real.pi : ℂ) * (v : ℂ) * (t : ℂ) ^ 2))
  rw [hA, hB, ← hsub]
  refine setIntegral_congr_fun measurableSet_Ioi ?_
  intro u hu
  dsimp only
  rw [hhalf u (mem_Ioi.mp hu)]
  ring


/-- **Reflected aperture bound.**  Below the critical line the completed Mellin evaluator obeys the
aperture bound with the reflected constant `C(1-w)` and the reflected exponent `A^(Re w - 1/2)`, by
transporting the ambient estimate across the archimedean functional equation. -/
theorem norm_soninMellinEvaluation_le_aperture_reflected
    {w : ℂ} (hlo : 0 < w.re) (hhi : w.re < 1 / 2) {A : ℝ} (hA : 0 < A)
    {f : ℝ → ℂ} (hf : Integrable f) (hFf : Integrable (𝓕 f))
    (heven : ∀ t : ℝ, f (-t) = f t)
    (hint : IntegrableOn (fun t : ℝ => ‖f t‖ * t ^ (-w.re)) (Ioi 0))
    (hFint : IntegrableOn (fun t : ℝ => ‖(𝓕 f) t‖ * t ^ (-(1 - w).re)) (Ioi 0))
    (hFmem : MemLp (𝓕 f) 2 (volume.restrict (Ioi (0 : ℝ))))
    (hFhead : SoninHeadConstant A (𝓕 f)) :
    ‖soninMellinEvaluation w f‖ ≤
      soninApertureConstant (1 - w) * A ^ (w.re - 1 / 2) * ‖hFmem.toLp _‖ := by
  have hre : (1 - w).re = 1 - w.re := by
    rw [Complex.sub_re, Complex.one_re]
  have h1 : 1 / 2 < (1 - w).re := by
    rw [hre]
    linarith
  have h2 : (1 - w).re < 1 := by
    rw [hre]
    linarith
  rw [soninMellinEvaluation_fourier hlo (by linarith) hf hFf heven hint hFint]
  have hbound := norm_soninMellinEvaluation_le_soninApertureConstant h1 h2 hA hFmem hFhead
  rwa [show (1 : ℝ) / 2 - (1 - w).re = w.re - 1 / 2 from by rw [hre]; ring] at hbound


/-! ## Even Poisson summation -/

/-- **Poisson summation for an even Schwartz function.**  Folding the integer lattice onto the
positive half turns Poisson summation into a statement about half-line sums with an explicit
central term.  This is the form used by the co-Poisson intertwining. -/
theorem even_poisson_summation (f : SchwartzMap ℝ ℂ)
    (heven : ∀ x : ℝ, f (-x) = f x)
    (hsum : Summable fun n : ℕ => f ((n : ℝ) + 1))
    (hsumF : Summable fun n : ℕ => (𝓕 (f : ℝ → ℂ)) ((n : ℝ) + 1)) :
    f 0 + 2 * ∑' n : ℕ, f ((n : ℝ) + 1) =
      (𝓕 (f : ℝ → ℂ)) 0 + 2 * ∑' n : ℕ, (𝓕 (f : ℝ → ℂ)) ((n : ℝ) + 1) := by
  have hFeven : ∀ x : ℝ, (𝓕 (f : ℝ → ℂ)) (-x) = (𝓕 (f : ℝ → ℂ)) x :=
    fourier_even_of_even heven
  have hcast : ∀ n : ℕ, (((n : ℤ) + 1 : ℤ) : ℝ) = (n : ℝ) + 1 := by
    intro n
    push_cast
    ring
  have hcastneg : ∀ n : ℕ, ((-((n : ℤ) + 1) : ℤ) : ℝ) = -((n : ℝ) + 1) := by
    intro n
    push_cast
    ring
  -- the two half-line families are summable in the integer parametrization
  have hsum1 : Summable fun n : ℕ => f ((((n : ℤ) + 1 : ℤ) : ℝ)) := by
    refine hsum.congr fun n => ?_
    rw [hcast n]
  have hsum2 : Summable fun n : ℕ => f (((-((n : ℤ) + 1) : ℤ) : ℝ)) := by
    refine hsum.congr fun n => ?_
    rw [hcastneg n, heven]
  have hsumF1 : Summable fun n : ℕ => (𝓕 (f : ℝ → ℂ)) ((((n : ℤ) + 1 : ℤ) : ℝ)) := by
    refine hsumF.congr fun n => ?_
    rw [hcast n]
  have hsumF2 : Summable fun n : ℕ => (𝓕 (f : ℝ → ℂ)) (((-((n : ℤ) + 1) : ℤ) : ℝ)) := by
    refine hsumF.congr fun n => ?_
    rw [hcastneg n, hFeven]
  have hsplit := tsum_of_add_one_of_neg_add_one (f := fun n : ℤ => f ((n : ℝ))) hsum1 hsum2
  have hsplitF :=
    tsum_of_add_one_of_neg_add_one (f := fun n : ℤ => (𝓕 (f : ℝ → ℂ)) ((n : ℝ))) hsumF1 hsumF2
  have hpoisson := SchwartzMap.tsum_eq_tsum_fourier f 0
  have hfz : ∀ n : ℤ, (fourier n) (((0 : ℝ) : UnitAddCircle)) = 1 := by
    intro n
    simp
  simp only [zero_add, hfz, mul_one, SchwartzMap.fourier_coe] at hpoisson
  rw [hsplit, hsplitF] at hpoisson
  have hL : (∑' n : ℕ, f ((((n : ℤ) + 1 : ℤ) : ℝ))) = ∑' n : ℕ, f ((n : ℝ) + 1) :=
    tsum_congr fun n => by rw [hcast n]
  have hL' : (∑' n : ℕ, f (((-((n : ℤ) + 1) : ℤ) : ℝ))) = ∑' n : ℕ, f ((n : ℝ) + 1) :=
    tsum_congr fun n => by rw [hcastneg n, heven]
  have hR : (∑' n : ℕ, (𝓕 (f : ℝ → ℂ)) ((((n : ℤ) + 1 : ℤ) : ℝ))) =
      ∑' n : ℕ, (𝓕 (f : ℝ → ℂ)) ((n : ℝ) + 1) :=
    tsum_congr fun n => by rw [hcast n]
  have hR' : (∑' n : ℕ, (𝓕 (f : ℝ → ℂ)) (((-((n : ℤ) + 1) : ℤ) : ℝ))) =
      ∑' n : ℕ, (𝓕 (f : ℝ → ℂ)) ((n : ℝ) + 1) :=
    tsum_congr fun n => by rw [hcastneg n, hFeven]
  rw [hL, hL', hR, hR'] at hpoisson
  push_cast at hpoisson
  linear_combination hpoisson


/-- **Fourier dilation rule.**  Compressing the argument by `c > 0` dilates the transform and scales
it by `1/c`. -/
theorem fourier_comp_mul_left {c : ℝ} (hc : 0 < c) (f : ℝ → ℂ) (w : ℝ) :
    (𝓕 fun v : ℝ => f (c * v)) w = (c : ℂ)⁻¹ • (𝓕 f) (w / c) := by
  have hcne : c ≠ 0 := ne_of_gt hc
  have harg : ∀ v : ℝ, (inner ℝ v w : ℝ) = inner ℝ (c * v) (w / c) := by
    intro v
    simp only [RCLike.inner_apply, conj_trivial]
    field_simp
  have hrewrite : ∀ v : ℝ,
      Real.fourierChar (-(inner ℝ v w)) • f (c * v) =
        (fun u : ℝ => Real.fourierChar (-(inner ℝ u (w / c))) • f u) (c * v) := by
    intro v
    rw [harg v]
  rw [Real.fourier_eq, Real.fourier_eq]
  simp only [hrewrite]
  rw [MeasureTheory.Measure.integral_comp_mul_left
      (fun u : ℝ => Real.fourierChar (-(inner ℝ u (w / c))) • f u) c,
    abs_of_pos (inv_pos.mpr hc), Complex.real_smul, Complex.ofReal_inv, smul_eq_mul]


/-! ## Dilated even Poisson summation -/

/-- Scalar dilation of the line as a continuous linear equivalence. -/
def realDilationEquiv {c : ℝ} (hc : c ≠ 0) : ℝ ≃L[ℝ] ℝ where
  toFun v := c * v
  invFun v := c⁻¹ * v
  map_add' x y := by ring
  map_smul' m x := by
    simp only [smul_eq_mul, RingHom.id_apply]
    ring
  left_inv v := by
    field_simp
  right_inv v := by
    field_simp
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

@[simp] theorem realDilationEquiv_apply {c : ℝ} (hc : c ≠ 0) (v : ℝ) :
    realDilationEquiv hc v = c * v := rfl

/-- The dilated Schwartz function `v ↦ f (c v)`. -/
def schwartzDilate (f : SchwartzMap ℝ ℂ) {c : ℝ} (hc : c ≠ 0) : SchwartzMap ℝ ℂ :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (realDilationEquiv hc) f

@[simp] theorem schwartzDilate_apply (f : SchwartzMap ℝ ℂ) {c : ℝ} (hc : c ≠ 0) (v : ℝ) :
    schwartzDilate f hc v = f (c * v) := rfl

/-- **Dilated even Poisson summation.**  Carrying the scale through the folded identity gives the
multiplicative form used by the co-Poisson intertwining. -/
theorem even_poisson_summation_dilate (f : SchwartzMap ℝ ℂ)
    (heven : ∀ x : ℝ, f (-x) = f x) {c : ℝ} (hc : 0 < c)
    (hsum : Summable fun n : ℕ => f (c * ((n : ℝ) + 1)))
    (hsumF : Summable fun n : ℕ => (𝓕 (f : ℝ → ℂ)) (((n : ℝ) + 1) / c)) :
    f 0 + 2 * ∑' n : ℕ, f (c * ((n : ℝ) + 1)) =
      (c : ℂ)⁻¹ *
        ((𝓕 (f : ℝ → ℂ)) 0 + 2 * ∑' n : ℕ, (𝓕 (f : ℝ → ℂ)) (((n : ℝ) + 1) / c)) := by
  have hcne : c ≠ 0 := ne_of_gt hc
  set g : SchwartzMap ℝ ℂ := schwartzDilate f hcne with hg
  have hgcoe : (g : ℝ → ℂ) = fun v : ℝ => f (c * v) := rfl
  have hgeven : ∀ x : ℝ, g (-x) = g x := by
    intro x
    show f (c * -x) = f (c * x)
    rw [show c * -x = -(c * x) from by ring, heven]
  have hgfourier : ∀ w : ℝ, (𝓕 (g : ℝ → ℂ)) w = (c : ℂ)⁻¹ * (𝓕 (f : ℝ → ℂ)) (w / c) := by
    intro w
    rw [hgcoe, fourier_comp_mul_left hc, smul_eq_mul]
  have hgsum : Summable fun n : ℕ => g ((n : ℝ) + 1) := hsum
  have hgsumF : Summable fun n : ℕ => (𝓕 (g : ℝ → ℂ)) ((n : ℝ) + 1) := by
    refine (hsumF.mul_left ((c : ℂ)⁻¹)).congr fun n => ?_
    rw [hgfourier]
  have hmain := even_poisson_summation g hgeven hgsum hgsumF
  have hg0 : g 0 = f 0 := by
    show f (c * 0) = f 0
    rw [mul_zero]
  have hgf0 : (𝓕 (g : ℝ → ℂ)) 0 = (c : ℂ)⁻¹ * (𝓕 (f : ℝ → ℂ)) 0 := by
    rw [hgfourier, zero_div]
  have hgtsum : (∑' n : ℕ, (𝓕 (g : ℝ → ℂ)) ((n : ℝ) + 1)) =
      (c : ℂ)⁻¹ * ∑' n : ℕ, (𝓕 (f : ℝ → ℂ)) (((n : ℝ) + 1) / c) := by
    rw [← tsum_mul_left]
    exact tsum_congr fun n => hgfourier _
  have hgtsumL : (∑' n : ℕ, g ((n : ℝ) + 1)) = ∑' n : ℕ, f (c * ((n : ℝ) + 1)) := rfl
  rw [hg0, hgf0, hgtsum, hgtsumL] at hmain
  rw [hmain]
  ring


/-! ## The co-Poisson intertwining -/

/-- The corrected co-Poisson sum of a Schwartz function at scale `c`: the multiplicative sum with
its two archimedean correction terms. -/
def coPoissonCorrected (f : SchwartzMap ℝ ℂ) (c : ℝ) : ℂ :=
  (∑' n : ℕ, f (c * ((n : ℝ) + 1))) + f 0 / 2 - (𝓕 (f : ℝ → ℂ)) 0 / (2 * c)

/-- **Co-Poisson intertwining.**  The corrected co-Poisson sum of `f` at scale `c`, rescaled by `c`,
is the uncorrected co-Poisson sum of the Fourier transform at the reciprocal scale.  This is the
exact form in which Poisson summation intertwines the multiplicative sum with the Fourier
transform. -/
theorem coPoisson_intertwine (f : SchwartzMap ℝ ℂ)
    (heven : ∀ x : ℝ, f (-x) = f x) {c : ℝ} (hc : 0 < c)
    (hsum : Summable fun n : ℕ => f (c * ((n : ℝ) + 1)))
    (hsumF : Summable fun n : ℕ => (𝓕 (f : ℝ → ℂ)) (((n : ℝ) + 1) / c)) :
    (c : ℂ) * coPoissonCorrected f c =
      ∑' k : ℕ, (𝓕 (f : ℝ → ℂ)) (((k : ℝ) + 1) / c) := by
  have hcne : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hc)
  have hdilate := even_poisson_summation_dilate f heven hc hsum hsumF
  have hd : (c : ℂ) * (f 0 + 2 * ∑' n : ℕ, f (c * ((n : ℝ) + 1))) =
      (𝓕 (f : ℝ → ℂ)) 0 + 2 * ∑' n : ℕ, (𝓕 (f : ℝ → ℂ)) (((n : ℝ) + 1) / c) := by
    rw [hdilate, ← mul_assoc, mul_inv_cancel₀ hcne, one_mul]
  rw [coPoissonCorrected]
  field_simp
  linear_combination hd

end RHTower
