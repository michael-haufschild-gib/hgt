import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.MeanInequalities

/-!
# Aperture bound for the completed Mellin evaluator on a constant head

For `f` in `L²((0,∞),dt)` which is almost everywhere constant on the aperture head `(0,A)`, the
completed right Mellin evaluation

`M f w = γ w * ∫_0^∞ f t * t^(-w) dt`,   `γ w = π^(-w/2) Γ(w/2)`,

is finite and obeys the exact aperture estimate

`‖M f w‖ ≤ ‖γ w‖ * (1/‖1-w‖ + 1/sqrt (2 Re w - 1)) * A^(1/2 - Re w) * ‖f‖`

for `1/2 < Re w < 1`.  The head contributes the explicit primitive `A^(1-w)/(1-w)` scaled by the
constant value, whose modulus is controlled by `‖c‖ sqrt A ≤ ‖f‖`, and the tail contributes the
Cauchy--Schwarz factor `(∫_A^∞ t^(-2 Re w) dt)^(1/2) = A^(1/2 - Re w)/sqrt (2 Re w - 1)`.

The exponent `1/2 - Re w` is the negative of the horizontal displacement `|Re w - 1/2|`, which is
the aperture exponent of the evaluator.
-/

open Complex Real MeasureTheory Set Filter Topology

noncomputable section

namespace RHTower

/-- The Gamma completion factor of the right Mellin transform. -/
def mellinCompletionFactor (w : ℂ) : ℂ :=
  (Real.pi : ℂ) ^ (-w / 2) * Complex.Gamma (w / 2)

/-- The right Mellin kernel `t ↦ t^(-w)` on the positive ray. -/
def soninMellinKernel (w : ℂ) (t : ℝ) : ℂ := (t : ℂ) ^ (-w)

/-- The completed right Mellin evaluation. -/
def soninMellinEvaluation (w : ℂ) (f : ℝ → ℂ) : ℂ :=
  mellinCompletionFactor w * ∫ t in Ioi (0 : ℝ), f t * soninMellinKernel w t

/-- A vector has constant aperture head `a` when it is almost everywhere constant on `(0,a)`. -/
def SoninHeadConstant (a : ℝ) (f : ℝ → ℂ) : Prop :=
  ∃ c : ℂ, ∀ᵐ t ∂(volume.restrict (Ioo (0 : ℝ) a)), f t = c

/-! ## The Mellin kernel on the positive ray -/

theorem soninMellinKernel_eq_exp {t : ℝ} (ht : 0 < t) (w : ℂ) :
    soninMellinKernel w t = Complex.exp ((Real.log t : ℂ) * (-w)) := by
  have hne : ((t : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt ht)
  rw [soninMellinKernel, Complex.cpow_def_of_ne_zero hne, ← Complex.ofReal_log ht.le]

theorem continuousOn_soninMellinKernel (w : ℂ) :
    ContinuousOn (soninMellinKernel w) (Ioi (0 : ℝ)) := by
  refine ContinuousOn.congr ?_ (fun t ht => soninMellinKernel_eq_exp (mem_Ioi.mp ht) w)
  refine Complex.continuous_exp.comp_continuousOn ?_
  refine ContinuousOn.mul ?_ continuousOn_const
  refine Complex.continuous_ofReal.comp_continuousOn ?_
  exact Real.continuousOn_log.mono (fun t ht => ne_of_gt (mem_Ioi.mp ht))

theorem norm_soninMellinKernel {t : ℝ} (ht : 0 < t) (w : ℂ) :
    ‖soninMellinKernel w t‖ = t ^ (-w.re) := by
  rw [soninMellinKernel, Complex.norm_cpow_eq_rpow_re_of_pos ht, Complex.neg_re]

theorem aestronglyMeasurable_soninMellinKernel (w : ℂ) {s : Set ℝ}
    (hs : MeasurableSet s) (hsub : s ⊆ Ioi (0 : ℝ)) :
    AEStronglyMeasurable (soninMellinKernel w) (volume.restrict s) :=
  ((continuousOn_soninMellinKernel w).mono hsub).aestronglyMeasurable hs

/-! ## The `L²` norm as an integral of squared norms -/

theorem norm_sq_toLp_eq_integral_norm_sq {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : α → ℂ} (hf : MemLp f 2 μ) :
    ‖hf.toLp f‖ ^ 2 = ∫ a, ‖f a‖ ^ 2 ∂μ := by
  have key := inner_self_eq_norm_sq (𝕜 := ℂ) (hf.toLp f)
  rw [MeasureTheory.L2.inner_def] at key
  have hint : (∫ a, inner ℂ ((hf.toLp f : α → ℂ) a) ((hf.toLp f : α → ℂ) a) ∂μ) =
      ((∫ a, ‖f a‖ ^ 2 ∂μ : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    refine integral_congr_ae ?_
    filter_upwards [hf.coeFn_toLp] with a ha
    rw [ha, RCLike.inner_apply, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [hint] at key
  simpa using key.symm

/-! ## The head estimate -/

/-- The exact primitive of the Mellin kernel on the aperture head. -/
theorem integral_Ioo_soninMellinKernel {w : ℂ} (hhi : w.re < 1) {A : ℝ} (hA : 0 < A) :
    (∫ t in Ioo (0 : ℝ) A, soninMellinKernel w t) = (A : ℂ) ^ (1 - w) / (1 - w) := by
  have hr : -1 < (-w).re := by
    rw [Complex.neg_re]
    linarith
  have hne : (1 : ℂ) - w ≠ 0 := by
    intro h
    have : w.re = 1 := by
      have := congrArg Complex.re h
      simp only [Complex.sub_re, Complex.one_re, Complex.zero_re] at this
      linarith
    linarith
  have hcalc := integral_cpow (a := (0 : ℝ)) (b := A) (r := -w) (Or.inl hr)
  rw [intervalIntegral.integral_of_le hA.le, integral_Ioc_eq_integral_Ioo] at hcalc
  have hzero : ((0 : ℝ) : ℂ) ^ (-w + 1) = 0 := by
    rw [Complex.ofReal_zero]
    refine Complex.zero_cpow ?_
    intro h
    apply hne
    linear_combination h
  rw [hzero, sub_zero] at hcalc
  have hrw : -w + 1 = 1 - w := by ring
  rw [hrw] at hcalc
  exact hcalc

theorem integrableOn_soninMellinKernel_Ioo {w : ℂ} (hhi : w.re < 1) {A : ℝ} (hA : 0 < A) :
    IntegrableOn (soninMellinKernel w) (Ioo (0 : ℝ) A) := by
  refine Integrable.mono'
    ((intervalIntegral.integrableOn_Ioo_rpow_iff hA).mpr (by linarith : -1 < -w.re))
    (aestronglyMeasurable_soninMellinKernel w measurableSet_Ioo
      (fun t ht => mem_Ioi.mpr ht.1)) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
  rw [norm_soninMellinKernel ht.1]

/-! ## The tail estimate -/

theorem integral_Ioi_rpow_neg_two_mul {σ : ℝ} (hσ : 1 / 2 < σ) {A : ℝ} (hA : 0 < A) :
    (∫ t in Ioi A, t ^ (-(2 * σ))) = A ^ (1 - 2 * σ) / (2 * σ - 1) := by
  have hlt : -(2 * σ) < -1 := by linarith
  have hexp : -(2 * σ) + 1 = 1 - 2 * σ := by ring
  rw [integral_Ioi_rpow_of_lt hlt hA, hexp,
    show (2 : ℝ) * σ - 1 = -(1 - 2 * σ) from by ring, div_neg, neg_div]

theorem memLp_soninMellinKernel_Ioi {w : ℂ} (hlo : 1 / 2 < w.re) {A : ℝ} (hA : 0 < A) :
    MemLp (soninMellinKernel w) 2 (volume.restrict (Ioi A)) := by
  have hmeas : AEStronglyMeasurable (soninMellinKernel w) (volume.restrict (Ioi A)) :=
    aestronglyMeasurable_soninMellinKernel w measurableSet_Ioi
      (fun t ht => mem_Ioi.mpr (lt_trans hA (mem_Ioi.mp ht)))
  rw [memLp_two_iff_integrable_sq_norm hmeas]
  have hbase : IntegrableOn (fun t : ℝ => t ^ (-(2 * w.re))) (Ioi A) :=
    (integrableOn_Ioi_rpow_iff hA).mpr (by linarith)
  refine hbase.congr_fun ?_ measurableSet_Ioi
  intro t ht
  have ht0 : 0 < t := lt_trans hA (mem_Ioi.mp ht)
  dsimp only
  rw [norm_soninMellinKernel ht0, ← Real.rpow_natCast (t ^ (-w.re)) 2,
    ← Real.rpow_mul ht0.le]
  congr 1
  push_cast
  ring

theorem integral_Ioi_norm_sq_soninMellinKernel {w : ℂ} (hlo : 1 / 2 < w.re) {A : ℝ} (hA : 0 < A) :
    (∫ t in Ioi A, ‖soninMellinKernel w t‖ ^ 2) = A ^ (1 - 2 * w.re) / (2 * w.re - 1) := by
  rw [← integral_Ioi_rpow_neg_two_mul hlo hA]
  refine setIntegral_congr_fun measurableSet_Ioi ?_
  intro t ht
  have ht0 : 0 < t := lt_trans hA (mem_Ioi.mp ht)
  dsimp only
  rw [norm_soninMellinKernel ht0, ← Real.rpow_natCast (t ^ (-w.re)) 2,
    ← Real.rpow_mul ht0.le]
  congr 1
  push_cast
  ring


/-! ## The aperture bound -/

/-- The constant head value is controlled by the `L²` norm. -/
theorem norm_head_mul_sqrt_le {A : ℝ} (hA : 0 < A) {f : ℝ → ℂ}
    (hf : MemLp f 2 (volume.restrict (Ioi (0 : ℝ)))) {c : ℂ}
    (hc : ∀ᵐ t ∂(volume.restrict (Ioo (0 : ℝ) A)), f t = c) :
    ‖c‖ * Real.sqrt A ≤ ‖hf.toLp f‖ := by
  have hsq : IntegrableOn (fun t => ‖f t‖ ^ 2) (Ioi (0 : ℝ)) :=
    (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mp hf
  have hIoo : (∫ t in Ioo (0 : ℝ) A, ‖f t‖ ^ 2) = ‖c‖ ^ 2 * A := by
    rw [setIntegral_congr_ae measurableSet_Ioo
      (by filter_upwards [(ae_restrict_iff' measurableSet_Ioo).mp hc] with t ht
          intro htmem
          rw [ht htmem]),
      setIntegral_const, smul_eq_mul]
    have hvol : (volume : Measure ℝ).real (Ioo (0 : ℝ) A) = A := by
      simp [hA.le]
    rw [hvol]
    ring
  have hmono : (∫ t in Ioo (0 : ℝ) A, ‖f t‖ ^ 2) ≤ ∫ t in Ioi (0 : ℝ), ‖f t‖ ^ 2 := by
    refine setIntegral_mono_set hsq ?_ ?_
    · filter_upwards with t
      positivity
    · exact Filter.Eventually.of_forall (fun t ht => mem_Ioi.mpr ht.1)
  have hnorm : ‖hf.toLp f‖ ^ 2 = ∫ t in Ioi (0 : ℝ), ‖f t‖ ^ 2 :=
    norm_sq_toLp_eq_integral_norm_sq hf
  have hle : (‖c‖ * Real.sqrt A) ^ 2 ≤ ‖hf.toLp f‖ ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hA.le, hnorm]
    calc ‖c‖ ^ 2 * A = ∫ t in Ioo (0 : ℝ) A, ‖f t‖ ^ 2 := hIoo.symm
      _ ≤ _ := hmono
  have h1 : 0 ≤ ‖c‖ * Real.sqrt A := by positivity
  have h2 : 0 ≤ ‖hf.toLp f‖ := norm_nonneg _
  have := Real.sqrt_le_sqrt hle
  rwa [Real.sqrt_sq h1, Real.sqrt_sq h2] at this

/-- On the aperture head the restricted measures of `Ioo` and `Ioc` agree. -/
theorem restrict_Ioo_eq_restrict_Ioc (a b : ℝ) :
    (volume : Measure ℝ).restrict (Ioo a b) = (volume : Measure ℝ).restrict (Ioc a b) :=
  Measure.restrict_congr_set Ioo_ae_eq_Ioc

theorem integrableOn_head_mul_kernel {w : ℂ} (hhi : w.re < 1) {A : ℝ} (hA : 0 < A)
    {f : ℝ → ℂ} {c : ℂ}
    (hc : ∀ᵐ t ∂(volume.restrict (Ioo (0 : ℝ) A)), f t = c) :
    IntegrableOn (fun t => f t * soninMellinKernel w t) (Ioc (0 : ℝ) A) := by
  have hbase : IntegrableOn (fun t => c * soninMellinKernel w t) (Ioo (0 : ℝ) A) :=
    (integrableOn_soninMellinKernel_Ioo hhi hA).const_mul c
  have hcongr : IntegrableOn (fun t => f t * soninMellinKernel w t) (Ioo (0 : ℝ) A) := by
    refine hbase.congr ?_
    filter_upwards [hc] with t ht
    rw [ht]
  rw [IntegrableOn, ← restrict_Ioo_eq_restrict_Ioc]
  exact hcongr

theorem integral_head_mul_kernel {w : ℂ} (hhi : w.re < 1) {A : ℝ} (hA : 0 < A)
    {f : ℝ → ℂ} {c : ℂ}
    (hc : ∀ᵐ t ∂(volume.restrict (Ioo (0 : ℝ) A)), f t = c) :
    (∫ t in Ioc (0 : ℝ) A, f t * soninMellinKernel w t) =
      c * ((A : ℂ) ^ (1 - w) / (1 - w)) := by
  rw [integral_Ioc_eq_integral_Ioo]
  rw [setIntegral_congr_ae measurableSet_Ioo
    (by filter_upwards [(ae_restrict_iff' measurableSet_Ioo).mp hc] with t ht
        intro htmem
        rw [ht htmem]),
    integral_const_mul, integral_Ioo_soninMellinKernel hhi hA]

theorem integrableOn_tail_mul_kernel {w : ℂ} (hlo : 1 / 2 < w.re) {A : ℝ} (hA : 0 < A)
    {f : ℝ → ℂ} (hf : MemLp f 2 (volume.restrict (Ioi (0 : ℝ)))) :
    IntegrableOn (fun t => f t * soninMellinKernel w t) (Ioi A) := by
  have hsub : (volume : Measure ℝ).restrict (Ioi A) =
      ((volume : Measure ℝ).restrict (Ioi (0 : ℝ))).restrict (Ioi A) := by
    rw [Measure.restrict_restrict measurableSet_Ioi,
      inter_eq_self_of_subset_left (fun t ht => mem_Ioi.mpr (lt_trans hA (mem_Ioi.mp ht)))]
  have hfA : MemLp f 2 (volume.restrict (Ioi A)) := by
    rw [hsub]
    exact hf.restrict (Ioi A)
  have hkA : MemLp (soninMellinKernel w) 2 (volume.restrict (Ioi A)) :=
    memLp_soninMellinKernel_Ioi hlo hA
  have hmul := hfA.integrable_mul hkA
  exact hmul.congr (Filter.Eventually.of_forall fun t => rfl)

/-- The head contributes exactly the aperture power divided by `‖1 - w‖`. -/
theorem norm_integral_head_le {w : ℂ} (hhi : w.re < 1) {A : ℝ} (hA : 0 < A)
    {f : ℝ → ℂ} (hf : MemLp f 2 (volume.restrict (Ioi (0 : ℝ)))) {c : ℂ}
    (hc : ∀ᵐ t ∂(volume.restrict (Ioo (0 : ℝ) A)), f t = c) :
    ‖∫ t in Ioc (0 : ℝ) A, f t * soninMellinKernel w t‖ ≤
      1 / ‖1 - w‖ * (A ^ (1 / 2 - w.re) * ‖hf.toLp f‖) := by
  have hne : (1 : ℂ) - w ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp only [Complex.sub_re, Complex.one_re, Complex.zero_re] at hre
    linarith
  have hnne : 0 < ‖(1 : ℂ) - w‖ := norm_pos_iff.mpr hne
  have hhead := norm_head_mul_sqrt_le hA hf hc
  have hApos : (0 : ℝ) < A ^ (1 - w.re) := Real.rpow_pos_of_pos hA _
  rw [integral_head_mul_kernel hhi hA hc, norm_mul, norm_div,
    Complex.norm_cpow_eq_rpow_re_of_pos hA, Complex.sub_re, Complex.one_re]
  have hsqrt : Real.sqrt A = A ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow A
  have hsplit : A ^ (1 - w.re) = A ^ (1 / 2 : ℝ) * A ^ (1 / 2 - w.re) := by
    rw [← Real.rpow_add hA]
    congr 1
    ring
  rw [hsplit, div_eq_mul_one_div]
  have hstep : ‖c‖ * A ^ (1 / 2 : ℝ) ≤ ‖hf.toLp f‖ := by
    rwa [hsqrt] at hhead
  have hnn : 0 ≤ A ^ (1 / 2 - w.re) * (1 / ‖(1 : ℂ) - w‖) := by positivity
  calc ‖c‖ * (A ^ (1 / 2 : ℝ) * A ^ (1 / 2 - w.re) * (1 / ‖(1 : ℂ) - w‖))
      = (‖c‖ * A ^ (1 / 2 : ℝ)) * (A ^ (1 / 2 - w.re) * (1 / ‖(1 : ℂ) - w‖)) := by ring
    _ ≤ ‖hf.toLp f‖ * (A ^ (1 / 2 - w.re) * (1 / ‖(1 : ℂ) - w‖)) :=
        mul_le_mul_of_nonneg_right hstep hnn
    _ = 1 / ‖1 - w‖ * (A ^ (1 / 2 - w.re) * ‖hf.toLp f‖) := by ring

/-- The tail contributes exactly the aperture power divided by `sqrt (2 Re w - 1)`. -/
theorem norm_integral_tail_le {w : ℂ} (hlo : 1 / 2 < w.re) {A : ℝ} (hA : 0 < A)
    {f : ℝ → ℂ} (hf : MemLp f 2 (volume.restrict (Ioi (0 : ℝ)))) :
    ‖∫ t in Ioi A, f t * soninMellinKernel w t‖ ≤
      1 / Real.sqrt (2 * w.re - 1) * (A ^ (1 / 2 - w.re) * ‖hf.toLp f‖) := by
  have hsub : (volume : Measure ℝ).restrict (Ioi A) =
      ((volume : Measure ℝ).restrict (Ioi (0 : ℝ))).restrict (Ioi A) := by
    rw [Measure.restrict_restrict measurableSet_Ioi,
      inter_eq_self_of_subset_left (fun t ht => mem_Ioi.mpr (lt_trans hA (mem_Ioi.mp ht)))]
  have hfA : MemLp f 2 (volume.restrict (Ioi A)) := by
    rw [hsub]; exact hf.restrict (Ioi A)
  have hkA : MemLp (soninMellinKernel w) 2 (volume.restrict (Ioi A)) :=
    memLp_soninMellinKernel_Ioi hlo hA
  have htwo : ENNReal.ofReal (2 : ℝ) = 2 := by simp
  have hholder : Real.HolderConjugate 2 2 := by
    rw [Real.holderConjugate_iff]
    constructor <;> norm_num
  have hCS := MeasureTheory.integral_mul_norm_le_Lp_mul_Lq (μ := volume.restrict (Ioi A))
    (f := f) (g := soninMellinKernel w) hholder (by rwa [htwo]) (by rwa [htwo])
  have hbound : ‖∫ t in Ioi A, f t * soninMellinKernel w t‖ ≤
      ∫ t in Ioi A, ‖f t‖ * ‖soninMellinKernel w t‖ := by
    refine le_trans (norm_integral_le_integral_norm _) ?_
    refine le_of_eq (integral_congr_ae ?_)
    filter_upwards with t
    rw [norm_mul]
  -- the two `L²` factors
  have hf2 : (∫ t in Ioi A, ‖f t‖ ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) ≤ ‖hf.toLp f‖ := by
    have hsqInt : IntegrableOn (fun t => ‖f t‖ ^ 2) (Ioi (0 : ℝ)) :=
      (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mp hf
    have hmono : (∫ t in Ioi A, ‖f t‖ ^ 2) ≤ ∫ t in Ioi (0 : ℝ), ‖f t‖ ^ 2 := by
      refine setIntegral_mono_set hsqInt ?_ ?_
      · filter_upwards with t; positivity
      · exact Filter.Eventually.of_forall
          (fun t ht => mem_Ioi.mpr (lt_trans hA (mem_Ioi.mp ht)))
    have hnorm : ‖hf.toLp f‖ ^ 2 = ∫ t in Ioi (0 : ℝ), ‖f t‖ ^ 2 :=
      norm_sq_toLp_eq_integral_norm_sq hf
    have hrpow : (∫ t in Ioi A, ‖f t‖ ^ (2 : ℝ)) = ∫ t in Ioi A, ‖f t‖ ^ 2 := by
      refine integral_congr_ae ?_
      filter_upwards with t
      rw [← Real.rpow_natCast ‖f t‖ 2]
      norm_num
    rw [hrpow, ← Real.sqrt_eq_rpow]
    have hle : (∫ t in Ioi A, ‖f t‖ ^ 2) ≤ ‖hf.toLp f‖ ^ 2 := by rw [hnorm]; exact hmono
    have := Real.sqrt_le_sqrt hle
    rwa [Real.sqrt_sq (norm_nonneg _)] at this
  have hpos : (0 : ℝ) < 2 * w.re - 1 := by linarith
  have hk2 : (∫ t in Ioi A, ‖soninMellinKernel w t‖ ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) =
      A ^ (1 / 2 - w.re) / Real.sqrt (2 * w.re - 1) := by
    have hrpow : (∫ t in Ioi A, ‖soninMellinKernel w t‖ ^ (2 : ℝ)) =
        ∫ t in Ioi A, ‖soninMellinKernel w t‖ ^ 2 := by
      refine integral_congr_ae ?_
      filter_upwards with t
      rw [← Real.rpow_natCast ‖soninMellinKernel w t‖ 2]
      norm_num
    have hApow : (0 : ℝ) ≤ A ^ (1 - 2 * w.re) := (Real.rpow_pos_of_pos hA _).le
    rw [hrpow, integral_Ioi_norm_sq_soninMellinKernel hlo hA, ← Real.sqrt_eq_rpow,
      Real.sqrt_div hApow]
    congr 1
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hA.le]
    congr 1
    ring
  calc ‖∫ t in Ioi A, f t * soninMellinKernel w t‖
      ≤ ∫ t in Ioi A, ‖f t‖ * ‖soninMellinKernel w t‖ := hbound
    _ ≤ (∫ t in Ioi A, ‖f t‖ ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) *
          (∫ t in Ioi A, ‖soninMellinKernel w t‖ ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) := hCS
    _ ≤ ‖hf.toLp f‖ * (A ^ (1 / 2 - w.re) / Real.sqrt (2 * w.re - 1)) := by
        rw [hk2]
        exact mul_le_mul_of_nonneg_right hf2 (by positivity)
    _ = 1 / Real.sqrt (2 * w.re - 1) * (A ^ (1 / 2 - w.re) * ‖hf.toLp f‖) := by
        field_simp

/-- **Aperture bound for the completed Mellin evaluator.**  On the class of `L²((0,∞))` vectors with
constant aperture head `A`, the completed right Mellin evaluation at `w` with `1/2 < Re w < 1` has
operator bound `C(w) A^(1/2 - Re w)`, with the explicit constant of the head/tail split. -/
theorem norm_soninMellinEvaluation_le_aperture
    {w : ℂ} (hlo : 1 / 2 < w.re) (hhi : w.re < 1)
    {A : ℝ} (hA : 0 < A) {f : ℝ → ℂ}
    (hf : MemLp f 2 (volume.restrict (Ioi (0 : ℝ))))
    (hhead : SoninHeadConstant A f) :
    ‖soninMellinEvaluation w f‖ ≤
      ‖mellinCompletionFactor w‖ *
        ((1 / ‖1 - w‖ + 1 / Real.sqrt (2 * w.re - 1)) *
          (A ^ (1 / 2 - w.re) * ‖hf.toLp f‖)) := by
  obtain ⟨c, hc⟩ := hhead
  have hsplit : (∫ t in Ioi (0 : ℝ), f t * soninMellinKernel w t) =
      (∫ t in Ioc (0 : ℝ) A, f t * soninMellinKernel w t) +
        ∫ t in Ioi A, f t * soninMellinKernel w t := by
    rw [← setIntegral_union (Set.Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
      (integrableOn_head_mul_kernel hhi hA hc) (integrableOn_tail_mul_kernel hlo hA hf),
      Set.Ioc_union_Ioi_eq_Ioi hA.le]
  rw [soninMellinEvaluation, norm_mul, hsplit]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  refine le_trans (norm_add_le _ _) ?_
  have h1 := norm_integral_head_le hhi hA hf hc
  have h2 := norm_integral_tail_le hlo hA hf
  calc ‖∫ t in Ioc (0 : ℝ) A, f t * soninMellinKernel w t‖ +
        ‖∫ t in Ioi A, f t * soninMellinKernel w t‖
      ≤ 1 / ‖1 - w‖ * (A ^ (1 / 2 - w.re) * ‖hf.toLp f‖) +
          1 / Real.sqrt (2 * w.re - 1) * (A ^ (1 / 2 - w.re) * ‖hf.toLp f‖) :=
        add_le_add h1 h2
    _ = (1 / ‖1 - w‖ + 1 / Real.sqrt (2 * w.re - 1)) *
          (A ^ (1 / 2 - w.re) * ‖hf.toLp f‖) := by ring


/-- The explicit ambient constant of the aperture bound. -/
def soninApertureConstant (w : ℂ) : ℝ :=
  ‖mellinCompletionFactor w‖ * (1 / ‖1 - w‖ + 1 / Real.sqrt (2 * w.re - 1))

theorem norm_soninMellinEvaluation_le_soninApertureConstant
    {w : ℂ} (hlo : 1 / 2 < w.re) (hhi : w.re < 1)
    {A : ℝ} (hA : 0 < A) {f : ℝ → ℂ}
    (hf : MemLp f 2 (volume.restrict (Ioi (0 : ℝ))))
    (hhead : SoninHeadConstant A f) :
    ‖soninMellinEvaluation w f‖ ≤
      soninApertureConstant w * A ^ (1 / 2 - w.re) * ‖hf.toLp f‖ := by
  have h := norm_soninMellinEvaluation_le_aperture hlo hhi hA hf hhead
  rw [soninApertureConstant]
  calc ‖soninMellinEvaluation w f‖
      ≤ ‖mellinCompletionFactor w‖ *
          ((1 / ‖1 - w‖ + 1 / Real.sqrt (2 * w.re - 1)) *
            (A ^ (1 / 2 - w.re) * ‖hf.toLp f‖)) := h
    _ = ‖mellinCompletionFactor w‖ * (1 / ‖1 - w‖ + 1 / Real.sqrt (2 * w.re - 1)) *
          A ^ (1 / 2 - w.re) * ‖hf.toLp f‖ := by ring

/-- **Aperture bound at the geometric samples.**  At the apertures `a N = a₀ r^(-N)` the evaluator
grows at most like `r^(N (Re w - 1/2))`, which is `r^(N |Re w - 1/2|)` in the off-axis right half
strip. -/
theorem norm_soninMellinEvaluation_le_geometric_sample
    {w : ℂ} (hlo : 1 / 2 < w.re) (hhi : w.re < 1)
    {a₀ r : ℝ} (ha₀ : 0 < a₀) (hr : 0 < r) (N : ℕ)
    {f : ℝ → ℂ} (hf : MemLp f 2 (volume.restrict (Ioi (0 : ℝ))))
    (hhead : SoninHeadConstant (a₀ * r ^ (-(N : ℝ))) f) :
    ‖soninMellinEvaluation w f‖ ≤
      soninApertureConstant w *
        (a₀ ^ (1 / 2 - w.re) * r ^ ((N : ℝ) * (w.re - 1 / 2))) * ‖hf.toLp f‖ := by
  have hrpow : (0 : ℝ) < r ^ (-(N : ℝ)) := Real.rpow_pos_of_pos hr _
  have hA : (0 : ℝ) < a₀ * r ^ (-(N : ℝ)) := mul_pos ha₀ hrpow
  have h := norm_soninMellinEvaluation_le_soninApertureConstant hlo hhi hA hf hhead
  have hfactor : (a₀ * r ^ (-(N : ℝ))) ^ (1 / 2 - w.re) =
      a₀ ^ (1 / 2 - w.re) * r ^ ((N : ℝ) * (w.re - 1 / 2)) := by
    rw [Real.mul_rpow ha₀.le hrpow.le, ← Real.rpow_mul hr.le]
    congr 2
    ring
  rwa [hfactor] at h

/-- The aperture exponent is exactly the horizontal displacement of the evaluation point: the
logarithmic growth rate along the geometric apertures is at most `|Re w - 1/2|`, with equality of
exponent shape `r^(N |Re w - 1/2|)`. -/
theorem soninAperture_geometric_exponent {w : ℂ} (hlo : 1 / 2 < w.re) {r : ℝ} (N : ℕ) :
    r ^ ((N : ℝ) * (w.re - 1 / 2)) = r ^ ((N : ℝ) * |w.re - 1 / 2|) := by
  rw [abs_of_pos (by linarith)]

end RHTower
