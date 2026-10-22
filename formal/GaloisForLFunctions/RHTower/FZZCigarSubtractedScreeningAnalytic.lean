import GaloisForLFunctions.RHTower.FZZCigarPlaneScreeningCutoff
import Mathlib.Probability.Moments.MGFAnalytic

/-!
# Analyticity of the original collision-subtracted plane source

The original local subtraction is signed. Splitting its fixed weight into
positive and negative parts gives two actual weighted exponential integrals;
open integrability intervals justify their analyticity. This proves dependence
on the singular exponent through the first nonintegrable strip.

For the regular exponent, log |z| is bounded and vanishes linearly on the disk
at one. The exact fixed-interval identity exp(a X)-1 = a integral_0^(1 : ℕ) X exp(a t X)
turns the original subtraction into a signed exponential integral over a product
measure. The logarithmic weight and the product integral are integrable before
Fubini is used. The resulting regular-exponent family is real analytic everywhere.

The exterior uses its proved open tail-integrability region. Combining these
original source terms with the explicitly retained collision counterterms gives
a pole-cleared family, separately real analytic on its full slices. Reflection,
its exact values on the pole lines, and equality with the clearing factor times
the audited whole-plane finite part are proved.

This does not yet identify the source with a continued Gamma formula, assert
joint parameter analyticity, transport the full physical replica/momentum
variation, fix its phase frame, or prove the FZZ Ward identity or RH.
-/

open MeasureTheory Set Metric Filter ProbabilityTheory
open scoped Topology
noncomputable section
namespace GaloisForLFunctions.RHTower

private def positiveWeightMeasure {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (f : Ω → ℝ) : Measure Ω :=
  μ.withDensity (fun z => ENNReal.ofReal (max (f z) 0))

private theorem positiveWeight_integrable {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (f X : Ω → ℝ) (hf : Measurable f) (hX : Measurable X) (t : ℝ)
    (hi : Integrable (fun z => f z*Real.exp (t*X z)) μ) :
    Integrable (fun z => Real.exp (t*X z)) (positiveWeightMeasure μ f) := by
  rw [positiveWeightMeasure, integrable_withDensity_iff_integrable_smul'
    (by fun_prop) (by filter_upwards with z; exact ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (le_max_right _ _), smul_eq_mul]
  apply hi.norm.mono' (by fun_prop)
  filter_upwards with z
  rw [norm_mul, norm_mul, Real.norm_of_nonneg (le_max_right _ _),
    Real.norm_of_nonneg (Real.exp_pos _).le]
  apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
  exact max_le (le_abs_self _) (abs_nonneg _)

private theorem positiveWeight_integral {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (f X : Ω → ℝ) (hf : Measurable f) (t : ℝ) :
    mgf X (positiveWeightMeasure μ f) t = ∫ z, max (f z) 0*Real.exp (t*X z) ∂μ := by
  rw [mgf, positiveWeightMeasure, integral_withDensity_eq_integral_toReal_smul
    (by fun_prop) (by filter_upwards with z; exact ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (le_max_right _ _), smul_eq_mul]

private theorem signed_exp_analyticAt {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (f X : Ω → ℝ) (hf : Measurable f) (hX : Measurable X) (t : ℝ)
    (hi : ∀ᶠ s in 𝓝 t, Integrable (fun z => f z*Real.exp (s*X z)) μ) :
    AnalyticAt ℝ (fun s => ∫ z, f z*Real.exp (s*X z) ∂μ) t := by
  have hn : ∀ᶠ s in 𝓝 t, Integrable (fun z => (-f z)*Real.exp (s*X z)) μ := by
    filter_upwards [hi] with s hs
    convert! hs.neg using 1
    ext z
    dsimp
    ring
  have hp : t ∈ interior (integrableExpSet X (positiveWeightMeasure μ f)) := by
    apply mem_interior_iff_mem_nhds.mpr
    filter_upwards [hi] with s hs
    exact positiveWeight_integrable μ f X hf hX s hs
  have hm : t ∈ interior (integrableExpSet X (positiveWeightMeasure μ (fun z => -f z))) := by
    apply mem_interior_iff_mem_nhds.mpr
    filter_upwards [hn] with s hs
    exact positiveWeight_integrable μ (fun z => -f z) X hf.neg hX s hs
  apply ((analyticAt_mgf hp).sub (analyticAt_mgf hm)).congr
  filter_upwards [hi, hn] with s hs ht
  simp only [Pi.sub_apply]
  rw [positiveWeight_integral μ f X hf, positiveWeight_integral μ (fun z => -f z) X hf.neg]
  have hip : Integrable (fun z => max (f z) 0*Real.exp (s*X z)) μ := by
    have h := positiveWeight_integrable μ f X hf hX s hs
    rw [positiveWeightMeasure, integrable_withDensity_iff_integrable_smul'
      (by fun_prop) (by filter_upwards with z; exact ENNReal.ofReal_lt_top)] at h
    simpa only [ENNReal.toReal_ofReal (le_max_right _ _), smul_eq_mul] using h
  have him : Integrable (fun z => max (-f z) 0*Real.exp (s*X z)) μ := by
    have h := positiveWeight_integrable μ (fun z => -f z) X hf.neg hX s ht
    rw [positiveWeightMeasure, integrable_withDensity_iff_integrable_smul'
      (by fun_prop) (by filter_upwards with z; exact ENNReal.ofReal_lt_top)] at h
    simpa only [ENNReal.toReal_ofReal (le_max_right _ _), smul_eq_mul] using h
  rw [← integral_sub hip him]
  apply integral_congr_ae
  filter_upwards with z
  by_cases hz : 0 ≤ f z
  · rw [max_eq_left hz, max_eq_right (neg_nonpos.mpr hz)]
    ring
  · have hz' := le_of_not_ge hz
    rw [max_eq_right hz', max_eq_left (neg_nonneg.mpr hz')]
    ring

private theorem zero_subtracted_admission (α β : ℝ) (ha : -3 < α) :
    IntegrableOn (fzzScreeningZeroSubtracted α β) (ball 0 (1/2)) := by
  have h := fzzScreeningZeroSubtracted_integrable (Real.log (α+3)) β
  rw [Real.exp_log (by linarith : 0 < α+3)] at h
  simpa only [show -3+(α+3) = α by ring] using h

private theorem zero_subtracted_shift (α β δ : ℝ) {z : ℂ} (hz : z ≠ 0) :
    fzzScreeningZeroSubtracted α β z*Real.exp (δ*Real.log ‖z‖) =
      fzzScreeningZeroSubtracted (α+δ) β z := by
  have hn := norm_pos_iff.mpr hz
  rw [show Real.exp (δ*Real.log ‖z‖) = ‖z‖^δ by rw [Real.rpow_def_of_pos hn, mul_comm]]
  unfold fzzScreeningZeroSubtracted
  rw [Real.rpow_add hn]
  ring

private theorem zero_subtracted_shift_analytic (α β : ℝ) (ha : -3 < α) :
    AnalyticAt ℝ (fun δ => ∫ z : ℂ in ball 0 (1/2),
      fzzScreeningZeroSubtracted (α+δ) β z) 0 := by
  have hshift : ∀ᶠ δ : ℝ in 𝓝 0, -3 < α+δ := by
    exact (isOpen_lt continuous_const (by fun_prop)).mem_nhds (by simpa using ha)
  have hi : ∀ᶠ δ : ℝ in 𝓝 0, Integrable
      (fun z => fzzScreeningZeroSubtracted α β z*Real.exp (δ*Real.log ‖z‖))
        (volume.restrict (ball 0 (1/2))) := by
    filter_upwards [hshift] with δ hδ
    apply (zero_subtracted_admission (α+δ) β hδ).congr
    filter_upwards [ae_restrict_of_ae (volume.ae_ne (0 : ℂ))] with z hz
    exact (zero_subtracted_shift α β δ hz).symm
  have han := signed_exp_analyticAt (volume.restrict (ball (0 : ℂ) (1/2)))
    (fzzScreeningZeroSubtracted α β) (fun z => Real.log ‖z‖)
    (by unfold fzzScreeningZeroSubtracted; fun_prop) (by fun_prop) 0 hi
  apply han.congr
  filter_upwards with δ
  apply integral_congr_ae
  filter_upwards [ae_restrict_of_ae (volume.ae_ne (0 : ℂ))] with z hz
  exact zero_subtracted_shift α β δ hz

/-- The collision-subtracted original source is analytic in its singular exponent,
through the first nonintegrable strip of the unrenormalized source. -/
theorem fzzScreeningZeroSubtracted_singular_mark_analytic (u β : ℝ) :
    AnalyticAt ℝ (fun δ => ∫ z : ℂ in ball 0 (1/2),
      fzzScreeningZeroSubtracted (-3+Real.exp u+δ) β z) 0 :=
  zero_subtracted_shift_analytic _ β (by linarith [Real.exp_pos u])



private theorem signed_bounded_exp_analytic {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (f X : Ω → ℝ) (hf : Measurable f) (hX : Measurable X)
    (hi : Integrable f μ) (C : ℝ) (hb : ∀ᵐ z ∂μ, ‖X z‖ ≤ C) (t : ℝ) :
    AnalyticAt ℝ (fun s => ∫ z, f z*Real.exp (s*X z) ∂μ) t := by
  apply signed_exp_analyticAt μ f X hf hX t
  apply Eventually.of_forall
  intro s
  apply hi.mul_bdd (by fun_prop)
  filter_upwards [hb] with z hz
  rw [Real.norm_of_nonneg (Real.exp_pos _).le]
  apply Real.exp_le_exp.mpr
  calc
    s*X z ≤ |s*X z| := le_abs_self _
    _ = |s| *‖X z‖ := by rw [abs_mul, Real.norm_eq_abs]
    _ ≤ |s| *C := mul_le_mul_of_nonneg_left hz (abs_nonneg _)

private theorem one_disk_ne_zero {z : ℂ} (hz : z ∈ closedBall (1 : ℂ) (1/2)) : z ≠ 0 := by
  intro h
  subst z
  norm_num [mem_closedBall, dist_eq_norm] at hz

private theorem log_norm_smooth_one :
    ContDiffOn ℝ 1 (fun z : ℂ => Real.log ‖z‖) (closedBall 1 (1/2)) :=
  (contDiffOn_id.norm ℂ (fun _ hz => one_disk_ne_zero hz)).log
    (fun _ hz => norm_ne_zero_iff.mpr (one_disk_ne_zero hz))

private def oneLogWeight (β : ℝ) (z : ℂ) : ℝ := ‖z-1‖^β*Real.log ‖z‖

private theorem oneLogWeight_integrable (β : ℝ) (hb : -3 < β) :
    IntegrableOn (oneLogWeight β) (ball 1 (1/2)) := by
  obtain ⟨C,hC⟩ := log_norm_smooth_one.exists_lipschitzOnWith (by simp)
    (convex_closedBall (1 : ℂ) (1/2)) (isCompact_closedBall (1 : ℂ) (1/2))
  have hi : IntegrableOn (fun z : ℂ => ‖z-1‖^(β+1)) (ball 1 (1/2)) := by
    have h := (fzzScreeningPlaneKernel_integrable_one_iff 0 (β+1)).mpr (by linarith)
    unfold fzzScreeningPlaneKernel at h
    simpa only [Real.rpow_zero, one_mul] using h
  apply (hi.const_mul (C : ℝ)).mono' (by unfold oneLogWeight; fun_prop)
  filter_upwards [ae_restrict_mem measurableSet_ball] with z hz
  have hl : ‖Real.log ‖z‖‖ ≤ (C : ℝ)*‖z-1‖ := by
    simpa [dist_eq_norm] using hC.dist_le_mul z (ball_subset_closedBall hz) 1
      (show (1 : ℂ) ∈ closedBall 1 (1/2) by simp)
  by_cases h1 : z = 1
  · subst z
    simp [oneLogWeight]
    positivity
  · have hn : 0 < ‖z-1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr h1)
    calc
      ‖oneLogWeight β z‖ = ‖z-1‖^β*‖Real.log ‖z‖‖ := by
        rw [oneLogWeight, norm_mul, Real.norm_of_nonneg (Real.rpow_nonneg hn.le _)]
      _ ≤ ‖z-1‖^β*((C : ℝ)*‖z-1‖) :=
        mul_le_mul_of_nonneg_left hl (Real.rpow_nonneg hn.le _)
      _ = (C : ℝ)*‖z-1‖^(β+1) := by rw [Real.rpow_add hn, Real.rpow_one]; ring

private theorem exp_sub_fixed_interval (a x : ℝ) :
    Real.exp (a*x)-1 = a*(∫ t : ℝ in Ioc 0 1, x*Real.exp (a*(t*x))) := by
  have hd : ∀ t : ℝ, HasDerivAt (fun t : ℝ => Real.exp (a*(t*x)))
      (a*(x*Real.exp (a*(t*x)))) t := by
    intro t
    convert! (((hasDerivAt_id t).mul_const x).const_mul a).exp using 1
    simp only [id_eq]
    ring
  have hi : IntervalIntegrable (fun t : ℝ => a*(x*Real.exp (a*(t*x)))) volume 0 1 :=
    (show Continuous _ by fun_prop).intervalIntegrable _ _
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t) hi
  rw [intervalIntegral.integral_of_le zero_le_one, integral_const_mul] at h
  simpa only [one_mul, zero_mul, mul_zero, Real.exp_zero] using h.symm

private abbrev markedDiskMeasure : Measure (ℂ × ℝ) :=
  (volume.restrict (ball (1 : ℂ) (1/2))).prod (volume.restrict (Ioc (0 : ℝ) 1))

private def diskExpVariable (q : ℂ × ℝ) : ℝ := q.2*Real.log ‖q.1‖

private theorem diskExpVariable_bounded :
    ∃ C : ℝ, ∀ᵐ q ∂markedDiskMeasure, ‖diskExpVariable q‖ ≤ C := by
  obtain ⟨C,hC⟩ := (isCompact_closedBall (1 : ℂ) (1/2)).exists_bound_of_continuousOn
    log_norm_smooth_one.continuousOn
  refine ⟨C, ?_⟩
  rw [Measure.ae_prod_iff_ae_ae (measurableSet_le
    (by unfold diskExpVariable; fun_prop) measurable_const)]
  filter_upwards [ae_restrict_mem measurableSet_ball] with z hz
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  have htz : |t| ≤ 1 := by rw [abs_of_nonneg ht.1.le]; exact ht.2
  rw [diskExpVariable, norm_mul, Real.norm_eq_abs]
  calc
    |t| *‖Real.log ‖z‖‖ ≤ 1*‖Real.log ‖z‖‖ :=
      mul_le_mul_of_nonneg_right htz (norm_nonneg _)
    _ ≤ C := by simpa only [one_mul] using hC z (ball_subset_closedBall hz)

private theorem disk_lift_integrable (β a : ℝ) (hb : -3 < β) :
    Integrable (fun q : ℂ × ℝ => oneLogWeight β q.1*Real.exp (a*diskExpVariable q))
      markedDiskMeasure := by
  have hi : Integrable (fun q : ℂ × ℝ => oneLogWeight β q.1) markedDiskMeasure := by
    have h := (oneLogWeight_integrable β hb).mul_prod
      (integrable_const (1 : ℝ) : Integrable (fun _ : ℝ => (1 : ℝ)) (volume.restrict (Ioc 0 1)))
    simpa only [mul_one] using h
  obtain ⟨C,hC⟩ := diskExpVariable_bounded
  apply hi.mul_bdd (by unfold diskExpVariable; fun_prop)
  filter_upwards [hC] with q hq
  rw [Real.norm_of_nonneg (Real.exp_pos _).le]
  apply Real.exp_le_exp.mpr
  calc
    a*diskExpVariable q ≤ |a*diskExpVariable q| := le_abs_self _
    _ = |a| *‖diskExpVariable q‖ := by rw [abs_mul, Real.norm_eq_abs]
    _ ≤ |a| *C := mul_le_mul_of_nonneg_left hq (abs_nonneg _)

private theorem disk_lift_identity (β a : ℝ) (hb : -3 < β) :
    (∫ z : ℂ in ball 1 (1/2), fzzScreeningOneSubtracted a β z) =
      a*(∫ q : ℂ × ℝ, oneLogWeight β q.1*Real.exp (a*diskExpVariable q)
        ∂markedDiskMeasure) := by
  rw [integral_prod _ (disk_lift_integrable β a hb), ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [ae_restrict_of_ae (volume.ae_ne (0 : ℂ))] with z hz
  have hn := norm_pos_iff.mpr hz
  have he : (fun t : ℝ => oneLogWeight β z*Real.exp (a*diskExpVariable (z,t))) =
      (fun t : ℝ => ‖z-1‖^β*(Real.log ‖z‖*Real.exp (a*(t*Real.log ‖z‖)))) := by
    funext t
    dsimp [oneLogWeight, diskExpVariable]
    ring
  rw [he, integral_const_mul]
  rw [fzzScreeningOneSubtracted, Real.rpow_def_of_pos hn,
    show Real.log ‖z‖*a = a*Real.log ‖z‖ by ring, exp_sub_fixed_interval]
  ring

private theorem one_subtracted_regular_analytic (β a : ℝ) (hb : -3 < β) :
    AnalyticAt ℝ (fun s => ∫ z : ℂ in ball 1 (1/2), fzzScreeningOneSubtracted s β z) a := by
  have hi : Integrable (fun q : ℂ × ℝ => oneLogWeight β q.1) markedDiskMeasure := by
    have h := disk_lift_integrable β 0 hb
    simpa only [zero_mul, Real.exp_zero, mul_one] using h
  obtain ⟨C,hC⟩ := diskExpVariable_bounded
  have h := signed_bounded_exp_analytic markedDiskMeasure (fun q => oneLogWeight β q.1)
    diskExpVariable (by unfold oneLogWeight; fun_prop) (by unfold diskExpVariable; fun_prop)
    hi C hC a
  have ha := (analyticAt_id (𝕜 := ℝ) (z := a)).mul h
  apply ha.congr
  filter_upwards with s
  exact (disk_lift_identity β s hb).symm

/-- The regular factor's exponent may vary through every real value after the original
collision subtraction, proved by a fixed-interval exponential representation. -/
theorem fzzScreeningOneSubtracted_regular_mark_analytic (v a : ℝ) :
    AnalyticAt ℝ (fun s => ∫ z : ℂ in ball 1 (1/2),
      fzzScreeningOneSubtracted s (-3+Real.exp v) z) a :=
  one_subtracted_regular_analytic _ a (by linarith [Real.exp_pos v])


private theorem exterior_admission (α β : ℝ) (hs : α+β < -2) :
    IntegrableOn (fzzScreeningPlaneKernel α β) fzzScreeningPlaneExterior := by
  have h := fzzScreeningPlaneExterior_integrable α (Real.log (-2-α-β))
  rw [Real.exp_log (by linarith : 0 < -2-α-β)] at h
  simpa only [show -2-α-(-2-α-β) = β by ring] using h

theorem plane_kernel_shift (α β δ : ℝ) {z : ℂ} (hz : z ≠ 0) :
    fzzScreeningPlaneKernel α β z*Real.exp (δ*Real.log ‖z‖) =
      fzzScreeningPlaneKernel (α+δ) β z := by
  have hn := norm_pos_iff.mpr hz
  rw [show Real.exp (δ*Real.log ‖z‖) = ‖z‖^δ by rw [Real.rpow_def_of_pos hn, mul_comm]]
  unfold fzzScreeningPlaneKernel
  rw [Real.rpow_add hn]
  ring

theorem exterior_shift_analytic (α β : ℝ) (hs : α+β < -2) :
    AnalyticAt ℝ (fun δ => ∫ z : ℂ in fzzScreeningPlaneExterior,
      fzzScreeningPlaneKernel (α+δ) β z) 0 := by
  have hshift : ∀ᶠ δ : ℝ in 𝓝 0, (α+δ)+β < -2 := by
    exact (isOpen_lt (by fun_prop) continuous_const).mem_nhds (by simpa using hs)
  have hi : ∀ᶠ δ : ℝ in 𝓝 0, Integrable
      (fun z => fzzScreeningPlaneKernel α β z*Real.exp (δ*Real.log ‖z‖))
        (volume.restrict fzzScreeningPlaneExterior) := by
    filter_upwards [hshift] with δ hδ
    apply (exterior_admission (α+δ) β hδ).congr
    filter_upwards [ae_restrict_of_ae (volume.ae_ne (0 : ℂ))] with z hz
    exact (plane_kernel_shift α β δ hz).symm
  have han := signed_exp_analyticAt (volume.restrict fzzScreeningPlaneExterior)
    (fzzScreeningPlaneKernel α β) (fun z => Real.log ‖z‖)
    (by unfold fzzScreeningPlaneKernel; fun_prop) (by fun_prop) 0 hi
  apply han.congr
  filter_upwards with δ
  apply integral_congr_ae
  filter_upwards [ae_restrict_of_ae (volume.ae_ne (0 : ℂ))] with z hz
  exact plane_kernel_shift α β δ hz

theorem exterior_analytic (α β : ℝ) (hs : α+β < -2) :
    AnalyticAt ℝ (fun s => ∫ z : ℂ in fzzScreeningPlaneExterior,
      fzzScreeningPlaneKernel s β z) α := by
  have h := (exterior_shift_analytic α β hs).comp_sub α
  have he (s : ℝ) : α+(s-α) = s := by ring
  simpa only [zero_add, he] using h

private theorem zero_subtracted_analytic (α β : ℝ) (ha : -3 < α) :
    AnalyticAt ℝ (fun s => ∫ z : ℂ in ball 0 (1/2),
      fzzScreeningZeroSubtracted s β z) α := by
  have h := (zero_subtracted_shift_analytic α β ha).comp_sub α
  have he (s : ℝ) : α+(s-α) = s := by ring
  simpa only [zero_add, he] using h

private theorem exterior_reflection (α β : ℝ) :
    (∫ z : ℂ in fzzScreeningPlaneExterior, fzzScreeningPlaneKernel α β z) =
      ∫ z : ℂ in fzzScreeningPlaneExterior, fzzScreeningPlaneKernel β α z := by
  have hp : (fun z : ℂ => 1-z) ⁻¹' fzzScreeningPlaneExterior = fzzScreeningPlaneExterior := by
    ext z
    simp only [fzzScreeningPlaneExterior, mem_preimage, mem_compl_iff, mem_union,
      mem_ball, dist_eq_norm, sub_zero, sub_sub_cancel_left, norm_neg, norm_sub_rev (1 : ℂ) z,
      or_comm]
  have h := (Measure.measurePreserving_sub_left (volume : Measure ℂ) 1).setIntegral_preimage_emb
    (Homeomorph.subLeft (1 : ℂ)).measurableEmbedding (fzzScreeningPlaneKernel α β)
      fzzScreeningPlaneExterior
  rw [hp] at h
  simpa only [fzzScreeningPlaneKernel_reflection] using h.symm

private theorem local_reflection (α β : ℝ) :
    (∫ z : ℂ in ball 1 (1/2), fzzScreeningOneSubtracted α β z) =
      ∫ z : ℂ in ball 0 (1/2), fzzScreeningZeroSubtracted β α z := by
  have h := fzzScreeningOneFinitePart_reflection α β
  unfold fzzScreeningOneFinitePart fzzScreeningZeroFinitePart at h
  exact add_right_cancel h

/-- The pole-cleared original subtracted source, defined explicitly even at alpha=-2
or beta=-2. It is not multiplication of a totalized singular quotient at those points. -/
def fzzScreeningPlaneClearedSource (α β : ℝ) : ℝ :=
  (α+2)*(β+2)*((∫ z : ℂ in ball 0 (1/2), fzzScreeningZeroSubtracted α β z) +
    (∫ z : ℂ in ball 1 (1/2), fzzScreeningOneSubtracted α β z) +
    (∫ z : ℂ in fzzScreeningPlaneExterior, fzzScreeningPlaneKernel α β z)) +
    2*Real.pi*(β+2)*(1/2 : ℝ)^(α+2) + 2*Real.pi*(α+2)*(1/2 : ℝ)^(β+2)

/-- Original reflection symmetry includes the exterior and both subtraction terms. -/
theorem fzzScreeningPlaneClearedSource_symm (α β : ℝ) :
    fzzScreeningPlaneClearedSource α β = fzzScreeningPlaneClearedSource β α := by
  unfold fzzScreeningPlaneClearedSource
  rw [local_reflection α β, local_reflection β α, exterior_reflection α β]
  ring

private theorem half_power_analytic (α : ℝ) :
    AnalyticAt ℝ (fun s : ℝ => (1/2 : ℝ)^(s+2)) α := by
  have h : AnalyticAt ℝ (fun s : ℝ => Real.exp (Real.log (1/2)*(s+2))) α := by fun_prop
  simpa only [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 1/2)] using h

private theorem cleared_source_analytic (α β : ℝ) (ha : -3 < α) (hb : -3 < β)
    (hs : α+β < -2) : AnalyticAt ℝ (fun s => fzzScreeningPlaneClearedSource s β) α := by
  have hi := ((zero_subtracted_analytic α β ha).add
    (one_subtracted_regular_analytic β α hb)).add (exterior_analytic α β hs)
  have hp : AnalyticAt ℝ (fun s : ℝ => (s+2)*(β+2)) α := by fun_prop
  have ht : AnalyticAt ℝ (fun s : ℝ => 2*Real.pi*(s+2)*(1/2 : ℝ)^(β+2)) α := by fun_prop
  have ht1 : AnalyticAt ℝ (fun s : ℝ => 2*Real.pi*(β+2)*(1/2 : ℝ)^(s+2)) α :=
    analyticAt_const.mul (half_power_analytic α)
  exact ((hp.mul hi).add ht1).add ht

/-- Analyticity of the explicitly pole-cleared original source on its full left slice.
The chart fixes beta>-3; the interval retains the exact tail condition. -/
theorem fzzScreeningPlaneClearedSource_analytic_left (v : ℝ) :
    AnalyticOnNhd ℝ (fun α => fzzScreeningPlaneClearedSource α (-3+Real.exp v))
      (Ioo (-3) (-2-(-3+Real.exp v))) := by
  intro α hα
  exact cleared_source_analytic α _ hα.1 (by linarith [Real.exp_pos v]) (by linarith [hα.2])

/-- Reflection gives the full right slice of the same original pole-cleared family. -/
theorem fzzScreeningPlaneClearedSource_analytic_right (u : ℝ) :
    AnalyticOnNhd ℝ (fun β => fzzScreeningPlaneClearedSource (-3+Real.exp u) β)
      (Ioo (-3) (-2-(-3+Real.exp u))) := by
  intro β hβ
  have h := fzzScreeningPlaneClearedSource_analytic_left u β hβ
  apply h.congr
  filter_upwards with s
  exact fzzScreeningPlaneClearedSource_symm s (-3+Real.exp u)


/-- The pole-cleared family retains the exact collision residues on both singular lines. -/
theorem fzzScreeningPlaneClearedSource_pole_values (β : ℝ) :
    fzzScreeningPlaneClearedSource (-2) β = 2*Real.pi*(β+2) ∧
      fzzScreeningPlaneClearedSource β (-2) = 2*Real.pi*(β+2) := by
  have h : fzzScreeningPlaneClearedSource (-2) β = 2*Real.pi*(β+2) := by
    simp [fzzScreeningPlaneClearedSource]
  exact ⟨h, (fzzScreeningPlaneClearedSource_symm β (-2)).trans h⟩

private theorem first_power_add_two_ne (u : ℝ) :
    fzzScreeningFirstContinuationPower u+2 ≠ 0 := by
  unfold fzzScreeningFirstContinuationPower
  have hp : 0 < (1+Real.exp u)⁻¹ := inv_pos.mpr (by positivity)
  linarith

/-- Away from the collision poles, the analytic source equals the explicit clearing
factor times the already proved original whole-plane finite part. -/
theorem fzzScreeningPlaneClearedSource_eq_finitePart (u v : ℝ) :
    fzzScreeningPlaneClearedSource (fzzScreeningFirstContinuationPower u)
      (fzzScreeningFirstContinuationPower v) =
      (fzzScreeningFirstContinuationPower u+2)*(fzzScreeningFirstContinuationPower v+2)*
        fzzScreeningPlaneFinitePart (fzzScreeningFirstContinuationPower u)
          (fzzScreeningFirstContinuationPower v) := by
  unfold fzzScreeningPlaneClearedSource fzzScreeningPlaneFinitePart
    fzzScreeningZeroFinitePart fzzScreeningOneFinitePart
  field_simp [first_power_add_two_ne u, first_power_add_two_ne v]
  ring

end GaloisForLFunctions.RHTower
