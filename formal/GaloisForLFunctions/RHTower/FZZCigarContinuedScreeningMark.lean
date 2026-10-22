import GaloisForLFunctions.RHTower.FZZCigarPlaneScreeningGammaContinuation
import Mathlib.Probability.Moments.MGFAnalytic
import GaloisForLFunctions.RHTower.FZZCigarPlaneScreeningMarkedDerivative

/-!
# Original logarithmic insertion after plane-screening continuation

The first exponent derivative is justified directly on the original source.
At zero and infinity, the proved open exponential-moment intervals admit the
logarithmic insertion. Splitting the signed source into positive and negative
weighted measures permits the moment-generating-function derivative theorem.
On the second collision disk, `log|z|` vanishes linearly at the puncture, which
admits the marked kernel and supplies a common local derivative bound.

The complete derivative retains all three integrals and the derivative of the
explicit power counterterm. Its normalization is legitimate because the
original finite part has a proved strictly negative sign. Only after original
differentiation is established do we use the source/Gamma continuation identity
to evaluate the response as four logarithmic Gamma derivatives.

These are derivatives of one independent position exponent in the first
continuation strip. Differentiated moving-cutoff limits, physical parameter
transport, higher screening sectors and the complete mixed Ward law are not
asserted here.
-/

open MeasureTheory Set Metric Filter ProbabilityTheory
open scoped Topology
noncomputable section
namespace GaloisForLFunctions.RHTower

private def positiveWeightMeasure {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (f : Ω → ℝ) : Measure Ω :=
  μ.withDensity (fun z => ENNReal.ofReal (max (f z) 0))

theorem positiveWeight_integrable {Ω : Type*} [MeasurableSpace Ω]
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

theorem positiveWeight_integralY {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (f Y : Ω → ℝ) (hf : Measurable f) :
    (∫ z, Y z ∂positiveWeightMeasure μ f) = ∫ z, max (f z) 0*Y z ∂μ := by
  rw [positiveWeightMeasure, integral_withDensity_eq_integral_toReal_smul
    (by fun_prop) (by filter_upwards with z; exact ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (le_max_right _ _), smul_eq_mul]

theorem positiveWeight_integrableY {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (f Y : Ω → ℝ) (hf : Measurable f)
    (hi : Integrable Y (positiveWeightMeasure μ f)) :
    Integrable (fun z => max (f z) 0*Y z) μ := by
  rw [positiveWeightMeasure, integrable_withDensity_iff_integrable_smul'
    (by fun_prop) (by filter_upwards with z; exact ENNReal.ofReal_lt_top)] at hi
  simpa only [ENNReal.toReal_ofReal (le_max_right _ _), smul_eq_mul] using hi

private theorem positive_sub_negative (r : ℝ) : max r 0-max (-r) 0 = r := by
  by_cases hr : 0 ≤ r
  · rw [max_eq_left hr, max_eq_right (neg_nonpos.mpr hr), sub_zero]
  · rw [max_eq_right (le_of_not_ge hr), max_eq_left (neg_nonneg.mpr (le_of_not_ge hr))]
    ring

theorem positive_exp_interior {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (f X : Ω → ℝ) (hf : Measurable f) (hX : Measurable X) (t : ℝ)
    (hi : ∀ᶠ s in 𝓝 t, Integrable (fun z => f z*Real.exp (s*X z)) μ) :
    t ∈ interior (integrableExpSet X (positiveWeightMeasure μ f)) := by
  apply mem_interior_iff_mem_nhds.mpr
  filter_upwards [hi] with s hs
  exact positiveWeight_integrable μ f X hf hX s hs

theorem signed_exp_hasDerivAt {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (f X : Ω → ℝ) (hf : Measurable f) (hX : Measurable X) (t : ℝ)
    (hi : ∀ᶠ s in 𝓝 t, Integrable (fun z => f z*Real.exp (s*X z)) μ) :
    Integrable (fun z => f z*(X z*Real.exp (t*X z))) μ ∧
      HasDerivAt (fun s => ∫ z, f z*Real.exp (s*X z) ∂μ)
        (∫ z, f z*(X z*Real.exp (t*X z)) ∂μ) t := by
  have hn : ∀ᶠ s in 𝓝 t, Integrable (fun z => (-f z)*Real.exp (s*X z)) μ := by
    filter_upwards [hi] with s hs
    convert! hs.neg using 1
    ext z
    dsimp
    ring
  have hp := positive_exp_interior μ f X hf hX t hi
  have hm := positive_exp_interior μ (fun z => -f z) X hf.neg hX t hn
  have hip : Integrable (fun z => max (f z) 0*(X z*Real.exp (t*X z))) μ := by
    apply positiveWeight_integrableY μ f _ hf
    simpa only [pow_one] using integrable_pow_mul_exp_of_mem_interior_integrableExpSet hp 1
  have him : Integrable (fun z => max (-f z) 0*(X z*Real.exp (t*X z))) μ := by
    apply positiveWeight_integrableY μ (fun z => -f z) _ hf.neg
    simpa only [pow_one] using integrable_pow_mul_exp_of_mem_interior_integrableExpSet hm 1
  have hpoint (z : Ω) (y : ℝ) :
      max (f z) 0*y-max (-f z) 0*y = f z*y := by
    rw [← sub_mul, positive_sub_negative]
  have hint : Integrable (fun z => f z*(X z*Real.exp (t*X z))) μ := by
    apply (hip.sub him).congr
    filter_upwards with z
    exact hpoint z _
  refine ⟨hint, ?_⟩
  have he : (fun s => ∫ z, f z*Real.exp (s*X z) ∂μ) =ᶠ[𝓝 t]
      (fun s => mgf X (positiveWeightMeasure μ f) s-
        mgf X (positiveWeightMeasure μ (fun z => -f z)) s) := by
    filter_upwards [hi,hn] with s hs ht
    have hsp := positiveWeight_integrableY μ f _ hf (positiveWeight_integrable μ f X hf hX s hs)
    have hsm := positiveWeight_integrableY μ (fun z => -f z) _ hf.neg
      (positiveWeight_integrable μ (fun z => -f z) X hf.neg hX s ht)
    rw [mgf, mgf, positiveWeight_integralY μ f _ hf,
      positiveWeight_integralY μ (fun z => -f z) _ hf.neg, ← integral_sub hsp hsm]
    apply integral_congr_ae
    filter_upwards with z
    exact (hpoint z _).symm
  have hd := ((hasDerivAt_mgf hp).sub (hasDerivAt_mgf hm)).congr_of_eventuallyEq he
  rw [positiveWeight_integralY μ f _ hf,
    positiveWeight_integralY μ (fun z => -f z) _ hf.neg, ← integral_sub hip him] at hd
  convert! hd using 1
  apply integral_congr_ae
  filter_upwards with z
  exact (hpoint z _).symm

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


private theorem exterior_admission (α β : ℝ) (hs : α+β < -2) :
    IntegrableOn (fzzScreeningPlaneKernel α β) fzzScreeningPlaneExterior := by
  have h := fzzScreeningPlaneExterior_integrable α (Real.log (-2-α-β))
  rw [Real.exp_log (by linarith : 0 < -2-α-β)] at h
  simpa only [show -2-α-(-2-α-β) = β by ring] using h


private theorem zero_marked_source (α β : ℝ) (ha : -3 < α) :
    IntegrableOn (fun z : ℂ => Real.log ‖z‖*fzzScreeningZeroSubtracted α β z)
      (ball 0 (1/2)) ∧
    HasDerivAt (fun δ => ∫ z : ℂ in ball 0 (1/2),
      fzzScreeningZeroSubtracted (α+δ) β z)
      (∫ z : ℂ in ball 0 (1/2), Real.log ‖z‖*fzzScreeningZeroSubtracted α β z) 0 := by
  have hshift : ∀ᶠ δ : ℝ in 𝓝 0, -3 < α+δ :=
    (isOpen_lt continuous_const (by fun_prop)).mem_nhds (by simpa using ha)
  have hi : ∀ᶠ δ : ℝ in 𝓝 0, Integrable
      (fun z => fzzScreeningZeroSubtracted α β z*Real.exp (δ*Real.log ‖z‖))
        (volume.restrict (ball 0 (1/2))) := by
    filter_upwards [hshift] with δ hδ
    apply (zero_subtracted_admission (α+δ) β hδ).congr
    filter_upwards [ae_restrict_of_ae (volume.ae_ne (0 : ℂ))] with z hz
    exact (zero_subtracted_shift α β δ hz).symm
  have h := signed_exp_hasDerivAt (volume.restrict (ball (0 : ℂ) (1/2)))
    (fzzScreeningZeroSubtracted α β) (fun z => Real.log ‖z‖)
    (by unfold fzzScreeningZeroSubtracted; fun_prop) (by fun_prop) 0 hi
  simp only [zero_mul, Real.exp_zero, mul_one] at h
  have he : (fun δ => ∫ z : ℂ in ball 0 (1/2), fzzScreeningZeroSubtracted (α+δ) β z) =ᶠ[𝓝 0]
      (fun δ => ∫ z : ℂ in ball 0 (1/2),
        fzzScreeningZeroSubtracted α β z*Real.exp (δ*Real.log ‖z‖)) := by
    filter_upwards with δ
    apply integral_congr_ae
    filter_upwards [ae_restrict_of_ae (volume.ae_ne (0 : ℂ))] with z hz
    exact (zero_subtracted_shift α β δ hz).symm
  constructor
  · simpa only [IntegrableOn, mul_comm] using h.1
  · simpa only [mul_comm] using h.2.congr_of_eventuallyEq he

theorem exterior_marked_source (α β : ℝ) (hs : α+β < -2) :
    IntegrableOn (fun z : ℂ => Real.log ‖z‖*fzzScreeningPlaneKernel α β z)
      fzzScreeningPlaneExterior ∧
    HasDerivAt (fun δ => ∫ z : ℂ in fzzScreeningPlaneExterior,
      fzzScreeningPlaneKernel (α+δ) β z)
      (∫ z : ℂ in fzzScreeningPlaneExterior, Real.log ‖z‖*fzzScreeningPlaneKernel α β z) 0 := by
  have hshift : ∀ᶠ δ : ℝ in 𝓝 0, (α+δ)+β < -2 :=
    (isOpen_lt (by fun_prop) continuous_const).mem_nhds (by simpa using hs)
  have hi : ∀ᶠ δ : ℝ in 𝓝 0, Integrable
      (fun z => fzzScreeningPlaneKernel α β z*Real.exp (δ*Real.log ‖z‖))
        (volume.restrict fzzScreeningPlaneExterior) := by
    filter_upwards [hshift] with δ hδ
    apply (exterior_admission (α+δ) β hδ).congr
    filter_upwards [ae_restrict_of_ae (volume.ae_ne (0 : ℂ))] with z hz
    exact (plane_kernel_shift α β δ hz).symm
  have h := signed_exp_hasDerivAt (volume.restrict fzzScreeningPlaneExterior)
    (fzzScreeningPlaneKernel α β) (fun z => Real.log ‖z‖)
    (by unfold fzzScreeningPlaneKernel; fun_prop) (by fun_prop) 0 hi
  simp only [zero_mul, Real.exp_zero, mul_one] at h
  have he : (fun δ => ∫ z : ℂ in fzzScreeningPlaneExterior, fzzScreeningPlaneKernel (α+δ) β z) =ᶠ[𝓝 0]
      (fun δ => ∫ z : ℂ in fzzScreeningPlaneExterior,
        fzzScreeningPlaneKernel α β z*Real.exp (δ*Real.log ‖z‖)) := by
    filter_upwards with δ
    apply integral_congr_ae
    filter_upwards [ae_restrict_of_ae (volume.ae_ne (0 : ℂ))] with z hz
    exact (plane_kernel_shift α β δ hz).symm
  constructor
  · simpa only [IntegrableOn, mul_comm] using h.1
  · simpa only [mul_comm] using h.2.congr_of_eventuallyEq he

private theorem one_marked_source (α β : ℝ) (hb : -3 < β) :
    IntegrableOn (fun z : ℂ => Real.log ‖z‖*fzzScreeningPlaneKernel α β z)
      (ball 1 (1/2)) ∧
    HasDerivAt (fun a => ∫ z : ℂ in ball 1 (1/2),
      fzzScreeningOneSubtracted a β z)
      (∫ z : ℂ in ball 1 (1/2), Real.log ‖z‖*fzzScreeningPlaneKernel α β z) α := by
  obtain ⟨C,hC⟩ := (isCompact_closedBall (1 : ℂ) (1/2)).exists_bound_of_continuousOn
    log_norm_smooth_one.continuousOn
  have hC0 : 0 ≤ C := by
    simpa using hC 1 (show (1 : ℂ) ∈ closedBall 1 (1/2) by simp)
  let B : ℂ → ℝ := fun z => ‖oneLogWeight β z‖*Real.exp ((|α|+1)*C)
  have hB : IntegrableOn B (ball 1 (1/2)) :=
    (oneLogWeight_integrable β hb).norm.mul_const _
  have hI : IntegrableOn (fzzScreeningOneSubtracted α β) (ball 1 (1/2)) := by
    have h := fzzScreeningOneSubtracted_integrable α (Real.log (β+3))
    rw [Real.exp_log (by linarith : 0 < β+3)] at h
    simpa only [show -3+(β+3) = β by ring] using h
  have hbound : ∀ᵐ z ∂(volume.restrict (ball (1 : ℂ) (1/2))),
      ∀ s ∈ Ioo (α-1) (α+1), ‖oneLogWeight β z*Real.exp (s*Real.log ‖z‖)‖ ≤ B z := by
    filter_upwards [ae_restrict_mem measurableSet_ball] with z hz s hs
    have hl := hC z (ball_subset_closedBall hz)
    have hsa : |s| ≤ |α|+1 := by
      apply abs_le.mpr
      constructor <;> linarith [le_abs_self α, neg_abs_le α, hs.1, hs.2]
    have he : s*Real.log ‖z‖ ≤ (|α|+1)*C := by
      calc
        _ ≤ |s*Real.log ‖z‖| := le_abs_self _
        _ = |s| * ‖Real.log ‖z‖‖ := by rw [abs_mul, Real.norm_eq_abs]
        _ ≤ (|α|+1)*C := mul_le_mul hsa hl (norm_nonneg _) (by positivity)
    rw [norm_mul, Real.norm_of_nonneg (Real.exp_pos _).le]
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr he) (norm_nonneg _)
  have hd : ∀ᵐ z ∂(volume.restrict (ball (1 : ℂ) (1/2))),
      ∀ s ∈ Ioo (α-1) (α+1), HasDerivAt (fun a => fzzScreeningOneSubtracted a β z)
        (oneLogWeight β z*Real.exp (s*Real.log ‖z‖)) s := by
    filter_upwards [ae_restrict_of_ae (volume.ae_ne (0 : ℂ))] with z hz s _
    have hn := norm_pos_iff.mpr hz
    have h := ((((hasDerivAt_id s).mul_const (Real.log ‖z‖)).exp).sub_const 1).const_mul (‖z-1‖^β)
    convert! h using 1
    · ext a
      simp only [fzzScreeningOneSubtracted, id_eq, Real.rpow_def_of_pos hn, mul_comm]
    · dsimp [oneLogWeight]
      ring
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun a z => fzzScreeningOneSubtracted a β z)
    (F' := fun a z => oneLogWeight β z*Real.exp (a*Real.log ‖z‖))
    (Ioo_mem_nhds (by linarith : α-1 < α) (by linarith : α < α+1))
    (by filter_upwards with a; unfold fzzScreeningOneSubtracted; fun_prop) hI
    (by unfold oneLogWeight; fun_prop) hbound hB hd
  have he : (fun z : ℂ => oneLogWeight β z*Real.exp (α*Real.log ‖z‖)) =ᶠ[
      ae (volume.restrict (ball 1 (1/2)))]
      (fun z : ℂ => Real.log ‖z‖*fzzScreeningPlaneKernel α β z) := by
    filter_upwards [ae_restrict_of_ae (volume.ae_ne (0 : ℂ))] with z hz
    rw [oneLogWeight, fzzScreeningPlaneKernel, Real.rpow_def_of_pos (norm_pos_iff.mpr hz)]
    rw [mul_comm (Real.log ‖z‖) α]
    ring
  exact ⟨h.1.congr he, (integral_congr_ae he) ▸ h.2⟩

/-- Derivative of a retained local power counterterm with respect to its exponent. -/
def fzzScreeningPowerCountertermMark (r α : ℝ) : ℝ :=
  2*Real.pi*r^(α+2)*(Real.log r/(α+2)-1/(α+2)^(2 : ℕ))

private theorem power_counterterm_hasDerivAt (r α : ℝ) (hr : 0 < r) (ha : α+2 ≠ 0) :
    HasDerivAt (fun a => 2*Real.pi*r^(a+2)/(a+2))
      (fzzScreeningPowerCountertermMark r α) α := by
  have hi : HasDerivAt (fun a : ℝ => a+2) 1 α := by
    simpa using (hasDerivAt_id α).add_const 2
  have hd := ((HasDerivAt.const_rpow hr hi).const_mul (2*Real.pi)).div hi ha
  convert! hd using 1
  unfold fzzScreeningPowerCountertermMark
  field_simp

/-- The complete first position mark: both original collision integrals, exterior,
and the derivative of the explicit local counterterm are retained. -/
def fzzScreeningPlaneContinuedMark (α β : ℝ) : ℝ :=
  (∫ z : ℂ in ball 0 (1/2), Real.log ‖z‖*fzzScreeningZeroSubtracted α β z) +
  (∫ z : ℂ in ball 1 (1/2), Real.log ‖z‖*fzzScreeningPlaneKernel α β z) +
  (∫ z : ℂ in fzzScreeningPlaneExterior, Real.log ‖z‖*fzzScreeningPlaneKernel α β z) +
  fzzScreeningPowerCountertermMark (1/2) α

private theorem first_power_range (u : ℝ) :
    -3 < fzzScreeningFirstContinuationPower u ∧ fzzScreeningFirstContinuationPower u < -2 := by
  have hden : 0 < 1+Real.exp u := by positivity
  have hp := inv_pos.mpr hden
  have hlt : (1+Real.exp u)⁻¹ < 1 := (inv_lt_one₀ hden).mpr (by linarith [Real.exp_pos u])
  unfold fzzScreeningFirstContinuationPower
  constructor <;> linarith

private theorem finitePart_hasDerivAt (α β : ℝ) (ha : -3 < α) (hb : -3 < β)
    (hs : α+β < -2) (ha2 : α+2 ≠ 0) :
    HasDerivAt (fun a => fzzScreeningPlaneFinitePart a β)
      (fzzScreeningPlaneContinuedMark α β) α := by
  have hz := (zero_marked_source α β ha).2
  have hz' : HasDerivAt (fun δ => ∫ z : ℂ in ball 0 (1/2),
      fzzScreeningZeroSubtracted (α+δ) β z)
      (∫ z : ℂ in ball 0 (1/2), Real.log ‖z‖*fzzScreeningZeroSubtracted α β z) (α-α) := by
    simpa using hz
  have hz0 := hz'.comp_of_eq α ((hasDerivAt_id α).sub_const α) rfl
  have he := (exterior_marked_source α β hs).2
  have he' : HasDerivAt (fun δ => ∫ z : ℂ in fzzScreeningPlaneExterior,
      fzzScreeningPlaneKernel (α+δ) β z)
      (∫ z : ℂ in fzzScreeningPlaneExterior, Real.log ‖z‖*fzzScreeningPlaneKernel α β z) (α-α) := by
    simpa using he
  have he0 := he'.comp_of_eq α ((hasDerivAt_id α).sub_const α) rfl
  have h1 := (one_marked_source α β hb).2.add_const
    (2*Real.pi*(1/2 : ℝ)^(β+2)/(β+2))
  have hc := power_counterterm_hasDerivAt (1/2) α (by norm_num) ha2
  have hd := ((hz0.add hc).add h1).add he0
  convert! hd using 1
  · ext a
    simp only [Pi.add_apply, Function.comp_apply, id_eq, fzzScreeningPlaneFinitePart, fzzScreeningZeroFinitePart,
      fzzScreeningOneFinitePart, show α+(a-α) = a by ring]
  · simp only [fzzScreeningPlaneContinuedMark, mul_one]
    ring

/-- All three retained original logarithmic integrals are absolutely convergent. -/
theorem fzzScreeningPlaneContinuedMark_integrable (u v : ℝ) :
    IntegrableOn (fun z : ℂ => Real.log ‖z‖*fzzScreeningZeroSubtracted
      (fzzScreeningFirstContinuationPower u) (fzzScreeningFirstContinuationPower v) z)
      (ball 0 (1/2)) ∧
    IntegrableOn (fun z : ℂ => Real.log ‖z‖*fzzScreeningPlaneKernel
      (fzzScreeningFirstContinuationPower u) (fzzScreeningFirstContinuationPower v) z)
      (ball 1 (1/2)) ∧
    IntegrableOn (fun z : ℂ => Real.log ‖z‖*fzzScreeningPlaneKernel
      (fzzScreeningFirstContinuationPower u) (fzzScreeningFirstContinuationPower v) z)
      fzzScreeningPlaneExterior := by
  have hu := first_power_range u
  have hv := first_power_range v
  exact ⟨(zero_marked_source _ _ hu.1).1, (one_marked_source _ _ hv.1).1,
    (exterior_marked_source _ _ (by linarith [hu.2,hv.2])).1⟩

/-- Differentiation of the actual continued original source retains its logarithmic
insertions and the differentiated collision counterterm. -/
theorem fzzScreeningPlaneFinitePart_hasDerivAt (u v : ℝ) :
    HasDerivAt (fun a => fzzScreeningPlaneFinitePart a (fzzScreeningFirstContinuationPower v))
      (fzzScreeningPlaneContinuedMark (fzzScreeningFirstContinuationPower u)
        (fzzScreeningFirstContinuationPower v)) (fzzScreeningFirstContinuationPower u) := by
  have hu := first_power_range u
  have hv := first_power_range v
  exact finitePart_hasDerivAt _ _ hu.1 hv.1 (by linarith [hu.2,hv.2]) (by linarith [hu.2])

/-- The actual normalized continued insertion is the derivative of the real logarithm
of the original finite part; its nonvanishing denominator is proved by the source sign. -/
theorem fzzScreeningPlaneFinitePart_log_hasDerivAt (u v : ℝ) :
    HasDerivAt (fun a => Real.log (fzzScreeningPlaneFinitePart a (fzzScreeningFirstContinuationPower v)))
      (fzzScreeningPlaneContinuedMark (fzzScreeningFirstContinuationPower u)
        (fzzScreeningFirstContinuationPower v) /
          fzzScreeningPlaneFinitePart (fzzScreeningFirstContinuationPower u)
            (fzzScreeningFirstContinuationPower v)) (fzzScreeningFirstContinuationPower u) :=
  (fzzScreeningPlaneFinitePart_hasDerivAt u v).log (fzzScreeningPlaneFinitePart_neg u v).ne

private theorem no_gamma_poles {s : ℝ} (hs : 0 < s ∨ (-1 < s ∧ s < 0)) :
    ∀ n : ℕ, s ≠ -n := by
  intro n hn
  rcases hs with hs|hs
  · have hp : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  · cases n with
    | zero => norm_num at hn; linarith [hs.2]
    | succ n =>
      have hp : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      push_cast at hn
      linarith [hs.1]

private theorem gamma_log_affine (s m : ℝ) (hs : 0 < s ∨ (-1 < s ∧ s < 0)) :
    HasDerivAt (fun δ : ℝ => Real.log (Real.Gamma (s+m*δ)))
      (m*fzzScreeningPlaneGammaLogSlope s) 0 := by
  have h := (Real.differentiableAt_Gamma (no_gamma_poles hs)).hasDerivAt.log
    (Real.Gamma_ne_zero (no_gamma_poles hs))
  have h0 : HasDerivAt (fun r : ℝ => Real.log (Real.Gamma r))
      (fzzScreeningPlaneGammaLogSlope s) (s+m*0) := by simpa only [fzzScreeningPlaneGammaLogSlope, mul_zero, add_zero] using h
  have hd := h0.comp_of_eq 0 ((hasDerivAt_const (0 : ℝ) s).add ((hasDerivAt_id (0 : ℝ)).const_mul m)) rfl
  convert! hd using 1
  simp [mul_comm]

private def continuedGammaLog (α β : ℝ) : ℝ :=
  Real.log Real.pi + Real.log (Real.Gamma (-α/2-β/2-1)) +
    Real.log (Real.Gamma (1+α/2)) + Real.log (Real.Gamma (1+β/2)) -
      Real.log (Real.Gamma (-α/2)) - Real.log (Real.Gamma (-β/2)) -
        Real.log (Real.Gamma (2+α/2+β/2))

private theorem continuedGamma_log_eq (α β : ℝ) (ha : -3 < α) (ha2 : α < -2)
    (hb : -3 < β) (hb2 : β < -2) :
    Real.log (fzzScreeningPlaneContinuedGamma α β) = continuedGammaLog α β := by
  have h0 := Real.pi_pos.ne'
  have h1 := Real.Gamma_ne_zero (no_gamma_poles (Or.inl (by linarith : 0 < -α/2-β/2-1)))
  have h2 : Real.Gamma (1+α/2) ≠ 0 := Real.Gamma_ne_zero (no_gamma_poles (Or.inr ⟨by linarith, by linarith⟩))
  have h3 : Real.Gamma (1+β/2) ≠ 0 := Real.Gamma_ne_zero (no_gamma_poles (Or.inr ⟨by linarith, by linarith⟩))
  have h4 := Real.Gamma_ne_zero (no_gamma_poles (Or.inl (by linarith : 0 < -α/2)))
  have h5 := Real.Gamma_ne_zero (no_gamma_poles (Or.inl (by linarith : 0 < -β/2)))
  have h6 : Real.Gamma (2+α/2+β/2) ≠ 0 := Real.Gamma_ne_zero (no_gamma_poles (Or.inr ⟨by linarith, by linarith⟩))
  unfold fzzScreeningPlaneContinuedGamma continuedGammaLog
  rw [Real.log_div (mul_ne_zero (mul_ne_zero (mul_ne_zero h0 h1) h2) h3)
    (mul_ne_zero (mul_ne_zero h4 h5) h6)]
  rw [Real.log_mul (mul_ne_zero (mul_ne_zero h0 h1) h2) h3,
    Real.log_mul (mul_ne_zero h0 h1) h2, Real.log_mul h0 h1,
    Real.log_mul (mul_ne_zero h4 h5) h6, Real.log_mul h4 h5]
  ring

/-- Four-term Gamma response, identified below with the original continued insertion. -/
def fzzScreeningPlaneContinuedGammaSlope (α β : ℝ) : ℝ :=
  (-fzzScreeningPlaneGammaLogSlope (-α/2-β/2-1) +
    fzzScreeningPlaneGammaLogSlope (1+α/2) + fzzScreeningPlaneGammaLogSlope (-α/2) -
      fzzScreeningPlaneGammaLogSlope (2+α/2+β/2))/2

private theorem continuedGammaLog_hasDerivAt (α β : ℝ) (ha : -3 < α) (ha2 : α < -2)
    (hb : -3 < β) (hb2 : β < -2) :
    HasDerivAt (fun δ : ℝ => continuedGammaLog (α+δ) β)
      (fzzScreeningPlaneContinuedGammaSlope α β) 0 := by
  have h1 := gamma_log_affine (-α/2-β/2-1) (-1/2) (Or.inl (by linarith))
  have h2 := gamma_log_affine (1+α/2) (1/2) (Or.inr ⟨by linarith,by linarith⟩)
  have h3 := gamma_log_affine (-α/2) (-1/2) (Or.inl (by linarith))
  have h4 := gamma_log_affine (2+α/2+β/2) (1/2) (Or.inr ⟨by linarith,by linarith⟩)
  have hd := (((((hasDerivAt_const (0 : ℝ) (Real.log Real.pi)).add h1).add h2).add_const
    (Real.log (Real.Gamma (1+β/2)))).sub h3 |>.sub_const (Real.log (Real.Gamma (-β/2)))).sub h4
  convert! hd using 1
  · ext δ
    simp only [Pi.add_apply, Pi.sub_apply, continuedGammaLog,
      show -α/2+(-1/2)*δ-β/2-1 = -α/2-β/2-1+(-1/2)*δ by ring,
      show 1+(α+δ)/2 = 1+α/2+(1/2)*δ by ring,
      show -(α+δ)/2 = -α/2+(-1/2)*δ by ring,
      show 2+(α+δ)/2+β/2 = 2+α/2+β/2+(1/2)*δ by ring]
  · unfold fzzScreeningPlaneContinuedGammaSlope
    ring

private theorem first_power_surjective (α : ℝ) (ha : -3 < α) (ha2 : α < -2) :
    ∃ u : ℝ, fzzScreeningFirstContinuationPower u = α := by
  have hp : 0 < (α+3)/(-α-2) := div_pos (by linarith) (by linarith)
  refine ⟨Real.log ((α+3)/(-α-2)), ?_⟩
  unfold fzzScreeningFirstContinuationPower
  rw [Real.exp_log hp]
  have hh : 1+(α+3)/(-α-2) = 1/(-α-2) := by
    field_simp [show -α-2 ≠ 0 by linarith] <;> ring
  rw [hh, one_div, inv_inv]
  ring

private theorem continued_source_gamma_log_eventually (α β : ℝ)
    (ha : -3 < α) (ha2 : α < -2) (hb : -3 < β) (hb2 : β < -2) :
    (fun δ : ℝ => Real.log (fzzScreeningPlaneFinitePart (α+δ) β)) =ᶠ[𝓝 0]
      (fun δ : ℝ => continuedGammaLog (α+δ) β) := by
  have hn : ∀ᶠ δ : ℝ in 𝓝 0, α+δ ∈ Ioo (-3) (-2) := by
    exact (isOpen_Ioo.preimage (show Continuous (fun δ : ℝ => α+δ) by fun_prop)).mem_nhds (by simpa using And.intro ha ha2)
  obtain ⟨v,hv⟩ := first_power_surjective β hb hb2
  filter_upwards [hn] with δ hδ
  obtain ⟨u,hu⟩ := first_power_surjective (α+δ) hδ.1 hδ.2
  have he := fzzScreeningPlaneFinitePart_eq_gamma u v
  rw [hu,hv] at he
  rw [he, continuedGamma_log_eq _ β hδ.1 hδ.2 hb hb2]


/-- The normalized original continued insertion equals the full four-term Gamma
response, after original differentiation and source continuation have both been proved. -/
theorem fzzScreeningPlaneContinuedMark_logResponse (u v : ℝ) :
    fzzScreeningPlaneContinuedMark (fzzScreeningFirstContinuationPower u)
      (fzzScreeningFirstContinuationPower v) /
        fzzScreeningPlaneFinitePart (fzzScreeningFirstContinuationPower u)
          (fzzScreeningFirstContinuationPower v) =
      fzzScreeningPlaneContinuedGammaSlope (fzzScreeningFirstContinuationPower u)
        (fzzScreeningFirstContinuationPower v) := by
  let α := fzzScreeningFirstContinuationPower u
  let β := fzzScreeningFirstContinuationPower v
  have hu := first_power_range u
  have hv := first_power_range v
  have hm := fzzScreeningPlaneFinitePart_log_hasDerivAt u v
  have h0 := hm.comp_of_eq 0 ((hasDerivAt_const (0 : ℝ) α).add (hasDerivAt_id (0 : ℝ)))
    (by simp [α])
  have hh : HasDerivAt (fun δ : ℝ => Real.log (fzzScreeningPlaneFinitePart (α+δ) β))
      (fzzScreeningPlaneContinuedMark α β/fzzScreeningPlaneFinitePart α β) 0 := by
    convert! h0 using 1 <;> simp [α, β]
  have hg := continuedGammaLog_hasDerivAt α β hu.1 hu.2 hv.1 hv.2
  exact hh.unique (hg.congr_of_eventuallyEq
    (continued_source_gamma_log_eventually α β hu.1 hu.2 hv.1 hv.2))

end GaloisForLFunctions.RHTower
