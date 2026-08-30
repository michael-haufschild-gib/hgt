import GaloisForLFunctions.RHTower.BurnolSoninUnitFirstJetEvaluation

/-!
# All-order bounded tail jets for the literal Burnol--Sonine Mellin transform

For the unit aperture, the tail of a Sonine vector is paired with
`t ↦ t⁻ʷ` on `(1,∞)`.  The `k`-th spectral derivative has the literal
kernel `(-log t)^k t⁻ʷ`.  This file proves, for every fixed natural `k`,
that this kernel is in `L²` in the strict right half strip and packages its
Riesz functional.  Thus the all-order *tail* obstruction is removed without
postulating a jet topology or differentiating an improper integral.

The remaining Burnol work is deliberately separate: the `L_a/K_a/P_a`
closed-span/complement and aperture-completeness/minimality arguments.  The
source-selected completed continuation and finite jet boundedness are
formalized in `BurnolSoninCompletedJetBridge`.
-/

open Complex Real MeasureTheory Set Filter Topology

noncomputable section

namespace RHTower

/-- The literal `k`-th logarithmic kernel on the Burnol--Sonine tail. -/
def soninMellinLogPowerKernel (k : ℕ) (w : ℂ) (t : ℝ) : ℂ :=
  (-(Real.log t : ℂ)) ^ k * soninMellinKernel w t

/-- The zeroth logarithmic kernel is the original Mellin kernel. -/
theorem soninMellinLogPowerKernel_zero (w : ℂ) :
    soninMellinLogPowerKernel 0 w = soninMellinKernel w := by
  funext t
  simp [soninMellinLogPowerKernel]

/-- The first logarithmic kernel is the already established derivative kernel. -/
theorem soninMellinLogPowerKernel_one (w : ℂ) :
    soninMellinLogPowerKernel 1 w = soninMellinDerivativeKernel w := by
  funext t
  simp [soninMellinLogPowerKernel, soninMellinDerivativeKernel]

/-- Exact norm of the literal `k`-th logarithmic Mellin kernel. -/
theorem norm_soninMellinLogPowerKernel {t : ℝ} (ht : 0 < t) (k : ℕ) (w : ℂ) :
    ‖soninMellinLogPowerKernel k w t‖ = |Real.log t| ^ k * t ^ (-w.re) := by
  rw [soninMellinLogPowerKernel, norm_mul, norm_pow, norm_neg,
    Complex.norm_real, Real.norm_eq_abs, norm_soninMellinKernel ht]

/-- Measurability of every literal logarithmic tail kernel. -/
theorem aestronglyMeasurable_soninMellinLogPowerKernel (k : ℕ) (w : ℂ) :
    AEStronglyMeasurable (soninMellinLogPowerKernel k w)
      (volume.restrict (Ioi (1 : ℝ))) := by
  have hlog : AEStronglyMeasurable (fun t : ℝ => (Real.log t : ℂ))
      (volume.restrict (Ioi (1 : ℝ))) := by
    refine (Complex.continuous_ofReal.comp_continuousOn ?_).aestronglyMeasurable measurableSet_Ioi
    exact Real.continuousOn_log.mono
      (fun t ht => ne_of_gt (lt_trans zero_lt_one (mem_Ioi.mp ht)))
  have hkernel : AEStronglyMeasurable (soninMellinKernel w)
      (volume.restrict (Ioi (1 : ℝ))) :=
    aestronglyMeasurable_soninMellinKernel w measurableSet_Ioi
      (fun t ht => lt_trans zero_lt_one (mem_Ioi.mp ht))
  change AEStronglyMeasurable
    ((fun t : ℝ => (-(Real.log t : ℂ)) ^ k) * soninMellinKernel w)
      (volume.restrict (Ioi (1 : ℝ)))
  exact (hlog.neg.pow k).mul hkernel

/-- Differentiating the literal order-`k` tail kernel produces exactly the
order-`k+1` tail kernel. -/
theorem hasDerivAt_soninMellinLogPowerKernel {t : ℝ} (ht : 0 < t)
    (k : ℕ) (w : ℂ) :
    HasDerivAt (fun z : ℂ => soninMellinLogPowerKernel k z t)
      (soninMellinLogPowerKernel (k + 1) w t) w := by
  change HasDerivAt
    (fun z : ℂ => (-(Real.log t : ℂ)) ^ k * soninMellinKernel z t) _ w
  have h := (hasDerivAt_soninMellinKernel ht w).const_mul
    ((-(Real.log t : ℂ)) ^ k)
  simpa [soninMellinLogPowerKernel, soninMellinDerivativeKernel, pow_succ,
    mul_assoc] using h

/-- A fixed strict strip margin gives one `L²` majorant for an arbitrary
finite logarithmic kernel throughout a spectral ball. -/
theorem norm_soninMellinLogPowerKernel_le_tail_majorant
    (k : ℕ) {w z : ℂ} {epsilon : ℝ} (hepsilon : 0 < epsilon)
    (hz : z ∈ Metric.ball w epsilon) {t : ℝ} (ht : 1 < t) :
    ‖soninMellinLogPowerKernel k z t‖ ≤
      ((epsilon / ((k : ℝ) + 1))⁻¹) ^ k *
        ‖soninMellinKernel (w - (2 * epsilon : ℝ)) t‖ := by
  let delta : ℝ := epsilon / ((k : ℝ) + 1)
  have hdelta : 0 < delta := by
    dsimp [delta]
    positivity
  have hdelta_eq : ((k : ℝ) + 1) * delta = epsilon := by
    dsimp [delta]
    field_simp
  have hkdelta : (k : ℝ) * delta ≤ epsilon := by
    have hk : (k : ℝ) ≤ (k : ℝ) + 1 := by linarith
    have := mul_le_mul_of_nonneg_right hk hdelta.le
    nlinarith
  have ht0 : 0 < t := lt_trans zero_lt_one ht
  have hdist : ‖w - z‖ < epsilon := by
    rw [Metric.mem_ball, dist_eq_norm] at hz
    calc
      ‖w - z‖ = ‖z - w‖ := by
        rw [← norm_neg (w - z)]
        congr 1
        ring
      _ < epsilon := hz
  have hlower : w.re - epsilon < z.re := by
    have h := (Complex.abs_re_le_norm (w - z)).trans_lt hdist
    rw [abs_lt] at h
    simp only [Complex.sub_re] at h
    linarith
  have hlog0 : 0 ≤ Real.log t := Real.log_nonneg ht.le
  have hlog : Real.log t ≤ t ^ delta / delta :=
    Real.log_le_rpow_div (le_trans zero_le_one ht.le) hdelta
  have hlogpow : (Real.log t) ^ k ≤ (t ^ delta / delta) ^ k :=
    pow_le_pow_left₀ hlog0 hlog k
  have hpow : 0 ≤ t ^ (-z.re) := Real.rpow_nonneg ht0.le _
  have hmul : (Real.log t) ^ k * t ^ (-z.re) ≤
      (t ^ delta / delta) ^ k * t ^ (-z.re) :=
    mul_le_mul_of_nonneg_right hlogpow hpow
  have hrewrite : (t ^ delta / delta) ^ k * t ^ (-z.re) =
      (delta⁻¹) ^ k * t ^ (delta * (k : ℝ) + -z.re) := by
    have htpow : (t ^ delta) ^ k = t ^ (delta * (k : ℝ)) := by
      calc
        (t ^ delta) ^ k = (t ^ delta) ^ (k : ℝ) :=
          (Real.rpow_natCast _ k).symm
        _ = t ^ (delta * (k : ℝ)) := (Real.rpow_mul ht0.le _ _).symm
    calc
      (t ^ delta / delta) ^ k * t ^ (-z.re) =
          (delta⁻¹) ^ k * ((t ^ delta) ^ k * t ^ (-z.re)) := by
            rw [div_eq_mul_inv, mul_pow]
            ring
      _ = (delta⁻¹) ^ k * (t ^ (delta * (k : ℝ)) * t ^ (-z.re)) := by
            rw [htpow]
      _ = (delta⁻¹) ^ k * t ^ (delta * (k : ℝ) + -z.re) := by
            rw [← Real.rpow_add ht0]
  have hexp : delta * (k : ℝ) + -z.re ≤
      -((w - (2 * epsilon : ℝ)).re) := by
    dsimp
    norm_num
    nlinarith
  have hmon : t ^ (delta * (k : ℝ) + -z.re) ≤
      t ^ (-((w - (2 * epsilon : ℝ)).re)) :=
    Real.rpow_le_rpow_of_exponent_le ht.le hexp
  have hscale : 0 ≤ (delta⁻¹) ^ k :=
    pow_nonneg (inv_nonneg.mpr hdelta.le) _
  rw [norm_soninMellinLogPowerKernel ht0, abs_of_nonneg hlog0,
    norm_soninMellinKernel ht0]
  calc
    (Real.log t) ^ k * t ^ (-z.re) ≤
        (t ^ delta / delta) ^ k * t ^ (-z.re) := hmul
    _ = (delta⁻¹) ^ k * t ^ (delta * (k : ℝ) + -z.re) := hrewrite
    _ ≤ (delta⁻¹) ^ k * t ^ (-((w - (2 * epsilon : ℝ)).re)) :=
      mul_le_mul_of_nonneg_left hmon hscale
    _ = ((epsilon / ((k : ℝ) + 1))⁻¹) ^ k *
        t ^ (-((w - (2 * epsilon : ℝ)).re)) := by
      rfl

/-- Every finite logarithmic Mellin jet is square-integrable on the literal
unit-aperture tail.  A small loss in the real exponent absorbs `log(t)^k`.
-/
theorem memLp_soninMellinLogPowerKernel_Ioi_one (k : ℕ) {w : ℂ}
    (hlo : 1 / 2 < w.re) :
    MemLp (soninMellinLogPowerKernel k w) 2 (volume.restrict (Ioi (1 : ℝ))) := by
  let delta : ℝ := (w.re - 1 / 2) / (2 * ((k : ℝ) + 1))
  have hdelta : 0 < delta := by
    dsimp [delta]
    positivity
  let w' : ℂ := w - ((k : ℝ) * delta)
  have hklt : (k : ℝ) < (k : ℝ) + 1 := by linarith
  have hdelta_eq : 2 * ((k : ℝ) + 1) * delta = w.re - 1 / 2 := by
    dsimp [delta]
    field_simp
  have hshift : (k : ℝ) * delta < (w.re - 1 / 2) / 2 := by
    have hkdelta : (k : ℝ) * delta < ((k : ℝ) + 1) * delta :=
      mul_lt_mul_of_pos_right hklt hdelta
    nlinarith
  have hw' : 1 / 2 < w'.re := by
    dsimp [w']
    norm_num
    linarith
  have hbase : MemLp (soninMellinKernel w') 2 (volume.restrict (Ioi (1 : ℝ))) :=
    memLp_soninMellinKernel_Ioi hw' zero_lt_one
  refine (hbase.const_mul (((delta⁻¹) ^ k : ℝ) : ℂ)).mono
    (aestronglyMeasurable_soninMellinLogPowerKernel k w) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have ht1 : 1 < t := mem_Ioi.mp ht
  have ht0 : 0 < t := lt_trans zero_lt_one ht1
  have hlog0 : 0 ≤ Real.log t := Real.log_nonneg ht1.le
  have hlog : Real.log t ≤ t ^ delta / delta :=
    Real.log_le_rpow_div (le_trans zero_le_one ht1.le) hdelta
  have hlogpow : (Real.log t) ^ k ≤ (t ^ delta / delta) ^ k :=
    pow_le_pow_left₀ hlog0 hlog k
  have hpow : 0 ≤ t ^ (-w.re) := Real.rpow_nonneg ht0.le _
  have hmul : (Real.log t) ^ k * t ^ (-w.re) ≤
      (t ^ delta / delta) ^ k * t ^ (-w.re) :=
    mul_le_mul_of_nonneg_right hlogpow hpow
  have hrewrite : (t ^ delta / delta) ^ k * t ^ (-w.re) =
      (delta⁻¹) ^ k * t ^ (-w'.re) := by
    have htpow : (t ^ delta) ^ k = t ^ (delta * (k : ℝ)) := by
      calc
        (t ^ delta) ^ k = (t ^ delta) ^ (k : ℝ) :=
          (Real.rpow_natCast _ k).symm
        _ = t ^ (delta * (k : ℝ)) := (Real.rpow_mul ht0.le _ _).symm
    calc
      (t ^ delta / delta) ^ k * t ^ (-w.re) =
          (delta⁻¹) ^ k * ((t ^ delta) ^ k * t ^ (-w.re)) := by
            rw [div_eq_mul_inv, mul_pow]
            ring
      _ = (delta⁻¹) ^ k * (t ^ (delta * (k : ℝ)) * t ^ (-w.re)) := by
            rw [htpow]
      _ = (delta⁻¹) ^ k * t ^ (delta * (k : ℝ) + -w.re) := by
            rw [← Real.rpow_add ht0]
      _ = (delta⁻¹) ^ k * t ^ (-w'.re) := by
            congr 2
            dsimp [w']
            norm_num
            ring
  have hscale : ‖(((delta⁻¹) ^ k : ℝ) : ℂ)‖ = (delta⁻¹) ^ k := by
    rw [Complex.norm_real, Real.norm_of_nonneg]
    exact pow_nonneg (inv_nonneg.mpr hdelta.le) _
  rw [norm_soninMellinLogPowerKernel ht0, abs_of_nonneg hlog0,
    norm_mul, hscale, norm_soninMellinKernel ht0]
  exact hmul.trans_eq hrewrite

/-- A literal `L²` Sonine tail can be paired with every logarithmic Mellin
kernel. -/
theorem integrableOn_tail_mul_soninMellinLogPowerKernel (k : ℕ) {w : ℂ}
    (hlo : 1 / 2 < w.re) {f : ℝ → ℂ}
    (hf : MemLp f 2 (volume.restrict (Ioi (0 : ℝ)))) :
    IntegrableOn (fun t => f t * soninMellinLogPowerKernel k w t) (Ioi (1 : ℝ)) := by
  have hsub : (volume : Measure ℝ).restrict (Ioi (1 : ℝ)) =
      ((volume : Measure ℝ).restrict (Ioi (0 : ℝ))).restrict (Ioi (1 : ℝ)) := by
    rw [Measure.restrict_restrict measurableSet_Ioi,
      inter_eq_self_of_subset_left
        (fun t ht => mem_Ioi.mpr (lt_trans zero_lt_one (mem_Ioi.mp ht)))]
  have hf1 : MemLp f 2 (volume.restrict (Ioi (1 : ℝ))) := by
    rw [hsub]
    exact hf.restrict (Ioi 1)
  have hkernel : MemLp (soninMellinLogPowerKernel k w) 2
      (volume.restrict (Ioi (1 : ℝ))) :=
    memLp_soninMellinLogPowerKernel_Ioi_one k hlo
  exact (hf1.integrable_mul hkernel).congr (Filter.Eventually.of_forall fun t => rfl)

/-- The literal order-`k` Mellin tail integral. -/
def soninMellinTailLogPowerIntegral (k : ℕ) (f : SoninL2) (w : ℂ) : ℂ :=
  ∫ t in Ioi (1 : ℝ), f t * soninMellinLogPowerKernel k w t

/-- The bounded `k`-th tail-jet functional represented by the literal
logarithmic kernel. -/
def soninMellinTailLogPowerEvaluation (k : ℕ) (w : ℂ)
    (hlo : 1 / 2 < w.re) : SoninL2 →L[ℂ] ℂ :=
  (innerSL ℂ
      ((memLp_soninMellinLogPowerKernel_Ioi_one k hlo).star.toLp
        (star (soninMellinLogPowerKernel k w)))).comp
    (LpToLpRestrictCLM ℝ ℂ ℂ (volume : Measure ℝ) 2 (Ioi (1 : ℝ)))

/-- The Riesz functional is the literal logarithmic tail integral. -/
theorem soninMellinTailLogPowerEvaluation_apply (k : ℕ) (w : ℂ)
    (hlo : 1 / 2 < w.re) (f : SoninL2) :
    soninMellinTailLogPowerEvaluation k w hlo f =
      ∫ t in Ioi (1 : ℝ), (f : ℝ → ℂ) t * soninMellinLogPowerKernel k w t := by
  rw [soninMellinTailLogPowerEvaluation, ContinuousLinearMap.comp_apply,
    innerSL_apply_apply, MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [LpToLpRestrictCLM_coeFn ℂ (Ioi (1 : ℝ)) f,
    (memLp_soninMellinLogPowerKernel_Ioi_one k hlo).star.coeFn_toLp] with t hf hk
  rw [RCLike.inner_apply, hf, hk]
  change (f : ℝ → ℂ) t * star (star (soninMellinLogPowerKernel k w t)) =
    (f : ℝ → ℂ) t * soninMellinLogPowerKernel k w t
  rw [star_star]

/-- **Recursive dominated tail differentiation.** Every order-`k` literal
tail integral differentiates to the bounded order-`k+1` Riesz evaluator. -/
theorem hasDerivAt_soninMellinTailLogPowerIntegral (k : ℕ) {w : ℂ}
    (hlo : 1 / 2 < w.re) (f : SoninL2) :
    HasDerivAt (soninMellinTailLogPowerIntegral k f)
      (soninMellinTailLogPowerEvaluation (k + 1) w hlo f) w := by
  let epsilon : ℝ := (w.re - 1 / 2) / 4
  have hepsilon : 0 < epsilon := by
    dsimp [epsilon]
    linarith
  let w' : ℂ := w - (2 * epsilon : ℝ)
  have hw' : 1 / 2 < w'.re := by
    dsimp [w', epsilon]
    norm_num
    linarith
  let scale : ℝ := ((((k + 1 : ℕ) : ℝ) + 1) / epsilon) ^ (k + 1)
  let bound : ℝ → ℝ := fun t => ‖f t‖ * (scale * ‖soninMellinKernel w' t‖)
  have hbound : Integrable bound (volume.restrict (Ioi (1 : ℝ))) := by
    have hf : MemLp (f : ℝ → ℂ) 2 (volume.restrict (Ioi (1 : ℝ))) := by
      have hrestrict := (memLp_restrict_Ioi f).restrict (Ioi (1 : ℝ))
      rw [Measure.restrict_restrict measurableSet_Ioi,
        inter_eq_self_of_subset_left
          (fun t ht => mem_Ioi.mpr (lt_trans zero_lt_one (mem_Ioi.mp ht)))] at hrestrict
      exact hrestrict
    have hk : MemLp (soninMellinKernel w') 2
        (volume.restrict (Ioi (1 : ℝ))) :=
      memLp_soninMellinKernel_Ioi hw' zero_lt_one
    have hprod : Integrable ((fun t => ‖f t‖) *
        (fun t => scale * ‖soninMellinKernel w' t‖))
        (volume.restrict (Ioi (1 : ℝ))) :=
      hf.norm.integrable_mul (hk.norm.const_mul scale)
    convert hprod using 1
    ext t
    simp only [bound, Pi.mul_apply]
  have hderiv := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Ioi (1 : ℝ)))
    (F := fun z t => f t * soninMellinLogPowerKernel k z t)
    (F' := fun z t => f t * soninMellinLogPowerKernel (k + 1) z t)
    (x₀ := w) (bound := bound)
    (Metric.ball_mem_nhds w hepsilon)
    (Filter.Eventually.of_forall fun z =>
      ((Lp.aestronglyMeasurable f).restrict).mul
        (aestronglyMeasurable_soninMellinLogPowerKernel k z))
    (integrableOn_tail_mul_soninMellinLogPowerKernel k hlo (memLp_restrict_Ioi f))
    (((Lp.aestronglyMeasurable f).restrict).mul
      (aestronglyMeasurable_soninMellinLogPowerKernel (k + 1) w))
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      intro z hz
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left
        (by
          simpa [scale, w'] using
            (norm_soninMellinLogPowerKernel_le_tail_majorant (k + 1)
              hepsilon hz (mem_Ioi.mp ht)))
        (norm_nonneg _))
    hbound
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      intro z hz
      exact (hasDerivAt_soninMellinLogPowerKernel
        (lt_trans zero_lt_one (mem_Ioi.mp ht)) k z).const_mul (f t))
  change HasDerivAt
    (fun z : ℂ => ∫ t in Ioi (1 : ℝ), (f : ℝ → ℂ) t * soninMellinLogPowerKernel k z t)
    (soninMellinTailLogPowerEvaluation (k + 1) w hlo f) w
  rw [soninMellinTailLogPowerEvaluation_apply]
  exact hderiv.2

/-- The zeroth logarithmic tail integral is the original literal Mellin tail
integral. -/
theorem soninMellinTailLogPowerIntegral_zero_eq_soninMellinTailIntegral
    (f : SoninL2) :
    soninMellinTailLogPowerIntegral 0 f = soninMellinTailIntegral f := by
  funext w
  simp [soninMellinTailLogPowerIntegral, soninMellinTailIntegral,
    soninMellinLogPowerKernel]

/-- Every finite iterated derivative of the order-zero literal tail integral
has one further dominated derivative represented by the next Riesz jet. -/
theorem hasDerivAt_iteratedDeriv_soninMellinTailLogPowerIntegral
    (n : ℕ) {w : ℂ} (hlo : 1 / 2 < w.re) (f : SoninL2) :
    HasDerivAt (iteratedDeriv n (soninMellinTailLogPowerIntegral 0 f))
      (soninMellinTailLogPowerEvaluation (n + 1) w hlo f) w := by
  induction n generalizing w with
  | zero =>
      simpa only [iteratedDeriv_zero] using
        (hasDerivAt_soninMellinTailLogPowerIntegral 0 hlo f)
  | succ n ih =>
      rw [iteratedDeriv_succ]
      let U : Set ℂ := {z | 1 / 2 < z.re}
      have hUopen : IsOpen U :=
        isOpen_lt' (1 / 2 : ℝ) |>.preimage Complex.continuous_re
      have hwU : w ∈ U := hlo
      have hnear : ∀ᶠ y in 𝓝 w, y ∈ U := hUopen.mem_nhds hwU
      have heq : deriv (iteratedDeriv n (soninMellinTailLogPowerIntegral 0 f)) =ᶠ[𝓝 w]
          soninMellinTailLogPowerIntegral (n + 1) f := by
        filter_upwards [hnear] with y hy
        have h := ih hy
        rw [h.deriv, soninMellinTailLogPowerEvaluation_apply]
        rfl
      rw [heq.hasDerivAt_iff]
      exact hasDerivAt_soninMellinTailLogPowerIntegral (n + 1) hlo f

/-- The literal all-order tail-jet formula. -/
theorem iteratedDeriv_soninMellinTailLogPowerIntegral
    (n : ℕ) {w : ℂ} (hlo : 1 / 2 < w.re) (f : SoninL2) :
    iteratedDeriv n (soninMellinTailLogPowerIntegral 0 f) w =
      soninMellinTailLogPowerEvaluation n w hlo f := by
  cases n with
  | zero =>
      rw [iteratedDeriv_zero]
      exact (soninMellinTailLogPowerEvaluation_apply 0 w hlo f).symm
  | succ n =>
      rw [iteratedDeriv_succ]
      exact (hasDerivAt_iteratedDeriv_soninMellinTailLogPowerIntegral n hlo f).deriv

/-- The original literal Mellin tail has every finite derivative, represented
by its coefficient-faithful logarithmic Riesz jet. -/
theorem iteratedDeriv_soninMellinTailIntegral
    (n : ℕ) {w : ℂ} (hlo : 1 / 2 < w.re) (f : SoninL2) :
    iteratedDeriv n (soninMellinTailIntegral f) w =
      soninMellinTailLogPowerEvaluation n w hlo f := by
  rw [← soninMellinTailLogPowerIntegral_zero_eq_soninMellinTailIntegral f]
  exact iteratedDeriv_soninMellinTailLogPowerIntegral n hlo f

/-- Order zero recovers the existing bounded Mellin tail evaluator. -/
theorem soninMellinTailLogPowerEvaluation_zero (w : ℂ)
    (hlo : 1 / 2 < w.re) :
    soninMellinTailLogPowerEvaluation 0 w hlo = soninMellinTailEvaluation w hlo := by
  ext f
  rw [soninMellinTailLogPowerEvaluation_apply,
    soninMellinTailEvaluation_apply, soninMellinLogPowerKernel_zero]

/-- Order one recovers the established literal first-derivative evaluator. -/
theorem soninMellinTailLogPowerEvaluation_one (w : ℂ)
    (hlo : 1 / 2 < w.re) :
    soninMellinTailLogPowerEvaluation 1 w hlo =
      soninMellinTailDerivativeEvaluation w hlo := by
  ext f
  rw [soninMellinTailLogPowerEvaluation_apply,
    soninMellinTailDerivativeEvaluation_apply, soninMellinLogPowerKernel_one]

end RHTower
