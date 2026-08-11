import GaloisForLFunctions.RHTower.HedenmalmThetaSourceSpectrumExact
import GaloisForLFunctions.RHTower.HedenmalmThetaTraceKernel
import GaloisForLFunctions.HTGeometry.BanachIntervalIntegralAbsoluteContinuity
import GaloisForLFunctions.HTGeometry.RegularizedResolventTraceOperator
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Analysis.Calculus.ContDiff.Deriv

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace RHTower.HedenmalmThetaSource

noncomputable section

open GaloisForLFunctions.HTGeometry
open HedenmalmQuantile HedenmalmHilbertSchmidt ContinuousLinearMap

local instance factTwoNeTopThetaRealResolventTrace : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by norm_num⟩

/-- Real resolvent of the source inverse pencil. -/
def thetaRealResolvent (r : ℝ) : H →L[ℂ] H :=
  Ring.inverse (1 + (r : ℂ) • thetaKernelOperator)

theorem isUnit_one_add_real_smul_thetaKernelOperator {r : ℝ}
    (hr : |r| * ‖thetaKernelOperator‖ < 1) :
    IsUnit (1 + (r : ℂ) • thetaKernelOperator) := by
  have hnorm : ‖(-(r : ℂ)) • thetaKernelOperator‖ < 1 := by
    rw [norm_smul, norm_neg, Complex.norm_real, Real.norm_eq_abs]
    exact hr
  have hunit := isUnit_one_sub_of_norm_lt_one hnorm
  simpa [sub_eq_add_neg] using hunit

theorem one_add_real_smul_mul_thetaRealResolvent {r : ℝ}
    (hr : |r| * ‖thetaKernelOperator‖ < 1) :
    (1 + (r : ℂ) • thetaKernelOperator) * thetaRealResolvent r = 1 := by
  exact Ring.mul_inverse_cancel _ (isUnit_one_add_real_smul_thetaKernelOperator hr)

theorem thetaRealResolvent_equation {r : ℝ}
    (hr : |r| * ‖thetaKernelOperator‖ < 1) (f : H) :
    thetaRealResolvent r f + (r : ℂ) •
      thetaKernelOperator (thetaRealResolvent r f) = f := by
  have h := congrArg (fun T : H →L[ℂ] H => T f)
    (one_add_real_smul_mul_thetaRealResolvent hr)
  change thetaRealResolvent r f +
    ((r : ℂ) • thetaKernelOperator) (thetaRealResolvent r f) = f
  simpa [ContinuousLinearMap.mul_def] using h

/-- Pointwise absolutely continuous representative of the pinned primitive. -/
def thetaPinnedPrimitive (f : H) (t : ℝ) : ℂ :=
  (∫ u in (0 : ℝ)..t, f u) - (t : ℂ) * pinnedMean f

theorem intervalIntegrable_coe_unit (f : H) :
    IntervalIntegrable (fun t : ℝ => f t) volume 0 1 := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
  have h : IntegrableOn (fun t : ℝ => f t) (Icc (0 : ℝ) 1) volume := by
    change Integrable (fun t : ℝ => f t) (volume.restrict (Icc (0 : ℝ) 1))
    simpa only [unitIntervalMeasure] using integrable_coe f
  exact h.mono_set Ioc_subset_Icc_self

theorem thetaPinnedPrimitive_eq_pinnedVolterraFun (f : H) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) :
    thetaPinnedPrimitive f t = pinnedVolterraFun f t := by
  rw [thetaPinnedPrimitive, pinnedVolterraFun, pinnedPrefix_eq_intervalIntegral f ht]

@[simp] theorem thetaPinnedPrimitive_zero (f : H) : thetaPinnedPrimitive f 0 = 0 := by
  simp [thetaPinnedPrimitive]

@[simp] theorem thetaPinnedPrimitive_one (f : H) : thetaPinnedPrimitive f 1 = 0 := by
  rw [thetaPinnedPrimitive_eq_pinnedVolterraFun f (by simp)]
  rw [pinnedVolterraFun]
  have hp : pinnedPrefix f 1 = pinnedMean f := by
    rw [pinnedPrefix, pinnedMean]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    simp [Set.indicator_of_mem (show t ∈ Iic (1 : ℝ) from ht.2)]
  rw [hp]
  norm_num

theorem absolutelyContinuousOnInterval_thetaPinnedPrimitive (f : H) :
    AbsolutelyContinuousOnInterval (thetaPinnedPrimitive f) 0 1 := by
  have hprim :=
    (intervalIntegrable_coe_unit f).absolutelyContinuousOnInterval_intervalIntegral_normed
      (show (0 : ℝ) ∈ uIcc 0 1 by simp)
  have hlin : AbsolutelyContinuousOnInterval
      (fun t : ℝ => (t : ℂ) * pinnedMean f) 0 1 := by
    have hof : AbsolutelyContinuousOnInterval (fun t : ℝ => (t : ℂ)) 0 1 :=
      RCLike.lipschitzWith_ofReal.lipschitzOnWith.absolutelyContinuousOnInterval
    simpa [smul_eq_mul, mul_comm] using hof.const_smul (pinnedMean f)
  exact hprim.sub hlin

theorem ae_hasDerivAt_thetaPinnedPrimitive (f : H) :
    ∀ᵐ t, t ∈ Icc (0 : ℝ) 1 →
      HasDerivAt (thetaPinnedPrimitive f) (f t - pinnedMean f) t := by
  have hder := (intervalIntegrable_coe_unit f).ae_hasDerivAt_integral
  filter_upwards [hder] with t htder ht
  have hp := htder (by simpa [uIcc_of_le zero_le_one] using ht)
    0 (by simp)
  have hlin : HasDerivAt (fun s : ℝ => (s : ℂ) * pinnedMean f) (pinnedMean f) t := by
    with_reducible_and_instances
      simpa using (hasDerivAt_id t).ofReal_comp.mul_const (pinnedMean f)
  exact hp.sub hlin

theorem thetaRealResolvent_coe_equation_ae {r : ℝ}
    (hr : |r| * ‖thetaKernelOperator‖ < 1) (f : H) :
    (fun t => thetaRealResolvent r f t + (r : ℂ) *
      thetaKernelOperator (thetaRealResolvent r f) t) =ᵐ[unitIntervalMeasure]
      fun t => f t := by
  let g := thetaRealResolvent r f
  have heq : g + (r : ℂ) • thetaKernelOperator g = f := by
    simpa using thetaRealResolvent_equation hr f
  have hcoeAdd := Lp.coeFn_add g ((r : ℂ) • thetaKernelOperator g)
  have hcoeSmul := Lp.coeFn_smul (r : ℂ) (thetaKernelOperator g)
  have hcoeEq : (fun t => (g + (r : ℂ) • thetaKernelOperator g) t) =ᵐ[unitIntervalMeasure]
      fun t => f t := by rw [heq]
  filter_upwards [hcoeAdd, hcoeSmul, hcoeEq] with t h1 h2 h3
  change g t + (r : ℂ) * thetaKernelOperator g t = f t
  rw [← h3, h1]
  change g t + (r : ℂ) * thetaKernelOperator g t =
    g t + ((r : ℂ) • thetaKernelOperator g) t
  rw [h2]
  rfl

theorem ae_hasDerivAt_thetaRealResolvent_pinnedPrimitive {r : ℝ}
    (hr : |r| * ‖thetaKernelOperator‖ < 1) (f : H) :
    ∀ᵐ t ∂unitIntervalMeasure,
      HasDerivAt (thetaPinnedPrimitive (thetaRealResolvent r f))
        (f t - Complex.I * (r : ℂ) * (quantileSpeed thetaSource t : ℂ) *
          thetaPinnedPrimitive (thetaRealResolvent r f) t -
          pinnedMean (thetaRealResolvent r f)) t := by
  let g := thetaRealResolvent r f
  have hder := ae_hasDerivAt_thetaPinnedPrimitive g
  have hder' : ∀ᵐ t ∂unitIntervalMeasure, t ∈ Icc (0 : ℝ) 1 →
      HasDerivAt (thetaPinnedPrimitive g) (g t - pinnedMean g) t := by
    change ∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) 1), t ∈ Icc (0 : ℝ) 1 →
      HasDerivAt (thetaPinnedPrimitive g) (g t - pinnedMean g) t
    exact ae_restrict_of_ae hder
  have htmem : ∀ᵐ t ∂unitIntervalMeasure, t ∈ Icc (0 : ℝ) 1 := by
    change ∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) 1), t ∈ Icc (0 : ℝ) 1
    exact ae_restrict_mem measurableSet_Icc
  have hop := pinnedKernelOperator_ae thetaSource hasFiniteKernelEnergy_thetaSource g
  have heq := thetaRealResolvent_coe_equation_ae hr f
  filter_upwards [hder', hop, heq, htmem] with t hderT hopT heqT ht
  have hB : thetaKernelOperator g t =
      Complex.I * (quantileSpeed thetaSource t : ℂ) * thetaPinnedPrimitive g t := by
    rw [thetaKernelOperator, hopT, pinnedKernelField_apply_eq_pinnedVolterraFun,
      ← thetaPinnedPrimitive_eq_pinnedVolterraFun g ht]
  have hg : g t = f t - (r : ℂ) * thetaKernelOperator g t := by
    rw [← heqT]
    ring
  have hd := hderT ht
  change HasDerivAt (thetaPinnedPrimitive g)
    (f t - Complex.I * (r : ℂ) * (quantileSpeed thetaSource t : ℂ) *
      thetaPinnedPrimitive g t - pinnedMean g) t
  convert hd using 1
  rw [hg, hB]
  ring

/-- Unit-modulus integrating factor for the real resolvent ODE. -/
def thetaRealIntegratingFactor (r : ℝ) (t : ℝ) : ℂ :=
  sourceChar (r : ℂ) (thetaSource.quantileFun t)

theorem norm_thetaRealIntegratingFactor (r t : ℝ) :
    ‖thetaRealIntegratingFactor r t‖ = 1 := by
  rw [thetaRealIntegratingFactor, norm_sourceChar]
  simp

theorem hasDerivAt_thetaRealIntegratingFactor (r : ℝ) {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (thetaRealIntegratingFactor r)
      (thetaRealIntegratingFactor r t *
        (Complex.I * (r : ℂ) * (quantileSpeed thetaSource t : ℂ))) t := by
  have hQ := hasDerivAt_quantileFun_complex thetaSource ht
  have hlin := hQ.const_mul (Complex.I * (r : ℂ))
  have hexp := hlin.cexp
  unfold thetaRealIntegratingFactor
  with_reducible_and_instances
    simpa [sourceChar] using hexp

theorem continuousOn_thetaRealIntegratingFactor (r : ℝ) :
    ContinuousOn (thetaRealIntegratingFactor r) (Ioo (0 : ℝ) 1) :=
  (continuous_sourceChar (r : ℂ)).comp_continuousOn
    (continuousOn_quantileFun thetaSource)

theorem contDiffOn_thetaRealIntegratingFactor (r : ℝ) :
    ContDiffOn ℝ 1 (thetaRealIntegratingFactor r) (Ioo (0 : ℝ) 1) := by
  rw [contDiffOn_one_iff_derivWithin isOpen_Ioo.uniqueDiffOn]
  constructor
  · intro t ht
    exact (hasDerivAt_thetaRealIntegratingFactor r ht).differentiableAt.differentiableWithinAt
  · have hformula : EqOn (derivWithin (thetaRealIntegratingFactor r) (Ioo (0 : ℝ) 1))
        (thetaRealIntegratingFactor r *
          fun t => Complex.I * (r : ℂ) * (quantileSpeed thetaSource t : ℂ))
        (Ioo (0 : ℝ) 1) := by
      intro t ht
      rw [derivWithin_of_isOpen isOpen_Ioo ht]
      exact (hasDerivAt_thetaRealIntegratingFactor r ht).deriv
    have hq : ContinuousOn (fun t : ℝ => (quantileSpeed thetaSource t : ℂ))
        (Ioo (0 : ℝ) 1) :=
      Complex.continuous_ofReal.comp_continuousOn
        (HedenmalmQuantile.continuousOn_quantileSpeed thetaSource)
    have hc : ContinuousOn
        (fun t : ℝ => Complex.I * (r : ℂ) * (quantileSpeed thetaSource t : ℂ))
        (Ioo (0 : ℝ) 1) := (continuousOn_const : ContinuousOn
          (fun _ : ℝ => Complex.I * (r : ℂ)) (Ioo (0 : ℝ) 1)).mul hq
    have hcont : ContinuousOn
        (thetaRealIntegratingFactor r *
          fun t => Complex.I * (r : ℂ) * (quantileSpeed thetaSource t : ℂ))
        (Ioo (0 : ℝ) 1) := (continuousOn_thetaRealIntegratingFactor r).mul hc
    exact hcont.congr hformula

theorem absolutelyContinuousOnInterval_thetaRealIntegratingFactor {r a b : ℝ}
    (hab : uIcc a b ⊆ Ioo (0 : ℝ) 1) :
    AbsolutelyContinuousOnInterval (thetaRealIntegratingFactor r) a b :=
  ((contDiffOn_thetaRealIntegratingFactor r).mono hab).absolutelyContinuousOnInterval

/-- Integrated right-hand side of the weak real resolvent ODE. -/
def thetaResolventPrimitive (r : ℝ) (f : H) (m : ℂ) (t : ℝ) : ℂ :=
  ∫ u in (0 : ℝ)..t, thetaRealIntegratingFactor r u * (f u - m)

theorem integrable_thetaRealIntegratingFactor_mul_sub (r : ℝ) (f : H) (m : ℂ) :
    Integrable (fun u => thetaRealIntegratingFactor r u * (f u - m))
      unitIntervalMeasure := by
  have hbase : Integrable (fun u => f u - m) unitIntervalMeasure :=
    (integrable_coe f).sub (integrable_const m)
  refine Integrable.mono' hbase.norm ?_ ?_
  · exact (((continuous_sourceChar (r : ℂ)).measurable.comp
      thetaSource.measurable_quantileFun).aestronglyMeasurable.mul hbase.1)
  · filter_upwards with u
    rw [norm_mul, norm_thetaRealIntegratingFactor, one_mul]

theorem intervalIntegrable_thetaRealIntegratingFactor_mul_sub
    (r : ℝ) (f : H) (m : ℂ) :
    IntervalIntegrable (fun u => thetaRealIntegratingFactor r u * (f u - m)) volume 0 1 := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
  have h : IntegrableOn (fun u => thetaRealIntegratingFactor r u * (f u - m))
      (Icc (0 : ℝ) 1) volume := by
    change Integrable (fun u => thetaRealIntegratingFactor r u * (f u - m))
      (volume.restrict (Icc (0 : ℝ) 1))
    simpa only [unitIntervalMeasure] using
      integrable_thetaRealIntegratingFactor_mul_sub r f m
  exact h.mono_set Ioc_subset_Icc_self

theorem absolutelyContinuousOnInterval_thetaResolventPrimitive
    (r : ℝ) (f : H) (m : ℂ) :
    AbsolutelyContinuousOnInterval (thetaResolventPrimitive r f m) 0 1 := by
  exact (intervalIntegrable_thetaRealIntegratingFactor_mul_sub r f m)
    |>.absolutelyContinuousOnInterval_intervalIntegral_normed (by simp)

@[simp] theorem thetaResolventPrimitive_zero (r : ℝ) (f : H) (m : ℂ) :
    thetaResolventPrimitive r f m 0 = 0 := by
  simp [thetaResolventPrimitive]

theorem ae_hasDerivAt_thetaResolventPrimitive (r : ℝ) (f : H) (m : ℂ) :
    ∀ᵐ t, t ∈ Icc (0 : ℝ) 1 →
      HasDerivAt (thetaResolventPrimitive r f m)
        (thetaRealIntegratingFactor r t * (f t - m)) t := by
  have h := (intervalIntegrable_thetaRealIntegratingFactor_mul_sub r f m)
    |>.ae_hasDerivAt_integral
  filter_upwards [h] with t ht htIcc
  exact ht (by simpa [uIcc_of_le zero_le_one] using htIcc) 0 (by simp)

theorem thetaResolvent_integratingFactor_identity_interior {r : ℝ}
    (hr : |r| * ‖thetaKernelOperator‖ < 1) (f : H)
    {a b : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo (0 : ℝ) 1) :
    thetaRealIntegratingFactor r b *
          thetaPinnedPrimitive (thetaRealResolvent r f) b -
        thetaResolventPrimitive r f (pinnedMean (thetaRealResolvent r f)) b =
      thetaRealIntegratingFactor r a *
          thetaPinnedPrimitive (thetaRealResolvent r f) a -
        thetaResolventPrimitive r f (pinnedMean (thetaRealResolvent r f)) a := by
  let g := thetaRealResolvent r f
  let h := thetaPinnedPrimitive g
  let m := pinnedMean g
  let E := thetaRealIntegratingFactor r
  let P := thetaResolventPrimitive r f m
  let d : ℝ → ℂ := E * h - P
  have hab : uIcc a b ⊆ Ioo (0 : ℝ) 1 := ordConnected_Ioo.uIcc_subset ha hb
  have hEac : AbsolutelyContinuousOnInterval E a b :=
    absolutelyContinuousOnInterval_thetaRealIntegratingFactor hab
  have hhac : AbsolutelyContinuousOnInterval h a b :=
    (absolutelyContinuousOnInterval_thetaPinnedPrimitive g).mono
      (by simpa [uIcc_of_le zero_le_one] using hab.trans Ioo_subset_Icc_self)
  have hPac : AbsolutelyContinuousOnInterval P a b :=
    (absolutelyContinuousOnInterval_thetaResolventPrimitive r f m).mono
      (by simpa [uIcc_of_le zero_le_one] using hab.trans Ioo_subset_Icc_self)
  have hdac : AbsolutelyContinuousOnInterval d a b := hEac.smul hhac |>.sub hPac
  have hODEunit := ae_hasDerivAt_thetaRealResolvent_pinnedPrimitive hr f
  have hODEvol : ∀ᵐ t, t ∈ Icc (0 : ℝ) 1 →
      HasDerivAt h
        (f t - Complex.I * (r : ℂ) * (quantileSpeed thetaSource t : ℂ) * h t - m) t := by
    exact (ae_restrict_iff' measurableSet_Icc).mp (by
      simpa only [unitIntervalMeasure] using hODEunit)
  have hPder := ae_hasDerivAt_thetaResolventPrimitive r f m
  have hdder : ∀ᵐ t, t ∈ uIcc a b → HasDerivAt d 0 t := by
    filter_upwards [hODEvol, hPder] with t hODE hP ht
    have htIoo := hab ht
    have hE := hasDerivAt_thetaRealIntegratingFactor r htIoo
    have hh := hODE (Ioo_subset_Icc_self htIoo)
    have hPd := hP (Ioo_subset_Icc_self htIoo)
    have hprod := hE.mul hh
    have hdz := hprod.sub hPd
    change HasDerivAt d 0 t
    convert hdz using 1
    · rfl
    · dsimp only [E, h, P, m]
      ring_nf
  obtain ⟨C, hC⟩ := hdac.const_of_ae_hasDerivAt_zero hdder
  change d b = d a
  rw [hC b (by simp), hC a (by simp)]

/-- The conserved integrating-factor expression has zero boundary constant.  Oscillation of the
character at the singular left quantile endpoint is harmless because its norm is one. -/
theorem thetaResolvent_integratingFactor_identity {r : ℝ}
    (hr : |r| * ‖thetaKernelOperator‖ < 1) (f : H)
    {b : ℝ} (hb : b ∈ Ioo (0 : ℝ) 1) :
    thetaRealIntegratingFactor r b *
        thetaPinnedPrimitive (thetaRealResolvent r f) b =
      thetaResolventPrimitive r f (pinnedMean (thetaRealResolvent r f)) b := by
  let g := thetaRealResolvent r f
  let h := thetaPinnedPrimitive g
  let m := pinnedMean g
  let E := thetaRealIntegratingFactor r
  let P := thetaResolventPrimitive r f m
  let d : ℝ → ℂ := E * h - P
  let a : ℕ → ℝ := fun n => (1 / 2 : ℝ) * (1 / ((n : ℝ) + 1))
  have ha_mem (n : ℕ) : a n ∈ Ioo (0 : ℝ) 1 := by
    dsimp only [a]
    have hn : 0 < (n : ℝ) + 1 := by positivity
    constructor
    · positivity
    · have hone : 1 / ((n : ℝ) + 1) ≤ 1 := by
        exact (div_le_one hn).2 (by linarith)
      nlinarith
  have ha_tend : Tendsto a atTop (𝓝 0) := by
    dsimp only [a]
    convert tendsto_const_nhds.mul
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)) using 1 <;> norm_num
  have ha_Icc : ∀ᶠ n in atTop, a n ∈ Icc (0 : ℝ) 1 :=
    Filter.Eventually.of_forall fun n => Ioo_subset_Icc_self (ha_mem n)
  have ha_tendWithin : Tendsto a atTop (𝓝[Icc (0 : ℝ) 1] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨ha_tend, ha_Icc⟩
  have hhcont : ContinuousWithinAt h (Icc (0 : ℝ) 1) 0 :=
    by simpa only [h, uIcc_of_le zero_le_one] using
      (absolutelyContinuousOnInterval_thetaPinnedPrimitive g).continuousOn 0 (by simp)
  have hh_tend : Tendsto (fun n => h (a n)) atTop (𝓝 0) := by
    have ht := Filter.Tendsto.comp hhcont ha_tendWithin
    change Tendsto (fun n => h (a n)) atTop (𝓝 (h 0)) at ht
    simpa only [h, thetaPinnedPrimitive_zero] using ht
  have hPcont : ContinuousWithinAt P (Icc (0 : ℝ) 1) 0 :=
    by simpa only [P, uIcc_of_le zero_le_one] using
      (absolutelyContinuousOnInterval_thetaResolventPrimitive r f m).continuousOn 0 (by simp)
  have hP_tend : Tendsto (fun n => P (a n)) atTop (𝓝 0) := by
    have ht := Filter.Tendsto.comp hPcont ha_tendWithin
    change Tendsto (fun n => P (a n)) atTop (𝓝 (P 0)) at ht
    simpa only [P, thetaResolventPrimitive_zero] using ht
  have hEh_tend : Tendsto (fun n => E (a n) * h (a n)) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    simpa only [norm_mul, E, norm_thetaRealIntegratingFactor, one_mul, norm_zero] using
      hh_tend.norm
  have hd_tend : Tendsto (fun n => d (a n)) atTop (𝓝 0) := by
    convert hEh_tend.sub hP_tend using 1 <;>
      simp only [d, Pi.sub_apply, Pi.mul_apply, sub_zero]
  have hconst (n : ℕ) : d b = d (a n) := by
    simpa only [d, E, h, P, m, Pi.sub_apply, Pi.mul_apply] using
      thetaResolvent_integratingFactor_identity_interior hr f (ha_mem n) hb
  have hconst_tend : Tendsto (fun _ : ℕ => d b) atTop (𝓝 0) :=
    hd_tend.congr' (Filter.Eventually.of_forall fun n => (hconst n).symm)
  have hdb : d b = 0 := tendsto_nhds_unique tendsto_const_nhds hconst_tend
  simpa only [d, E, h, P, m, Pi.sub_apply, Pi.mul_apply, sub_eq_zero] using hdb

/-- The integrated resolvent right-hand side vanishes at the right pinned endpoint. -/
theorem thetaResolventPrimitive_one_eq_zero {r : ℝ}
    (hr : |r| * ‖thetaKernelOperator‖ < 1) (f : H) :
    thetaResolventPrimitive r f (pinnedMean (thetaRealResolvent r f)) 1 = 0 := by
  let g := thetaRealResolvent r f
  let h := thetaPinnedPrimitive g
  let m := pinnedMean g
  let E := thetaRealIntegratingFactor r
  let P := thetaResolventPrimitive r f m
  let a : ℕ → ℝ := fun n => (1 / 2 : ℝ) * (1 / ((n : ℝ) + 1))
  let b : ℕ → ℝ := fun n => 1 - a n
  have ha_mem (n : ℕ) : a n ∈ Ioo (0 : ℝ) 1 := by
    dsimp only [a]
    have hn : 0 < (n : ℝ) + 1 := by positivity
    constructor
    · positivity
    · have hone : 1 / ((n : ℝ) + 1) ≤ 1 := (div_le_one hn).2 (by linarith)
      nlinarith
  have hb_mem (n : ℕ) : b n ∈ Ioo (0 : ℝ) 1 := by
    dsimp only [b]
    exact ⟨by linarith [(ha_mem n).2], by linarith [(ha_mem n).1]⟩
  have ha_tend : Tendsto a atTop (𝓝 0) := by
    dsimp only [a]
    convert tendsto_const_nhds.mul
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)) using 1 <;> norm_num
  have hb_tend : Tendsto b atTop (𝓝 1) := by
    dsimp only [b]
    convert tendsto_const_nhds.sub ha_tend using 1 <;> norm_num
  have hb_Icc : ∀ᶠ n in atTop, b n ∈ Icc (0 : ℝ) 1 :=
    Filter.Eventually.of_forall fun n => Ioo_subset_Icc_self (hb_mem n)
  have hb_tendWithin : Tendsto b atTop (𝓝[Icc (0 : ℝ) 1] 1) :=
    tendsto_nhdsWithin_iff.mpr ⟨hb_tend, hb_Icc⟩
  have hhcont : ContinuousWithinAt h (Icc (0 : ℝ) 1) 1 := by
    simpa only [h, uIcc_of_le zero_le_one] using
      (absolutelyContinuousOnInterval_thetaPinnedPrimitive g).continuousOn 1 (by simp)
  have hh_tend : Tendsto (fun n => h (b n)) atTop (𝓝 0) := by
    have ht := Filter.Tendsto.comp hhcont hb_tendWithin
    change Tendsto (fun n => h (b n)) atTop (𝓝 (h 1)) at ht
    simpa only [h, thetaPinnedPrimitive_one] using ht
  have hEh_tend : Tendsto (fun n => E (b n) * h (b n)) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    simpa only [norm_mul, E, norm_thetaRealIntegratingFactor, one_mul, norm_zero] using
      hh_tend.norm
  have hPzero_tend : Tendsto (fun n => P (b n)) atTop (𝓝 0) := by
    refine hEh_tend.congr' (Filter.Eventually.of_forall fun n => ?_)
    simpa only [E, h, P, m] using
      thetaResolvent_integratingFactor_identity hr f (hb_mem n)
  have hPcont : ContinuousWithinAt P (Icc (0 : ℝ) 1) 1 := by
    simpa only [P, uIcc_of_le zero_le_one] using
      (absolutelyContinuousOnInterval_thetaResolventPrimitive r f m).continuousOn 1 (by simp)
  have hPone_tend : Tendsto (fun n => P (b n)) atTop (𝓝 (P 1)) := by
    have ht := Filter.Tendsto.comp hPcont hb_tendWithin
    change Tendsto (fun n => P (b n)) atTop (𝓝 (P 1)) at ht
    exact ht
  have hPone : P 1 = 0 := tendsto_nhds_unique hPone_tend hPzero_tend
  simpa only [P, m] using hPone

theorem integrable_thetaRealIntegratingFactor (r : ℝ) :
    Integrable (thetaRealIntegratingFactor r) unitIntervalMeasure := by
  refine Integrable.mono' (integrable_const (1 : ℝ)) ?_ ?_
  · exact ((continuous_sourceChar (r : ℂ)).measurable.comp
      thetaSource.measurable_quantileFun).aestronglyMeasurable
  · filter_upwards with t
    rw [norm_thetaRealIntegratingFactor]

theorem intervalIntegrable_thetaRealIntegratingFactor (r : ℝ) :
    IntervalIntegrable (thetaRealIntegratingFactor r) volume 0 1 := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
  have h : IntegrableOn (thetaRealIntegratingFactor r) (Icc (0 : ℝ) 1) volume := by
    change Integrable (thetaRealIntegratingFactor r)
      (volume.restrict (Icc (0 : ℝ) 1))
    simpa only [unitIntervalMeasure] using integrable_thetaRealIntegratingFactor r
  exact h.mono_set Ioc_subset_Icc_self

/-- The scalar moment determining the rank-one boundary correction in the real resolvent. -/
def thetaRealResolventMoment (r : ℝ) (f : H) : ℂ :=
  ∫ u in (0 : ℝ)..1, thetaRealIntegratingFactor r u * f u

theorem pinnedMean_thetaRealResolvent_eq {r : ℝ}
    (hr : |r| * ‖thetaKernelOperator‖ < 1) (f : H)
    (hA : rootA thetaSource (r : ℂ) 1 ≠ 0) :
    pinnedMean (thetaRealResolvent r f) =
      thetaRealResolventMoment r f / rootA thetaSource (r : ℂ) 1 := by
  let m := pinnedMean (thetaRealResolvent r f)
  let E := thetaRealIntegratingFactor r
  have hzero := thetaResolventPrimitive_one_eq_zero hr f
  have hEf : IntervalIntegrable (fun u => E u * f u) volume 0 1 := by
    have h := intervalIntegrable_thetaRealIntegratingFactor_mul_sub r f 0
    simpa only [E, sub_zero] using h
  have hEm : IntervalIntegrable (fun u => E u * m) volume 0 1 :=
    (intervalIntegrable_thetaRealIntegratingFactor r).mul_const m
  have hsplit :
      (∫ u in (0 : ℝ)..1, E u * (f u - m)) =
        (∫ u in (0 : ℝ)..1, E u * f u) -
          (∫ u in (0 : ℝ)..1, E u * m) := by
    rw [← intervalIntegral.integral_sub hEf hEm]
    apply intervalIntegral.integral_congr
    intro u _
    ring
  have hEmul : (∫ u in (0 : ℝ)..1, E u * m) =
      (∫ u in (0 : ℝ)..1, E u) * m := by
    rw [intervalIntegral.integral_mul_const]
  have hroot : (∫ u in (0 : ℝ)..1, E u) = rootA thetaSource (r : ℂ) 1 := by
    rfl
  have heq : thetaRealResolventMoment r f -
      rootA thetaSource (r : ℂ) 1 * m = 0 := by
    rw [thetaRealResolventMoment, ← hroot, ← hEmul, ← hsplit]
    simpa only [thetaResolventPrimitive, E, m] using hzero
  apply (eq_div_iff hA).2
  rw [mul_comm]
  exact (sub_eq_zero.mp heq).symm

/-- Explicit Green primitive for the real source resolvent. -/
def thetaRealGreenPrimitive (r : ℝ) (f : H) (t : ℝ) : ℂ :=
  rootFactor thetaSource (r : ℂ) t *
    ((∫ u in (0 : ℝ)..t, thetaRealIntegratingFactor r u * f u) -
      rootA thetaSource (r : ℂ) t /
        rootA thetaSource (r : ℂ) 1 * thetaRealResolventMoment r f)

theorem thetaPinnedPrimitive_thetaRealResolvent_eq_green {r : ℝ}
    (hr : |r| * ‖thetaKernelOperator‖ < 1) (f : H)
    (hA : rootA thetaSource (r : ℂ) 1 ≠ 0)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    thetaPinnedPrimitive (thetaRealResolvent r f) t =
      thetaRealGreenPrimitive r f t := by
  let g := thetaRealResolvent r f
  let h := thetaPinnedPrimitive g
  let m := pinnedMean g
  let E := thetaRealIntegratingFactor r
  have hIF := thetaResolvent_integratingFactor_identity hr f ht
  have hm := pinnedMean_thetaRealResolvent_eq hr f hA
  change m = thetaRealResolventMoment r f / rootA thetaSource (r : ℂ) 1 at hm
  have hFE : rootFactor thetaSource (r : ℂ) t * E t = 1 := by
    exact rootFactor_mul_sourceChar thetaSource (r : ℂ) t
  calc
    h t = rootFactor thetaSource (r : ℂ) t * (E t * h t) := by rw [← mul_assoc, hFE, one_mul]
    _ = rootFactor thetaSource (r : ℂ) t *
        thetaResolventPrimitive r f m t := by
      rw [hIF]
    _ = thetaRealGreenPrimitive r f t := by
      rw [thetaRealGreenPrimitive, thetaResolventPrimitive]
      have h0t : uIcc (0 : ℝ) t ⊆ uIcc (0 : ℝ) 1 := by
        rw [uIcc_of_le ht.1.le, uIcc_of_le zero_le_one]
        exact fun x hx => ⟨hx.1, hx.2.trans ht.2.le⟩
      have hE : IntervalIntegrable (fun u => E u * f u) volume 0 t := by
        simpa only [E, sub_zero] using
          (intervalIntegrable_thetaRealIntegratingFactor_mul_sub r f 0).mono_set h0t
      have hEm : IntervalIntegrable (fun u => E u * m) volume 0 t := by
        exact ((intervalIntegrable_thetaRealIntegratingFactor r).mul_const m).mono_set
          h0t
      rw [show (∫ u in (0 : ℝ)..t, E u * (f u - m)) =
          (∫ u in (0 : ℝ)..t, E u * f u) -
            (∫ u in (0 : ℝ)..t, E u * m) by
        rw [← intervalIntegral.integral_sub hE hEm]
        apply intervalIntegral.integral_congr
        intro u _
        ring]
      rw [intervalIntegral.integral_mul_const]
      change rootFactor thetaSource (r : ℂ) t *
          ((∫ u in (0 : ℝ)..t, E u * f u) -
            (∫ u in (0 : ℝ)..t, E u) * m) = _
      have hAint : (∫ u in (0 : ℝ)..t, E u) = rootA thetaSource (r : ℂ) t := rfl
      rw [hAint, hm]
      ring

/-! ### The transposed Riesz row in the Green formula -/

/-- The integrating-factor pairing with the Riesz vector of the transposed source kernel row. -/
def thetaTransposeRieszIntegrand (r t u : ℝ) : ℂ :=
  thetaRealIntegratingFactor r u *
    (Complex.I * (quantileSpeed thetaSource u : ℂ) *
      (pinnedKernelSlice u t : ℂ))

theorem integrable_thetaTransposeRieszIntegrand (r : ℝ) {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) 1) :
    Integrable (thetaTransposeRieszIntegrand r t) unitIntervalMeasure := by
  have hbase : Integrable
      (fun u => ((quantileSpeed thetaSource u * pinnedKernelSlice u t : ℝ) : ℂ))
      unitIntervalMeasure :=
    (integrable_quantileSpeed_mul_pinnedKernelSlice thetaSource
      hasFiniteKernelEnergy_thetaSource ht).ofReal
  refine Integrable.mono' hbase.norm ?_ ?_
  · exact (((continuous_sourceChar (r : ℂ)).measurable.comp
        thetaSource.measurable_quantileFun).aestronglyMeasurable.mul
      ((measurable_const.mul
        (Complex.measurable_ofReal.comp
          (measurable_const.div
            (thetaSource.continuous_k.measurable.comp
              thetaSource.measurable_quantileFun)))).mul
        (Complex.measurable_ofReal.comp
          ((Measurable.ite
            (measurableSet_le measurable_const measurable_id)
            measurable_const measurable_const).sub measurable_id))).aestronglyMeasurable)
  · filter_upwards with u
    simpa only [thetaTransposeRieszIntegrand, norm_mul,
      norm_thetaRealIntegratingFactor, Complex.norm_I, Complex.norm_real,
      Real.norm_eq_abs, one_mul, abs_mul,
      abs_of_pos (quantileSpeed_pos thetaSource u)] using
      (le_refl (quantileSpeed thetaSource u * |pinnedKernelSlice u t|))

theorem intervalIntegrable_thetaTransposeRieszIntegrand (r : ℝ) {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) 1) :
    IntervalIntegrable (thetaTransposeRieszIntegrand r t) volume 0 1 := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
  have h : IntegrableOn (thetaTransposeRieszIntegrand r t) (Icc (0 : ℝ) 1) volume := by
    change Integrable (thetaTransposeRieszIntegrand r t)
      (volume.restrict (Icc (0 : ℝ) 1))
    simpa only [unitIntervalMeasure] using
      integrable_thetaTransposeRieszIntegrand r ht
  exact h.mono_set Ioc_subset_Icc_self

theorem integral_thetaTransposeRieszIntegrand_zero_t {r t : ℝ}
    (hr : r ≠ 0) (ht : t ∈ Ioo (0 : ℝ) 1) :
    (∫ u in (0 : ℝ)..t, thetaTransposeRieszIntegrand r t u) =
      (rootA thetaSource (r : ℂ) t -
        (t : ℂ) * thetaRealIntegratingFactor r t) / (r : ℂ) := by
  let E := thetaRealIntegratingFactor r
  let L : ℝ → ℂ := fun u => u • E u
  let D : ℝ → ℂ := fun u => E u - (r : ℂ) * thetaTransposeRieszIntegrand r t u
  have h0t : uIcc (0 : ℝ) t ⊆ uIcc (0 : ℝ) 1 := by
    rw [uIcc_of_le ht.1.le, uIcc_of_le zero_le_one]
    exact fun x hx => ⟨hx.1, hx.2.trans ht.2.le⟩
  have hderiv : ∀ u ∈ Ioo (0 : ℝ) t, HasDerivAt L (D u) u := by
    intro u hu
    have huIoo : u ∈ Ioo (0 : ℝ) 1 := ⟨hu.1, hu.2.trans ht.2⟩
    have huE : HasDerivAt (fun s : ℝ => s) 1 u := hasDerivAt_id u
    have hE := hasDerivAt_thetaRealIntegratingFactor r huIoo
    have hprod := huE.smul hE
    have hprod' : HasDerivAt L
        (u • (E u * (Complex.I * (r : ℂ) * (quantileSpeed thetaSource u : ℂ))) +
          (1 : ℝ) • E u) u := by
      exact hprod
    refine hprod'.congr_deriv ?_
    dsimp only [D]
    simp only [Complex.real_smul]
    rw [thetaTransposeRieszIntegrand]
    rw [show pinnedKernelSlice u t = -u by
      simp [pinnedKernelSlice, not_le.mpr hu.2]]
    push_cast
    ring
  have hDint : IntervalIntegrable D volume 0 t := by
    have hEint := (intervalIntegrable_thetaRealIntegratingFactor r).mono_set
      h0t
    have hTint := (intervalIntegrable_thetaTransposeRieszIntegrand r ht).mono_set
      h0t
    exact hEint.sub (hTint.const_mul (r : ℂ))
  have hzero : Tendsto L (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    have hid : Tendsto (fun u : ℝ => u) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
      continuousAt_id.tendsto.mono_left nhdsWithin_le_nhds
    have habs : Tendsto (fun u : ℝ => |u|) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      simpa only [Real.norm_eq_abs, norm_zero] using hid.norm
    convert habs using 1
    · ext u
      dsimp only [L]
      rw [norm_smul, Real.norm_eq_abs,
        norm_thetaRealIntegratingFactor, mul_one]
  have htend : Tendsto L (𝓝[<] t) (𝓝 ((t : ℂ) * E t)) := by
    have hcont : ContinuousAt L t := by
      exact continuousAt_id.smul
        (hasDerivAt_thetaRealIntegratingFactor r ht).continuousAt
    simpa only [L, Complex.real_smul] using
      hcont.tendsto.mono_left nhdsWithin_le_nhds
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto
    ht.1 hderiv hDint hzero htend
  have hEint := (intervalIntegrable_thetaRealIntegratingFactor r).mono_set
    h0t
  have hTint := (intervalIntegrable_thetaTransposeRieszIntegrand r ht).mono_set
    h0t
  have hsplit : (∫ u in (0 : ℝ)..t, D u) =
      (∫ u in (0 : ℝ)..t, E u) -
        (r : ℂ) * ∫ u in (0 : ℝ)..t, thetaTransposeRieszIntegrand r t u := by
    rw [intervalIntegral.integral_sub hEint (hTint.const_mul (r : ℂ)),
      intervalIntegral.integral_const_mul]
  rw [hsplit] at hFTC
  have hA : (∫ u in (0 : ℝ)..t, E u) = rootA thetaSource (r : ℂ) t := rfl
  rw [hA] at hFTC
  dsimp only [L, E] at hFTC
  rw [sub_zero] at hFTC
  apply (eq_div_iff (show (r : ℂ) ≠ 0 by exact_mod_cast hr)).2
  calc
    (∫ u in (0 : ℝ)..t, thetaTransposeRieszIntegrand r t u) * (r : ℂ) =
        (r : ℂ) * ∫ u in (0 : ℝ)..t, thetaTransposeRieszIntegrand r t u := mul_comm _ _
    _ = rootA thetaSource (r : ℂ) t -
        (t : ℂ) * thetaRealIntegratingFactor r t := by
      linear_combination -hFTC

theorem integral_thetaTransposeRieszIntegrand_t_one {r t : ℝ}
    (hr : r ≠ 0) (ht : t ∈ Ioo (0 : ℝ) 1) :
    (∫ u in t..(1 : ℝ), thetaTransposeRieszIntegrand r t u) =
      (rootA thetaSource (r : ℂ) 1 - rootA thetaSource (r : ℂ) t -
        ((1 - t : ℝ) : ℂ) * thetaRealIntegratingFactor r t) / (r : ℂ) := by
  let E := thetaRealIntegratingFactor r
  let R : ℝ → ℂ := fun u => (1 - u) • E u
  let D : ℝ → ℂ := fun u => -E u + (r : ℂ) * thetaTransposeRieszIntegrand r t u
  have h0t : uIcc (0 : ℝ) t ⊆ uIcc (0 : ℝ) 1 := by
    rw [uIcc_of_le ht.1.le, uIcc_of_le zero_le_one]
    exact fun x hx => ⟨hx.1, hx.2.trans ht.2.le⟩
  have ht1 : uIcc t (1 : ℝ) ⊆ uIcc (0 : ℝ) 1 := by
    rw [uIcc_of_le ht.2.le, uIcc_of_le zero_le_one]
    exact fun x hx => ⟨ht.1.le.trans hx.1, hx.2⟩
  have hderiv : ∀ u ∈ Ioo t (1 : ℝ), HasDerivAt R (D u) u := by
    intro u hu
    have huIoo : u ∈ Ioo (0 : ℝ) 1 := ⟨ht.1.trans hu.1, hu.2⟩
    have huLin : HasDerivAt (fun s : ℝ => 1 - s) (-1) u := by
      simpa using (hasDerivAt_id u).const_sub (1 : ℝ)
    have hE := hasDerivAt_thetaRealIntegratingFactor r huIoo
    have hprod := huLin.smul hE
    have hprod' : HasDerivAt R
        ((1 - u) •
          (E u * (Complex.I * (r : ℂ) * (quantileSpeed thetaSource u : ℂ))) +
          (-1 : ℝ) • E u) u := by
      exact hprod
    refine hprod'.congr_deriv ?_
    dsimp only [D]
    simp only [Complex.real_smul]
    rw [thetaTransposeRieszIntegrand]
    rw [show pinnedKernelSlice u t = 1 - u by
      simp [pinnedKernelSlice, hu.1.le]]
    push_cast
    ring
  have hDint : IntervalIntegrable D volume t 1 := by
    have hEint := (intervalIntegrable_thetaRealIntegratingFactor r).mono_set
      ht1
    have hTint := (intervalIntegrable_thetaTransposeRieszIntegrand r ht).mono_set
      ht1
    exact hEint.neg.add (hTint.const_mul (r : ℂ))
  have htend : Tendsto R (𝓝[>] t)
      (𝓝 (((1 - t : ℝ) : ℂ) * E t)) := by
    have hcont : ContinuousAt R t := by
      exact (continuousAt_const.sub continuousAt_id).smul
          (hasDerivAt_thetaRealIntegratingFactor r ht).continuousAt
    simpa only [R, Complex.real_smul] using
      hcont.tendsto.mono_left nhdsWithin_le_nhds
  have hone : Tendsto R (𝓝[<] (1 : ℝ)) (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    have hcont : ContinuousAt (fun u : ℝ => 1 - u) 1 :=
      continuousAt_const.sub continuousAt_id
    have hid : Tendsto (fun u : ℝ => 1 - u) (𝓝[<] (1 : ℝ)) (𝓝 0) := by
      simpa using hcont.tendsto.mono_left nhdsWithin_le_nhds
    have habs : Tendsto (fun u : ℝ => |1 - u|) (𝓝[<] (1 : ℝ)) (𝓝 0) := by
      simpa only [Real.norm_eq_abs, norm_zero] using hid.norm
    convert habs using 1
    · ext u
      dsimp only [R]
      rw [norm_smul, Real.norm_eq_abs,
        norm_thetaRealIntegratingFactor, mul_one]
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto
    ht.2 hderiv hDint htend hone
  have hEint : IntervalIntegrable E volume t 1 :=
    (intervalIntegrable_thetaRealIntegratingFactor r).mono_set ht1
  have hTint : IntervalIntegrable (thetaTransposeRieszIntegrand r t) volume t 1 :=
    (intervalIntegrable_thetaTransposeRieszIntegrand r ht).mono_set ht1
  have hsplit : (∫ u in t..(1 : ℝ), D u) =
      -(∫ u in t..(1 : ℝ), E u) +
        (r : ℂ) * ∫ u in t..(1 : ℝ), thetaTransposeRieszIntegrand r t u := by
    change (∫ u in t..(1 : ℝ),
      (-E) u + ((r : ℂ) • thetaTransposeRieszIntegrand r t) u) = _
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [intervalIntegral.integral_add hEint.neg (hTint.const_mul (r : ℂ))]
    have hneg : (∫ u in t..(1 : ℝ), (-E) u) =
        -(∫ u in t..(1 : ℝ), E u) := by
      simpa only [Pi.neg_apply] using
        (intervalIntegral.integral_neg (μ := volume) (a := t) (b := (1 : ℝ)) (f := E))
    have hmul : (∫ u in t..(1 : ℝ),
        (r : ℂ) * thetaTransposeRieszIntegrand r t u) =
        (r : ℂ) * ∫ u in t..(1 : ℝ), thetaTransposeRieszIntegrand r t u := by
      exact intervalIntegral.integral_const_mul (r : ℂ)
        (thetaTransposeRieszIntegrand r t)
    rw [hneg, hmul]
  rw [hsplit] at hFTC
  have hE : (∫ u in t..(1 : ℝ), E u) =
      rootA thetaSource (r : ℂ) 1 - rootA thetaSource (r : ℂ) t := by
    have hsum := intervalIntegral.integral_add_adjacent_intervals
      ((intervalIntegrable_thetaRealIntegratingFactor r).mono_set h0t)
      ((intervalIntegrable_thetaRealIntegratingFactor r).mono_set ht1)
    change (∫ u in (0 : ℝ)..t, E u) + (∫ u in t..(1 : ℝ), E u) =
      ∫ u in (0 : ℝ)..1, E u at hsum
    rw [show (∫ u in (0 : ℝ)..t, E u) = rootA thetaSource (r : ℂ) t from rfl,
      show (∫ u in (0 : ℝ)..1, E u) = rootA thetaSource (r : ℂ) 1 from rfl] at hsum
    linear_combination hsum
  rw [hE] at hFTC
  dsimp only [R, E] at hFTC
  rw [zero_sub] at hFTC
  apply (eq_div_iff (show (r : ℂ) ≠ 0 by exact_mod_cast hr)).2
  linear_combination hFTC

theorem thetaRealResolventMoment_neg_transposeVec {r t : ℝ}
    (hr : r ≠ 0) (ht : t ∈ Ioo (0 : ℝ) 1) :
    thetaRealResolventMoment r
        (-(transposeVec thetaSource hasFiniteKernelEnergy_thetaSource t)) =
      (rootA thetaSource (r : ℂ) 1 - thetaRealIntegratingFactor r t) / (r : ℂ) := by
  have hcoe :
      (fun u => thetaRealIntegratingFactor r u *
        ((-(transposeVec thetaSource hasFiniteKernelEnergy_thetaSource t) : H) u))
        =ᵐ[unitIntervalMeasure] thetaTransposeRieszIntegrand r t := by
    filter_upwards [Lp.coeFn_neg
      (transposeVec thetaSource hasFiniteKernelEnergy_thetaSource t),
      transposeVec_coeFn thetaSource hasFiniteKernelEnergy_thetaSource ht] with u hneg htrans
    rw [hneg]
    simp only [Pi.neg_apply]
    rw [htrans, transposeKernelFun, thetaTransposeRieszIntegrand]
    ring
  rw [thetaRealResolventMoment]
  have hfull : (∫ u in (0 : ℝ)..1,
      thetaRealIntegratingFactor r u *
        ((-(transposeVec thetaSource hasFiniteKernelEnergy_thetaSource t) : H) u)) =
      ∫ u in (0 : ℝ)..1, thetaTransposeRieszIntegrand r t u := by
    apply intervalIntegral.integral_congr_ae
    have hcoe' :
        (fun u => thetaRealIntegratingFactor r u *
          ((-(transposeVec thetaSource hasFiniteKernelEnergy_thetaSource t) : H) u))
          =ᵐ[volume.restrict (Icc (0 : ℝ) 1)] thetaTransposeRieszIntegrand r t := by
      simpa only [unitIntervalMeasure] using hcoe
    have hcoeVol := (ae_restrict_iff' measurableSet_Icc).mp hcoe'
    filter_upwards [hcoeVol] with u hu
    intro huIoc
    exact hu (by
      rw [uIoc_of_le zero_le_one] at huIoc
      exact Ioc_subset_Icc_self huIoc)
  have h0t : uIcc (0 : ℝ) t ⊆ uIcc (0 : ℝ) 1 := by
    rw [uIcc_of_le ht.1.le, uIcc_of_le zero_le_one]
    exact fun x hx => ⟨hx.1, hx.2.trans ht.2.le⟩
  have ht1 : uIcc t (1 : ℝ) ⊆ uIcc (0 : ℝ) 1 := by
    rw [uIcc_of_le ht.2.le, uIcc_of_le zero_le_one]
    exact fun x hx => ⟨ht.1.le.trans hx.1, hx.2⟩
  rw [hfull, ← intervalIntegral.integral_add_adjacent_intervals
    ((intervalIntegrable_thetaTransposeRieszIntegrand r ht).mono_set
      h0t)
    ((intervalIntegrable_thetaTransposeRieszIntegrand r ht).mono_set
      ht1),
    integral_thetaTransposeRieszIntegrand_zero_t hr ht,
    integral_thetaTransposeRieszIntegrand_t_one hr ht]
  field_simp [hr]
  push_cast
  ring

/-- The Green primitive on a transposed Riesz row, in closed form. -/
theorem thetaPinnedPrimitive_thetaRealResolvent_neg_transposeVec {r t : ℝ}
    (hr0 : r ≠ 0) (hr : |r| * ‖thetaKernelOperator‖ < 1)
    (hA : rootA thetaSource (r : ℂ) 1 ≠ 0)
    (ht : t ∈ Ioo (0 : ℝ) 1) :
    thetaPinnedPrimitive
        (thetaRealResolvent r
          (-(transposeVec thetaSource hasFiniteKernelEnergy_thetaSource t))) t =
      (rootA thetaSource (r : ℂ) t /
          rootA thetaSource (r : ℂ) 1 - (t : ℂ)) / (r : ℂ) := by
  have hcoe :
      (fun u => thetaRealIntegratingFactor r u *
        ((-(transposeVec thetaSource hasFiniteKernelEnergy_thetaSource t) : H) u))
        =ᵐ[unitIntervalMeasure] thetaTransposeRieszIntegrand r t := by
    filter_upwards [Lp.coeFn_neg
      (transposeVec thetaSource hasFiniteKernelEnergy_thetaSource t),
      transposeVec_coeFn thetaSource hasFiniteKernelEnergy_thetaSource ht] with u hneg htrans
    rw [hneg]
    simp only [Pi.neg_apply]
    rw [htrans, transposeKernelFun, thetaTransposeRieszIntegrand]
    ring
  have hprefix : (∫ u in (0 : ℝ)..t,
      thetaRealIntegratingFactor r u *
        ((-(transposeVec thetaSource hasFiniteKernelEnergy_thetaSource t) : H) u)) =
      (rootA thetaSource (r : ℂ) t -
        (t : ℂ) * thetaRealIntegratingFactor r t) / (r : ℂ) := by
    rw [show (∫ u in (0 : ℝ)..t,
        thetaRealIntegratingFactor r u *
          ((-(transposeVec thetaSource hasFiniteKernelEnergy_thetaSource t) : H) u)) =
        ∫ u in (0 : ℝ)..t, thetaTransposeRieszIntegrand r t u by
      apply intervalIntegral.integral_congr_ae
      have hcoe' :
          (fun u => thetaRealIntegratingFactor r u *
            ((-(transposeVec thetaSource hasFiniteKernelEnergy_thetaSource t) : H) u))
            =ᵐ[volume.restrict (Icc (0 : ℝ) 1)] thetaTransposeRieszIntegrand r t := by
        simpa only [unitIntervalMeasure] using hcoe
      have hcoeVol := (ae_restrict_iff' measurableSet_Icc).mp hcoe'
      filter_upwards [hcoeVol] with u hu
      intro huIoc
      rw [uIoc_of_le ht.1.le] at huIoc
      exact hu ⟨huIoc.1.le, huIoc.2.trans ht.2.le⟩]
    exact integral_thetaTransposeRieszIntegrand_zero_t hr0 ht
  rw [thetaPinnedPrimitive_thetaRealResolvent_eq_green hr _ hA ht,
    thetaRealGreenPrimitive, hprefix,
    thetaRealResolventMoment_neg_transposeVec hr0 ht]
  have hFE : rootFactor thetaSource (r : ℂ) t *
      thetaRealIntegratingFactor r t = 1 :=
    rootFactor_mul_sourceChar thetaSource (r : ℂ) t
  have hcollapse (x : ℂ) : rootFactor thetaSource (r : ℂ) t * x *
      thetaRealIntegratingFactor r t = x := by
    calc
      rootFactor thetaSource (r : ℂ) t * x * thetaRealIntegratingFactor r t =
          x * (rootFactor thetaSource (r : ℂ) t * thetaRealIntegratingFactor r t) := by
        ring
      _ = x := by rw [hFE, mul_one]
  field_simp [hr0, hA]
  calc
    rootFactor thetaSource (r : ℂ) t *
        ((rootA thetaSource (r : ℂ) t -
              (t : ℂ) * thetaRealIntegratingFactor r t) *
            rootA thetaSource (r : ℂ) 1 -
          rootA thetaSource (r : ℂ) t *
            (rootA thetaSource (r : ℂ) 1 - thetaRealIntegratingFactor r t)) =
        (rootFactor thetaSource (r : ℂ) t *
            rootA thetaSource (r : ℂ) t * thetaRealIntegratingFactor r t) -
          (rootFactor thetaSource (r : ℂ) t * (t : ℂ) *
            thetaRealIntegratingFactor r t) * rootA thetaSource (r : ℂ) 1 := by
      ring
    _ = rootA thetaSource (r : ℂ) t -
        (t : ℂ) * rootA thetaSource (r : ℂ) 1 := by
      rw [hcollapse (rootA thetaSource (r : ℂ) t), hcollapse (t : ℂ)]

/-! ### Hilbert--Schmidt field of the regularized real resolvent -/

/-- Precomposition on the continuous dual, as a bounded operator. -/
def thetaDualPrecomp (J : H →L[ℂ] H) : (H →L[ℂ] ℂ) →L[ℂ] (H →L[ℂ] ℂ) :=
  (ContinuousLinearMap.apply ℂ (H →L[ℂ] ℂ) J).comp
    (ContinuousLinearMap.compL ℂ H H ℂ)

@[simp] theorem thetaDualPrecomp_apply (J : H →L[ℂ] H) (ell : H →L[ℂ] ℂ) (f : H) :
    thetaDualPrecomp J ell f = ell (J f) := rfl

/-- Kernel field representing `r B (I+rB)⁻¹`. -/
def thetaRealRegularizedResolventField (r : ℝ) :
    Lp (H →L[ℂ] ℂ) 2 unitIntervalMeasure :=
  (((r : ℂ) • thetaDualPrecomp (thetaRealResolvent r)).compLpL
      2 unitIntervalMeasure)
    (pinnedKernelL2 thetaSource hasFiniteKernelEnergy_thetaSource)

theorem thetaRealRegularizedResolventField_coeFn (r : ℝ) :
    (thetaRealRegularizedResolventField r : ℝ → H →L[ℂ] ℂ)
      =ᵐ[unitIntervalMeasure]
        fun t => (r : ℂ) •
          (pinnedKernelField thetaSource t).comp (thetaRealResolvent r) := by
  have hcomp := (((r : ℂ) • thetaDualPrecomp (thetaRealResolvent r)).coeFn_compLpL
    (p := (2 : ENNReal)) (μ := unitIntervalMeasure)
    (pinnedKernelL2 thetaSource hasFiniteKernelEnergy_thetaSource))
  filter_upwards [hcomp,
    pinnedKernelL2_coeFn thetaSource hasFiniteKernelEnergy_thetaSource] with t h1 h2
  rw [thetaRealRegularizedResolventField]
  rw [h1, h2]
  rfl

/-- The kernel operator of the transformed field is the regularized resolvent factor. -/
theorem kernelOperator_thetaRealRegularizedResolventField (r : ℝ) :
    kernelOperator (E := H) unitIntervalMeasure
        (thetaRealRegularizedResolventField r) =
      (r : ℂ) • (thetaKernelOperator ∘L thetaRealResolvent r) := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [
    kernelOperator_ae_of_field (K := thetaRealRegularizedResolventField r) f,
    thetaRealRegularizedResolventField_coeFn r,
    kernelOperator_ae_of_field
      (K := pinnedKernelL2 thetaSource hasFiniteKernelEnergy_thetaSource)
      (thetaRealResolvent r f),
    pinnedKernelL2_coeFn thetaSource hasFiniteKernelEnergy_thetaSource,
    Lp.coeFn_smul (r : ℂ) (thetaKernelOperator (thetaRealResolvent r f))]
      with t hleft hfield hpinned hpinfield hsmul
  rw [hleft, hfield]
  change (r : ℂ) * pinnedKernelField thetaSource t (thetaRealResolvent r f) = _
  simp only [ContinuousLinearMap.comp_apply, smul_apply]
  rw [hsmul]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [thetaKernelOperator]
  rw [hpinned, hpinfield]

/-- Operator trace of the regularized real source resolvent. -/
def thetaRealRegularizedTrace (r : ℝ) : ℂ :=
  opTrace (thetaKernelOperator ∘L
    ((r : ℂ) • (thetaKernelOperator ∘L thetaRealResolvent r)))

theorem thetaRealRegularizedTrace_eq_field_integral (r : ℝ) :
    thetaRealRegularizedTrace r =
      ∫ t, (inner ℂ
        ((InnerProductSpace.toDual ℂ H).symm
          (thetaRealRegularizedResolventField r t))
        ((InnerProductSpace.toDual ℂ H).symm
          (transposeKernelL2 thetaSource hasFiniteKernelEnergy_thetaSource t)) : ℂ)
        ∂unitIntervalMeasure := by
  rw [thetaRealRegularizedTrace,
    ContinuousLinearMap.opTrace_comp_eq_hsInner]
  rw [← kernelOperator_thetaRealRegularizedResolventField r]
  rw [thetaKernelOperator,
    adjoint_kernelOperator_eq thetaSource hasFiniteKernelEnergy_thetaSource]
  exact hsInner_kernelOperator (E := H) unitIntervalMeasure
    (transposeKernelL2 thetaSource hasFiniteKernelEnergy_thetaSource)
    (thetaRealRegularizedResolventField r)

theorem inner_riesz_thetaRealRegularizedResolventField {r t : ℝ}
    (hr0 : r ≠ 0) (hr : |r| * ‖thetaKernelOperator‖ < 1)
    (hA : rootA thetaSource (r : ℂ) 1 ≠ 0)
    (ht : t ∈ Ioo (0 : ℝ) 1) :
    (inner ℂ
      ((InnerProductSpace.toDual ℂ H).symm
        ((r : ℂ) •
          (pinnedKernelField thetaSource t).comp (thetaRealResolvent r)))
      ((InnerProductSpace.toDual ℂ H).symm
        (transposeKernelField thetaSource hasFiniteKernelEnergy_thetaSource t)) : ℂ) =
      Complex.I * (quantileSpeed thetaSource t : ℂ) *
        (rootA thetaSource (r : ℂ) t /
          rootA thetaSource (r : ℂ) 1 - (t : ℂ)) := by
  rw [toDual_symm_transposeKernelField]
  let ell : H →L[ℂ] ℂ := (r : ℂ) •
    (pinnedKernelField thetaSource t).comp (thetaRealResolvent r)
  let v : H := -(transposeVec thetaSource hasFiniteKernelEnergy_thetaSource t)
  have hdual := (InnerProductSpace.toDual ℂ H).apply_symm_apply ell
  have heval := congrArg (fun psi : H →L[ℂ] ℂ => psi v) hdual
  change (inner ℂ ((InnerProductSpace.toDual ℂ H).symm ell) v : ℂ) = ell v at heval
  rw [heval]
  dsimp only [ell, v]
  simp only [smul_apply, ContinuousLinearMap.comp_apply,
    smul_eq_mul]
  rw [pinnedKernelField_apply_eq_pinnedVolterraFun,
    ← thetaPinnedPrimitive_eq_pinnedVolterraFun _ (Ioo_subset_Icc_self ht),
    thetaPinnedPrimitive_thetaRealResolvent_neg_transposeVec hr0 hr hA ht]
  field_simp [hr0]

theorem thetaRealRegularizedTrace_eq_quantile_integral {r : ℝ}
    (hr0 : r ≠ 0) (hr : |r| * ‖thetaKernelOperator‖ < 1)
    (hA : rootA thetaSource (r : ℂ) 1 ≠ 0) :
    thetaRealRegularizedTrace r =
      ∫ t, Complex.I * (quantileSpeed thetaSource t : ℂ) *
        (rootA thetaSource (r : ℂ) t /
          rootA thetaSource (r : ℂ) 1 - (t : ℂ))
        ∂unitIntervalMeasure := by
  rw [thetaRealRegularizedTrace_eq_field_integral]
  apply integral_congr_ae
  filter_upwards [thetaRealRegularizedResolventField_coeFn r,
    transposeKernelL2_coeFn thetaSource hasFiniteKernelEnergy_thetaSource,
    ae_unitIntervalMeasure_mem_Ioo] with t hfield htrans ht
  rw [hfield, htrans]
  exact inner_riesz_thetaRealRegularizedResolventField hr0 hr hA ht

/-! ### Collapse of the quantile trace integral -/

theorem memLp_thetaRealIntegratingFactor (r : ℝ) :
    MemLp (thetaRealIntegratingFactor r) 2 unitIntervalMeasure := by
  refine MemLp.of_bound (integrable_thetaRealIntegratingFactor r).1 1 ?_
  filter_upwards with t
  rw [norm_thetaRealIntegratingFactor]

/-- The unit-modulus integrating factor as an `L²` vector. -/
def thetaRealIntegratingFactorVec (r : ℝ) : H :=
  (memLp_thetaRealIntegratingFactor r).toLp (thetaRealIntegratingFactor r)

theorem thetaRealIntegratingFactorVec_coeFn (r : ℝ) :
    (thetaRealIntegratingFactorVec r : ℝ → ℂ)
      =ᵐ[unitIntervalMeasure] thetaRealIntegratingFactor r :=
  MemLp.coeFn_toLp _

theorem pinnedMean_thetaRealIntegratingFactorVec (r : ℝ) :
    pinnedMean (thetaRealIntegratingFactorVec r) =
      rootA thetaSource (r : ℂ) 1 := by
  rw [pinnedMean]
  have hcoe := thetaRealIntegratingFactorVec_coeFn r
  rw [integral_congr_ae hcoe]
  change (∫ u, thetaRealIntegratingFactor r u
      ∂volume.restrict (Icc (0 : ℝ) 1)) = _
  rw [← MeasureTheory.integral_indicator measurableSet_Icc]
  rw [show (∫ u, (Icc (0 : ℝ) 1).indicator
        (thetaRealIntegratingFactor r) u) =
      ∫ u in Icc (0 : ℝ) 1, thetaRealIntegratingFactor r u by
    rw [MeasureTheory.integral_indicator measurableSet_Icc]]
  rw [integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le zero_le_one]
  rfl

theorem pinnedVolterraFun_thetaRealIntegratingFactorVec {r t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) :
    pinnedVolterraFun (thetaRealIntegratingFactorVec r) t =
      rootA thetaSource (r : ℂ) t -
        (t : ℂ) * rootA thetaSource (r : ℂ) 1 := by
  rw [pinnedVolterraFun,
    pinnedPrefix_eq_intervalIntegral (thetaRealIntegratingFactorVec r) ht,
    pinnedMean_thetaRealIntegratingFactorVec]
  congr 1
  apply intervalIntegral.integral_congr_ae
  have hcoe' :
      (thetaRealIntegratingFactorVec r : ℝ → ℂ)
        =ᵐ[volume.restrict (Icc (0 : ℝ) 1)] thetaRealIntegratingFactor r := by
    simpa only [unitIntervalMeasure] using thetaRealIntegratingFactorVec_coeFn r
  have hcoeVol := (ae_restrict_iff' measurableSet_Icc).mp hcoe'
  filter_upwards [hcoeVol] with u hu
  intro huIoc
  rw [uIoc_of_le ht.1] at huIoc
  exact hu ⟨huIoc.1.le, huIoc.2.trans ht.2⟩

theorem integral_thetaRealIntegratingFactor_mul_pinnedKernelSlice {r t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) 1) :
    (∫ s, thetaRealIntegratingFactor r s * (pinnedKernelSlice t s : ℂ)
        ∂unitIntervalMeasure) =
      rootA thetaSource (r : ℂ) t -
        (t : ℂ) * rootA thetaSource (r : ℂ) 1 := by
  let f := thetaRealIntegratingFactorVec r
  have hinner : (inner ℂ (pinnedSliceVec t) f : ℂ) = pinnedVolterraFun f t := by
    rw [MeasureTheory.L2.inner_def, pinnedVolterraFun, pinnedPrefix, pinnedMean]
    have hcoe : (fun u => (inner ℂ ((pinnedSliceVec t : ℝ → ℂ) u) (f u) : ℂ))
        =ᵐ[unitIntervalMeasure]
        fun u => (Iic t).indicator (fun u => f u) u - (t : ℂ) * f u := by
      filter_upwards [pinnedSliceVec_coeFn t] with u hu
      rw [hu, RCLike.inner_apply', pinnedKernelSlice]
      by_cases hut : u ≤ t <;> simp [hut] <;> ring
    rw [integral_congr_ae hcoe]
    rw [MeasureTheory.integral_sub]
    · rw [MeasureTheory.integral_const_mul]
    · exact (integrable_coe f).indicator measurableSet_Iic
    · exact (integrable_coe f).const_mul (t : ℂ)
  have hintegral : (inner ℂ (pinnedSliceVec t) f : ℂ) =
      ∫ s, thetaRealIntegratingFactor r s * (pinnedKernelSlice t s : ℂ)
        ∂unitIntervalMeasure := by
    rw [MeasureTheory.L2.inner_def]
    apply integral_congr_ae
    filter_upwards [pinnedSliceVec_coeFn t,
      thetaRealIntegratingFactorVec_coeFn r] with s hs hf
    rw [hs, hf, RCLike.inner_apply', Complex.conj_ofReal]
    ring
  rw [← hintegral, hinner,
    pinnedVolterraFun_thetaRealIntegratingFactorVec (Ioo_subset_Icc_self ht)]

set_option maxHeartbeats 2000000 in
theorem integral_quantile_resolvent_eq_neg_first_moment {r : ℝ}
    (hA : rootA thetaSource (r : ℂ) 1 ≠ 0) :
    (∫ t, Complex.I * (quantileSpeed thetaSource t : ℂ) *
        (rootA thetaSource (r : ℂ) t /
          rootA thetaSource (r : ℂ) 1 - (t : ℂ))
        ∂unitIntervalMeasure) =
      -(Complex.I / rootA thetaSource (r : ℂ) 1) *
        ∫ s, (thetaSource.quantileFun s : ℂ) *
          thetaRealIntegratingFactor r s ∂unitIntervalMeasure := by
  let A1 := rootA thetaSource (r : ℂ) 1
  let C := Complex.I / A1
  let F : ℝ → ℝ → ℂ := fun t s =>
    C * (quantileSpeed thetaSource t : ℂ) *
      thetaRealIntegratingFactor r s * (pinnedKernelSlice t s : ℂ)
  have hmq : Measurable (quantileSpeed thetaSource) :=
    measurable_const.div
      (thetaSource.continuous_k.measurable.comp thetaSource.measurable_quantileFun)
  have hset : MeasurableSet {p : ℝ × ℝ | p.2 ≤ p.1} :=
    measurableSet_le measurable_snd measurable_fst
  have hslice : Measurable (fun p : ℝ × ℝ => pinnedKernelSlice p.1 p.2) :=
    (Measurable.ite hset measurable_const measurable_const).sub measurable_fst
  have hE : Measurable (thetaRealIntegratingFactor r) :=
    (continuous_sourceChar (r : ℂ)).measurable.comp thetaSource.measurable_quantileFun
  have hFmeas : AEStronglyMeasurable (Function.uncurry F)
      (unitIntervalMeasure.prod unitIntervalMeasure) := by
    exact (((measurable_const.mul
      (Complex.measurable_ofReal.comp (hmq.comp measurable_fst))).mul
        (hE.comp measurable_snd)).mul
          (Complex.measurable_ofReal.comp hslice)).aestronglyMeasurable
  have hFint : Integrable (Function.uncurry F)
      (unitIntervalMeasure.prod unitIntervalMeasure) := by
    refine Integrable.mono'
      ((integrable_uncurry_abs_slice thetaSource
        hasFiniteKernelEnergy_thetaSource).const_mul ‖C‖) hFmeas ?_
    filter_upwards with p
    have hq : 0 < quantileSpeed thetaSource p.1 := quantileSpeed_pos thetaSource p.1
    dsimp only [F, Function.uncurry]
    rw [norm_mul, norm_mul, norm_mul, norm_thetaRealIntegratingFactor,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hq, mul_one]
    rw [show ‖(pinnedKernelSlice p.1 p.2 : ℂ)‖ =
        |pinnedKernelSlice p.1 p.2| by
      rw [Complex.norm_real, Real.norm_eq_abs]]
    simpa only [mul_assoc] using
      (le_refl (‖C‖ * quantileSpeed thetaSource p.1 *
        |pinnedKernelSlice p.1 p.2|))
  have hpoint : ∀ᵐ t ∂unitIntervalMeasure,
      Complex.I * (quantileSpeed thetaSource t : ℂ) *
          (rootA thetaSource (r : ℂ) t /
            rootA thetaSource (r : ℂ) 1 - (t : ℂ)) =
        ∫ s, F t s ∂unitIntervalMeasure := by
    filter_upwards [ae_unitIntervalMeasure_mem_Ioo] with t ht
    have hsliceInt := integral_thetaRealIntegratingFactor_mul_pinnedKernelSlice
      (r := r) ht
    have hfactor : (∫ s, F t s ∂unitIntervalMeasure) =
        C * (quantileSpeed thetaSource t : ℂ) *
          (rootA thetaSource (r : ℂ) t -
            (t : ℂ) * rootA thetaSource (r : ℂ) 1) := by
      calc
        (∫ s, F t s ∂unitIntervalMeasure) =
            C * (quantileSpeed thetaSource t : ℂ) *
              ∫ s, thetaRealIntegratingFactor r s *
                (pinnedKernelSlice t s : ℂ) ∂unitIntervalMeasure := by
          rw [← MeasureTheory.integral_const_mul]
          apply integral_congr_ae
          filter_upwards with s
          dsimp only [F]
          ring
        _ = _ := by rw [hsliceInt]
    rw [hfactor]
    dsimp only [C, A1]
    field_simp [hA]
  rw [integral_congr_ae hpoint, integral_integral_swap hFint]
  have houter : (∫ s, ∫ t, F t s ∂unitIntervalMeasure
      ∂unitIntervalMeasure) =
      ∫ s, -C * ((thetaSource.quantileFun s : ℂ) *
        thetaRealIntegratingFactor r s) ∂unitIntervalMeasure := by
    apply integral_congr_ae
    filter_upwards [ae_unitIntervalMeasure_mem_Ioo] with s hs
    have hinner : (∫ t, F t s ∂unitIntervalMeasure) =
        C * thetaRealIntegratingFactor r s *
          (sliceMoment thetaSource s : ℂ) := by
      calc
        (∫ t, F t s ∂unitIntervalMeasure) =
            C * thetaRealIntegratingFactor r s *
              ∫ t, ((quantileSpeed thetaSource t *
                pinnedKernelSlice t s : ℝ) : ℂ) ∂unitIntervalMeasure := by
          rw [← MeasureTheory.integral_const_mul]
          apply integral_congr_ae
          filter_upwards with t
          dsimp only [F]
          push_cast
          ring
        _ = C * thetaRealIntegratingFactor r s *
            (sliceMoment thetaSource s : ℂ) := by
          rw [integral_complex_ofReal]
          rfl
    rw [hinner, sliceMoment_eq_neg_quantileFun hs]
    push_cast
    ring
  rw [houter, ← MeasureTheory.integral_const_mul]

theorem deriv_XiC_ofReal_eq_quantile_first_moment (r : ℝ) :
    deriv XiC (r : ℂ) =
      Complex.I * (thetaSource.mass : ℂ) *
        ∫ s, (thetaSource.quantileFun s : ℂ) *
          thetaRealIntegratingFactor r s ∂unitIntervalMeasure := by
  let g : ℝ → ℂ := fun x => (x : ℂ) * sourceChar (r : ℂ) x
  have hgmeas : AEStronglyMeasurable g (volume : Measure ℝ) := by
    exact (Complex.continuous_ofReal.mul
      (continuous_sourceChar (r : ℂ))).aestronglyMeasurable
  have hquant := integral_comp_quantile thetaSource g hgmeas
  rw [← unitIntervalMeasure_eq] at hquant
  have htransport : (thetaSource.mass : ℂ) *
      (∫ s, (thetaSource.quantileFun s : ℂ) *
        thetaRealIntegratingFactor r s ∂unitIntervalMeasure) =
      ∫ x, (thetaSource.k x : ℂ) * (x : ℂ) *
        sourceChar (r : ℂ) x := by
    change (thetaSource.mass : ℂ) *
      (∫ s, g (thetaSource.quantileFun s) ∂unitIntervalMeasure) = _
    rw [hquant, ← MeasureTheory.integral_const_mul]
    apply integral_congr_ae
    filter_upwards with x
    dsimp only [g]
    rw [Complex.real_smul]
    rw [show thetaSource.normalized x =
      thetaSource.k x / thetaSource.mass from rfl]
    have hM : (thetaSource.mass : ℂ) ≠ 0 := by
      exact_mod_cast thetaSource.mass_ne_zero
    push_cast
    field_simp [hM]
  have hFL := hasDerivAt_thetaCuspFourierLaplace_all (-(r : ℂ))
  have hneg : HasDerivAt (fun z : ℂ => -z) (-1) (r : ℂ) :=
    (hasDerivAt_id (r : ℂ)).neg
  have hcomp := hFL.comp (r : ℂ) hneg
  change HasDerivAt (fun z : ℂ => thetaCuspFourierLaplace (-z))
    ((∫ x : ℝ, thetaCuspFourierLaplaceDerivativeIntegrand (-(r : ℂ)) x) * (-1))
    (r : ℂ) at hcomp
  have hfun : (fun z : ℂ => thetaCuspFourierLaplace (-z)) = XiC := by
    funext z
    rw [thetaCuspFourierLaplace_eq_XiC_all, XiC_even]
  rw [hfun] at hcomp
  have hderiv : deriv XiC (r : ℂ) =
      -(∫ x : ℝ, thetaCuspFourierLaplaceDerivativeIntegrand (-(r : ℂ)) x) := by
    rw [hcomp.deriv]
    ring
  have hphysical :
      -(∫ x : ℝ, thetaCuspFourierLaplaceDerivativeIntegrand (-(r : ℂ)) x) =
        Complex.I * ∫ x, (thetaSource.k x : ℂ) * (x : ℂ) *
          sourceChar (r : ℂ) x := by
    rw [← MeasureTheory.integral_neg, ← MeasureTheory.integral_const_mul]
    apply integral_congr_ae
    filter_upwards with x
    rw [thetaCuspFourierLaplaceDerivativeIntegrand,
      thetaCuspFourierLaplaceIntegrand, sourceChar, thetaSource_k]
    ring
  rw [hderiv, hphysical, ← htransport]
  ring

/-- Real regularized resolvent trace is the negative Xi logarithmic derivative. -/
theorem thetaRealRegularizedTrace_eq_neg_logDeriv_XiC {r : ℝ}
    (hr0 : r ≠ 0) (hr : |r| * ‖thetaKernelOperator‖ < 1)
    (hA : rootA thetaSource (r : ℂ) 1 ≠ 0) :
    thetaRealRegularizedTrace r =
      -(deriv XiC (r : ℂ) / XiC (r : ℂ)) := by
  rw [thetaRealRegularizedTrace_eq_quantile_integral hr0 hr hA,
    integral_quantile_resolvent_eq_neg_first_moment hA,
    deriv_XiC_ofReal_eq_quantile_first_moment]
  have hM : (thetaSource.mass : ℂ) ≠ 0 := by
    exact_mod_cast thetaSource.mass_ne_zero
  have hXi : XiC (r : ℂ) ≠ 0 := by
    intro hzero
    apply hA
    rw [rootA_one, xiC_thetaSource_all, hzero, zero_div]
  rw [rootA_one, xiC_thetaSource_all]
  field_simp [hM, hXi]

/-! ### Coordinate transfer of the regularized trace -/

/-- Quantile-space coordinate isometry as a bounded linear map. -/
def thetaCoordinateMap :
    H →L[ℂ] lp (fun _ : thetaIndex => ℂ) 2 :=
  thetaCoord.toContinuousLinearEquiv.toContinuousLinearMap

/-- Inverse coordinate isometry as a bounded linear map. -/
def thetaCoordinateMapInv :
    lp (fun _ : thetaIndex => ℂ) 2 →L[ℂ] H :=
  thetaCoord.symm.toContinuousLinearEquiv.toContinuousLinearMap

@[simp] theorem thetaCoordinateMapInv_apply_thetaCoordinateMap (f : H) :
    thetaCoordinateMapInv (thetaCoordinateMap f) = f := by
  simp [thetaCoordinateMap, thetaCoordinateMapInv]

@[simp] theorem thetaCoordinateMap_apply_thetaCoordinateMapInv
    (w : lp (fun _ : thetaIndex => ℂ) 2) :
    thetaCoordinateMap (thetaCoordinateMapInv w) = w := by
  simp [thetaCoordinateMap, thetaCoordinateMapInv]

theorem thetaCoordinateMap_intertwines_neg_sourceInverse (f : H) :
    thetaCoordinateMap ((-thetaKernelOperator) f) =
      HilbertSchmidt.toOperator isHS_neg_thetaKernelMatrix (thetaCoordinateMap f) := by
  change thetaCoord ((-thetaKernelOperator) f) =
    HilbertSchmidt.toOperator isHS_neg_thetaKernelMatrix (thetaCoord f)
  exact thetaCoord_intertwines_neg_sourceInverse f

/-- Coordinate and quantile real resolvents intertwine on their common small disc. -/
theorem thetaCoordinateResolvent_intertwines {r : ℝ}
    (hr : |r| * ‖thetaKernelOperator‖ < 1)
    (hz : ‖(r : ℂ)‖ * HilbertSchmidt.hsNorm (-thetaKernelMatrix) < 1) (f : H) :
    Ring.inverse
        (1 - (r : ℂ) • HilbertSchmidt.toOperator isHS_neg_thetaKernelMatrix)
        (thetaCoordinateMap f) =
      thetaCoordinateMap (thetaRealResolvent r f) := by
  let T := HilbertSchmidt.toOperator isHS_neg_thetaKernelMatrix
  let A := 1 - (r : ℂ) • T
  let Jc := Ring.inverse A
  have hnorm : ‖(r : ℂ) • T‖ < 1 := by
    rw [norm_smul]
    exact (mul_le_mul_of_nonneg_left
      (HilbertSchmidt.norm_toOperator_le isHS_neg_thetaKernelMatrix)
      (norm_nonneg (r : ℂ))).trans_lt hz
  have hunit : IsUnit A := by
    exact isUnit_one_sub_of_norm_lt_one hnorm
  have hleft : Jc * A = 1 := Ring.inverse_mul_cancel A hunit
  have hpencil : A (thetaCoordinateMap (thetaRealResolvent r f)) =
      thetaCoordinateMap f := by
    have hinter := thetaCoordinateMap_intertwines_neg_sourceInverse
      (thetaRealResolvent r f)
    change thetaCoordinateMap ((-thetaKernelOperator) (thetaRealResolvent r f)) =
      T (thetaCoordinateMap (thetaRealResolvent r f)) at hinter
    change thetaCoordinateMap (thetaRealResolvent r f) -
      (r : ℂ) • T (thetaCoordinateMap (thetaRealResolvent r f)) =
        thetaCoordinateMap f
    rw [← hinter]
    rw [← map_smul, ← map_sub]
    congr 1
    have heq := thetaRealResolvent_equation hr f
    simpa [sub_eq_add_neg] using heq
  change Jc (thetaCoordinateMap f) = _
  calc
    Jc (thetaCoordinateMap f) =
        Jc (A (thetaCoordinateMap (thetaRealResolvent r f))) := by rw [hpencil]
    _ = (Jc * A) (thetaCoordinateMap (thetaRealResolvent r f)) := by
      rfl
    _ = thetaCoordinateMap (thetaRealResolvent r f) := by
      rw [hleft]
      rfl

/-- The coordinate regularized resolvent trace is the quantile-space trace. -/
theorem resolventTrace_neg_thetaKernelMatrix_ofReal_eq_thetaRealRegularizedTrace
    {r : ℝ} (hr : |r| * ‖thetaKernelOperator‖ < 1)
    (hz : ‖(r : ℂ)‖ * HilbertSchmidt.hsNorm (-thetaKernelMatrix) < 1) :
    HilbertSchmidt.resolventTrace (-thetaKernelMatrix) (r : ℂ) =
      thetaRealRegularizedTrace r := by
  let T := HilbertSchmidt.toOperator isHS_neg_thetaKernelMatrix
  let Jc := Ring.inverse (1 - (r : ℂ) • T)
  let U := thetaCoordinateMap
  let V := thetaCoordinateMapInv
  let B := thetaKernelOperator
  let J := thetaRealResolvent r
  let R : H →L[ℂ] H := (r : ℂ) • (B ∘L J)
  let A : H →L[ℂ] lp (fun _ : thetaIndex => ℂ) 2 := U ∘L B
  let C : lp (fun _ : thetaIndex => ℂ) 2 →L[ℂ] H := R ∘L V
  have hB : B.IsHilbertSchmidt := by
    exact isHilbertSchmidt_thetaKernelOperator'
  have hR : R.IsHilbertSchmidt := by
    exact (hB.comp_right J).smul (r : ℂ)
  have hA : A.IsHilbertSchmidt := hB.comp_left U
  have hC : C.IsHilbertSchmidt := hR.comp_right V
  have hP : T ∘L ((r : ℂ) • (T ∘L Jc)) = A ∘L C := by
    apply ContinuousLinearMap.ext
    intro w
    have hJ := thetaCoordinateResolvent_intertwines hr hz (V w)
    change Jc (U (V w)) = U (J (V w)) at hJ
    rw [thetaCoordinateMap_apply_thetaCoordinateMapInv] at hJ
    have houter := thetaCoordinateMap_intertwines_neg_sourceInverse
      ((-B) (J (V w)))
    have hinner := thetaCoordinateMap_intertwines_neg_sourceInverse (J (V w))
    change U ((-B) ((-B) (J (V w)))) =
      T (U ((-B) (J (V w)))) at houter
    change U ((-B) (J (V w))) = T (U (J (V w))) at hinner
    simp only [ContinuousLinearMap.comp_apply, smul_apply]
    rw [hJ, ← hinner]
    rw [map_smul, ← houter]
    simp only [A, C, R, ContinuousLinearMap.comp_apply, smul_apply, map_smul]
    have hneg : (-B) ((-B) (J (V w))) = B (B (J (V w))) := by
      change -B (-B (J (V w))) = B (B (J (V w)))
      rw [map_neg]
      simp
    rw [hneg]
  have hCA : C ∘L A = R ∘L B := by
    apply ContinuousLinearMap.ext
    intro f
    simp only [C, A, R, U, V, ContinuousLinearMap.comp_apply, smul_apply]
    rw [thetaCoordinateMapInv_apply_thetaCoordinateMap]
  rw [HilbertSchmidt.resolventTrace_eq_opTrace_regularizedResolvent
    isHS_neg_thetaKernelMatrix (r : ℂ) hz]
  change opTrace (T ∘L ((r : ℂ) • (T ∘L Jc))) = _
  rw [hP, ContinuousLinearMap.opTrace_comp_comm hA hC, hCA,
    ContinuousLinearMap.opTrace_comp_comm hR hB]
  rfl


end

end RHTower.HedenmalmThetaSource

