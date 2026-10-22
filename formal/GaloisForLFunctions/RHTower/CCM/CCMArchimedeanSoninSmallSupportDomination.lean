import GaloisForLFunctions.RHTower.CCM.CCMArchimedeanSoninTimeBandSlope
import GaloisForLFunctions.HTGeometry.MeanZeroTentQuadraticForm

/-!
# Sonin-trace domination for small supports, and its failure for positive tests

At cutoff one the generic part splits as `G = M - A` with `M ≥ 0` and the time-band part `A`, whose
scaling trace is `Tr(A ϑ_u) = T(|u|)` with `T(u) = Tr(P P̂ ϑ_u)` smooth and `T'(0) = 1`.  Hence

* **domination for small supports.**  If `g` vanishes off `(-ε₀, ε₀)` and `∫ g = 0`, then
  `Re Tr(ϑ(g) G ϑ(g)†) ≥ -Re Tr(ϑ(g) A ϑ(g)†) = 2 ‖Γ‖² (T'(0) - ∫₀^{2ε₀} |T''|) ≥ 0`
  (`Γ` the primitive of `g`; the kernel `T(|u|) - T(0) - |u|` is a mixture of tents
  `(|u| - w)₊` with density `T''`), i.e. the Connes--Consani Sonin-trace domination
  `Re Tr(ϑ(g★ ⋆ g) S) ≤ -Re W(g★ ⋆ g)` holds with the single condition `ĝ(0) = 0`;
* **failure for positive tests.**  `Re Tr(G ϑ_u) ≤ T(0) - T(|u|) ≤ -|u|/2` near `0`, so for every
  nonzero nonnegative test of small support the generic trace is negative and domination fails:
  the vanishing condition cannot be dropped.
-/

noncomputable section

open MeasureTheory Set ContinuousLinearMap
open GaloisForLFunctions.HTGeometry
open scoped InnerProductSpace ComplexConjugate

namespace RHTower

local notation "Pc" => evenIndicatorCutoff 1
local notation "Rc" => evenFourierCutoff 1
local notation "Ac" => ccmSoninTimeBandPart

/-! ## The scaling trace of the time-band part -/

theorem adjoint_ccmSoninTimeBandPart : ContinuousLinearMap.adjoint Ac = Ac := by
  have hP : ∀ x y : evenSubspace, ⟪Pc x, y⟫_ℂ = ⟪x, Pc y⟫_ℂ := fun x y => by
    rw [← ContinuousLinearMap.adjoint_inner_right, adjoint_evenIndicatorCutoff]
  have hR : ∀ x y : evenSubspace, ⟪Rc x, y⟫_ℂ = ⟪x, Rc y⟫_ℂ := fun x y => by
    rw [← ContinuousLinearMap.adjoint_inner_right, adjoint_evenFourierCutoff]
  refine ContinuousLinearMap.isSelfAdjoint_iff'.mp
    (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr fun x y => ?_)
  change ⟪Pc (Rc x) + Rc (Pc x) - Pc (Rc (Pc x)), y⟫_ℂ =
    ⟪x, Pc (Rc y) + Rc (Pc y) - Pc (Rc (Pc y))⟫_ℂ
  simp only [inner_sub_left, inner_add_left, inner_sub_right, inner_add_right, hP, hR]
  ring

/-- **`Tr(A ϑ_u) = T(|u|)`.** -/
theorem ccmScalingTrace_ccmSoninTimeBandPart (u : ℝ) :
    ccmScalingTrace Ac u = (ccmTimeBandTrace |u| : ℂ) := by
  rcases le_or_gt 0 u with hu | hu
  · rw [abs_of_nonneg hu, ccmScalingTrace_ccmSoninTimeBandPart_of_nonneg hu,
      ccmScalingTrace_evenIndicatorCutoff_mul_evenFourierCutoff]
  · have h := conj_ccmScalingTrace memSchattenClass_one_ccmSoninTimeBandPart (-u)
    rw [adjoint_ccmSoninTimeBandPart, neg_neg,
      ccmScalingTrace_ccmSoninTimeBandPart_of_nonneg (by linarith : (0 : ℝ) ≤ -u),
      ccmScalingTrace_evenIndicatorCutoff_mul_evenFourierCutoff, Complex.conj_ofReal] at h
    rw [← h, abs_of_neg hu]

/-! ## Taylor form of `T` -/

theorem hasDerivAt_ccmTimeBandTaylorAux (r w : ℝ) :
    HasDerivAt (fun v => (r - v) * ccmTimeBandTrace' v + ccmTimeBandTrace v)
      ((r - w) * ccmTimeBandTrace'' w) w := by
  have h1 := ((hasDerivAt_const w r).sub (hasDerivAt_id' w)).mul (hasDerivAt_ccmTimeBandTrace' w)
  have h2 := hasDerivAt_ccmTimeBandTrace w
  refine (h1.add h2).congr_deriv ?_
  simp only [Pi.sub_apply]
  ring

/-- `T(r) = T(0) + r + ∫₀^δ (r - w)₊ T''(w) dw` for `0 ≤ r ≤ δ`. -/
theorem ccmTimeBandTrace_taylor {r δ : ℝ} (hr : 0 ≤ r) (hrδ : r ≤ δ) :
    ccmTimeBandTrace r = ccmTimeBandTrace 0 + r +
      ∫ w in Ioc 0 δ, max (r - w) 0 * ccmTimeBandTrace'' w := by
  have hcont : Continuous fun w => max (r - w) 0 * ccmTimeBandTrace'' w :=
    (continuous_const.sub continuous_id).max continuous_const |>.mul continuous_ccmTimeBandTrace''
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun w _ => hasDerivAt_ccmTimeBandTaylorAux r w)
    (Continuous.intervalIntegrable
      (show Continuous fun w => (r - w) * ccmTimeBandTrace'' w from
        (continuous_const.sub continuous_id).mul continuous_ccmTimeBandTrace'') 0 r)
  rw [sub_self, zero_mul, zero_add, sub_zero, ccmTimeBandTrace'_zero, mul_one] at hftc
  have hsplit : ∫ w in (0 : ℝ)..δ, max (r - w) 0 * ccmTimeBandTrace'' w =
      ∫ w in (0 : ℝ)..r, (r - w) * ccmTimeBandTrace'' w := by
    rw [← intervalIntegral.integral_add_adjacent_intervals (b := r) (hcont.intervalIntegrable _ _)
      (hcont.intervalIntegrable _ _)]
    have h1 : ∫ w in (0 : ℝ)..r, max (r - w) 0 * ccmTimeBandTrace'' w =
        ∫ w in (0 : ℝ)..r, (r - w) * ccmTimeBandTrace'' w := by
      refine intervalIntegral.integral_congr fun w hw => ?_
      rw [uIcc_of_le hr] at hw
      simp only [max_eq_left (show 0 ≤ r - w by linarith [hw.2])]
    have h2 : ∫ w in r..δ, max (r - w) 0 * ccmTimeBandTrace'' w = 0 := by
      refine (intervalIntegral.integral_congr fun w hw => ?_).trans intervalIntegral.integral_zero
      rw [uIcc_of_le hrδ] at hw
      simp only [max_eq_right (show r - w ≤ 0 by linarith [hw.1]), zero_mul]
    rw [h1, h2, add_zero]
  rw [← intervalIntegral.integral_of_le (hr.trans hrδ), hsplit, hftc]
  ring

/-! ## The small-support radius -/

/-- `ε₀ = 1 / (2 (B + 1))`, `B` the bound of `|T''|` on `[-1, 1]`. -/
def ccmSoninSmallSupportRadius : ℝ := 1 / (2 * (ccmTimeBandBound₂ 0 + 1))

theorem ccmTimeBandBound₂_nonneg : 0 ≤ ccmTimeBandBound₂ 0 := by
  unfold ccmTimeBandBound₂; positivity

theorem ccmSoninSmallSupportRadius_pos : 0 < ccmSoninSmallSupportRadius := by
  unfold ccmSoninSmallSupportRadius; have := ccmTimeBandBound₂_nonneg; positivity

theorem two_mul_ccmSoninSmallSupportRadius_le_one : 2 * ccmSoninSmallSupportRadius ≤ 1 := by
  have hB := ccmTimeBandBound₂_nonneg
  have h : 2 * ccmSoninSmallSupportRadius = 1 / (ccmTimeBandBound₂ 0 + 1) := by
    unfold ccmSoninSmallSupportRadius; field_simp
  rw [h, div_le_one (by linarith)]
  linarith

theorem two_mul_ccmSoninSmallSupportRadius_mul_le_one :
    2 * ccmSoninSmallSupportRadius * ccmTimeBandBound₂ 0 ≤ 1 := by
  have hB := ccmTimeBandBound₂_nonneg
  have h : 2 * ccmSoninSmallSupportRadius * ccmTimeBandBound₂ 0 =
      ccmTimeBandBound₂ 0 / (ccmTimeBandBound₂ 0 + 1) := by
    unfold ccmSoninSmallSupportRadius; field_simp
  rw [h, div_le_one (by linarith)]
  linarith

/-- `∫₀^δ |T''| ≤ δ B` for `0 ≤ δ ≤ 1`. -/
theorem integral_abs_ccmTimeBandTrace''_le {δ : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    ∫ w in Ioc 0 δ, |ccmTimeBandTrace'' w| ≤ δ * ccmTimeBandBound₂ 0 := by
  calc ∫ w in Ioc 0 δ, |ccmTimeBandTrace'' w| ≤ ∫ _w in Ioc 0 δ, ccmTimeBandBound₂ 0 := by
        refine setIntegral_mono_on continuous_ccmTimeBandTrace''.abs.integrableOn_Ioc
          continuous_const.integrableOn_Ioc measurableSet_Ioc fun w hw => ?_
        refine abs_ccmTimeBandTrace''_le (u := 0) ?_
        rw [abs_zero, zero_add, abs_le]
        constructor <;> linarith [hw.1, hw.2]
    _ = δ * ccmTimeBandBound₂ 0 := by
        rw [setIntegral_const, smul_eq_mul, Measure.real, Real.volume_Ioc, sub_zero,
          ENNReal.toReal_ofReal hδ]

/-! ## Domination for small supports -/

/-- **The time-band Toeplitz form is nonpositive on small-support mean-zero tests.**
`Re ∫∫ conj (g s) g t T(|t - s|) ≤ -2 (1 - 2ε B) ‖Γ‖² ≤ 0`. -/
theorem re_integral_integral_mul_ccmTimeBandTrace_abs_nonpos (g : CCMCompactSchwartzLogTest)
    {ε : ℝ} (hε : 0 < ε) (hε₀ : ε ≤ ccmSoninSmallSupportRadius) (hsupp : ∀ x, ε ≤ |x| → g x = 0)
    (hmean : ∫ x, g x = 0) :
    (∫ s, ∫ t, conj (g s) * g t * ((ccmTimeBandTrace |t - s| : ℝ) : ℂ)).re ≤ 0 := by
  set f : ℝ → ℂ := fun x => g x
  have hf : Continuous f := g.toSchwartzMap.continuous
  set δ := 2 * ε
  have hδ0 : 0 ≤ δ := by positivity
  have hδ1 : δ ≤ 1 := le_trans (by linarith) two_mul_ccmSoninSmallSupportRadius_le_one
  have hδB : δ * ccmTimeBandBound₂ 0 ≤ 1 := le_trans
    (mul_le_mul_of_nonneg_right (by linarith) ccmTimeBandBound₂_nonneg)
    two_mul_ccmSoninSmallSupportRadius_mul_le_one
  have hTcont : Continuous ccmTimeBandTrace :=
    continuous_iff_continuousAt.mpr fun u => (hasDerivAt_ccmTimeBandTrace u).continuousAt
  set ρ : ℝ → ℝ := fun u => ccmTimeBandTrace |u| - ccmTimeBandTrace 0 - |u|
  have hρcont : Continuous ρ :=
    ((hTcont.comp continuous_abs).sub continuous_const).sub continuous_abs
  -- bounds on the support square
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := -(2 * ε)) (b := 2 * ε)).exists_bound_of_continuousOn
    (hTcont.comp continuous_abs).continuousOn
  obtain ⟨Cρ, hCρ⟩ := (isCompact_Icc (a := -(2 * ε)) (b := 2 * ε)).exists_bound_of_continuousOn
    hρcont.continuousOn
  have hdiff : ∀ p : ℝ × ℝ, p ∈ Icc (-ε) ε ×ˢ Icc (-ε) ε → p.2 - p.1 ∈ Icc (-(2 * ε)) (2 * ε) := by
    intro p hp
    obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hp
    constructor <;> linarith
  have hiT := integrable_conj_mul_mul hf hsupp (k := fun p : ℝ × ℝ => ccmTimeBandTrace |p.2 - p.1|)
    (show Continuous fun p : ℝ × ℝ => ccmTimeBandTrace |p.2 - p.1| from
      hTcont.comp (by fun_prop)) (C := C) fun p hp => by
      simpa [Real.norm_eq_abs] using hC _ (hdiff p hp)
  have hiA := integrable_conj_mul_mul hf hsupp (k := fun p : ℝ × ℝ => |p.2 - p.1|)
    (by fun_prop) (C := 2 * ε) fun p hp => by
      have := hdiff p hp
      rw [abs_abs, abs_le]; exact this
  have hiR := integrable_conj_mul_mul hf hsupp (k := fun p : ℝ × ℝ => ρ (p.2 - p.1))
    (show Continuous fun p : ℝ × ℝ => ρ (p.2 - p.1) from hρcont.comp (by fun_prop))
    (C := Cρ) fun p hp => by simpa [Real.norm_eq_abs] using hCρ _ (hdiff p hp)
  have hiC := integrable_conj_mul_mul hf hsupp (continuous_const (y := ccmTimeBandTrace 0))
    (C := |ccmTimeBandTrace 0|) fun p _ => le_refl _
  -- split the kernel `T(|u|) = T(0) + |u| + ρ(u)`
  have hsplit : ∫ s, ∫ t, conj (g s) * g t * ((ccmTimeBandTrace |t - s| : ℝ) : ℂ) =
      (∫ s, ∫ t, conj (f s) * f t * ((ccmTimeBandTrace 0 : ℝ) : ℂ)) +
        (∫ s, ∫ t, conj (f s) * f t * ((|t - s| : ℝ) : ℂ)) +
          ∫ s, ∫ t, conj (f s) * f t * ((ρ (t - s) : ℝ) : ℂ) := by
    rw [← integral_prod _ hiT, ← integral_prod _ hiC, ← integral_prod _ hiA,
      ← integral_prod _ hiR, ← integral_add hiC hiA, ← integral_add (show Integrable
        (fun p : ℝ × ℝ => conj (f p.1) * f p.2 * ((ccmTimeBandTrace 0 : ℝ) : ℂ) +
          conj (f p.1) * f p.2 * ((|p.2 - p.1| : ℝ) : ℂ)) (volume.prod volume) from hiC.add hiA) hiR]
    refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
    simp only [ρ]
    push_cast
    ring
  have hC0 : ∫ s, ∫ t, conj (f s) * f t * ((ccmTimeBandTrace 0 : ℝ) : ℂ) = 0 := by
    refine (integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)).trans (integral_zero _ _)
    change ∫ t, conj (f s) * f t * ((ccmTimeBandTrace 0 : ℝ) : ℂ) = 0
    rw [integral_mul_const, integral_const_mul, hmean, mul_zero, zero_mul]
  have hA := integral_integral_mul_abs_sub hf hsupp hmean
  -- the remainder is a tent mixture with density `T''`
  have hRm : ∫ s, ∫ t, conj (f s) * f t * ((ρ (t - s) : ℝ) : ℂ) =
      ∫ s, ∫ t, conj (f s) * f t *
        ((∫ w in Ioc 0 δ, max (|t - s| - w) 0 * ccmTimeBandTrace'' w : ℝ) : ℂ) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    change conj (f s) * f t * ((ρ (t - s) : ℝ) : ℂ) = conj (f s) * f t *
      ((∫ w in Ioc 0 δ, max (|t - s| - w) 0 * ccmTimeBandTrace'' w : ℝ) : ℂ)
    by_cases hs : ε ≤ |s|
    · simp [f, hsupp s hs]
    by_cases ht : ε ≤ |t|
    · simp [f, hsupp t ht]
    rw [not_le] at hs ht
    have hst : |t - s| ≤ δ := by
      have := abs_sub_le t 0 s
      rw [sub_zero, zero_sub, abs_neg] at this
      linarith
    have hT := ccmTimeBandTrace_taylor (abs_nonneg (t - s)) hst
    simp only [ρ]
    rw [hT]
    congr 2
    ring
  have hmix := norm_integral_integral_mul_tentMixture_le hf hsupp hmean
    continuous_ccmTimeBandTrace'' δ
  have hI := integral_abs_ccmTimeBandTrace''_le hδ0 hδ1
  set Q := ∫ x, ‖tentPrimitive f ε x‖ ^ 2
  have hQ : 0 ≤ Q := integral_nonneg fun x => sq_nonneg _
  rw [hsplit, hC0, zero_add, hA, hRm, Complex.add_re]
  have hre : (∫ s, ∫ t, conj (f s) * f t *
      ((∫ w in Ioc 0 δ, max (|t - s| - w) 0 * ccmTimeBandTrace'' w : ℝ) : ℂ)).re ≤ 2 * Q :=
    (Complex.re_le_norm _).trans (hmix.trans (by nlinarith))
  have hre2 : (-2 * ((Q : ℝ) : ℂ)).re = -2 * Q := by simp
  rw [hre2]
  linarith

/-- **Connes--Consani Sonin-trace domination for small supports.**  For every compact test `g`
vanishing off `(-ε₀, ε₀)` with `∫ g = 0`,
`Re Tr(ϑ(g★ ⋆ g) S) ≤ -Re W(g★ ⋆ g)`.  Only the condition `ĝ(0) = 0` is used. -/
theorem ccmSoninTraceDomination_of_small_support (g : CCMCompactSchwartzLogTest) {ε : ℝ}
    (hε : 0 < ε) (hε₀ : ε ≤ ccmSoninSmallSupportRadius) (hsupp : ∀ x, ε ≤ |x| → g x = 0)
    (hmean : ∫ x, g x = 0) :
    (opTrace (ccmIntegratedScaling (ccmSchwartzLogKernel (ccmSoninGramTest g).toSchwartzMap) *
        evenCentralSoninProjection 1)).re ≤
      (-ccmArchimedeanWeilDistribution (ccmSoninGramTest g)).re := by
  rw [ccmSoninTraceDomination_iff_toeplitz, ← opTrace_ccmSoninGenericPartAt_eq_toeplitz g one_pos]
  refine le_trans ?_ (neg_re_opTrace_conj_ccmSoninTimeBandPart_le _)
  rw [opTrace_conj_ccmIntegratedScaling_eq_toeplitz g memSchattenClass_one_ccmSoninTimeBandPart]
  simp_rw [ccmScalingTrace_ccmSoninTimeBandPart]
  linarith [re_integral_integral_mul_ccmTimeBandTrace_abs_nonpos g hε hε₀ hsupp hmean]

/-! ## Failure for nonnegative tests -/

/-- `T(r) - T(0) ≥ r - r² B` for `0 ≤ r ≤ 1`. -/
theorem ccmTimeBandTrace_sub_zero_ge {r : ℝ} (hr : 0 ≤ r) (hr1 : r ≤ 1) :
    r - r ^ 2 * ccmTimeBandBound₂ 0 ≤ ccmTimeBandTrace r - ccmTimeBandTrace 0 := by
  have hT := ccmTimeBandTrace_taylor hr (le_refl r)
  have hcont : Continuous fun w => max (r - w) 0 * ccmTimeBandTrace'' w :=
    ((continuous_const.sub continuous_id).max continuous_const).mul continuous_ccmTimeBandTrace''
  have hbound : |∫ w in Ioc 0 r, max (r - w) 0 * ccmTimeBandTrace'' w| ≤
      r ^ 2 * ccmTimeBandBound₂ 0 := by
    calc |∫ w in Ioc 0 r, max (r - w) 0 * ccmTimeBandTrace'' w|
        ≤ ∫ w in Ioc 0 r, |max (r - w) 0 * ccmTimeBandTrace'' w| := abs_integral_le_integral_abs
      _ ≤ ∫ _w in Ioc 0 r, r * ccmTimeBandBound₂ 0 := by
          refine setIntegral_mono_on hcont.abs.integrableOn_Ioc continuous_const.integrableOn_Ioc
            measurableSet_Ioc fun w hw => ?_
          rw [abs_mul, abs_of_nonneg (le_max_right _ _)]
          have h1 : max (r - w) 0 ≤ r := max_le (by linarith [hw.1]) hr
          have h2 : |ccmTimeBandTrace'' w| ≤ ccmTimeBandBound₂ 0 := by
            refine abs_ccmTimeBandTrace''_le (u := 0) ?_
            rw [abs_zero, zero_add, abs_le]
            constructor <;> linarith [hw.1, hw.2]
          exact mul_le_mul h1 h2 (abs_nonneg _) hr
      _ = r ^ 2 * ccmTimeBandBound₂ 0 := by
          rw [setIntegral_const, smul_eq_mul, Measure.real, Real.volume_Ioc, sub_zero,
            ENNReal.toReal_ofReal hr]
          ring
  have := neg_abs_le (∫ w in Ioc 0 r, max (r - w) 0 * ccmTimeBandTrace'' w)
  linarith

/-- `Re Tr(G ϑ_u) ≤ -(|u| - |u|² B)` for `|u| ≤ 1`. -/
theorem re_ccmSoninToeplitzKernel_le_neg {u : ℝ} (hu : |u| ≤ 1) :
    (ccmSoninToeplitzKernel 1 u).re ≤ -(|u| - |u| ^ 2 * ccmTimeBandBound₂ 0) := by
  have h := re_ccmSoninToeplitzKernel_le u
  rw [ccmScalingTrace_ccmSoninTimeBandPart, ccmScalingTrace_ccmSoninTimeBandPart, abs_zero,
    Complex.ofReal_re, Complex.ofReal_re] at h
  linarith [ccmTimeBandTrace_sub_zero_ge (abs_nonneg u) hu]

/-- **Sonin-trace domination fails for nonnegative tests of small support.**  If `g` is real,
nonnegative, not identically zero, and vanishes off `(-ε₀, ε₀)`, then
`Re Tr(ϑ(g★ ⋆ g) S) > -Re W(g★ ⋆ g)`: the vanishing condition `ĝ(0) = 0` cannot be dropped. -/
theorem not_ccmSoninTraceDomination_of_nonneg (g : CCMCompactSchwartzLogTest) {ε : ℝ}
    (hε : 0 < ε) (hε₀ : ε ≤ ccmSoninSmallSupportRadius) (hsupp : ∀ x, ε ≤ |x| → g x = 0)
    (hreal : ∀ x, (g x).im = 0) (hnonneg : ∀ x, 0 ≤ (g x).re) {x₀ : ℝ} (hx₀ : g x₀ ≠ 0) :
    (-ccmArchimedeanWeilDistribution (ccmSoninGramTest g)).re <
      (opTrace (ccmIntegratedScaling (ccmSchwartzLogKernel (ccmSoninGramTest g).toSchwartzMap) *
        evenCentralSoninProjection 1)).re := by
  rw [← not_le, ccmSoninTraceDomination_iff_toeplitz, not_le]
  set f : ℝ → ℂ := fun x => g x
  have hf : Continuous f := g.toSchwartzMap.continuous
  set φ : ℝ → ℝ := fun x => (g x).re
  have hφc : Continuous φ := Complex.continuous_re.comp hf
  have hfφ : ∀ x, f x = (φ x : ℂ) := fun x => Complex.ext (by simp [φ, f]) (by simp [f, hreal x])
  set B := ccmTimeBandBound₂ 0
  have hB := ccmTimeBandBound₂_nonneg
  have hδ1 : 2 * ε ≤ 1 := le_trans (by linarith) two_mul_ccmSoninSmallSupportRadius_le_one
  have hδB : 2 * ε * B ≤ 1 := le_trans
    (mul_le_mul_of_nonneg_right (by linarith) hB) two_mul_ccmSoninSmallSupportRadius_mul_le_one
  have hsuppφ : ∀ x, ε ≤ |x| → φ x = 0 := fun x hx => by simp [φ, hsupp x hx]
  -- the kernel is real
  set k : ℝ × ℝ → ℝ := fun p => (ccmSoninToeplitzKernel 1 (p.2 - p.1)).re
  have hkc : Continuous k := Complex.continuous_re.comp
    ((continuous_ccmSoninToeplitzKernel one_pos).comp (continuous_snd.sub continuous_fst))
  have hτ : ∀ u, ccmSoninToeplitzKernel 1 u = ((ccmSoninToeplitzKernel 1 u).re : ℂ) := fun u =>
    Complex.ext rfl (by simp [im_ccmSoninToeplitzKernel one_pos u])
  have hF := integrable_conj_mul_mul hf hsupp hkc
    (C := traceNorm evenSubspace (ccmSoninGenericPartAt 1)) fun p _ =>
      (Complex.abs_re_le_norm _).trans (norm_ccmSoninToeplitzKernel_le one_pos _)
  have hplane : ∫ s, ∫ t, conj (g s) * g t * ccmSoninToeplitzKernel 1 (t - s) =
      ∫ p : ℝ × ℝ, conj (f p.1) * f p.2 * ((k p : ℝ) : ℂ) ∂(volume.prod volume) := by
    rw [integral_prod _ hF]
    refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    change conj (f s) * f t * ccmSoninToeplitzKernel 1 (t - s) = _
    rw [hτ]
  rw [hplane]
  change RCLike.re (∫ p : ℝ × ℝ, conj (f p.1) * f p.2 * ((k p : ℝ) : ℂ) ∂(volume.prod volume)) < 0
  rw [← integral_re hF]
  have hre : ∀ p : ℝ × ℝ, RCLike.re (conj (f p.1) * f p.2 * ((k p : ℝ) : ℂ)) =
      φ p.1 * φ p.2 * k p := by
    intro p
    rw [hfφ, hfφ, Complex.conj_ofReal]
    change (((φ p.1 : ℂ) * (φ p.2 : ℂ) * (k p : ℂ))).re = _
    norm_cast
  simp_rw [hre]
  -- comparison with `-φ(s) φ(t) |t - s| (1 - |t - s| B)`
  set h : ℝ × ℝ → ℝ := fun p => φ p.1 * φ p.2 * (|p.2 - p.1| - |p.2 - p.1| ^ 2 * B)
  have hhc : Continuous h := by
    refine ((hφc.comp continuous_fst).mul (hφc.comp continuous_snd)).mul ?_
    fun_prop
  have hin : ∀ p : ℝ × ℝ, φ p.1 ≠ 0 → φ p.2 ≠ 0 → |p.2 - p.1| < 2 * ε := by
    intro p h1 h2
    have a1 : |p.1| < ε := lt_of_not_ge fun h => h1 (hsuppφ _ h)
    have a2 : |p.2| < ε := lt_of_not_ge fun h => h2 (hsuppφ _ h)
    calc |p.2 - p.1| ≤ |p.2| + |p.1| := abs_sub _ _
      _ < 2 * ε := by linarith
  have hfactor : ∀ p : ℝ × ℝ, φ p.1 ≠ 0 → φ p.2 ≠ 0 → 0 ≤ |p.2 - p.1| - |p.2 - p.1| ^ 2 * B := by
    intro p h1 h2
    have hd := hin p h1 h2
    have : |p.2 - p.1| * B ≤ 1 := by nlinarith [abs_nonneg (p.2 - p.1)]
    nlinarith [abs_nonneg (p.2 - p.1)]
  have hh0 : 0 ≤ h := fun p => by
    by_cases h1 : φ p.1 = 0
    · simp [h, h1]
    by_cases h2 : φ p.2 = 0
    · simp [h, h2]
    exact mul_nonneg (mul_nonneg (hnonneg _) (hnonneg _)) (hfactor p h1 h2)
  have hhsupp : HasCompactSupport h := by
    refine HasCompactSupport.intro (K := Icc (-ε) ε ×ˢ Icc (-ε) ε)
      ((isCompact_Icc (a := -ε) (b := ε)).prod (isCompact_Icc (a := -ε) (b := ε))) fun p hp => ?_
    rw [mem_prod, not_and_or] at hp
    rcases hp with hp | hp
    · simp [h, hsuppφ p.1 (by
        rw [mem_Icc, not_and_or, not_le, not_le] at hp
        rcases hp with hp | hp
        · exact (by linarith : ε ≤ -p.1).trans (neg_le_abs _)
        · exact hp.le.trans (le_abs_self _))]
    · simp [h, hsuppφ p.2 (by
        rw [mem_Icc, not_and_or, not_le, not_le] at hp
        rcases hp with hp | hp
        · exact (by linarith : ε ≤ -p.2).trans (neg_le_abs _)
        · exact hp.le.trans (le_abs_self _))]
  -- a point where `h > 0`
  have hφ₀ : 0 < φ x₀ := by
    refine lt_of_le_of_ne (hnonneg x₀) (Ne.symm fun h0 => hx₀ ?_)
    change f x₀ = 0
    rw [hfφ, h0, Complex.ofReal_zero]
  obtain ⟨ε', hε', hball⟩ := Metric.eventually_nhds_iff.mp
    (hφc.continuousAt.eventually (lt_mem_nhds hφ₀))
  set η := min (ε' / 2) ε
  have hη : 0 < η := lt_min (by linarith) hε
  have hφ₁ : 0 < φ (x₀ + η) := hball (by
    rw [Real.dist_eq, add_sub_cancel_left, abs_of_pos hη]
    exact lt_of_le_of_lt (min_le_left _ _) (by linarith))
  have hpos : h (x₀, x₀ + η) ≠ 0 := by
    have hd : |(x₀ + η) - x₀| = η := by rw [add_sub_cancel_left, abs_of_pos hη]
    have hηB : η * B < 1 := by
      have : η ≤ ε := min_le_right _ _
      rcases hB.lt_or_eq with hB' | hB'
      · nlinarith
      · have hB0 : B = 0 := hB'.symm
        rw [hB0, mul_zero]; norm_num
    simp only [h, hd]
    have : 0 < η - η ^ 2 * B := by nlinarith
    positivity
  have hint := Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero
    (μ := volume.prod volume) hhc hhsupp hh0 hpos
  have hle : ∫ p : ℝ × ℝ, φ p.1 * φ p.2 * k p ∂(volume.prod volume) ≤
      ∫ p : ℝ × ℝ, -h p ∂(volume.prod volume) := by
    refine integral_mono ?_ (hhc.integrable_of_hasCompactSupport hhsupp).neg fun p => ?_
    · exact hF.re.congr (Filter.Eventually.of_forall hre)
    · by_cases h1 : φ p.1 = 0
      · simp [h, h1]
      by_cases h2 : φ p.2 = 0
      · simp [h, h2]
      have hd := hin p h1 h2
      have hk := re_ccmSoninToeplitzKernel_le_neg (u := p.2 - p.1) (by linarith)
      have hφφ : 0 ≤ φ p.1 * φ p.2 := mul_nonneg (hnonneg _) (hnonneg _)
      simp only [h, k]
      nlinarith
  rw [integral_neg] at hle
  linarith

end RHTower
