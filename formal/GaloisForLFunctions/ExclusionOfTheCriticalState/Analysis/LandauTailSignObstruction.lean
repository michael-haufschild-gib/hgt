import GaloisForLFunctions.ExclusionOfTheCriticalState.TheStateChangesSignOnEveryRay
import GaloisForLFunctions.RHTower.MobiusDivisorCompactClockTailSeparation

/-!
# Landau's obstruction for measurable one-signed tails

A measurable integrable profile on the negative half-line has a positive tail
measure whenever its tail has one sign almost everywhere. Its compact head has
an entire transform. If a continuation is analytic along a real interval,
real-analytic uniqueness and Landau's theorem force every absolute exponential
moment in that interval to converge. Continuity of the profile is unnecessary.
-/

noncomputable section
open MeasureTheory Set Filter Topology Zeta23
namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open ArithmeticHodgeTheoryOfDegenerations ArithmeticCastelnuovoSeveri
  CriticalArithmeticCorrelationTheory HTGeometry _root_.RHTower
open GaloisForLFunctions.RHTower (laplaceMass laplaceReal IsAbscissa complexLaplace
  hasDerivAt_complexLaplace complexLaplace_ofReal false_of_analyticAt_abscissa)

private theorem integrable_abs_exp_nonneg {f : ℝ → ℝ} (hf : Integrable f)
    (hs : ∀ u, 0 ≤ u → f u = 0) {c : ℝ} (hc : 0 ≤ c) :
    Integrable fun u => |f u| * Real.exp (c*u) := by
  refine hf.norm.mono' (hf.aestronglyMeasurable.norm.mul (by fun_prop)) ?_
  exact Eventually.of_forall fun u => by
    rw [Real.norm_of_nonneg (by positivity),Real.norm_eq_abs]
    rcases le_or_gt 0 u with hu | hu
    · simp only [hs u hu,abs_zero,zero_mul,le_refl]
    · exact mul_le_of_le_one_right (abs_nonneg _)
        (Real.exp_le_one_iff.mpr (mul_nonpos_of_nonneg_of_nonpos hc hu.le))

private theorem integrable_abs_exp_of_tail {f : ℝ → ℝ} (hm : Measurable f)
    (hf : Integrable f) (hs : ∀ u, 0 ≤ u → f u = 0) {T c : ℝ}
    (ht : IntegrableOn (fun u => |f u| *Real.exp (c*u)) (Iio (-T))) :
    Integrable fun u => |f u| *Real.exp (c*u) := by
  have hh : IntegrableOn (fun u => |f u| *Real.exp (c*u)) (Ici (-T)) := by
    refine (hf.abs.mul_const (Real.exp (|c| *|T|))).integrableOn.mono'
      ((hm.abs.mul (by fun_prop)).aestronglyMeasurable)
      ((ae_restrict_iff' measurableSet_Ici).mpr (Eventually.of_forall fun u hu => ?_))
    rw [Real.norm_of_nonneg (by positivity)]
    rcases lt_or_ge u 0 with hneg | hnon
    · apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      apply Real.exp_le_exp.mpr
      have hub : |u| ≤ |T| := by
        rw [abs_of_neg hneg]
        exact (neg_le.mpr hu).trans (le_abs_self T)
      exact (le_abs_self (c*u)).trans (by
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left hub (abs_nonneg c))
    · simp only [hs u hnon,abs_zero,zero_mul,le_refl]
  have hi := ht.union hh
  rwa [Iio_union_Ici,integrableOn_univ] at hi

/-- A nonnegative tail cannot have a finite abscissa inside a regular real continuation. -/
theorem integrable_exp_of_nonnegative_tail_of_real_continuation
    {f : ℝ → ℝ} (hm : Measurable f) (hf : Integrable f)
    (hs : ∀ u, 0 ≤ u → f u = 0) {G : ℂ → ℂ} {κ : ℝ}
    (hG : ∀ x : ℝ, κ < x → AnalyticAt ℂ G (x : ℂ))
    (heq : ∀ x : ℝ, 0 < x → negativeHalfLineLaplace (cx f) (x : ℂ) = G x)
    {T : ℝ} (hT : 0 ≤ T) (hpos : ∀ᵐ u ∂volume.restrict (Iio (-T)), 0 ≤ f u)
    {σ : ℝ} (hσ : κ < σ) : Integrable fun u => |f u| *Real.exp (σ*u) := by
  by_contra hnot
  let ν := tailMeasure f T
  have hmass := laplaceMass_tailMeasure_ne_top_iff hm hT hpos
  have hto (x : ℝ) (hx : Integrable fun u => |f u| *Real.exp (x*u)) :
      IntegrableOn (fun u => f u*Real.exp (x*u)) (Iio (-T)) := by
    refine hx.integrableOn.mono' ((hm.mul (by fun_prop)).aestronglyMeasurable) ?_
    exact Eventually.of_forall fun u => by
      rw [Real.norm_eq_abs,abs_mul,abs_of_pos (Real.exp_pos _)]
  have hfrom (x : ℝ) (hx : IntegrableOn (fun u => f u*Real.exp (x*u)) (Iio (-T))) :
      Integrable fun u => |f u| *Real.exp (x*u) := by
    apply integrable_abs_exp_of_tail hm hf hs (T := T)
    exact hx.norm.congr (Eventually.of_forall fun u => by
      rw [Real.norm_eq_abs,abs_mul,abs_of_pos (Real.exp_pos _)])
  have h0 : laplaceMass ν σ = ⊤ := by
    by_contra h
    exact hnot (hfrom σ ((hmass σ).mp h))
  have h1 : laplaceMass ν 1 ≠ ⊤ :=
    (hmass 1).mpr (hto 1 (integrable_abs_exp_nonneg hf hs zero_le_one))
  obtain ⟨hc,hσc⟩ := isAbscissa_sInf h0 h1
  let c := sInf {x | laplaceMass ν x ≠ ⊤}
  have hκc : κ < c := hσ.trans_le hσc
  have hc0 : c ≤ 0 := by
    by_contra hh
    have hcpos : 0 < c := lt_of_not_ge hh
    have hfin : laplaceMass ν (c/2) ≠ ⊤ :=
      (hmass _).mpr (hto _ (integrable_abs_exp_nonneg hf hs (half_pos hcpos).le))
    exact hfin (hc.2 _ (by linarith only [hcpos]))
  let head : ℝ → ℝ := (Ici (-T)).indicator f
  have hhead := differentiable_laplace_of_head (hm.indicator measurableSet_Ici)
    (hf.indicator measurableSet_Ici)
    (fun u hu => by simp only [Set.indicator]; split_ifs <;> simp [hs u hu])
    (fun u hu => by exact indicator_of_notMem (not_le.mpr hu) f)
  let Φ : ℂ → ℂ := fun w => G w-negativeHalfLineLaplace (cx head) w
  have hΦ (x : ℝ) (hx : κ < x) : AnalyticAt ℂ Φ (x : ℂ) :=
    (hG x hx).sub (hhead.analyticAt _)
  have hCL (z : ℂ) (hz : c < z.re) : AnalyticAt ℂ (complexLaplace ν) z := by
    have hopen : IsOpen {w : ℂ | c < w.re} := isOpen_lt continuous_const Complex.continuous_re
    have hd : DifferentiableOn ℂ (complexLaplace ν) {w : ℂ | c < w.re} :=
      fun w hw => ((hasDerivAt_complexLaplace hc hw).differentiableAt).differentiableWithinAt
    exact hd.analyticAt (hopen.mem_nhds hz)
  have hinit (x : ℝ) (hx : 0 < x) : Φ (x : ℂ) = complexLaplace ν (x : ℂ) := by
    have hi : Integrable fun u => f u*Real.exp (x*u) := by
      refine (integrable_abs_exp_nonneg hf hs hx.le).mono'
        ((hm.mul (by fun_prop)).aestronglyMeasurable) ?_
      exact Eventually.of_forall fun u => by
        rw [Real.norm_eq_abs,abs_mul,abs_of_pos (Real.exp_pos _)]
    have hsplit : (∫ u,f u*Real.exp (x*u)) =
        (∫ u in Iio (-T),f u*Real.exp (x*u)) + ∫ u,head u*Real.exp (x*u) := by
      rw [← integral_add_compl measurableSet_Iio hi,compl_Iio,
        ← integral_indicator measurableSet_Ici]
      congr 1
      apply integral_congr_ae
      exact Eventually.of_forall fun u => by
        simp only [head,Set.indicator]; split_ifs <;> simp
    dsimp only [Φ]
    rw [← heq x hx,negativeHalfLineLaplace_ofReal,negativeHalfLineLaplace_ofReal,
      complexLaplace_ofReal,laplaceReal_tailMeasure hm hT hpos,← Complex.ofReal_sub]
    congr 1
    linarith only [hsplit]
  have hray (x : ℝ) (hx : c < x) : Φ (x : ℂ) = complexLaplace ν (x : ℂ) := by
    have hA : AnalyticOnNhd ℝ (fun t : ℝ => Φ (t : ℂ)) (Ioi c) :=
      fun t ht => analyticAt_ofReal_comp (hΦ t (hκc.trans ht))
    have hB : AnalyticOnNhd ℝ (fun t : ℝ => complexLaplace ν (t : ℂ)) (Ioi c) :=
      fun t ht => analyticAt_ofReal_comp (hCL _ (by simpa using ht))
    have he : (fun t : ℝ => Φ (t : ℂ)) =ᶠ[𝓝 (1 : ℝ)]
        fun t : ℝ => complexLaplace ν (t : ℂ) := by
      filter_upwards [isOpen_Ioi.mem_nhds (show (0:ℝ)<1 by norm_num)] with t ht
      exact hinit t ht
    exact hA.eqOn_of_preconnected_of_eventuallyEq hB isPreconnected_Ioi
      (by linarith only [hc0]) he hx
  obtain ⟨δ,hδ,hball⟩ := (hΦ c hκc).exists_ball_analyticOnNhd
  exact false_of_analyticAt_abscissa hc hδ hball
    (fun x hx _ => by rw [hray x hx,complexLaplace_ofReal])


/-- The Landau obstruction depends only on an almost-everywhere tail sign. -/
theorem integrable_exp_of_signed_tail_of_real_continuation
    {f : ℝ → ℝ} (hm : Measurable f) (hf : Integrable f)
    (hs : ∀ u, 0 ≤ u → f u = 0) {G : ℂ → ℂ} {κ : ℝ}
    (hG : ∀ x : ℝ, κ < x → AnalyticAt ℂ G (x : ℂ))
    (heq : ∀ x : ℝ, 0 < x → negativeHalfLineLaplace (cx f) (x : ℂ) = G x)
    {s T : ℝ} (hsign : s = 1 ∨ s = -1) (hT : 0 ≤ T)
    (hpos : ∀ᵐ u ∂volume.restrict (Iio (-T)), 0 ≤ s*f u)
    {σ : ℝ} (hσ : κ < σ) : Integrable fun u => |f u| * Real.exp (σ*u) := by
  have habs : |s| = 1 := by rcases hsign with rfl | rfl <;> norm_num
  have heq' (x : ℝ) (hx : 0 < x) :
      negativeHalfLineLaplace (cx (fun u => s*f u)) (x : ℂ) = (s:ℂ)*G x := by
    calc
      _ = ((s*(∫ u,f u*Real.exp (x*u)) : ℝ) : ℂ) := by
        rw [negativeHalfLineLaplace_ofReal,← integral_const_mul]
        congr 1
        exact integral_congr_ae (Eventually.of_forall fun u => by ring)
      _ = _ := by
        rw [← heq x hx,negativeHalfLineLaplace_ofReal,Complex.ofReal_mul]
  have hh := integrable_exp_of_nonnegative_tail_of_real_continuation
    (measurable_const.mul hm) (hf.const_mul s)
    (fun u hu => by change s*f u = 0; rw [hs u hu,mul_zero])
    (fun x hx => analyticAt_const.mul (hG x hx)) heq' hT hpos hσ
  simpa only [Pi.mul_apply,abs_mul,habs,one_mul] using hh

end GaloisForLFunctions.ExclusionOfTheCriticalState
