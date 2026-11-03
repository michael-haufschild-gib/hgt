import GaloisForLFunctions.SelbergClass.CompletedEulerQuotient
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.Meromorphic.Order

/-!
# Continuation at the critical Euler abscissa

Absolute convergence on the critical line gives a continuous nonvanishing
boundary value for the completed Euler quotient. Its meromorphic germ can
therefore have neither a zero nor a pole. The functional equations identify
this germ with the reflected quotient on the left.
-/

noncomputable section
open Complex Filter Set Topology

namespace GaloisForLFunctions.SelbergClass

private theorem continuousOn_LSeries_closed {b : ℕ → ℂ} {σ : ℝ}
    (hb : LSeriesSummable b σ) :
    ContinuousOn (LSeries b) {s : ℂ | σ ≤ s.re} := by
  apply continuousOn_tsum _ hb.norm
    (fun n s hs => LSeries.norm_term_le_of_re_le_re b hs n)
  intro n
  by_cases hn : n = 0
  · subst n
    simpa only [LSeries.term_zero] using continuousOn_const (c := (0 : ℂ))
  · simp only [LSeries.term_of_ne_zero hn]
    have hpow : Differentiable ℂ (fun s : ℂ => (n : ℂ) ^ s) :=
      differentiable_id.const_cpow (.inl (Nat.cast_ne_zero.mpr hn))
    exact continuousOn_const.div hpow.continuous.continuousOn
      (fun s _ => Complex.cpow_ne_zero_iff.mpr (.inl (Nat.cast_ne_zero.mpr hn)))

private theorem tendsto_rightRay (s : ℂ) :
    Tendsto (fun t : ℝ => s + (t : ℂ)) (𝓝[>] 0) (𝓝[≠] s) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · simpa using (show ContinuousAt (fun t : ℝ => s + (t : ℂ)) 0 by fun_prop).tendsto.mono_left
      nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with t ht
    change s + (t : ℂ) ≠ s
    simpa using (Complex.ofReal_ne_zero.mpr (ne_of_gt ht))

private theorem tendsto_rightRay_closed {σ : ℝ} {s : ℂ} (hs : σ ≤ s.re) :
    Tendsto (fun t : ℝ => s + (t : ℂ)) (𝓝[>] 0) (𝓝[{z : ℂ | σ ≤ z.re}] s) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · exact (tendsto_rightRay s).mono_right nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with t ht
    change 0 < t at ht
    simp only [add_re, ofReal_re]
    linarith

private theorem eulerQuotient_continuousWithinAt (F G : RHTower.SelbergClass) {σ : ℝ}
    (hb : LSeriesSummable (fun n => F.eulerLogCoeff n - G.eulerLogCoeff n) σ)
    {s : ℂ} (hs : σ ≤ s.re) :
    ContinuousWithinAt (eulerQuotient F G) {z : ℂ | σ ≤ z.re} s :=
  (continuousOn_LSeries_closed hb s hs).cexp

/-- The quotient identity holds also on the line of absolute convergence. -/
theorem eulerQuotient_mul_value_of_summable_closed (F G : RHTower.SelbergClass) {σ : ℝ}
    (hσ : σ < 1)
    (hb : LSeriesSummable (fun n => F.eulerLogCoeff n - G.eulerLogCoeff n) σ)
    {s : ℂ} (hs : σ ≤ s.re) (hs1 : s ≠ 1) :
    eulerQuotient F G s * G s = F s := by
  have ht := (tendsto_rightRay s).mono_right nhdsWithin_le_nhds
  have hR := (eulerQuotient_continuousWithinAt F G hb hs).tendsto.comp
    (tendsto_rightRay_closed hs)
  have hG := (G.continuation.analyticAt_value_of_ne_one hs1).continuousAt.tendsto.comp ht
  have hF := (F.continuation.analyticAt_value_of_ne_one hs1).continuousAt.tendsto.comp ht
  apply tendsto_nhds_unique (hR.mul hG)
  apply hF.congr'
  have hone : ∀ᶠ t : ℝ in 𝓝[>] 0, s + (t : ℂ) ≠ 1 :=
    ht.eventually ((isOpen_ne_fun continuous_id continuous_const).mem_nhds hs1)
  filter_upwards [self_mem_nhdsWithin, hone] with t ht ht1
  change 0 < t at ht
  exact (eulerQuotient_mul_value_of_summable F G hσ hb
    (by simp only [add_re, ofReal_re]; linarith) ht1).symm

private theorem rightCompletedEulerQuotient_continuousWithinAt
    (F G : RHTower.SelbergClass)
    (hb : LSeriesSummable (fun n => F.eulerLogCoeff n - G.eulerLogCoeff n) (1 / 2 : ℝ))
    {s : ℂ} (hs : 1 / 2 ≤ s.re) :
    ContinuousWithinAt (rightCompletedEulerQuotient F G) {z : ℂ | 1 / 2 ≤ z.re} s := by
  have hs0 : 0 < s.re := by linarith
  exact (((gammaFactor_analytic_ne_zero F.gammaData hs0).1.div
    (gammaFactor_analytic_ne_zero G.gammaData hs0).1
    (gammaFactor_analytic_ne_zero G.gammaData hs0).2).continuousAt.continuousWithinAt).mul
      (eulerQuotient_continuousWithinAt F G hb hs)

/-- A nonzero limit along any punctured approach rules out both signs of the
meromorphic order, and thus determines a nonvanishing analytic germ. -/
private theorem analytic_germ_of_nonzero_limit {α : Type*} {l : Filter α} [NeBot l]
    {f : ℂ → ℂ} {p c : ℂ} {r : α → ℂ}
    (hf : MeromorphicAt f p) (hr : Tendsto r l (𝓝[≠] p))
    (hc : c ≠ 0) (hlim : Tendsto (fun t => f (r t)) l (𝓝 c)) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g p ∧ g p = c ∧ f =ᶠ[𝓝[≠] p] g := by
  have ho : meromorphicOrderAt f p = 0 := by
    rcases lt_trichotomy (meromorphicOrderAt f p) 0 with hneg | hzero | hpos
    · exfalso
      exact not_tendsto_atTop_of_tendsto_nhds hlim.norm
        ((tendsto_norm_atTop_iff_cobounded.mpr
          (tendsto_cobounded_of_meromorphicOrderAt_neg hneg)).comp hr)
    · exact hzero
    · exact (hc (tendsto_nhds_unique hlim
        ((tendsto_zero_of_meromorphicOrderAt_pos hpos).comp hr))).elim
  obtain ⟨g, hg, _, heq⟩ := (meromorphicOrderAt_eq_int_iff hf).mp ho
  have heq' : f =ᶠ[𝓝[≠] p] g := by
    filter_upwards [heq] with z hz
    simpa only [zpow_zero, one_smul] using hz
  refine ⟨g, hg, ?_, heq'⟩
  exact tendsto_nhds_unique
    (hg.continuousAt.tendsto.comp (hr.mono_right nhdsWithin_le_nhds))
    (hlim.congr' (hr.eventually heq'))

private theorem rightCompletedEulerQuotient_mul_completed
    (F G : RHTower.SelbergClass)
    (hb : LSeriesSummable (fun n => F.eulerLogCoeff n - G.eulerLogCoeff n) (1 / 2 : ℝ))
    {s : ℂ} (hs : 1 / 2 ≤ s.re) (hs1 : s ≠ 1) :
    rightCompletedEulerQuotient F G s * (G.gammaData.gammaFactor s * G s) =
      F.gammaData.gammaFactor s * F s := by
  have hG := (gammaFactor_analytic_ne_zero G.gammaData (by linarith : 0 < s.re)).2
  have hv := eulerQuotient_mul_value_of_summable_closed F G (by norm_num) hb hs hs1
  dsimp only [rightCompletedEulerQuotient]
  rw [← hv]
  field_simp

/-- The reflected quotient has the actual completed product throughout the strip. -/
private theorem completedEulerQuotient_mul_completed_strip
    (F G : RHTower.SelbergClass)
    (hb : LSeriesSummable (fun n => F.eulerLogCoeff n - G.eulerLogCoeff n) (1 / 2 : ℝ))
    {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    completedEulerQuotient F G s * (G.gammaData.gammaFactor s * G s) =
      F.gammaData.gammaFactor s * F s := by
  have hne : s ≠ 1 := by intro h; simp [h] at hs1
  by_cases hs : 1 / 2 ≤ s.re
  · rw [completedEulerQuotient_eq_right F G hs]
    exact rightCompletedEulerQuotient_mul_completed F G hb hs hne
  have hr0 : 0 < (1 - star s).re := by simpa using (by linarith : 0 < 1 - s.re)
  have hr1 : 1 - star s ≠ 1 := by
    intro h
    have := congrArg Complex.re h
    simp only [sub_re, one_re, RCLike.star_def, conj_re] at this
    linarith
  have hcomp (A : RHTower.SelbergClass) (z : ℂ) (hz : 0 < z.re) (hz1 : z ≠ 1) :
      AnalyticAt ℂ (RHTower.selbergCompletedValue A.gammaData A.continuation) z :=
    (gammaFactor_analytic_ne_zero A.gammaData hz).1.mul
      (A.continuation.analyticAt_value_of_ne_one hz1)
  have eF := F.toExtendedSelbergClass.completedFE_eq_of_analytic_pair
    (hcomp F s hs0 hne) (hcomp F (1 - star s) hr0 hr1)
  have eG := G.toExtendedSelbergClass.completedFE_eq_of_analytic_pair
    (hcomp G s hs0 hne) (hcomp G (1 - star s) hr0 hr1)
  change F.gammaData.gammaFactor s * F s = F.gammaData.rootNumber *
    star (F.gammaData.gammaFactor (1 - star s) * F (1 - star s)) at eF
  change G.gammaData.gammaFactor s * G s = G.gammaData.rootNumber *
    star (G.gammaData.gammaFactor (1 - star s) * G (1 - star s)) at eG
  have hr : 1 / 2 ≤ (1 - star s).re := by simpa using (by linarith : 1 / 2 ≤ 1 - s.re)
  have hprod := rightCompletedEulerQuotient_mul_completed F G hb hr hr1
  have hroot : G.gammaData.rootNumber ≠ 0 := by
    intro h
    have := G.gammaData.rootNumber_norm
    simp [h] at this
  rw [completedEulerQuotient, if_neg hs, eF, eG, ← hprod, star_mul]
  field_simp
  simp only [star_mul]
  ring

/-- At a critical-line point, the nonzero boundary limit removes the meromorphic
singularity, even when both completed functions vanish there. -/
private theorem completedEulerQuotient_analyticAt_critical
    (F G : RHTower.SelbergClass)
    (hb : LSeriesSummable (fun n => F.eulerLogCoeff n - G.eulerLogCoeff n) (1 / 2 : ℝ))
    {s : ℂ} (hs : s.re = 1 / 2) : AnalyticAt ℂ (completedEulerQuotient F G) s := by
  let f (z : ℂ) := F.gammaData.gammaFactor z * F z
  let g (z : ℂ) := G.gammaData.gammaFactor z * G z
  let q (z : ℂ) := f z / g z
  have hs0 : 0 < s.re := by rw [hs]; norm_num
  have hs1 : s ≠ 1 := by
    intro h
    have he := congrArg Complex.re h
    rw [hs] at he
    norm_num at he
  have hf : AnalyticAt ℂ f s := (gammaFactor_analytic_ne_zero F.gammaData hs0).1.mul
    (F.continuation.analyticAt_value_of_ne_one hs1)
  have hg : AnalyticAt ℂ g s := (gammaFactor_analytic_ne_zero G.gammaData hs0).1.mul
    (G.continuation.analyticAt_value_of_ne_one hs1)
  have hstrip : ∀ᶠ z in 𝓝 s, 0 < z.re ∧ z.re < 1 :=
    ((isOpen_lt continuous_const continuous_re).inter
      (isOpen_lt continuous_re continuous_const)).mem_nhds (by simp only [hs]; norm_num)
  have hgn : ∀ᶠ z in 𝓝[≠] s, g z ≠ 0 := by
    filter_upwards [hstrip.filter_mono nhdsWithin_le_nhds,
      value_eventually_ne_zero G s hs1] with z hz hn
    exact mul_ne_zero (gammaFactor_analytic_ne_zero G.gammaData hz.1).2 hn
  have hqT : q =ᶠ[𝓝[≠] s] completedEulerQuotient F G := by
    filter_upwards [hstrip.filter_mono nhdsWithin_le_nhds, hgn] with z hz hn
    exact ((eq_div_iff hn).mpr
      (completedEulerQuotient_mul_completed_strip F G hb hz.1 hz.2)).symm
  have hright := (rightCompletedEulerQuotient_continuousWithinAt F G hb hs.ge).tendsto.comp
    (tendsto_rightRay_closed hs.ge)
  have hqright : (fun t : ℝ => rightCompletedEulerQuotient F G (s + (t : ℂ)))
      =ᶠ[𝓝[>] 0] (fun t => q (s + (t : ℂ))) := by
    filter_upwards [self_mem_nhdsWithin, (tendsto_rightRay s).eventually hqT] with t ht heq
    change 0 < t at ht
    rw [heq, completedEulerQuotient_eq_right F G]
    simp only [add_re, ofReal_re, hs]
    linarith
  obtain ⟨u, hu, hus, hqu⟩ := analytic_germ_of_nonzero_limit
    (hf.meromorphicAt.div hg.meromorphicAt) (tendsto_rightRay s)
    (rightCompletedEulerQuotient_ne_zero F G hs0) (hright.congr' hqright)
  have heq : completedEulerQuotient F G =ᶠ[𝓝[≠] s] u := hqT.symm.trans hqu
  apply hu.congr
  filter_upwards [eventually_nhdsWithin_iff.mp heq] with z hz
  by_cases hzs : z = s
  · subst z
    rw [hus, completedEulerQuotient_eq_right F G hs.ge]
  · exact (hz hzs).symm

/-- Absolute convergence on the critical line suffices for an entire completed
quotient; no equality of Gamma factors is required. -/
theorem completedEulerQuotient_analyticOnNhd_of_critical_discrepancy
    (F G : RHTower.SelbergClass)
    (hb : LSeriesSummable (fun n => F.eulerLogCoeff n - G.eulerLogCoeff n) (1 / 2 : ℝ)) :
    AnalyticOnNhd ℂ (completedEulerQuotient F G) univ := by
  have hR := rightCompletedEulerQuotient_analyticOnNhd F G (by norm_num : (0 : ℝ) ≤ 1 / 2) hb
  intro s _
  rcases lt_trichotomy s.re (1 / 2) with hs | hs | hs
  · have hr : 1 / 2 < (1 - star s).re := by simpa using (by linarith : 1 / 2 < 1 - s.re)
    have ha : AnalyticAt ℂ (fun z => F.gammaData.rootNumber / G.gammaData.rootNumber *
        star (rightCompletedEulerQuotient F G (1 - star z))) s :=
      analyticAt_const.mul (RHTower.analyticAt_selbergConjugateReflection (hR _ hr))
    apply ha.congr
    filter_upwards [(isOpen_lt continuous_re continuous_const).mem_nhds hs] with z hz
    exact (if_neg (not_le.mpr hz)).symm
  · exact completedEulerQuotient_analyticAt_critical F G hb hs
  · apply (hR s hs).congr
    filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds hs] with z hz
    exact (completedEulerQuotient_eq_right F G hz.le).symm

end GaloisForLFunctions.SelbergClass
