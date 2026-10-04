import GaloisForLFunctions.RHTower.RoutePNativeMixedWeightedFTC
import GaloisForLFunctions.RHTower.SPEQuantileRieszRoutePSourceNoAnalyticExtension
import GaloisForLFunctions.HTGeometry.ClockParametricIntegralHolomorphy

/-!
# Signed native mixed-primitive growth

A subcritical exponential envelope would analytically continue the
literal source through its Hardy-zero barrier. All removal jumps, the
finite initial source head, and the actual decaying correction remain.
-/

noncomputable section
open MeasureTheory Set Filter Topology
open GaloisForLFunctions.HTGeometry

namespace RHTower.NativeMixedLaplace

private def head (f : ℝ → ℝ) (a : ℝ) (z : ℂ) : ℂ :=
  ∫ t in (0 : ℝ)..a, expRay z t * (f t : ℂ)

private theorem head_differentiable {f : ℝ → ℝ} (hf : Continuous f) (a : ℝ) :
    Differentiable ℂ (head f a) := by
  intro z
  have hcont : Continuous (fun q : ℝ × ℂ => expRay q.2 q.1 * (f q.1 : ℂ)) := by
    have he : Continuous (fun q : ℝ × ℂ => expRay q.2 q.1) := by
      unfold expRay
      fun_prop
    exact he.mul (Complex.continuous_ofReal.comp (hf.comp continuous_fst))
  have hd : ∀ t : ℝ, DifferentiableOn ℂ (fun w => expRay w t * (f t : ℂ))
      (imStrip (|z.im| + 2)) := by
    intro t w _
    exact (by unfold expRay; fun_prop : DifferentiableAt ℂ
      (fun w => expRay w t * (f t : ℂ)) w).differentiableWithinAt
  change DifferentiableAt ℂ (fun w => ∫ t in (0 : ℝ)..a, expRay w t * (f t : ℂ)) z
  exact differentiableAt_intervalIntegral_of_holomorphic
    (by linarith : |z.im| + 1 < |z.im| + 2) hcont hd
    (mem_imStrip.mpr (by linarith : |z.im| < |z.im| + 1))

private def correction (t : ℝ) : ℝ :=
  2 * routePNativeCriticalProfile t - routePSourceRay t

private theorem source_continuous : Continuous routePSourceRay :=
  GaloisForLFunctions.RHTower.continuous_criticalMellinChebyshevResolventRayRepresentative

private theorem correction_continuous : Continuous correction := by
  change Continuous (fun t => 2 * routePNativeCriticalProfile t - routePSourceRay t)
  exact (continuous_const.mul continuous_routePNativeCriticalProfile).sub source_continuous

private theorem correction_bound {t : ℝ} (ht : 0 ≤ t) :
    |correction t| ≤ 20 / 3 * Real.exp (-t / 2) := by
  have hd := criticalAbel_routeP_difference_le ht
  rw [← mobiusDivisorFullHead_eq_criticalContinuousAbel] at hd
  have hh : 0 < correction t ∧ correction t ≤ 20 / 3 * Real.exp (-t / 2) := by
    simpa only [correction, routePNativeCriticalProfile, mul_assoc, neg_div] using hd
  rw [abs_of_pos hh.1]
  exact hh.2

private theorem correction_admission {a c : ℝ} (ha : 0 ≤ a) (hc : -(1 / 2 : ℝ) < c) :
    IntegrableOn (fun t => Real.exp (-c * t) * correction t) (Ioi a) := by
  apply ((integrableOn_exp_mul_Ioi (by linarith : -(c + 1 / 2) < 0) a).const_mul
    (20 / 3 : ℝ)).mono'
  · exact ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul
      correction_continuous).aestronglyMeasurable.restrict
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    have he : Real.exp (-c * t) * Real.exp (-t / 2) = Real.exp (-(c + 1 / 2) * t) := by
      rw [← Real.exp_add]
      congr 1
      ring
    calc
      _ ≤ Real.exp (-c * t) * (20 / 3 * Real.exp (-t / 2)) :=
        mul_le_mul_of_nonneg_left (correction_bound (ha.trans ht.le)) (Real.exp_pos _).le
      _ = (20 / 3) * (Real.exp (-c * t) * Real.exp (-t / 2)) := by ring
      _ = _ := by rw [he]

private theorem source_head_tail {a : ℝ} (ha : 0 ≤ a) {z : ℂ} (hz : 1 / 2 < z.re) :
    head routePSourceRay a z + 2 * tail routePNativeCriticalProfile a z -
      tail correction a z = routePSourceLaplaceContinuation z := by
  have hH := native_admission ha hz
  have hR := complex_admission z correction_continuous.aestronglyMeasurable.restrict
    (correction_admission ha (by linarith))
  have hfun : (fun t => expRay z t * (routePSourceRay t : ℂ)) =
      (fun t => (2 : ℂ) * (expRay z t * (routePNativeCriticalProfile t : ℂ)) -
        expRay z t * (correction t : ℂ)) := by
    funext t
    dsimp only [correction]
    push_cast
    ring
  have hS : IntegrableOn (fun t => expRay z t * (routePSourceRay t : ℂ)) (Ioi a) := by
    rw [hfun]
    simpa only [IntegrableOn, Pi.sub_def] using (hH.const_mul (2 : ℂ)).sub hR
  have hhead : IntervalIntegrable (fun t => expRay z t * (routePSourceRay t : ℂ))
      volume 0 a := ((continuous_expRay z).mul
      (Complex.continuous_ofReal.comp source_continuous)).intervalIntegrable 0 a
  have hsplit := intervalIntegral.integral_interval_add_Ioi' hhead hS
  have ht : (∫ t in Ioi a, expRay z t * (routePSourceRay t : ℂ)) =
      2 * tail routePNativeCriticalProfile a z - tail correction a z := by
    rw [tail_eq_integral _ ha, tail_eq_integral _ ha, hfun,
      integral_sub (hH.const_mul (2 : ℂ)) hR, integral_const_mul]
  calc
    _ = head routePSourceRay a z + ∫ t in Ioi a,
        expRay z t * (routePSourceRay t : ℂ) := by rw [ht]; ring
    _ = ∫ t in Ioi (0 : ℝ), expRay z t * (routePSourceRay t : ℂ) := hsplit
    _ = routePSourceLaplaceContinuation z := by
      rw [routePSourceLaplaceContinuation_eq_laplace hz]
      unfold GaloisForLFunctions.RHTower.criticalMellinChebyshevResolventLaplace ccmAbelLaplaceTail
      congr 1
      funext t
      simp only [expRay, neg_mul]

private theorem no_growth_bound {ε b A C : ℝ}
    (hε : 0 < ε) (hεhalf : ε < 1 / 2) (hb : 0 ≤ b) (hbδ : b < 1 / 2 - ε) (hC : 0 ≤ C)
    (hQ : ∀ t : ℝ, A < t → |routePNativeLatePrimeMixedPrimitive ε t| ≤ C * Real.exp (b * t)) :
    False := by
  obtain ⟨Th, hTh, hh⟩ := exists_nativeTailHolomorphy
  obtain ⟨Ti, _, hi⟩ := exists_tailIdentity
  let a : ℝ := max A (max Th Ti) + 1
  have hAa : A < a := by dsimp only [a]; linarith [le_max_left A (max Th Ti)]
  have hha : Th < a := by
    dsimp only [a]
    linarith [le_max_left Th Ti, le_max_right A (max Th Ti)]
  have hia : Ti < a := by
    dsimp only [a]
    linarith [le_max_right Th Ti, le_max_right A (max Th Ti)]
  have ha : 0 < a := hTh.trans hha
  have hQa : ∀ t : ℝ, a < t →
      |routePNativeLatePrimeMixedPrimitive ε t| ≤ C * Real.exp (b * t) :=
    fun t ht => hQ t (hAa.trans ht)
  have hol := hh ε b a C hha hb hC hQa
  have hid := hi ε b a C hia hb hC hQa
  let δ : ℝ := 1 / 2 - ε
  let c : ℝ := (b - δ) / 2
  have hc : c < 0 := by dsimp only [c, δ]; linarith
  have hclower : -(1 / 2 : ℝ) < c := by dsimp only [c, δ]; linarith
  let L : ℂ → ℂ := fun z => head routePSourceRay a z +
    2 * (-(expRay (z + (δ : ℂ)) a * (routePNativeMixedCorrectedPrimitive ε a : ℂ)) +
      tail (density ε) a (z + (δ : ℂ)) +
      (z + (δ : ℂ)) * tail (routePNativeMixedCorrectedPrimitive ε) a (z + (δ : ℂ))) -
    tail correction a z
  have hR : AnalyticOnNhd ℂ (tail correction a) {z : ℂ | -(1 / 2 : ℝ) < z.re} :=
    tail_analytic correction_continuous.aestronglyMeasurable.restrict
      (fun d hd => correction_admission ha.le hd)
  have hL : AnalyticOnNhd ℂ L {z : ℂ | c < z.re} := by
    intro z hz
    change c < z.re at hz
    have hw : b < (z + (δ : ℂ)).re := by
      simp only [Complex.add_re, Complex.ofReal_re]
      dsimp only [c, δ] at *
      linarith
    have hs : AnalyticAt ℂ (fun z : ℂ => z + (δ : ℂ)) z := by fun_prop
    have hp : AnalyticAt ℂ (fun q =>
        tail (routePNativeMixedCorrectedPrimitive ε) a (q + (δ : ℂ))) z :=
      AnalyticAt.comp (f := fun q : ℂ => q + (δ : ℂ)) (hol.1 _ hw) hs
    have hd : AnalyticAt ℂ (fun q => tail (density ε) a (q + (δ : ℂ))) z :=
      AnalyticAt.comp (f := fun q : ℂ => q + (δ : ℂ)) (hol.2.1 _ hw) hs
    have he : AnalyticAt ℂ (fun z => expRay (z + (δ : ℂ)) a *
        (routePNativeMixedCorrectedPrimitive ε a : ℂ)) z := by unfold expRay; fun_prop
    change AnalyticAt ℂ (fun z => head routePSourceRay a z +
      2 * (-(expRay (z + (δ : ℂ)) a * (routePNativeMixedCorrectedPrimitive ε a : ℂ)) +
        tail (density ε) a (z + (δ : ℂ)) +
        (z + (δ : ℂ)) * tail (routePNativeMixedCorrectedPrimitive ε) a (z + (δ : ℂ))) -
      tail correction a z) z
    exact (((head_differentiable source_continuous a).analyticAt z).add
      (analyticAt_const.mul ((he.neg.add hd).add (hs.mul hp)))).sub
      (hR z (hclower.trans hz))
  apply no_routePSourceLaplace_analytic_extension_negative_abscissa hc L hL
  intro z hz
  have hw : b < (z + (δ : ℂ)).re := by
    simp only [Complex.add_re, Complex.ofReal_re]
    dsimp only [δ]
    linarith
  have heq : z + (δ : ℂ) - ((1 / 2 - ε : ℝ) : ℂ) = z := by
    dsimp only [δ]
    ring
  have hh := hid (z + (δ : ℂ)) hw (by simpa only [heq] using hz)
  rw [heq] at hh
  change head routePSourceRay a z + 2 * _ - tail correction a z = _
  rw [← hh]
  exact source_head_tail ha.le hz

/-- The actual signed native mixed primitive exceeds every subcritical
exponential envelope at arbitrarily late physical clocks. -/
theorem nativeMixedPrimitive_exponential_escape {ε b : ℝ}
    (hε : 0 < ε) (hεhalf : ε < 1 / 2) (hb : b < 1 / 2 - ε) (C A : ℝ) :
    ∃ t : ℝ, A < t ∧ C * Real.exp (b * t) < |routePNativeLatePrimeMixedPrimitive ε t| := by
  by_contra h
  push Not at h
  have hmax : max b 0 < 1 / 2 - ε := max_lt_iff.mpr ⟨hb, by linarith⟩
  apply no_growth_bound hε hεhalf (le_max_right b 0) hmax (le_max_right C 0)
    (A := max A 0)
  intro t ht
  have htA : A < t := (le_max_left _ _).trans_lt ht
  have ht0 : 0 ≤ t := ((le_max_right _ _).trans_lt ht).le
  calc
    _ ≤ C * Real.exp (b * t) := h t htA
    _ ≤ max C 0 * Real.exp (b * t) :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le
    _ ≤ max C 0 * Real.exp (max b 0 * t) :=
      mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (le_max_left _ _) ht0))
        (le_max_right _ _)

end RHTower.NativeMixedLaplace
