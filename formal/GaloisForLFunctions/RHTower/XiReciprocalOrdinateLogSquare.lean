import GaloisForLFunctions.RHTower.RiemannVonMangoldt
import GaloisForLFunctions.RHTower.XiOrderedPositiveZeros
import GaloisForLFunctions.RHTower.CentralReciprocalMoments

/-!
# Reciprocal Xi ordinates: the log-square law

With `N(T)` the number of Xi zeros with ordinate in `(0, T]` (multiplicity), Abel summation over
the finite set of supports gives, for `C¹` weights `f`,
`Σ_{0<γ≤T} m(ρ) f(γ) = N(T) f(T) − ∫_δ^T N(t) f'(t) dt`
(`δ` below every positive ordinate).  With `f = 1/t` and the Riemann–von Mangoldt law
`N(t) = (1/2π + o(1)) t log t`,

`Σ_{0<γ≤T} m(ρ)/γ = (1/(4π) + o(1)) (log T)²`.
-/

open MeasureTheory Set Filter Topology intervalIntegral

namespace RHTower

noncomputable section

/-! ## Counting through a fixed finite support set -/

theorem mem_xiSupportsPos_of_le {T U : ℝ} (hTU : T ≤ U) {ρ : XiDivisorSupport} (hρ : ρ ∈ xiSupportsPos T) :
    ρ ∈ xiSupportsPos U := by
  rw [mem_xiSupportsPos] at hρ ⊢
  exact ⟨hρ.1.trans hTU, hρ.2⟩

theorem xiSupportsPos_eq_filter {t T : ℝ} (htT : t ≤ T) :
    xiSupportsPos t = (xiSupportsPos T).filter (fun ρ : XiDivisorSupport => (ρ : ℂ).im ≤ t) := by
  ext ρ
  rw [Finset.mem_filter, mem_xiSupportsPos, mem_xiSupportsPos]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨⟨h1.trans htT, h2⟩, (le_abs_self _).trans h1⟩
  · rintro ⟨⟨_, h2⟩, h3⟩
    exact ⟨by rw [abs_of_pos h2]; exact h3, h2⟩

/-- `N(t) = Σ_{ρ ∈ supp(T), γ ≤ t} m(ρ)` for `0 ≤ t ≤ T`. -/
theorem xiZeroCount_eq_sum_filter {t T : ℝ} (ht : 0 ≤ t) (htT : t ≤ T) :
    (xiZeroCount t : ℝ) = ∑ ρ ∈ (xiSupportsPos T).filter (fun ρ : XiDivisorSupport => (ρ : ℂ).im ≤ t),
      (xiSupportMultiplicity ρ : ℝ) := by
  rw [xiZeroCount_eq_pos_sum ht, ← xiSupportsPos_eq_filter htT]
  push_cast; rfl

/-- A positive lower bound for all positive ordinates. -/
theorem exists_pos_lt_im_xiSupport : ∃ δ : ℝ, 0 < δ ∧ ∀ ρ : XiDivisorSupport, 0 < (ρ : ℂ).im → δ < (ρ : ℂ).im := by
  obtain ⟨δ, hδ, hconst⟩ := exists_xiZeroCount_eq_on_right (T := 0) le_rfl
  refine ⟨δ, hδ, fun ρ hρ => ?_⟩
  by_contra hle
  push Not at hle
  have h1 := hconst (ρ : ℂ).im hρ.le (by linarith)
  rw [xiZeroCount_zero] at h1
  have h2 : (xiSupportMultiplicity ρ : ℝ) ≤ xiZeroCount (ρ : ℂ).im := by
    rw [xiZeroCount_eq_sum_filter hρ.le le_rfl]
    exact Finset.single_le_sum (f := fun ρ => (xiSupportMultiplicity ρ : ℝ)) (fun _ _ => by positivity)
      (Finset.mem_filter.2 ⟨(mem_xiSupportsPos).2 ⟨by rw [abs_of_pos hρ], hρ⟩, le_rfl⟩)
  rw [h1] at h2
  have h3 : (1 : ℝ) ≤ xiSupportMultiplicity ρ := by exact_mod_cast xiSupportMultiplicity_pos ρ
  push_cast at h2
  linarith

/-! ## Abel summation -/

/-- **Abel summation over the positive Xi ordinates.** -/
theorem sum_xiSupportsPos_mul_eq {T δ : ℝ} (hδ : 0 < δ) (hδT : δ ≤ T)
    (hδρ : ∀ ρ : XiDivisorSupport, 0 < (ρ : ℂ).im → δ < (ρ : ℂ).im) {f f' : ℝ → ℝ}
    (hf : ∀ t ∈ Icc δ T, HasDerivAt f (f' t) t) (hf' : ContinuousOn f' (Icc δ T)) :
    ∑ ρ ∈ xiSupportsPos T, (xiSupportMultiplicity ρ : ℝ) * f (ρ : ℂ).im =
      (xiZeroCount T : ℝ) * f T - ∫ t in δ..T, (xiZeroCount t : ℝ) * f' t := by
  classical
  set S := xiSupportsPos T
  have hγ : ∀ ρ ∈ S, δ < (ρ : ℂ).im ∧ (ρ : ℂ).im ≤ T := fun ρ hρ => by
    rw [mem_xiSupportsPos] at hρ
    exact ⟨hδρ ρ hρ.2, (le_abs_self _).trans hρ.1⟩
  have hint : IntegrableOn f' (Ioc δ T) volume := by
    have := (hf'.mono (by rw [uIcc_of_le hδT])).intervalIntegrable (μ := volume)
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hδT).1 this
  have hftc : ∀ ρ ∈ S, f (ρ : ℂ).im = f T - ∫ t in ((ρ : ℂ).im)..T, f' t := by
    intro ρ hρ
    have hsub : uIcc ((ρ : ℂ).im) T ⊆ Icc δ T := by
      rw [uIcc_of_le (hγ ρ hρ).2]; exact Icc_subset_Icc (hγ ρ hρ).1.le le_rfl
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t ht => hf t (hsub ht))
      ((hf'.mono hsub).intervalIntegrable)]
    ring
  have hind : ∀ ρ ∈ S, ∫ t in ((ρ : ℂ).im)..T, f' t = ∫ t in δ..T, (Ici (ρ : ℂ).im).indicator f' t := by
    intro ρ hρ
    obtain ⟨h1, h2⟩ := hγ ρ hρ
    rw [intervalIntegral.integral_of_le h2, intervalIntegral.integral_of_le hδT,
      MeasureTheory.integral_indicator measurableSet_Ici, Measure.restrict_restrict measurableSet_Ici,
      show Ici (ρ : ℂ).im ∩ Ioc δ T = Icc (ρ : ℂ).im T by
        ext t; simp only [mem_inter_iff, mem_Ici, mem_Ioc, mem_Icc]
        constructor
        · rintro ⟨ha, -, hb⟩; exact ⟨ha, hb⟩
        · rintro ⟨ha, hb⟩; exact ⟨ha, h1.trans_le ha, hb⟩,
      integral_Icc_eq_integral_Ioc]
  have hsumN : ∀ t ∈ uIcc δ T, ∑ ρ ∈ S, (xiSupportMultiplicity ρ : ℝ) * (Ici (ρ : ℂ).im).indicator f' t =
      (xiZeroCount t : ℝ) * f' t := by
    intro t ht
    rw [uIcc_of_le hδT] at ht
    rw [xiZeroCount_eq_sum_filter (hδ.le.trans ht.1) ht.2, Finset.sum_mul, Finset.sum_filter]
    refine Finset.sum_congr rfl fun ρ _ => ?_
    by_cases hρt : (ρ : ℂ).im ≤ t
    · rw [indicator_of_mem (show t ∈ Ici (ρ : ℂ).im from hρt), if_pos hρt]
    · rw [indicator_of_notMem (show t ∉ Ici (ρ : ℂ).im from hρt), if_neg hρt, mul_zero]
  have hintρ : ∀ ρ ∈ S, IntervalIntegrable (fun t => (xiSupportMultiplicity ρ : ℝ) *
      (Ici (ρ : ℂ).im).indicator f' t) volume δ T := fun ρ _ =>
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le hδT).2 (hint.indicator measurableSet_Ici)).const_mul _
  calc ∑ ρ ∈ S, (xiSupportMultiplicity ρ : ℝ) * f (ρ : ℂ).im
      = ∑ ρ ∈ S, ((xiSupportMultiplicity ρ : ℝ) * f T -
          ∫ t in δ..T, (xiSupportMultiplicity ρ : ℝ) * (Ici (ρ : ℂ).im).indicator f' t) := by
        refine Finset.sum_congr rfl fun ρ hρ => ?_
        rw [hftc ρ hρ, hind ρ hρ, intervalIntegral.integral_const_mul]; ring
    _ = (∑ ρ ∈ S, (xiSupportMultiplicity ρ : ℝ)) * f T -
          ∫ t in δ..T, ∑ ρ ∈ S, (xiSupportMultiplicity ρ : ℝ) * (Ici (ρ : ℂ).im).indicator f' t := by
        rw [Finset.sum_sub_distrib, Finset.sum_mul, intervalIntegral.integral_finsetSum hintρ]
    _ = (xiZeroCount T : ℝ) * f T - ∫ t in δ..T, (xiZeroCount t : ℝ) * f' t := by
        rw [intervalIntegral.integral_congr hsumN, xiZeroCount_eq_pos_sum (hδ.le.trans hδT)]
        push_cast; rfl

/-! ## The log-square law -/

/-- `S(T) = Σ_{0<γ≤T} m(ρ)/γ`. -/
def xiReciprocalOrdinateSum (T : ℝ) : ℝ :=
  ∑ ρ ∈ xiSupportsPos T, (xiSupportMultiplicity ρ : ℝ) / (ρ : ℂ).im

theorem xiReciprocalOrdinateSum_nonneg (T : ℝ) : 0 ≤ xiReciprocalOrdinateSum T := by
  refine Finset.sum_nonneg fun ρ hρ => ?_
  rw [mem_xiSupportsPos] at hρ
  exact div_nonneg (by positivity) hρ.2.le

theorem intervalIntegrable_xiZeroCount_div_sq {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable (fun t => (xiZeroCount t : ℝ) * (1 / t ^ 2)) volume a b := by
  have hmono : MonotoneOn (fun t => (xiZeroCount t : ℝ)) (uIcc a b) := by
    intro x hx y hy hxy
    show (xiZeroCount x : ℝ) ≤ xiZeroCount y
    exact_mod_cast xiZeroCount_mono hxy
  refine (hmono.intervalIntegrable).mul_continuousOn ?_
  intro t ht
  rw [uIcc_of_le hab] at ht
  have : t ≠ 0 := (ha.trans_le ht.1).ne'
  exact (continuousAt_const.div (continuousAt_id.pow 2) (pow_ne_zero 2 this)).continuousWithinAt

/-- `S(T) = N(T)/T + ∫_δ^T N(t)/t² dt`. -/
theorem xiReciprocalOrdinateSum_eq {T δ : ℝ} (hδ : 0 < δ) (hδT : δ ≤ T)
    (hδρ : ∀ ρ : XiDivisorSupport, 0 < (ρ : ℂ).im → δ < (ρ : ℂ).im) :
    xiReciprocalOrdinateSum T = (xiZeroCount T : ℝ) / T + ∫ t in δ..T, (xiZeroCount t : ℝ) * (1 / t ^ 2) := by
  have h := sum_xiSupportsPos_mul_eq hδ hδT hδρ (f := fun t => 1 / t) (f' := fun t => -(1 / t ^ 2))
    (fun t ht => by
      have ht0 : t ≠ 0 := (hδ.trans_le ht.1).ne'
      have := (hasDerivAt_inv ht0)
      simpa [one_div] using this)
    (fun t ht => by
      have ht0 : t ≠ 0 := (hδ.trans_le ht.1).ne'
      exact (continuousAt_const.div (continuousAt_id.pow 2) (pow_ne_zero 2 ht0)).neg.continuousWithinAt)
  simp only [mul_neg, intervalIntegral.integral_neg, sub_neg_eq_add] at h
  rw [xiReciprocalOrdinateSum, div_eq_mul_one_div (xiZeroCount T : ℝ) T, ← h]
  exact Finset.sum_congr rfl fun ρ _ => div_eq_mul_one_div _ _

theorem integral_log_div {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∫ t in a..b, Real.log t / t = (Real.log b ^ 2 - Real.log a ^ 2) / 2 := by
  have hderiv : ∀ t ∈ uIcc a b, HasDerivAt (fun t => Real.log t ^ 2 / 2) (Real.log t / t) t := by
    intro t ht
    rw [uIcc_of_le hab] at ht
    have ht0 : t ≠ 0 := (ha.trans_le ht.1).ne'
    have := ((Real.hasDerivAt_log ht0).pow 2).div_const 2
    refine this.congr_deriv ?_
    simp only [Nat.cast_ofNat, Nat.add_one_sub_one, pow_one]
    field_simp
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv]
  · ring
  · refine ContinuousOn.intervalIntegrable fun t ht => ?_
    rw [uIcc_of_le hab] at ht
    have ht0 : t ≠ 0 := (ha.trans_le ht.1).ne'
    exact ((Real.continuousAt_log ht0).div continuousAt_id ht0).continuousWithinAt

/-- Bounds for `∫_{T₀}^T N(t)/t²` from the Riemann–von Mangoldt law. -/
theorem integral_xiZeroCount_div_sq_bounds {ε T₀ : ℝ} (hT₀ : 4 ≤ T₀)
    (hclose : ∀ T : ℝ, T₀ ≤ T →
      |(xiZeroCount T : ℝ) - (1 / (2 * Real.pi)) * (T * Real.log T)| ≤ ε * (T * Real.log T))
    {T : ℝ} (hT : T₀ ≤ T) :
    (1 / (2 * Real.pi) - ε) * ((Real.log T ^ 2 - Real.log T₀ ^ 2) / 2) ≤
        ∫ t in T₀..T, (xiZeroCount t : ℝ) * (1 / t ^ 2) ∧
      ∫ t in T₀..T, (xiZeroCount t : ℝ) * (1 / t ^ 2) ≤
        (1 / (2 * Real.pi) + ε) * ((Real.log T ^ 2 - Real.log T₀ ^ 2) / 2) := by
  have hT₀0 : 0 < T₀ := by linarith
  have hint := intervalIntegrable_xiZeroCount_div_sq hT₀0 hT
  have hlogint : IntervalIntegrable (fun t => Real.log t / t) volume T₀ T := by
    refine ContinuousOn.intervalIntegrable fun t ht => ?_
    rw [uIcc_of_le hT] at ht
    have ht0 : t ≠ 0 := (hT₀0.trans_le ht.1).ne'
    exact ((Real.continuousAt_log ht0).div continuousAt_id ht0).continuousWithinAt
  have hbound : ∀ t ∈ Icc T₀ T, |(xiZeroCount t : ℝ) * (1 / t ^ 2) - (1 / (2 * Real.pi)) * (Real.log t / t)| ≤
      ε * (Real.log t / t) := by
    intro t ht
    have ht0 : 0 < t := hT₀0.trans_le ht.1
    have h := hclose t ht.1
    have heq : (xiZeroCount t : ℝ) * (1 / t ^ 2) - (1 / (2 * Real.pi)) * (Real.log t / t) =
        ((xiZeroCount t : ℝ) - (1 / (2 * Real.pi)) * (t * Real.log t)) / t ^ 2 := by
      field_simp
    rw [heq, abs_div, abs_of_pos (by positivity : (0 : ℝ) < t ^ 2), div_le_iff₀ (by positivity)]
    calc |(xiZeroCount t : ℝ) - 1 / (2 * Real.pi) * (t * Real.log t)| ≤ ε * (t * Real.log t) := h
      _ = ε * (Real.log t / t) * t ^ 2 := by field_simp
  rw [← integral_log_div hT₀0 hT]
  constructor
  · rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_mono_on hT (hlogint.const_mul _) hint fun t ht => ?_
    have := (abs_le.1 (hbound t ht)).1
    linarith
  · rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_mono_on hT hint (hlogint.const_mul _) fun t ht => ?_
    have := (abs_le.1 (hbound t ht)).2
    linarith

/-- **Log-square law for reciprocal ordinates**: `Σ_{0<γ≤T} m/γ = (1/(4π) + o(1))(log T)²`. -/
theorem tendsto_xiReciprocalOrdinateSum_div_log_sq :
    Tendsto (fun T => xiReciprocalOrdinateSum T / Real.log T ^ 2) atTop (𝓝 (1 / (4 * Real.pi))) := by
  obtain ⟨δ, hδ, hδρ⟩ := exists_pos_lt_im_xiSupport
  have hlog : Tendsto (fun T : ℝ => Real.log T) atTop atTop := Real.tendsto_log_atTop
  have hpi := Real.pi_pos
  rw [tendsto_order]
  constructor
  · intro a ha
    set ε := (1 / (4 * Real.pi) - a) / 2
    have hε : 0 < ε := by simp only [ε]; linarith
    obtain ⟨T₀', hT₀', hclose⟩ := exists_xiZeroCount_close ε hε
    set T₀ := max T₀' δ
    have hT₀4 : 4 ≤ T₀ := hT₀'.trans (le_max_left _ _)
    have hclose' : ∀ T, T₀ ≤ T →
        |(xiZeroCount T : ℝ) - (1 / (2 * Real.pi)) * (T * Real.log T)| ≤ ε * (T * Real.log T) :=
      fun T hT => hclose T ((le_max_left _ _).trans hT)
    have ev : ∀ᶠ T in atTop, (ε + 1 / (4 * Real.pi)) * Real.log T₀ ^ 2 ≤ ε * Real.log T ^ 2 := by
      have : Tendsto (fun T => ε * Real.log T ^ 2) atTop atTop :=
        (tendsto_pow_atTop (two_ne_zero)).comp hlog |>.const_mul_atTop hε
      exact this.eventually_ge_atTop _
    filter_upwards [ev, eventually_ge_atTop T₀, hlog.eventually_gt_atTop 0] with T hT hTT₀ hlogT
    have hδT : δ ≤ T := (le_max_right _ _).trans hTT₀
    have hS := xiReciprocalOrdinateSum_eq hδ hδT hδρ
    have hδT₀ : δ ≤ T₀ := le_max_right _ _
    have hsplit := intervalIntegral.integral_add_adjacent_intervals
      (intervalIntegrable_xiZeroCount_div_sq hδ hδT₀)
      (intervalIntegrable_xiZeroCount_div_sq (hδ.trans_le hδT₀) hTT₀)
    have hK : 0 ≤ ∫ t in δ..T₀, (xiZeroCount t : ℝ) * (1 / t ^ 2) :=
      intervalIntegral.integral_nonneg (le_max_right _ _) fun t ht => by
        have := xiZeroCount_nonneg t
        positivity
    have hN : 0 ≤ (xiZeroCount T : ℝ) / T := by
      have := xiZeroCount_nonneg T
      have hT0 : 0 < T := hδ.trans_le hδT
      positivity
    have hlow := (integral_xiZeroCount_div_sq_bounds hT₀4 hclose' hTT₀).1
    have hL₀ : 0 < Real.log T₀ := Real.log_pos (by linarith)
    have hεL₀ : 0 < ε * Real.log T₀ ^ 2 := by positivity
    have hcL₀ : 0 < 1 / (2 * Real.pi) * Real.log T₀ ^ 2 := by positivity
    have ha : a = 1 / (4 * Real.pi) - 2 * ε := by simp only [ε]; ring
    rw [lt_div_iff₀ (by positivity), hS, ← hsplit, ha]
    have h4 : 1 / (4 * Real.pi) = 1 / (2 * Real.pi) / 2 := by field_simp; ring
    rw [h4] at hT ⊢
    linarith
  · intro b hb
    set ε := (b - 1 / (4 * Real.pi)) / 2
    have hε : 0 < ε := by simp only [ε]; linarith
    obtain ⟨T₀', hT₀', hclose⟩ := exists_xiZeroCount_close ε hε
    set T₀ := max T₀' δ
    have hT₀4 : 4 ≤ T₀ := hT₀'.trans (le_max_left _ _)
    have hclose' : ∀ T, T₀ ≤ T →
        |(xiZeroCount T : ℝ) - (1 / (2 * Real.pi)) * (T * Real.log T)| ≤ ε * (T * Real.log T) :=
      fun T hT => hclose T ((le_max_left _ _).trans hT)
    set K := ∫ t in δ..T₀, (xiZeroCount t : ℝ) * (1 / t ^ 2)
    have ev : ∀ᶠ T in atTop, K + (1 / (2 * Real.pi) + ε) * Real.log T < ε * Real.log T ^ 2 := by
      have h1 : Tendsto (fun T => (ε * Real.log T - (1 / (2 * Real.pi) + ε)) * Real.log T) atTop atTop := by
        have hA : Tendsto (fun T => ε * Real.log T - (1 / (2 * Real.pi) + ε)) atTop atTop :=
          tendsto_atTop_add_const_right _ _ (hlog.const_mul_atTop hε)
        exact hA.atTop_mul_atTop₀ hlog
      filter_upwards [h1.eventually_gt_atTop K] with T hT
      nlinarith
    filter_upwards [ev, eventually_ge_atTop T₀, hlog.eventually_gt_atTop 0] with T hT hTT₀ hlogT
    have hδT : δ ≤ T := (le_max_right _ _).trans hTT₀
    have hT0 : 0 < T := hδ.trans_le hδT
    have hS := xiReciprocalOrdinateSum_eq hδ hδT hδρ
    have hδT₀ : δ ≤ T₀ := le_max_right _ _
    have hsplit := intervalIntegral.integral_add_adjacent_intervals
      (intervalIntegrable_xiZeroCount_div_sq hδ hδT₀)
      (intervalIntegrable_xiZeroCount_div_sq (hδ.trans_le hδT₀) hTT₀)
    have hup := (integral_xiZeroCount_div_sq_bounds hT₀4 hclose' hTT₀).2
    have hNT : (xiZeroCount T : ℝ) / T ≤ (1 / (2 * Real.pi) + ε) * Real.log T := by
      have h := hclose' T hTT₀
      rw [div_le_iff₀ hT0]
      have := (abs_le.1 h).2
      nlinarith
    have hcε : 0 ≤ (1 / (2 * Real.pi) + ε) * Real.log T₀ ^ 2 := by positivity
    have hεL : 0 ≤ ε * Real.log T ^ 2 := by positivity
    have hb : b = 1 / (4 * Real.pi) + 2 * ε := by simp only [ε]; ring
    rw [div_lt_iff₀ (by positivity), hS, ← hsplit, hb]
    have h4 : 1 / (4 * Real.pi) = 1 / (2 * Real.pi) / 2 := by field_simp; ring
    rw [h4]
    linarith

end

end RHTower
