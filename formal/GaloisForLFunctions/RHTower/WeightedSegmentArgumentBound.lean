import GaloisForLFunctions.HTGeometry.SegmentArgumentBound

/-!
# The weighted horizontal edge of a Littlewood rectangle

Littlewood's weighted identity carries the horizontal edges with the linear weight `x − c`.  Backlund's
bound controls the *unweighted* argument variation on every initial subsegment, and one integration
by parts converts that into a bound for the weighted integral, at the cost of a factor `2(b−a)`:

```text
∫_a^b (t−a) q(t) dt = (b−a)·V(b) − ∫_a^b V,          V(y) = ∫_a^y q,
```

so a uniform bound `|V| ≤ B` on `[a,b]` gives `|∫ (t−a) q| ≤ 2(b−a)B`.
-/

open Complex MeasureTheory Set intervalIntegral
open scoped Interval

noncomputable section

namespace RHTower

/-- Integration by parts against the linear weight: a uniform bound for the primitive bounds the
weighted integral. -/
theorem abs_integral_weighted_le_of_primitive_bound {a b : ℝ} (hab : a ≤ b) {q : ℝ → ℝ}
    (hq : Continuous q) {B : ℝ} (hB : ∀ y ∈ Set.Icc a b, |∫ t in a..y, q t| ≤ B) :
    |∫ t in a..b, (t - a) * q t| ≤ 2 * (b - a) * B := by
  set V : ℝ → ℝ := fun y => ∫ t in a..y, q t with hV
  have hVderiv : ∀ x : ℝ, HasDerivAt V (q x) x := fun x =>
    intervalIntegral.integral_hasDerivAt_right (hq.intervalIntegrable a x)
      (hq.stronglyMeasurableAtFilter _ _) hq.continuousAt
  have hVcont : Continuous V := by
    refine continuous_iff_continuousAt.mpr fun x => ?_
    exact (hVderiv x).continuousAt
  have hu : ∀ x ∈ Set.uIcc a b, HasDerivAt (fun t : ℝ => t - a) 1 x := by
    intro x _
    simpa using (hasDerivAt_id x).sub_const a
  have hbyparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    hu (fun x _ => hVderiv x) intervalIntegrable_const (hq.intervalIntegrable a b)
  have hVa : V a = 0 := by simp [hV]
  have hVbound : ∀ y ∈ Set.Icc a b, |V y| ≤ B := hB
  have hB0 : 0 ≤ B := le_trans (abs_nonneg _) (hB a ⟨le_rfl, hab⟩)
  have hint : |∫ t in a..b, (1 : ℝ) * V t| ≤ (b - a) * B := by
    have hrw : (∫ t in a..b, (1 : ℝ) * V t) = ∫ t in a..b, V t := by
      simp
    rw [hrw]
    have hmono : |∫ t in a..b, V t| ≤ ∫ t in a..b, |V t| :=
      intervalIntegral.abs_integral_le_integral_abs hab
    refine le_trans hmono ?_
    have hle : (∫ t in a..b, |V t|) ≤ ∫ _t in a..b, B := by
      refine intervalIntegral.integral_mono_on hab ((hVcont.abs).intervalIntegrable a b)
        intervalIntegrable_const ?_
      intro t ht
      exact hVbound t ht
    simpa [mul_comm] using hle
  have hfin : |(b - a) * V b| ≤ (b - a) * B := by
    rw [abs_mul, abs_of_nonneg (by linarith : (0:ℝ) ≤ b - a)]
    exact mul_le_mul_of_nonneg_left (hVbound b ⟨hab, le_rfl⟩) (by linarith)
  rw [hbyparts, hVa]
  have hsplit : |(b - a) * V b - (a - a) * 0 - ∫ t in a..b, (1 : ℝ) * V t|
      ≤ |(b - a) * V b| + |∫ t in a..b, (1 : ℝ) * V t| := by
    have h1 : (b - a) * V b - (a - a) * 0 - (∫ t in a..b, (1 : ℝ) * V t)
        = (b - a) * V b - (∫ t in a..b, (1 : ℝ) * V t) := by ring
    rw [h1]
    exact abs_sub _ _
  calc |(b - a) * V b - (a - a) * 0 - ∫ t in a..b, (1 : ℝ) * V t|
      ≤ |(b - a) * V b| + |∫ t in a..b, (1 : ℝ) * V t| := hsplit
    _ ≤ (b - a) * B + (b - a) * B := by linarith [hfin, hint]
    _ = 2 * (b - a) * B := by ring

/-- **The weighted Backlund bound.**  For a nonvanishing continuously differentiable path, the
weighted argument variation across `[a,b]` is at most `2(b−a)π` times one more than the number of
real-part zeros. -/
theorem abs_integral_weighted_im_logDeriv_le_of_finite_re_zeros {a b : ℝ} (hab : a ≤ b)
    {f f' : ℝ → ℂ} (hf : ∀ t : ℝ, HasDerivAt f (f' t) t)
    (hfc : Continuous f) (hf'c : Continuous f')
    (hne : ∀ t ∈ Set.Icc a b, f t ≠ 0)
    (Z : Finset ℝ) (hZ : ∀ t ∈ Set.Ioo a b, (f t).re = 0 → t ∈ Z) :
    |∫ t in a..b, (t - a) * (f' t / f t).im|
      ≤ 2 * (b - a) * ((((Z.filter (fun z => z ∈ Set.Ioo a b)).card : ℝ) + 1) * Real.pi) := by
  classical
  set clamp : ℝ → ℝ := fun x => max a (min b x) with hclamp
  have hclampcont : Continuous clamp := by
    refine continuous_const.max (continuous_const.min continuous_id)
  have hclampmem : ∀ x : ℝ, clamp x ∈ Set.Icc a b := by
    intro x
    constructor
    · exact le_max_left _ _
    · exact max_le hab (min_le_left _ _)
  have hclampeq : ∀ x ∈ Set.Icc a b, clamp x = x := by
    intro x hx
    show max a (min b x) = x
    rw [min_eq_right hx.2, max_eq_right hx.1]
  set q : ℝ → ℝ := fun t => (f' t / f t).im with hq
  set Q : ℝ → ℝ := fun t => q (clamp t) with hQ
  have hqcont : ContinuousOn q (Set.Icc a b) := by
    refine Complex.continuous_im.comp_continuousOn ?_
    exact ContinuousOn.div hf'c.continuousOn hfc.continuousOn hne
  have hQcont : Continuous Q := hqcont.comp_continuous hclampcont hclampmem
  have hQeq : ∀ y ∈ Set.Icc a b, (∫ t in a..y, Q t) = ∫ t in a..y, q t := by
    intro y hy
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [uIcc_of_le hy.1] at ht
    exact congrArg q (hclampeq t ⟨ht.1, le_trans ht.2 hy.2⟩)
  set B : ℝ := (((Z.filter (fun z => z ∈ Set.Ioo a b)).card : ℝ) + 1) * Real.pi with hB
  have hprim : ∀ y ∈ Set.Icc a b, |∫ t in a..y, Q t| ≤ B := by
    intro y hy
    rw [hQeq y hy]
    have hbase := abs_integral_im_logDeriv_le_of_finite_re_zeros hy.1
      (f := f) (f' := f') (fun t _ => hf t)
      (ContinuousOn.div hf'c.continuousOn hfc.continuousOn
        (fun t ht => hne t ⟨ht.1, le_trans ht.2 hy.2⟩))
      (fun t ht => hne t ⟨ht.1, le_trans ht.2 hy.2⟩) Z
      (fun t ht hre => hZ t ⟨ht.1, lt_of_lt_of_le ht.2 hy.2⟩ hre)
    refine le_trans hbase ?_
    have hcard : ((Z.filter (fun z => z ∈ Set.Ioo a y)).card : ℝ)
        ≤ ((Z.filter (fun z => z ∈ Set.Ioo a b)).card : ℝ) := by
      have : (Z.filter (fun z => z ∈ Set.Ioo a y)).card
          ≤ (Z.filter (fun z => z ∈ Set.Ioo a b)).card := by
        refine Finset.card_le_card ?_
        intro z hz
        rw [Finset.mem_filter] at hz ⊢
        exact ⟨hz.1, ⟨hz.2.1, lt_of_lt_of_le hz.2.2 hy.2⟩⟩
      exact_mod_cast this
    rw [hB]
    have hπ : (0 : ℝ) ≤ Real.pi := Real.pi_pos.le
    nlinarith
  have hmain := abs_integral_weighted_le_of_primitive_bound hab hQcont hprim
  have hcongr : (∫ t in a..b, (t - a) * Q t) = ∫ t in a..b, (t - a) * q t := by
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [uIcc_of_le hab] at ht
    exact congrArg _ (congrArg q (hclampeq t ht))
  rwa [hcongr] at hmain

end RHTower

end
