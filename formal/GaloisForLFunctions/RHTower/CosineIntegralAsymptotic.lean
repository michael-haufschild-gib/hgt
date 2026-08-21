import GaloisForLFunctions.RHTower.EulerMascheroniGaussKernel
import GaloisForLFunctions.HTGeometry.FrullaniIntegral
import GaloisForLFunctions.RHTower.DigammaIntegralRepresentation

/-!
# The cosine integral and the Frullani evaluation `∫ (e^{-u} - cos u)/u du = 0`

The oscillatory tail `∫_1^∞ cos t / t dt` converges only conditionally.  Integrating by parts
against `t⁻¹` turns it into an absolutely convergent integral,

`∫_1^y cos t/t dt = sin y / y - sin 1 + ∫_1^y sin t / t² dt`,

so the truncated integrals converge to

`cosTailValue = - sin 1 + ∫_1^∞ sin t / t² dt`.

The same integration by parts, applied to the damped kernel `e^{-εt} cos t / t`, is stable as
`ε → 0+`: the extra term carries a factor `ε ∫_1^∞ e^{-εt}/t dt = ε(-log ε + Ein(ε) - γ)`, which
vanishes.  Combining this with the complex Frullani evaluation at rates `1` and `ε - i`, whose real
part is `½ log(1+ε²)`, identifies the tail value and yields

`∫_0^1 (e^{-t} - cos t)/t dt + ∫_1^∞ e^{-t}/t dt = cosTailValue`,

which is the statement that the (improper) integral `∫_0^∞ (e^{-t} - cos t)/t dt` vanishes.
-/

open MeasureTheory Set Filter Real Complex
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace RHTower

/-! ## The absolutely convergent partner `sin t / t²` -/

theorem integrableOn_sin_div_sq {R : ℝ} (hR : 0 < R) :
    IntegrableOn (fun t : ℝ => Real.sin t / t ^ 2) (Ioi R) volume := by
  have hmaj : IntegrableOn (fun t : ℝ => (1 : ℝ) / t ^ 2) (Ioi R) volume := by
    have hcont : ContinuousWithinAt (fun v : ℝ => -v⁻¹) (Ici R) R :=
      (continuousAt_inv₀ (ne_of_gt hR)).neg.continuousWithinAt
    have hderiv : ∀ t ∈ Ioi R, HasDerivAt (fun v : ℝ => -v⁻¹) ((1 : ℝ) / t ^ 2) t := by
      intro t ht
      have ht0 : 0 < t := lt_trans hR ht
      have h := (hasDerivAt_inv (ne_of_gt ht0)).neg
      refine h.congr_deriv ?_
      field_simp
    have hpos : ∀ t ∈ Ioi R, (0 : ℝ) ≤ (1 : ℝ) / t ^ 2 := by
      intro t ht
      have ht0 : 0 < t := lt_trans hR ht
      positivity
    have htend : Tendsto (fun v : ℝ => -v⁻¹) atTop (nhds 0) := by
      simpa using (tendsto_inv_atTop_zero (𝕜 := ℝ)).neg
    exact MeasureTheory.integrableOn_Ioi_deriv_of_nonneg hcont hderiv hpos htend
  have hmeas : AEStronglyMeasurable (fun t : ℝ => Real.sin t / t ^ 2)
      (volume.restrict (Ioi R)) := by
    refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    intro t ht
    have ht0 : 0 < t := lt_trans hR ht
    exact ContinuousAt.continuousWithinAt
      (ContinuousAt.div (by fun_prop) (by fun_prop) (by positivity))
  refine hmaj.mono' hmeas ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have ht0 : 0 < t := lt_trans hR ht
  rw [Real.norm_eq_abs, abs_div, abs_of_nonneg (by positivity : (0:ℝ) ≤ t ^ 2)]
  have hsin : |Real.sin t| ≤ 1 := Real.abs_sin_le_one t
  rw [div_le_div_iff_of_pos_right (by positivity)]
  exact hsin

/-- The integration-by-parts identity for the oscillatory tail. -/
theorem intervalIntegral_cos_div (y : ℝ) (hy : 1 ≤ y) :
    (∫ t in (1 : ℝ)..y, Real.cos t / t)
      = Real.sin y / y - Real.sin 1 + ∫ t in (1 : ℝ)..y, Real.sin t / t ^ 2 := by
  have hderiv_u : ∀ t ∈ Set.uIcc (1 : ℝ) y, HasDerivAt (fun v : ℝ => v⁻¹) (-(t ^ 2)⁻¹) t := by
    intro t ht
    rw [Set.uIcc_of_le hy] at ht
    have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht.1
    simpa using hasDerivAt_inv (ne_of_gt ht0)
  have hderiv_v : ∀ t ∈ Set.uIcc (1 : ℝ) y, HasDerivAt Real.sin (Real.cos t) t :=
    fun t _ => Real.hasDerivAt_sin t
  have hint_u : IntervalIntegrable (fun t : ℝ => -(t ^ 2)⁻¹) volume 1 y := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [Set.uIcc_of_le hy]
    intro t ht
    have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht.1
    exact ContinuousAt.continuousWithinAt (by
      have : ContinuousAt (fun v : ℝ => (v ^ 2)⁻¹) t :=
        (continuousAt_inv₀ (by positivity)).comp (by fun_prop)
      exact this.neg)
  have hint_v : IntervalIntegrable Real.cos volume 1 y :=
    Real.continuous_cos.intervalIntegrable _ _
  have hIBP := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    hderiv_u hderiv_v hint_u hint_v
  have hleft : (∫ t in (1 : ℝ)..y, t⁻¹ * Real.cos t) = ∫ t in (1 : ℝ)..y, Real.cos t / t := by
    refine intervalIntegral.integral_congr ?_
    intro t _
    dsimp only
    rw [div_eq_inv_mul]
  have hright : (∫ t in (1 : ℝ)..y, -(t ^ 2)⁻¹ * Real.sin t)
      = -∫ t in (1 : ℝ)..y, Real.sin t / t ^ 2 := by
    rw [← intervalIntegral.integral_neg]
    refine intervalIntegral.integral_congr ?_
    intro t _
    dsimp only
    rw [div_eq_inv_mul]
    ring
  rw [hleft, hright] at hIBP
  rw [hIBP]
  simp only [inv_one, one_mul]
  rw [div_eq_inv_mul]
  ring

/-- The limiting value of the oscillatory tail. -/
def cosTailValue : ℝ := -Real.sin 1 + ∫ t in Ioi (1 : ℝ), Real.sin t / t ^ 2

theorem tendsto_intervalIntegral_cos_div :
    Tendsto (fun y : ℝ => ∫ t in (1 : ℝ)..y, Real.cos t / t) atTop (nhds cosTailValue) := by
  have hsinq : Tendsto (fun y : ℝ => ∫ t in (1 : ℝ)..y, Real.sin t / t ^ 2) atTop
      (nhds (∫ t in Ioi (1 : ℝ), Real.sin t / t ^ 2)) := by
    have h := MeasureTheory.intervalIntegral_tendsto_integral_Ioi (a := (1 : ℝ))
      (f := fun t : ℝ => Real.sin t / t ^ 2) (integrableOn_sin_div_sq zero_lt_one)
      (b := fun n : ℝ => n) tendsto_id
    exact h
  have hsy : Tendsto (fun y : ℝ => Real.sin y / y) atTop (nhds 0) := by
    refine squeeze_zero_norm' (a := fun y : ℝ => |y|⁻¹) ?_ ?_
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with y hy
      rw [Real.norm_eq_abs, abs_div, abs_of_pos hy]
      rw [div_le_iff₀ hy, inv_mul_cancel₀ (ne_of_gt hy)]
      exact Real.abs_sin_le_one y
    · have habs : Tendsto (fun y : ℝ => |y|) atTop atTop := by
        simpa using (tendsto_abs_atTop_atTop (G := ℝ))
      exact tendsto_inv_atTop_zero.comp habs
  have hcomb := (hsy.sub (tendsto_const_nhds (x := Real.sin 1))).add hsinq
  rw [zero_sub] at hcomb
  rw [cosTailValue]
  refine hcomb.congr' ?_
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with y hy
  rw [intervalIntegral_cos_div y hy]


/-! ## The damped tail -/

/-- The damped oscillatory tail `∫_1^∞ e^{-εt} cos t / t dt`, after integration by parts. -/
def dampedCosTail (ε : ℝ) : ℝ :=
  -(Real.exp (-ε) * Real.sin 1)
    + ∫ t in Ioi (1 : ℝ), Real.sin t * (Real.exp (-(ε * t)) * (ε / t + 1 / t ^ 2))

theorem intervalIntegral_damped_cos_div (ε : ℝ) {y : ℝ} (hy : 1 ≤ y) :
    (∫ t in (1 : ℝ)..y, Real.exp (-(ε * t)) * Real.cos t / t)
      = Real.exp (-(ε * y)) * Real.sin y / y - Real.exp (-ε) * Real.sin 1
        + ∫ t in (1 : ℝ)..y, Real.sin t * (Real.exp (-(ε * t)) * (ε / t + 1 / t ^ 2)) := by
  have hderiv_u : ∀ t ∈ Set.uIcc (1 : ℝ) y,
      HasDerivAt (fun v : ℝ => Real.exp (-(ε * v)) * v⁻¹)
        (-(Real.exp (-(ε * t)) * (ε / t + 1 / t ^ 2))) t := by
    intro t ht
    rw [Set.uIcc_of_le hy] at ht
    have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht.1
    have hexp : HasDerivAt (fun v : ℝ => Real.exp (-(ε * v))) (Real.exp (-(ε * t)) * -ε) t := by
      have hlin : HasDerivAt (fun v : ℝ => -(ε * v)) (-ε) t := by
        have h0 : HasDerivAt (fun v : ℝ => ε * v) ε t := by
          simpa using (hasDerivAt_id t).const_mul ε
        exact h0.neg.congr_deriv (by ring)
      simpa using hlin.exp
    have hinv : HasDerivAt (fun v : ℝ => v⁻¹) (-(t ^ 2)⁻¹) t := by
      simpa using hasDerivAt_inv (ne_of_gt ht0)
    refine (hexp.mul hinv).congr_deriv ?_
    field_simp
    ring
  have hderiv_v : ∀ t ∈ Set.uIcc (1 : ℝ) y, HasDerivAt Real.sin (Real.cos t) t :=
    fun t _ => Real.hasDerivAt_sin t
  have hint_u : IntervalIntegrable
      (fun t : ℝ => -(Real.exp (-(ε * t)) * (ε / t + 1 / t ^ 2))) volume 1 y := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [Set.uIcc_of_le hy]
    intro t ht
    have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht.1
    refine ContinuousAt.continuousWithinAt ?_
    have h1 : ContinuousAt (fun v : ℝ => Real.exp (-(ε * v))) t := by fun_prop
    have h2 : ContinuousAt (fun v : ℝ => ε / v + 1 / v ^ 2) t := by
      refine ContinuousAt.add ?_ ?_
      · exact ContinuousAt.div continuousAt_const continuousAt_id (ne_of_gt ht0)
      · exact ContinuousAt.div continuousAt_const (by fun_prop) (by positivity)
    exact (h1.mul h2).neg
  have hint_v : IntervalIntegrable Real.cos volume 1 y :=
    Real.continuous_cos.intervalIntegrable _ _
  have hIBP := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    hderiv_u hderiv_v hint_u hint_v
  have hleft : (∫ t in (1 : ℝ)..y, Real.exp (-(ε * t)) * t⁻¹ * Real.cos t)
      = ∫ t in (1 : ℝ)..y, Real.exp (-(ε * t)) * Real.cos t / t := by
    refine intervalIntegral.integral_congr ?_
    intro t _
    dsimp only
    field_simp
  have hright : (∫ t in (1 : ℝ)..y,
      -(Real.exp (-(ε * t)) * (ε / t + 1 / t ^ 2)) * Real.sin t)
      = -∫ t in (1 : ℝ)..y, Real.sin t * (Real.exp (-(ε * t)) * (ε / t + 1 / t ^ 2)) := by
    rw [← intervalIntegral.integral_neg]
    refine intervalIntegral.integral_congr ?_
    intro t _
    dsimp only
    ring
  rw [hleft, hright] at hIBP
  rw [hIBP]
  have hone : Real.exp (-(ε * 1)) * (1 : ℝ)⁻¹ = Real.exp (-ε) := by
    norm_num
  rw [hone]
  have hy0 : Real.exp (-(ε * y)) * y⁻¹ * Real.sin y
      = Real.exp (-(ε * y)) * Real.sin y / y := by
    field_simp
  rw [hy0]
  ring


/-! ## Exponential tails with a general rate -/

theorem integrableOn_exp_neg_mul_Ioi {ε : ℝ} (hε : 0 < ε) (a : ℝ) :
    IntegrableOn (fun t : ℝ => Real.exp (-(ε * t))) (Ioi a) volume := by
  simpa [neg_mul] using exp_neg_integrableOn_Ioi a hε

theorem integral_exp_neg_mul_Ioi {ε : ℝ} (hε : 0 < ε) (a : ℝ) :
    (∫ t in Ioi a, Real.exp (-(ε * t))) = Real.exp (-(ε * a)) / ε := by
  have hderiv : ∀ t ∈ Ioi a,
      HasDerivAt (fun v : ℝ => -(Real.exp (-(ε * v)) / ε)) (Real.exp (-(ε * t))) t := by
    intro t _
    have hlin : HasDerivAt (fun v : ℝ => -(ε * v)) (-ε) t := by
      have h0 : HasDerivAt (fun v : ℝ => ε * v) ε t := by
        simpa using (hasDerivAt_id t).const_mul ε
      exact h0.neg.congr_deriv (by ring)
    have hexp : HasDerivAt (fun v : ℝ => Real.exp (-(ε * v)))
        (Real.exp (-(ε * t)) * -ε) t := by
      simpa using hlin.exp
    have h := (hexp.div_const ε).neg
    refine h.congr_deriv ?_
    field_simp
  have hcont : ContinuousWithinAt (fun v : ℝ => -(Real.exp (-(ε * v)) / ε)) (Ici a) a := by
    have : ContinuousAt (fun v : ℝ => -(Real.exp (-(ε * v)) / ε)) a := by fun_prop
    exact this.continuousWithinAt
  have hint : IntegrableOn (fun t : ℝ => Real.exp (-(ε * t))) (Ioi a) volume :=
    integrableOn_exp_neg_mul_Ioi hε a
  have htend : Tendsto (fun v : ℝ => -(Real.exp (-(ε * v)) / ε)) atTop (nhds 0) := by
    have hmul : Tendsto (fun v : ℝ => -(ε * v)) atTop atBot := by
      have h0 : Tendsto (fun v : ℝ => ε * v) atTop atTop :=
        Filter.Tendsto.const_mul_atTop hε tendsto_id
      exact tendsto_neg_atTop_atBot.comp h0
    have hexp : Tendsto (fun v : ℝ => Real.exp (-(ε * v))) atTop (nhds 0) :=
      Real.tendsto_exp_atBot.comp hmul
    have := (hexp.div_const ε).neg
    simpa using this
  have h := integral_Ioi_of_hasDerivAt_of_tendsto hcont hderiv hint htend
  rw [h]
  ring

theorem integral_exp_neg_mul_div_Ioi_le {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    (∫ t in Ioi (1 : ℝ), Real.exp (-(ε * t)) / t) ≤ Real.log (1 / ε) + 1 := by
  have hR : (1 : ℝ) ≤ 1 / ε := by
    rw [le_div_iff₀ hε]; linarith
  have hsplit : Set.Ioc (1 : ℝ) (1 / ε) ∪ Set.Ioi (1 / ε) = Set.Ioi (1 : ℝ) :=
    Set.Ioc_union_Ioi_eq_Ioi hR
  have hint : IntegrableOn (fun t : ℝ => Real.exp (-(ε * t)) / t) (Ioi (1 : ℝ)) volume := by
    have hmaj : IntegrableOn (fun t : ℝ => Real.exp (-(ε * t))) (Ioi (1 : ℝ)) volume :=
      integrableOn_exp_neg_mul_Ioi hε 1
    have hmeas : AEStronglyMeasurable (fun t : ℝ => Real.exp (-(ε * t)) / t)
        (volume.restrict (Ioi (1 : ℝ))) := by
      refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
      intro t ht
      have ht0 : 0 < t := lt_trans zero_lt_one ht
      exact ContinuousAt.continuousWithinAt
        (ContinuousAt.div (by fun_prop) continuousAt_id (ne_of_gt ht0))
    refine hmaj.mono' hmeas ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht1 : (1 : ℝ) ≤ t := le_of_lt ht
    have ht0 : (0 : ℝ) < t := lt_of_lt_of_le zero_lt_one ht1
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), div_le_iff₀ ht0]
    nlinarith [Real.exp_pos (-(ε * t))]
  have hIoc : IntegrableOn (fun t : ℝ => Real.exp (-(ε * t)) / t)
      (Set.Ioc (1 : ℝ) (1 / ε)) volume := hint.mono_set (fun t ht => lt_of_lt_of_le ht.1 le_rfl)
  have hIoi : IntegrableOn (fun t : ℝ => Real.exp (-(ε * t)) / t)
      (Set.Ioi (1 / ε)) volume := hint.mono_set (Set.Ioi_subset_Ioi hR)
  have hdisj : Disjoint (Set.Ioc (1 : ℝ) (1 / ε)) (Set.Ioi (1 / ε)) := by
    rw [Set.disjoint_left]
    intro x hx hx'
    exact absurd hx' (not_lt.mpr hx.2)
  have hunion := MeasureTheory.setIntegral_union (μ := volume)
    (f := fun t : ℝ => Real.exp (-(ε * t)) / t) hdisj measurableSet_Ioi hIoc hIoi
  rw [hsplit] at hunion
  -- the head
  have hhead : (∫ t in Set.Ioc (1 : ℝ) (1 / ε), Real.exp (-(ε * t)) / t) ≤ Real.log (1 / ε) := by
    have hbound : IntegrableOn (fun t : ℝ => 1 / t) (Set.Ioc (1 : ℝ) (1 / ε)) volume := by
      have h := intervalIntegrable_one_div_pos zero_lt_one hR
      rwa [intervalIntegrable_iff_integrableOn_Ioc_of_le hR] at h
    have hmono : (∫ t in Set.Ioc (1 : ℝ) (1 / ε), Real.exp (-(ε * t)) / t)
        ≤ ∫ t in Set.Ioc (1 : ℝ) (1 / ε), 1 / t := by
      refine MeasureTheory.integral_mono_of_nonneg ?_ hbound ?_
      · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
        have ht0 : (0 : ℝ) < t := lt_trans zero_lt_one ht.1
        positivity
      · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
        have ht0 : (0 : ℝ) < t := lt_trans zero_lt_one ht.1
        have hexp : Real.exp (-(ε * t)) ≤ 1 := by
          rw [Real.exp_le_one_iff]
          nlinarith [le_of_lt ht.1]
        gcongr
    have hval : (∫ t in Set.Ioc (1 : ℝ) (1 / ε), 1 / t) = Real.log (1 / ε) := by
      rw [← intervalIntegral.integral_of_le hR, integral_one_div_of_pos zero_lt_one (by positivity)]
      rw [div_one]
    rw [hval] at hmono
    exact hmono
  -- the tail
  have htail : (∫ t in Set.Ioi (1 / ε), Real.exp (-(ε * t)) / t) ≤ 1 := by
    have hbound : IntegrableOn (fun t : ℝ => ε * Real.exp (-(ε * t)))
        (Set.Ioi (1 / ε)) volume := (integrableOn_exp_neg_mul_Ioi hε (1 / ε)).const_mul _
    have hmono : (∫ t in Set.Ioi (1 / ε), Real.exp (-(ε * t)) / t)
        ≤ ∫ t in Set.Ioi (1 / ε), ε * Real.exp (-(ε * t)) := by
      refine MeasureTheory.integral_mono_of_nonneg ?_ hbound ?_
      · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        have htlt : 1 / ε < t := ht
        have ht0 : (0 : ℝ) < t := lt_of_lt_of_le (by positivity) (le_of_lt htlt)
        positivity
      · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        have htlt : 1 / ε < t := ht
        have ht0 : (0 : ℝ) < t := lt_of_lt_of_le (by positivity) (le_of_lt htlt)
        have hinv : 1 / t ≤ ε := by
          rw [div_le_iff₀ ht0]
          have h1 : (1 : ℝ) / ε ≤ t := le_of_lt htlt
          rw [div_le_iff₀ hε] at h1
          nlinarith
        have hexppos : (0 : ℝ) < Real.exp (-(ε * t)) := Real.exp_pos _
        calc Real.exp (-(ε * t)) / t = Real.exp (-(ε * t)) * (1 / t) := by ring
          _ ≤ Real.exp (-(ε * t)) * ε := by
              exact mul_le_mul_of_nonneg_left hinv (le_of_lt hexppos)
          _ = ε * Real.exp (-(ε * t)) := by ring
    have hval : (∫ t in Set.Ioi (1 / ε), ε * Real.exp (-(ε * t))) = Real.exp (-1 : ℝ) := by
      rw [MeasureTheory.integral_const_mul, integral_exp_neg_mul_Ioi hε]
      have : ε * (1 / ε) = 1 := by field_simp
      rw [this]
      field_simp
    rw [hval] at hmono
    refine hmono.trans ?_
    have : Real.exp (-1 : ℝ) ≤ 1 := by
      rw [Real.exp_le_one_iff]; norm_num
    exact this
  linarith [hunion.ge, hunion.le, hhead, htail]


/-! ## Identifying the damped tail -/

theorem integrableOn_damped_cos_div {ε : ℝ} (hε : 0 < ε) :
    IntegrableOn (fun t : ℝ => Real.exp (-(ε * t)) * Real.cos t / t) (Ioi (1 : ℝ)) volume := by
  have hmaj : IntegrableOn (fun t : ℝ => Real.exp (-(ε * t))) (Ioi (1 : ℝ)) volume :=
    integrableOn_exp_neg_mul_Ioi hε 1
  have hmeas : AEStronglyMeasurable (fun t : ℝ => Real.exp (-(ε * t)) * Real.cos t / t)
      (volume.restrict (Ioi (1 : ℝ))) := by
    refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    intro t ht
    have ht0 : 0 < t := lt_trans zero_lt_one ht
    exact ContinuousAt.continuousWithinAt
      (ContinuousAt.div (by fun_prop) continuousAt_id (ne_of_gt ht0))
  refine hmaj.mono' hmeas ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have ht1 : (1 : ℝ) ≤ t := le_of_lt ht
  have ht0 : (0 : ℝ) < t := lt_of_lt_of_le zero_lt_one ht1
  have hexppos : (0 : ℝ) < Real.exp (-(ε * t)) := Real.exp_pos _
  rw [Real.norm_eq_abs, abs_div, abs_mul, abs_of_pos ht0,
    abs_of_pos hexppos, div_le_iff₀ ht0]
  have hc : |Real.cos t| ≤ 1 := Real.abs_cos_le_one t
  nlinarith

theorem integrableOn_dampedIBPKernel {ε : ℝ} (hε : 0 < ε) :
    IntegrableOn (fun t : ℝ => Real.sin t * (Real.exp (-(ε * t)) * (ε / t + 1 / t ^ 2)))
      (Ioi (1 : ℝ)) volume := by
  have h1 : IntegrableOn (fun t : ℝ => ε * Real.exp (-(ε * t))) (Ioi (1 : ℝ)) volume :=
    (integrableOn_exp_neg_mul_Ioi hε 1).const_mul _
  have h2 : IntegrableOn (fun t : ℝ => (1 : ℝ) / t ^ 2) (Ioi (1 : ℝ)) volume := by
    have hcont : ContinuousWithinAt (fun v : ℝ => -v⁻¹) (Ici (1 : ℝ)) 1 :=
      (continuousAt_inv₀ one_ne_zero).neg.continuousWithinAt
    have hderiv : ∀ t ∈ Ioi (1 : ℝ), HasDerivAt (fun v : ℝ => -v⁻¹) ((1 : ℝ) / t ^ 2) t := by
      intro t ht
      have ht0 : 0 < t := lt_trans zero_lt_one ht
      refine ((hasDerivAt_inv (ne_of_gt ht0)).neg).congr_deriv ?_
      field_simp
    have hpos : ∀ t ∈ Ioi (1 : ℝ), (0 : ℝ) ≤ (1 : ℝ) / t ^ 2 := by
      intro t ht
      have ht0 : 0 < t := lt_trans zero_lt_one ht
      positivity
    have htend : Tendsto (fun v : ℝ => -v⁻¹) atTop (nhds 0) := by
      simpa using (tendsto_inv_atTop_zero (𝕜 := ℝ)).neg
    exact MeasureTheory.integrableOn_Ioi_deriv_of_nonneg hcont hderiv hpos htend
  have hmeas : AEStronglyMeasurable
      (fun t : ℝ => Real.sin t * (Real.exp (-(ε * t)) * (ε / t + 1 / t ^ 2)))
      (volume.restrict (Ioi (1 : ℝ))) := by
    refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    intro t ht
    have ht0 : 0 < t := lt_trans zero_lt_one ht
    refine ContinuousAt.continuousWithinAt ?_
    refine ContinuousAt.mul (by fun_prop) (ContinuousAt.mul (by fun_prop) ?_)
    refine ContinuousAt.add ?_ ?_
    · exact ContinuousAt.div continuousAt_const continuousAt_id (ne_of_gt ht0)
    · exact ContinuousAt.div continuousAt_const (by fun_prop) (by positivity)
  refine (h1.add h2).mono' hmeas ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have ht1 : (1 : ℝ) ≤ t := le_of_lt ht
  have ht0 : (0 : ℝ) < t := lt_of_lt_of_le zero_lt_one ht1
  have hexppos : (0 : ℝ) < Real.exp (-(ε * t)) := Real.exp_pos _
  have hexple : Real.exp (-(ε * t)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    nlinarith
  have hs : |Real.sin t| ≤ 1 := Real.abs_sin_le_one t
  have hεt : ε / t ≤ ε := by
    rw [div_le_iff₀ ht0]
    nlinarith
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos hexppos]
  have habs : |ε / t + 1 / t ^ 2| = ε / t + 1 / t ^ 2 := by
    apply abs_of_nonneg
    positivity
  rw [habs]
  have hstep : Real.exp (-(ε * t)) * (ε / t + 1 / t ^ 2)
      ≤ ε * Real.exp (-(ε * t)) + 1 / t ^ 2 := by
    have h1' : Real.exp (-(ε * t)) * (ε / t) ≤ ε * Real.exp (-(ε * t)) := by
      have := mul_le_mul_of_nonneg_left hεt (le_of_lt hexppos)
      linarith [this]
    have h2' : Real.exp (-(ε * t)) * (1 / t ^ 2) ≤ 1 / t ^ 2 := by
      have hnn : (0 : ℝ) ≤ 1 / t ^ 2 := by positivity
      nlinarith
    nlinarith
  simp only [Pi.add_apply]
  have hXnn : (0 : ℝ) ≤ Real.exp (-(ε * t)) * (ε / t + 1 / t ^ 2) := by positivity
  calc |Real.sin t| * (Real.exp (-(ε * t)) * (ε / t + 1 / t ^ 2))
      ≤ 1 * (Real.exp (-(ε * t)) * (ε / t + 1 / t ^ 2)) :=
        mul_le_mul_of_nonneg_right hs hXnn
    _ = Real.exp (-(ε * t)) * (ε / t + 1 / t ^ 2) := one_mul _
    _ ≤ ε * Real.exp (-(ε * t)) + 1 / t ^ 2 := hstep

theorem integral_damped_cos_div_Ioi {ε : ℝ} (hε : 0 < ε) :
    (∫ t in Ioi (1 : ℝ), Real.exp (-(ε * t)) * Real.cos t / t) = dampedCosTail ε := by
  have hL : Tendsto (fun y : ℝ => ∫ t in (1 : ℝ)..y, Real.exp (-(ε * t)) * Real.cos t / t)
      atTop (nhds (∫ t in Ioi (1 : ℝ), Real.exp (-(ε * t)) * Real.cos t / t)) :=
    MeasureTheory.intervalIntegral_tendsto_integral_Ioi (a := (1 : ℝ))
      (integrableOn_damped_cos_div hε) tendsto_id
  have hK : Tendsto (fun y : ℝ =>
      ∫ t in (1 : ℝ)..y, Real.sin t * (Real.exp (-(ε * t)) * (ε / t + 1 / t ^ 2)))
      atTop (nhds (∫ t in Ioi (1 : ℝ),
        Real.sin t * (Real.exp (-(ε * t)) * (ε / t + 1 / t ^ 2)))) :=
    MeasureTheory.intervalIntegral_tendsto_integral_Ioi (a := (1 : ℝ))
      (integrableOn_dampedIBPKernel hε) tendsto_id
  have hboundary : Tendsto (fun y : ℝ => Real.exp (-(ε * y)) * Real.sin y / y)
      atTop (nhds 0) := by
    refine squeeze_zero_norm' (a := fun y : ℝ => |y|⁻¹) ?_ ?_
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with y hy
      have hexppos : (0 : ℝ) < Real.exp (-(ε * y)) := Real.exp_pos _
      have hexple : Real.exp (-(ε * y)) ≤ 1 := by
        rw [Real.exp_le_one_iff]
        nlinarith
      rw [Real.norm_eq_abs, abs_div, abs_mul, abs_of_pos hexppos, abs_of_pos hy,
        div_le_iff₀ hy, inv_mul_cancel₀ (ne_of_gt hy)]
      nlinarith [Real.abs_sin_le_one y, abs_nonneg (Real.sin y)]
    · have habs : Tendsto (fun y : ℝ => |y|) atTop atTop := by
        simpa using (tendsto_abs_atTop_atTop (G := ℝ))
      exact tendsto_inv_atTop_zero.comp habs
  have hcomb := (hboundary.sub (tendsto_const_nhds
    (x := Real.exp (-ε) * Real.sin 1))).add hK
  rw [zero_sub] at hcomb
  refine tendsto_nhds_unique hL ?_
  refine hcomb.congr' ?_
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with y hy
  rw [intervalIntegral_damped_cos_div ε hy]


/-! ## The Abel limit of the damped tail -/

theorem tendsto_mul_log_inv : Tendsto (fun ε : ℝ => ε * (Real.log (1 / ε) + 1))
    (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
  have hu : Tendsto (fun ε : ℝ => ε⁻¹) (nhdsWithin (0 : ℝ) (Ioi 0)) atTop :=
    tendsto_inv_nhdsGT_zero
  have hlog : Tendsto (fun u : ℝ => (Real.log u + 1) / u) atTop (nhds 0) := by
    have hbase : Tendsto (fun v : ℝ => Real.log v / v) atTop (nhds 0) := by
      simpa [Function.comp_def] using Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
    have hconst : Tendsto (fun v : ℝ => (1 : ℝ) / v) atTop (nhds 0) :=
      Filter.Tendsto.div_atTop tendsto_const_nhds tendsto_id
    have := hbase.add hconst
    simpa [add_div] using this
  have hcomp := hlog.comp hu
  refine hcomp.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hε0 : ε ≠ 0 := ne_of_gt hε
  simp only [Function.comp_apply, one_div]
  field_simp

theorem tendsto_dampedCosTail :
    Tendsto dampedCosTail (nhdsWithin 0 (Ioi 0)) (nhds cosTailValue) := by
  have hsmall : ∀ᶠ ε in nhdsWithin (0 : ℝ) (Ioi 0), ε ≤ 1 :=
    Filter.eventually_of_mem
      (mem_nhdsWithin_of_mem_nhds (Iic_mem_nhds (by norm_num))) (fun x hx => hx)
  -- the `1/t²` piece
  have hbound2 : IntegrableOn (fun t : ℝ => (1 : ℝ) / t ^ 2) (Ioi (1 : ℝ)) volume := by
    have hcont : ContinuousWithinAt (fun v : ℝ => -v⁻¹) (Ici (1 : ℝ)) 1 :=
      (continuousAt_inv₀ one_ne_zero).neg.continuousWithinAt
    have hderiv : ∀ t ∈ Ioi (1 : ℝ), HasDerivAt (fun v : ℝ => -v⁻¹) ((1 : ℝ) / t ^ 2) t := by
      intro t ht
      have ht0 : 0 < t := lt_trans zero_lt_one ht
      refine ((hasDerivAt_inv (ne_of_gt ht0)).neg).congr_deriv ?_
      field_simp
    have hpos : ∀ t ∈ Ioi (1 : ℝ), (0 : ℝ) ≤ (1 : ℝ) / t ^ 2 := by
      intro t ht
      have ht0 : 0 < t := lt_trans zero_lt_one ht
      positivity
    have htend : Tendsto (fun v : ℝ => -v⁻¹) atTop (nhds 0) := by
      simpa using (tendsto_inv_atTop_zero (𝕜 := ℝ)).neg
    exact MeasureTheory.integrableOn_Ioi_deriv_of_nonneg hcont hderiv hpos htend
  have hDCT : Tendsto
      (fun ε : ℝ => ∫ t in Ioi (1 : ℝ), Real.sin t * (Real.exp (-(ε * t)) * (1 / t ^ 2)))
      (nhdsWithin 0 (Ioi 0)) (nhds (∫ t in Ioi (1 : ℝ), Real.sin t * (1 / t ^ 2))) := by
    refine MeasureTheory.tendsto_integral_filter_of_dominated_convergence
      (fun t : ℝ => (1 : ℝ) / t ^ 2) ?_ ?_ hbound2 ?_
    · filter_upwards [self_mem_nhdsWithin] with ε _
      refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
      intro t ht
      have ht0 : 0 < t := lt_trans zero_lt_one ht
      refine ContinuousAt.continuousWithinAt ?_
      exact ContinuousAt.mul (by fun_prop)
        (ContinuousAt.mul (by fun_prop)
          (ContinuousAt.div continuousAt_const (by fun_prop) (by positivity)))
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      have hεpos : (0 : ℝ) < ε := hε
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have ht1 : (1 : ℝ) ≤ t := le_of_lt ht
      have ht0 : (0 : ℝ) < t := lt_of_lt_of_le zero_lt_one ht1
      have hexppos : (0 : ℝ) < Real.exp (-(ε * t)) := Real.exp_pos _
      have hexple : Real.exp (-(ε * t)) ≤ 1 := by
        rw [Real.exp_le_one_iff]
        nlinarith [hεpos.le]
      have hs : |Real.sin t| ≤ 1 := Real.abs_sin_le_one t
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos hexppos,
        abs_of_nonneg (by positivity : (0:ℝ) ≤ (1:ℝ) / t ^ 2)]
      have hnn : (0 : ℝ) ≤ (1 : ℝ) / t ^ 2 := by positivity
      have hXnn : (0 : ℝ) ≤ Real.exp (-(ε * t)) * (1 / t ^ 2) := by positivity
      calc |Real.sin t| * (Real.exp (-(ε * t)) * (1 / t ^ 2))
          ≤ 1 * (Real.exp (-(ε * t)) * (1 / t ^ 2)) := mul_le_mul_of_nonneg_right hs hXnn
        _ = Real.exp (-(ε * t)) * (1 / t ^ 2) := one_mul _
        _ ≤ 1 * (1 / t ^ 2) := mul_le_mul_of_nonneg_right hexple hnn
        _ = 1 / t ^ 2 := one_mul _
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have ht0 : (0 : ℝ) < t := lt_trans zero_lt_one ht
      have hexp : Tendsto (fun ε : ℝ => Real.exp (-(ε * t))) (nhdsWithin 0 (Ioi 0)) (nhds 1) := by
        have hcont : ContinuousAt (fun ε : ℝ => Real.exp (-(ε * t))) 0 := by fun_prop
        have h1 : Tendsto (fun ε : ℝ => Real.exp (-(ε * t)))
            (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds (Real.exp (-(0 * t)))) :=
          hcont.tendsto.mono_left nhdsWithin_le_nhds
        simpa using h1
      have := (hexp.const_mul (1 / t ^ 2)).const_mul (Real.sin t)
      simpa [mul_comm] using this
  -- the `ε/t` piece
  have hεpiece : Tendsto
      (fun ε : ℝ => ε * ∫ t in Ioi (1 : ℝ), Real.sin t * (Real.exp (-(ε * t)) / t))
      (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
    refine squeeze_zero_norm' (a := fun ε : ℝ => ε * (Real.log (1 / ε) + 1)) ?_
      tendsto_mul_log_inv
    filter_upwards [self_mem_nhdsWithin, hsmall] with ε hε hε1
    have hint : IntegrableOn (fun t : ℝ => Real.exp (-(ε * t)) / t) (Ioi (1 : ℝ)) volume := by
      have hmaj : IntegrableOn (fun t : ℝ => Real.exp (-(ε * t))) (Ioi (1 : ℝ)) volume :=
        integrableOn_exp_neg_mul_Ioi hε 1
      have hmeas : AEStronglyMeasurable (fun t : ℝ => Real.exp (-(ε * t)) / t)
          (volume.restrict (Ioi (1 : ℝ))) := by
        refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
        intro t ht
        have ht0 : 0 < t := lt_trans zero_lt_one ht
        exact ContinuousAt.continuousWithinAt
          (ContinuousAt.div (by fun_prop) continuousAt_id (ne_of_gt ht0))
      refine hmaj.mono' hmeas ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have ht1 : (1 : ℝ) ≤ t := le_of_lt ht
      have ht0 : (0 : ℝ) < t := lt_of_lt_of_le zero_lt_one ht1
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), div_le_iff₀ ht0]
      nlinarith [Real.exp_pos (-(ε * t))]
    have hnormle : ‖∫ t in Ioi (1 : ℝ), Real.sin t * (Real.exp (-(ε * t)) / t)‖
        ≤ ∫ t in Ioi (1 : ℝ), Real.exp (-(ε * t)) / t := by
      have hle : ∀ᵐ t ∂(volume.restrict (Ioi (1 : ℝ))),
          ‖Real.sin t * (Real.exp (-(ε * t)) / t)‖ ≤ Real.exp (-(ε * t)) / t := by
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        have ht1 : (1 : ℝ) ≤ t := le_of_lt ht
        have ht0 : (0 : ℝ) < t := lt_of_lt_of_le zero_lt_one ht1
        have hnn : (0 : ℝ) ≤ Real.exp (-(ε * t)) / t := by positivity
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hnn]
        nlinarith [Real.abs_sin_le_one t, abs_nonneg (Real.sin t)]
      calc ‖∫ t in Ioi (1 : ℝ), Real.sin t * (Real.exp (-(ε * t)) / t)‖
          ≤ ∫ t in Ioi (1 : ℝ), ‖Real.sin t * (Real.exp (-(ε * t)) / t)‖ :=
            MeasureTheory.norm_integral_le_integral_norm _
        _ ≤ ∫ t in Ioi (1 : ℝ), Real.exp (-(ε * t)) / t := by
            refine MeasureTheory.integral_mono_of_nonneg ?_ hint hle
            filter_upwards with t using norm_nonneg _
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos hε]
    have hbnd := integral_exp_neg_mul_div_Ioi_le hε hε1
    have hεpos : (0 : ℝ) < ε := hε
    have habs : |∫ t in Ioi (1 : ℝ), Real.sin t * (Real.exp (-(ε * t)) / t)|
        ≤ Real.log (1 / ε) + 1 := by
      rw [← Real.norm_eq_abs]
      linarith [hnormle, hbnd]
    exact mul_le_mul_of_nonneg_left habs hεpos.le
  -- the boundary term
  have hboundary : Tendsto (fun ε : ℝ => -(Real.exp (-ε) * Real.sin 1))
      (nhdsWithin 0 (Ioi 0)) (nhds (-Real.sin 1)) := by
    have hcont : ContinuousAt (fun ε : ℝ => -(Real.exp (-ε) * Real.sin 1)) 0 := by fun_prop
    have h1 : Tendsto (fun ε : ℝ => -(Real.exp (-ε) * Real.sin 1))
        (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds (-(Real.exp (-0 : ℝ) * Real.sin 1))) :=
      hcont.tendsto.mono_left nhdsWithin_le_nhds
    simpa using h1
  have hsum := (hboundary.add hεpiece).add hDCT
  rw [add_zero] at hsum
  have hval : (∫ t in Ioi (1 : ℝ), Real.sin t * (1 / t ^ 2))
      = ∫ t in Ioi (1 : ℝ), Real.sin t / t ^ 2 := by
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi ?_
    intro t _
    dsimp only
    ring
  rw [hval] at hsum
  rw [cosTailValue]
  refine hsum.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hsplit : (∫ t in Ioi (1 : ℝ),
      Real.sin t * (Real.exp (-(ε * t)) * (ε / t + 1 / t ^ 2)))
      = (ε * ∫ t in Ioi (1 : ℝ), Real.sin t * (Real.exp (-(ε * t)) / t))
        + ∫ t in Ioi (1 : ℝ), Real.sin t * (Real.exp (-(ε * t)) * (1 / t ^ 2)) := by
    have hA : IntegrableOn
        (fun t : ℝ => ε * (Real.sin t * (Real.exp (-(ε * t)) / t))) (Ioi (1 : ℝ)) volume := by
      have hmaj : IntegrableOn (fun t : ℝ => Real.exp (-(ε * t))) (Ioi (1 : ℝ)) volume :=
        integrableOn_exp_neg_mul_Ioi hε 1
      have hmeas : AEStronglyMeasurable
          (fun t : ℝ => ε * (Real.sin t * (Real.exp (-(ε * t)) / t)))
          (volume.restrict (Ioi (1 : ℝ))) := by
        refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
        intro t ht
        have ht0 : 0 < t := lt_trans zero_lt_one ht
        refine ContinuousAt.continuousWithinAt ?_
        exact ContinuousAt.mul continuousAt_const
          (ContinuousAt.mul (by fun_prop)
            (ContinuousAt.div (by fun_prop) continuousAt_id (ne_of_gt ht0)))
      refine (hmaj.const_mul ε).mono' hmeas ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have ht1 : (1 : ℝ) ≤ t := le_of_lt ht
      have ht0 : (0 : ℝ) < t := lt_of_lt_of_le zero_lt_one ht1
      have hexppos : (0 : ℝ) < Real.exp (-(ε * t)) := Real.exp_pos _
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos hε, abs_div, abs_of_pos hexppos,
        abs_of_pos ht0]
      have hdiv : Real.exp (-(ε * t)) / t ≤ Real.exp (-(ε * t)) := by
        rw [div_le_iff₀ ht0]
        nlinarith
      have hs : |Real.sin t| ≤ 1 := Real.abs_sin_le_one t
      have hXnn : (0 : ℝ) ≤ Real.exp (-(ε * t)) / t := by positivity
      have hεpos : (0 : ℝ) < ε := hε
      nlinarith [mul_le_mul_of_nonneg_right hs hXnn, hdiv, hεpos, hXnn,
        Real.exp_pos (-(ε * t))]
    have hB : IntegrableOn
        (fun t : ℝ => Real.sin t * (Real.exp (-(ε * t)) * (1 / t ^ 2))) (Ioi (1 : ℝ)) volume := by
      have hmeas : AEStronglyMeasurable
          (fun t : ℝ => Real.sin t * (Real.exp (-(ε * t)) * (1 / t ^ 2)))
          (volume.restrict (Ioi (1 : ℝ))) := by
        refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
        intro t ht
        have ht0 : 0 < t := lt_trans zero_lt_one ht
        refine ContinuousAt.continuousWithinAt ?_
        exact ContinuousAt.mul (by fun_prop)
          (ContinuousAt.mul (by fun_prop)
            (ContinuousAt.div continuousAt_const (by fun_prop) (by positivity)))
      refine hbound2.mono' hmeas ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have ht1 : (1 : ℝ) ≤ t := le_of_lt ht
      have ht0 : (0 : ℝ) < t := lt_of_lt_of_le zero_lt_one ht1
      have hexppos : (0 : ℝ) < Real.exp (-(ε * t)) := Real.exp_pos _
      have hεpos : (0 : ℝ) < ε := hε
      have hexple : Real.exp (-(ε * t)) ≤ 1 := by
        rw [Real.exp_le_one_iff]
        nlinarith [hεpos.le]
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos hexppos,
        abs_of_nonneg (by positivity : (0:ℝ) ≤ (1:ℝ) / t ^ 2)]
      have hs : |Real.sin t| ≤ 1 := Real.abs_sin_le_one t
      have hnn : (0 : ℝ) ≤ (1 : ℝ) / t ^ 2 := by positivity
      have hXnn : (0 : ℝ) ≤ Real.exp (-(ε * t)) * (1 / t ^ 2) := by positivity
      calc |Real.sin t| * (Real.exp (-(ε * t)) * (1 / t ^ 2))
          ≤ 1 * (Real.exp (-(ε * t)) * (1 / t ^ 2)) := mul_le_mul_of_nonneg_right hs hXnn
        _ = Real.exp (-(ε * t)) * (1 / t ^ 2) := one_mul _
        _ ≤ 1 * (1 / t ^ 2) := mul_le_mul_of_nonneg_right hexple hnn
        _ = 1 / t ^ 2 := one_mul _
    rw [← MeasureTheory.integral_const_mul]
    rw [← MeasureTheory.integral_add hA hB]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi ?_
    intro t ht
    have ht0 : (0 : ℝ) < t := lt_trans zero_lt_one ht
    dsimp only
    field_simp
  rw [dampedCosTail, hsplit]
  ring


/-! ## The damped Frullani evaluation -/

theorem integral_dampedFrullani {ε : ℝ} (hε : 0 < ε) :
    (∫ t in Ioi (0 : ℝ), (Real.exp (-t) - Real.exp (-(ε * t)) * Real.cos t) / t)
      = Real.log (Real.sqrt (ε ^ 2 + 1)) := by
  have hare : (0 : ℝ) < (1 : ℂ).re := by simp
  have hbre : (0 : ℝ) < ((ε : ℂ) - Complex.I).re := by
    simp only [Complex.sub_re, Complex.ofReal_re, Complex.I_re, sub_zero]
    exact hε
  have hfr := integral_frullani hare hbre
  have hint := integrableOn_frullani hare hbre
  have hcomm := Complex.reCLM.integral_comp_comm hint
  simp only [Complex.reCLM_apply] at hcomm
  have hre : ∀ t ∈ Ioi (0 : ℝ),
      ((Complex.exp (-((1 : ℂ) * (t : ℂ))) - Complex.exp (-(((ε : ℂ) - Complex.I) * (t : ℂ))))
        / (t : ℂ)).re
        = (Real.exp (-t) - Real.exp (-(ε * t)) * Real.cos t) / t := by
    intro t ht
    have hr : (-(((ε : ℂ) - Complex.I) * (t : ℂ))).re = -(ε * t) := by
      simp only [Complex.neg_re, Complex.mul_re, Complex.sub_re, Complex.sub_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
      ring
    have him : (-(((ε : ℂ) - Complex.I) * (t : ℂ))).im = t := by
      simp only [Complex.neg_im, Complex.mul_im, Complex.sub_re, Complex.sub_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
      ring
    have h1 : (Complex.exp (-((1 : ℂ) * (t : ℂ)))).re = Real.exp (-t) := by
      rw [show (-((1 : ℂ) * (t : ℂ))) = ((-t : ℝ) : ℂ) from by push_cast; ring,
        ← Complex.ofReal_exp, Complex.ofReal_re]
    have h2 : (Complex.exp (-(((ε : ℂ) - Complex.I) * (t : ℂ)))).re
        = Real.exp (-(ε * t)) * Real.cos t := by
      rw [Complex.exp_re, hr, him]
    rw [div_ofReal_re, Complex.sub_re, h1, h2]
  have hleft : (∫ t in Ioi (0 : ℝ),
      (Real.exp (-t) - Real.exp (-(ε * t)) * Real.cos t) / t)
      = (∫ t in Ioi (0 : ℝ),
          (Complex.exp (-((1 : ℂ) * (t : ℂ)))
            - Complex.exp (-(((ε : ℂ) - Complex.I) * (t : ℂ)))) / (t : ℂ)).re := by
    rw [← hcomm]
    exact (MeasureTheory.setIntegral_congr_fun measurableSet_Ioi hre).symm
  rw [hleft, hfr, Complex.log_one, sub_zero, Complex.log_re]
  congr 1
  rw [Complex.norm_eq_sqrt_sq_add_sq]
  simp


/-! ## The head block and the vanishing identity -/

/-- The head block `∫_0^1 (e^{-t} - cos t)/t dt`. -/
def gaussCosineHead : ℝ := ∫ t in Ioc (0 : ℝ) 1, (Real.exp (-t) - Real.cos t) / t

theorem abs_exp_sub_cos_le {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) {ε : ℝ} (hε : 0 < ε)
    (hε1 : ε ≤ 1) :
    |Real.exp (-t) - Real.exp (-(ε * t)) * Real.cos t| ≤ 3 * t := by
  have h1 : |Real.exp (-t) - 1| ≤ t := by
    have hle : Real.exp (-t) ≤ 1 := by
      rw [Real.exp_le_one_iff]; linarith
    have hge : 1 - t ≤ Real.exp (-t) := by
      have := Real.add_one_le_exp (-t)
      linarith
    rw [abs_of_nonpos (by linarith)]
    linarith
  have h2 : |1 - Real.exp (-(ε * t))| ≤ t := by
    have hle : Real.exp (-(ε * t)) ≤ 1 := by
      rw [Real.exp_le_one_iff]; nlinarith
    have hge : 1 - ε * t ≤ Real.exp (-(ε * t)) := by
      have := Real.add_one_le_exp (-(ε * t))
      linarith
    rw [abs_of_nonneg (by linarith)]
    nlinarith
  have h3 : |Real.exp (-(ε * t)) * (1 - Real.cos t)| ≤ t := by
    have hexp1 : Real.exp (-(ε * t)) ≤ 1 := by
      rw [Real.exp_le_one_iff]; nlinarith
    have hexppos : (0 : ℝ) < Real.exp (-(ε * t)) := Real.exp_pos _
    have hcos : 1 - Real.cos t ≤ t ^ 2 / 2 := by
      have := Real.one_sub_sq_div_two_le_cos (x := t)
      linarith
    have hcosnn : (0 : ℝ) ≤ 1 - Real.cos t := by
      have := Real.cos_le_one t
      linarith
    rw [abs_of_nonneg (by positivity)]
    nlinarith
  have hsplit : Real.exp (-t) - Real.exp (-(ε * t)) * Real.cos t
      = (Real.exp (-t) - 1) + (1 - Real.exp (-(ε * t)))
        + Real.exp (-(ε * t)) * (1 - Real.cos t) := by ring
  rw [hsplit]
  calc |Real.exp (-t) - 1 + (1 - Real.exp (-(ε * t)))
        + Real.exp (-(ε * t)) * (1 - Real.cos t)|
      ≤ |Real.exp (-t) - 1 + (1 - Real.exp (-(ε * t)))|
        + |Real.exp (-(ε * t)) * (1 - Real.cos t)| := abs_add_le _ _
    _ ≤ (|Real.exp (-t) - 1| + |1 - Real.exp (-(ε * t))|)
        + |Real.exp (-(ε * t)) * (1 - Real.cos t)| := by
        gcongr
        exact abs_add_le _ _
    _ ≤ (t + t) + t := by linarith
    _ = 3 * t := by ring

theorem integrableOn_headBlock {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    IntegrableOn (fun t : ℝ => (Real.exp (-t) - Real.exp (-(ε * t)) * Real.cos t) / t)
      (Ioc (0 : ℝ) 1) volume := by
  have hmeas : AEStronglyMeasurable
      (fun t : ℝ => (Real.exp (-t) - Real.exp (-(ε * t)) * Real.cos t) / t)
      (volume.restrict (Ioc (0 : ℝ) 1)) := by
    refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioc
    intro t ht
    have ht0 : 0 < t := ht.1
    exact ContinuousAt.continuousWithinAt
      (ContinuousAt.div (by fun_prop) continuousAt_id (ne_of_gt ht0))
  have hconst : IntegrableOn (fun _ : ℝ => (3 : ℝ)) (Ioc (0 : ℝ) 1) volume :=
    continuous_const.integrableOn_Ioc
  refine hconst.mono' hmeas ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  have ht0 : (0 : ℝ) < t := ht.1
  rw [Real.norm_eq_abs, abs_div, abs_of_pos ht0, div_le_iff₀ ht0]
  have := abs_exp_sub_cos_le (le_of_lt ht0) ht.2 hε hε1
  nlinarith

theorem integrableOn_tailBlock {ε : ℝ} (hε : 0 < ε) :
    IntegrableOn (fun t : ℝ => (Real.exp (-t) - Real.exp (-(ε * t)) * Real.cos t) / t)
      (Ioi (1 : ℝ)) volume := by
  have h1 : IntegrableOn (fun t : ℝ => Real.exp (-t) / t) (Ioi (1 : ℝ)) volume :=
    integrableOn_exp_neg_div_Ioi_one
  have h2 : IntegrableOn (fun t : ℝ => Real.exp (-(ε * t)) * Real.cos t / t)
      (Ioi (1 : ℝ)) volume := integrableOn_damped_cos_div hε
  refine (h1.sub h2).congr_fun (fun t ht => ?_) measurableSet_Ioi
  have ht0 : (0 : ℝ) < t := lt_trans zero_lt_one ht
  simp only [Pi.sub_apply]
  field_simp

theorem integral_tailBlock {ε : ℝ} (hε : 0 < ε) :
    (∫ t in Ioi (1 : ℝ), (Real.exp (-t) - Real.exp (-(ε * t)) * Real.cos t) / t)
      = frullaniTail - dampedCosTail ε := by
  have h1 : IntegrableOn (fun t : ℝ => Real.exp (-t) / t) (Ioi (1 : ℝ)) volume :=
    integrableOn_exp_neg_div_Ioi_one
  have h2 : IntegrableOn (fun t : ℝ => Real.exp (-(ε * t)) * Real.cos t / t)
      (Ioi (1 : ℝ)) volume := integrableOn_damped_cos_div hε
  have hcongr : (∫ t in Ioi (1 : ℝ),
      (Real.exp (-t) - Real.exp (-(ε * t)) * Real.cos t) / t)
      = ∫ t in Ioi (1 : ℝ),
          (Real.exp (-t) / t - Real.exp (-(ε * t)) * Real.cos t / t) := by
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi ?_
    intro t ht
    have ht0 : (0 : ℝ) < t := lt_trans zero_lt_one ht
    dsimp only
    field_simp
  rw [hcongr, MeasureTheory.integral_sub h1 h2, integral_damped_cos_div_Ioi hε]
  rfl

theorem gaussCosineIdentity : gaussCosineHead + frullaniTail = cosTailValue := by
  have hsmall : ∀ᶠ ε in nhdsWithin (0 : ℝ) (Ioi 0), ε ≤ 1 :=
    Filter.eventually_of_mem
      (mem_nhdsWithin_of_mem_nhds (Iic_mem_nhds (by norm_num))) (fun x hx => hx)
  have hheadmeas : ∀ ε : ℝ, AEStronglyMeasurable
      (fun t : ℝ => (Real.exp (-t) - Real.exp (-(ε * t)) * Real.cos t) / t)
      (volume.restrict (Ioc (0 : ℝ) 1)) := by
    intro ε
    refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioc
    intro t ht
    have ht0 : 0 < t := ht.1
    exact ContinuousAt.continuousWithinAt
      (ContinuousAt.div (by fun_prop) continuousAt_id (ne_of_gt ht0))
  have hheadDCT : Tendsto
      (fun ε : ℝ => ∫ t in Ioc (0 : ℝ) 1,
        (Real.exp (-t) - Real.exp (-(ε * t)) * Real.cos t) / t)
      (nhdsWithin 0 (Ioi 0)) (nhds gaussCosineHead) := by
    have hconst : Integrable (fun _ : ℝ => (3 : ℝ)) (volume.restrict (Ioc (0 : ℝ) 1)) :=
      continuous_const.integrableOn_Ioc
    refine MeasureTheory.tendsto_integral_filter_of_dominated_convergence
      (fun _ : ℝ => (3 : ℝ)) ?_ ?_ hconst ?_
    · filter_upwards [self_mem_nhdsWithin] with ε _
      exact hheadmeas ε
    · filter_upwards [self_mem_nhdsWithin, hsmall] with ε hε hε1
      have hεpos : (0 : ℝ) < ε := hε
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      have ht0 : (0 : ℝ) < t := ht.1
      rw [Real.norm_eq_abs, abs_div, abs_of_pos ht0, div_le_iff₀ ht0]
      have := abs_exp_sub_cos_le (le_of_lt ht0) ht.2 hεpos hε1
      nlinarith
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      have ht0 : (0 : ℝ) < t := ht.1
      have hexp : Tendsto (fun ε : ℝ => Real.exp (-(ε * t))) (nhdsWithin 0 (Ioi 0)) (nhds 1) := by
        have hcont : ContinuousAt (fun ε : ℝ => Real.exp (-(ε * t))) 0 := by fun_prop
        have h1 : Tendsto (fun ε : ℝ => Real.exp (-(ε * t)))
            (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds (Real.exp (-(0 * t)))) :=
          hcont.tendsto.mono_left nhdsWithin_le_nhds
        simpa using h1
      have hnum : Tendsto (fun ε : ℝ => Real.exp (-t) - Real.exp (-(ε * t)) * Real.cos t)
          (nhdsWithin 0 (Ioi 0)) (nhds (Real.exp (-t) - Real.cos t)) := by
        have := (tendsto_const_nhds (x := Real.exp (-t))
          (f := nhdsWithin (0 : ℝ) (Ioi 0))).sub (hexp.mul_const (Real.cos t))
        simpa using this
      exact hnum.div_const t
  have hRHS : Tendsto
      (fun ε : ℝ => (∫ t in Ioc (0 : ℝ) 1,
          (Real.exp (-t) - Real.exp (-(ε * t)) * Real.cos t) / t)
        + frullaniTail - dampedCosTail ε)
      (nhdsWithin 0 (Ioi 0)) (nhds (gaussCosineHead + frullaniTail - cosTailValue)) :=
    (hheadDCT.add tendsto_const_nhds).sub tendsto_dampedCosTail
  have hLHS : Tendsto (fun ε : ℝ => Real.log (Real.sqrt (ε ^ 2 + 1)))
      (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
    have hcont : ContinuousAt (fun ε : ℝ => Real.log (Real.sqrt (ε ^ 2 + 1))) 0 := by
      refine ContinuousAt.log ?_ ?_
      · fun_prop
      · simp
    have h1 : Tendsto (fun ε : ℝ => Real.log (Real.sqrt (ε ^ 2 + 1)))
        (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds (Real.log (Real.sqrt ((0 : ℝ) ^ 2 + 1)))) :=
      hcont.tendsto.mono_left nhdsWithin_le_nhds
    simpa using h1
  have hEq : Tendsto (fun ε : ℝ => Real.log (Real.sqrt (ε ^ 2 + 1)))
      (nhdsWithin 0 (Ioi 0)) (nhds (gaussCosineHead + frullaniTail - cosTailValue)) := by
    refine hRHS.congr' ?_
    filter_upwards [self_mem_nhdsWithin, hsmall] with ε hε hε1
    have hεpos : (0 : ℝ) < ε := hε
    have hsplit : Set.Ioc (0 : ℝ) 1 ∪ Set.Ioi (1 : ℝ) = Set.Ioi (0 : ℝ) :=
      Set.Ioc_union_Ioi_eq_Ioi zero_le_one
    have hdisj : Disjoint (Set.Ioc (0 : ℝ) 1) (Set.Ioi (1 : ℝ)) := by
      rw [Set.disjoint_left]
      intro x hx hx'
      exact absurd hx' (not_lt.mpr hx.2)
    have hunion := MeasureTheory.setIntegral_union (μ := volume)
      (f := fun t : ℝ => (Real.exp (-t) - Real.exp (-(ε * t)) * Real.cos t) / t)
      hdisj measurableSet_Ioi (integrableOn_headBlock hεpos hε1) (integrableOn_tailBlock hεpos)
    rw [hsplit] at hunion
    rw [← integral_dampedFrullani hεpos, hunion, integral_tailBlock hεpos]
    ring
  have := tendsto_nhds_unique hLHS hEq
  linarith


/-! ## The cosine integral near the origin -/

/-- The regularized profile `(cos t - 1)/t`, extended by `0` at the origin. -/
def cosMinusOneProfile (t : ℝ) : ℝ := if t = 0 then 0 else (Real.cos t - 1) / t

theorem cosMinusOneProfile_of_ne {t : ℝ} (ht : t ≠ 0) :
    cosMinusOneProfile t = (Real.cos t - 1) / t := if_neg ht

@[simp]
theorem cosMinusOneProfile_zero : cosMinusOneProfile 0 = 0 := if_pos rfl

theorem abs_cosMinusOneProfile_le {t : ℝ} (ht : 0 ≤ t) : |cosMinusOneProfile t| ≤ t / 2 := by
  rcases eq_or_lt_of_le ht with rfl | ht0
  · simp [cosMinusOneProfile]
  · rw [cosMinusOneProfile_of_ne (ne_of_gt ht0), abs_div, abs_of_pos ht0,
      div_le_iff₀ ht0]
    have hupper : Real.cos t ≤ 1 := Real.cos_le_one t
    have hlower : 1 - t ^ 2 / 2 ≤ Real.cos t := by
      have := Real.one_sub_sq_div_two_le_cos (x := t)
      linarith
    rw [abs_of_nonpos (by linarith)]
    nlinarith

theorem intervalIntegrable_cosMinusOneProfile {x : ℝ} (hx : 0 ≤ x) :
    IntervalIntegrable cosMinusOneProfile volume 0 x := by
  have hmeas : AEStronglyMeasurable cosMinusOneProfile (volume.restrict (Ioc (0 : ℝ) x)) := by
    refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioc
    intro t ht
    have ht0 : 0 < t := ht.1
    have hcong : ∀ u ∈ Ioc (0 : ℝ) x, cosMinusOneProfile u = (Real.cos u - 1) / u := by
      intro u hu
      rw [cosMinusOneProfile_of_ne (ne_of_gt hu.1)]
    refine ContinuousWithinAt.congr ?_ hcong (hcong t ht)
    exact ContinuousAt.continuousWithinAt
      (ContinuousAt.div (by fun_prop) continuousAt_id (ne_of_gt ht0))
  have hconst : IntegrableOn (fun _ : ℝ => x / 2) (Ioc (0 : ℝ) x) volume :=
    continuous_const.integrableOn_Ioc
  have hIoc : IntegrableOn cosMinusOneProfile (Ioc (0 : ℝ) x) volume := by
    refine hconst.mono' hmeas ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    rw [Real.norm_eq_abs]
    refine (abs_cosMinusOneProfile_le (le_of_lt ht.1)).trans ?_
    have : t ≤ x := ht.2
    linarith
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hx]
  exact hIoc

/-- `∫_0^x (cos t - 1)/t dt`. -/
def cinNeg (x : ℝ) : ℝ := ∫ t in (0 : ℝ)..x, cosMinusOneProfile t

theorem abs_cinNeg_le {x : ℝ} (hx : 0 ≤ x) : |cinNeg x| ≤ x ^ 2 / 2 := by
  have hbound : ∀ t ∈ Set.uIoc (0 : ℝ) x, ‖cosMinusOneProfile t‖ ≤ x / 2 := by
    intro t ht
    rw [Set.uIoc_of_le hx] at ht
    rw [Real.norm_eq_abs]
    refine (abs_cosMinusOneProfile_le (le_of_lt ht.1)).trans ?_
    have : t ≤ x := ht.2
    linarith
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (C := x / 2) hbound
  rw [cinNeg, Real.norm_eq_abs] at *
  rw [sub_zero, abs_of_nonneg hx] at h
  calc |∫ t in (0 : ℝ)..x, cosMinusOneProfile t| ≤ x / 2 * x := h
    _ = x ^ 2 / 2 := by ring

theorem tendsto_cinNeg_nhdsWithin_zero {a : ℝ} (ha : 0 < a) :
    Tendsto (fun ε : ℝ => cinNeg (a * ε)) (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
  refine squeeze_zero_norm' (a := fun ε : ℝ => (a * ε) ^ 2 / 2) ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    have hεpos : (0 : ℝ) < ε := hε
    rw [Real.norm_eq_abs]
    exact abs_cinNeg_le (by positivity)
  · have hid : Tendsto (fun ε : ℝ => ε) (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds 0) :=
      tendsto_id.mono_left nhdsWithin_le_nhds
    have : Tendsto (fun ε : ℝ => (a * ε) ^ 2 / 2) (nhdsWithin (0 : ℝ) (Ioi 0))
        (nhds ((a * 0) ^ 2 / 2)) := by
      exact (((hid.const_mul a).pow 2).div_const 2)
    simpa using this

theorem intervalIntegral_cos_div_head {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) :
    (∫ t in x..(1 : ℝ), Real.cos t / t) = -Real.log x + (cinNeg 1 - cinNeg x) := by
  have hcongr : (∫ t in x..(1 : ℝ), Real.cos t / t)
      = ∫ t in x..(1 : ℝ), (1 / t + cosMinusOneProfile t) := by
    refine intervalIntegral.integral_congr ?_
    intro t ht
    rw [Set.uIcc_of_le hx1] at ht
    have ht0 : (0 : ℝ) < t := lt_of_lt_of_le hx ht.1
    dsimp only
    rw [cosMinusOneProfile_of_ne (ne_of_gt ht0)]
    field_simp
    ring
  have hsplit : (∫ t in x..(1 : ℝ), cosMinusOneProfile t) = cinNeg 1 - cinNeg x := by
    have hadd := intervalIntegral.integral_add_adjacent_intervals
      (μ := volume) (f := cosMinusOneProfile) (a := 0) (b := x) (c := 1)
      (intervalIntegrable_cosMinusOneProfile (le_of_lt hx))
      ((intervalIntegrable_cosMinusOneProfile zero_le_one).mono_set
        (by rw [Set.uIcc_of_le hx1, Set.uIcc_of_le zero_le_one]
            exact Set.Icc_subset_Icc (le_of_lt hx) le_rfl))
    rw [← cinNeg, ← cinNeg] at hadd
    linarith
  rw [hcongr, intervalIntegral.integral_add (intervalIntegrable_one_div_pos hx hx1)
      ((intervalIntegrable_cosMinusOneProfile zero_le_one).mono_set
        (by rw [Set.uIcc_of_le hx1, Set.uIcc_of_le zero_le_one]
            exact Set.Icc_subset_Icc (le_of_lt hx) le_rfl)),
    hsplit, integral_one_div_of_pos hx zero_lt_one, one_div, Real.log_inv]

theorem neg_cinNeg_one : -cinNeg 1 = gaussCosineHead + frullaniHead := by
  have hcongr : (∫ t in (0 : ℝ)..1, (-cosMinusOneProfile t - einProfile t))
      = ∫ t in Ioc (0 : ℝ) 1, (Real.exp (-t) - Real.cos t) / t := by
    rw [← intervalIntegral.integral_of_le zero_le_one]
    refine intervalIntegral.integral_congr ?_
    intro t ht
    rw [Set.uIcc_of_le zero_le_one] at ht
    dsimp only
    rcases eq_or_lt_of_le ht.1 with h0 | h0
    · rw [← h0]
      simp [einProfile]
    · rw [cosMinusOneProfile_of_ne (ne_of_gt h0), einProfile, if_neg (ne_of_gt h0)]
      field_simp
      ring
  have hnegint : IntervalIntegrable (fun t : ℝ => -cosMinusOneProfile t) volume 0 1 :=
    (intervalIntegrable_cosMinusOneProfile zero_le_one).neg
  have hsplit : (∫ t in (0 : ℝ)..1, (-cosMinusOneProfile t - einProfile t))
      = -cinNeg 1 - frullaniHead := by
    rw [intervalIntegral.integral_sub hnegint (intervalIntegrable_einProfile zero_le_one),
      intervalIntegral.integral_neg, ← cinNeg, ← frullaniHead]
  rw [hsplit] at hcongr
  rw [gaussCosineHead, ← hcongr]
  ring

/-- The improper cosine integral tail `-Ci(x) = ∫_x^∞ cos t/t dt`, in closed form. -/
def cosIntegralTail (x : ℝ) : ℝ := (∫ t in x..(1 : ℝ), Real.cos t / t) + cosTailValue

theorem tendsto_cosIntegralTail {x : ℝ} (hx : 0 < x) :
    Tendsto (fun y : ℝ => ∫ t in x..y, Real.cos t / t) atTop (nhds (cosIntegralTail x)) := by
  have hcos : ∀ p q : ℝ, 0 < p → 0 < q →
      IntervalIntegrable (fun t : ℝ => Real.cos t / t) volume p q := by
    intro p q hp hq
    refine ContinuousOn.intervalIntegrable ?_
    intro t ht
    have ht0 : 0 < t := by
      rcases le_total p q with h | h
      · rw [Set.uIcc_of_le h] at ht; exact lt_of_lt_of_le hp ht.1
      · rw [Set.uIcc_of_ge h] at ht; exact lt_of_lt_of_le hq ht.1
    exact ContinuousAt.continuousWithinAt
      (ContinuousAt.div (by fun_prop) continuousAt_id (ne_of_gt ht0))
  have hshift : ∀ y : ℝ, 1 ≤ y →
      (∫ t in x..y, Real.cos t / t)
        = (∫ t in x..(1 : ℝ), Real.cos t / t) + ∫ t in (1 : ℝ)..y, Real.cos t / t := by
    intro y hy
    exact (intervalIntegral.integral_add_adjacent_intervals
      (hcos x 1 hx zero_lt_one) (hcos 1 y zero_lt_one (lt_of_lt_of_le zero_lt_one hy))).symm
  rw [cosIntegralTail]
  refine (tendsto_const_nhds.add tendsto_intervalIntegral_cos_div).congr' ?_
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with y hy
  exact (hshift y hy).symm

/-- **Suzuki's archimedean cancellation.**  For every `a > 0`,

`∫_ε^∞ e^{-u}/u du - ∫_{aε}^∞ cos u/u du → log a`  as `ε → 0+`.

Both terms diverge like `-log ε`; their difference is the finite `log a`.  This is the source's
`E₁(ε) + Ci(|z/2|ε) = log|z| - log 2 + O(ε)`. -/
theorem tendsto_expIntegralTail_sub_cosIntegralTail {a : ℝ} (ha : 0 < a) :
    Tendsto (fun ε : ℝ => (∫ t in Ioi ε, Real.exp (-t) / t) - cosIntegralTail (a * ε))
      (nhdsWithin 0 (Ioi 0)) (nhds (Real.log a)) := by
  have hsmall : ∀ᶠ ε in nhdsWithin (0 : ℝ) (Ioi 0), ε ≤ 1 :=
    Filter.eventually_of_mem
      (mem_nhdsWithin_of_mem_nhds (Iic_mem_nhds (by norm_num))) (fun x hx => hx)
  have hsmalla : ∀ᶠ ε in nhdsWithin (0 : ℝ) (Ioi 0), a * ε ≤ 1 := by
    have hid : Tendsto (fun ε : ℝ => ε) (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds 0) :=
      tendsto_id.mono_left nhdsWithin_le_nhds
    have hcont : Tendsto (fun ε : ℝ => a * ε) (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds 0) := by
      simpa using hid.const_mul a
    exact hcont.eventually_le_const (by norm_num)
  have hconst : -Real.eulerMascheroniConstant - cinNeg 1 - cosTailValue = 0 := by
    have h3 := neg_cinNeg_one
    have h4 := gaussCosineIdentity
    have h5 := frullani_eq_eulerMascheroni
    linarith
  have hlimit : Tendsto (fun ε : ℝ => Real.log a + ein ε + cinNeg (a * ε))
      (nhdsWithin 0 (Ioi 0)) (nhds (Real.log a)) := by
    have := ((tendsto_const_nhds (x := Real.log a)
      (f := nhdsWithin (0 : ℝ) (Ioi 0))).add tendsto_ein_nhdsWithin_zero).add
      (tendsto_cinNeg_nhdsWithin_zero ha)
    simpa using this
  refine hlimit.congr' ?_
  filter_upwards [self_mem_nhdsWithin, hsmall, hsmalla] with ε hε hε1 haε1
  have hεpos : (0 : ℝ) < ε := hε
  have haεpos : (0 : ℝ) < a * ε := by positivity
  have h1 := integral_expNegDiv_Ioi_small hεpos hε1
  have h2 := intervalIntegral_cos_div_head haεpos haε1
  have hlog : Real.log (a * ε) = Real.log a + Real.log ε :=
    Real.log_mul (ne_of_gt ha) (ne_of_gt hεpos)
  rw [h1, cosIntegralTail, h2, hlog]
  linarith

end RHTower
