import GaloisForLFunctions.RHTower.EulerDeletionPowerSumRemainder
import Mathlib.Topology.Algebra.Order.Floor
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-!
# The first coefficient of the ordinary arithmetic remainder

The periodic Bernoulli kernel has mean `-1/12`. Its centered primitive is bounded
and vanishes at every integer, so integration by parts retains an explicit tail
with one extra power of decay. The resulting coefficient is derived from the
literal ordinary power-sum remainder without an assumed asymptotic.
-/

noncomputable section
open MeasureTheory Set Filter Topology
namespace RHTower.DeletionMixedRefinement

private theorem continuous_bernoulli : Continuous RHTower.bernoulliPeriodic := by
  have hc : Continuous (fun x : ℝ => (x^2-x)/2) := by fun_prop
  exact hc.continuousOn.comp_fract'' (by norm_num)

private def centeredBernoulli (x : ℝ) : ℝ := RHTower.bernoulliPeriodic x + 1/12

private theorem continuous_centeredBernoulli : Continuous centeredBernoulli :=
  continuous_bernoulli.add continuous_const

private theorem centeredBernoulli_mean : (∫ x in (0:ℝ)..1, centeredBernoulli x) = 0 := by
  have he : (∫ x in (0:ℝ)..1, centeredBernoulli x) =
      ∫ x in (0:ℝ)..1, (x^2-x)/2+1/12 := by
    apply intervalIntegral.integral_congr
    intro x hxi
    have hxi' : x ∈ Icc (0:ℝ) 1 := by simpa using hxi
    by_cases hx : x = 1
    · subst x
      norm_num [centeredBernoulli, RHTower.bernoulliPeriodic]
    · have hf := Int.fract_eq_self.mpr ⟨hxi'.1, lt_of_le_of_ne hxi'.2 hx⟩
      simp only [centeredBernoulli, RHTower.bernoulliPeriodic, hf]
  rw [he]
  have hd : ∀ x ∈ Set.uIcc (0:ℝ) 1,
      HasDerivAt (fun y:ℝ => y^3/6-y^2/4+y/12) ((x^2-x)/2+1/12) x := by
    intro x _
    convert! ((((hasDerivAt_id x).pow 3).div_const 6).sub
      (((hasDerivAt_id x).pow 2).div_const 4)).add ((hasDerivAt_id x).div_const 12) using 1
    norm_num
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd (by
    apply Continuous.intervalIntegrable
    fun_prop)]
  norm_num

/-- A bounded periodic primitive of the centered ordinary remainder kernel. -/
def bernoulliCenteredPrimitive (x : ℝ) : ℝ := ∫ y in (0:ℝ)..x, centeredBernoulli y

private theorem primitive_deriv (x : ℝ) :
    HasDerivAt bernoulliCenteredPrimitive (centeredBernoulli x) x :=
  intervalIntegral.integral_hasDerivAt_right
    (continuous_centeredBernoulli.intervalIntegrable 0 x)
    (continuous_centeredBernoulli.stronglyMeasurableAtFilter _ _)
    continuous_centeredBernoulli.continuousAt

private theorem primitive_continuous : Continuous bernoulliCenteredPrimitive :=
  continuous_iff_continuousAt.mpr (fun x => (primitive_deriv x).continuousAt)

private theorem primitive_periodic : Function.Periodic bernoulliCenteredPrimitive 1 := by
  have hp : Function.Periodic centeredBernoulli 1 := by
    intro x
    simp [centeredBernoulli, RHTower.bernoulliPeriodic, Int.fract_add_one]
  intro x
  have ha := intervalIntegral.integral_add_adjacent_intervals
    (continuous_centeredBernoulli.intervalIntegrable (μ := volume) 0 x)
    (continuous_centeredBernoulli.intervalIntegrable (μ := volume) x (x+1))
  have ht := hp.intervalIntegral_add_eq x 0
  rw [zero_add] at ht
  simp only [bernoulliCenteredPrimitive, ← ha, ht, centeredBernoulli_mean, add_zero]

private theorem primitive_nat (N : ℕ) : bernoulliCenteredPrimitive N = 0 := by
  simpa [bernoulliCenteredPrimitive] using primitive_periodic.nat_mul_eq N

/-- The centered primitive is bounded uniformly on the whole real line. -/
theorem abs_bernoulliCenteredPrimitive_le (x : ℝ) : |bernoulliCenteredPrimitive x| ≤ 1 := by
  have hs := primitive_periodic.sub_int_mul_eq (x := x) ⌊x⌋
  have he : x - (⌊x⌋:ℝ)*1 = Int.fract x := by rw [mul_one]; rfl
  rw [he] at hs
  rw [← hs]
  have hb : ∀ y ∈ Set.uIoc (0:ℝ) (Int.fract x), ‖centeredBernoulli y‖ ≤ (1:ℝ) := by
    intro y _
    rw [Real.norm_eq_abs, abs_le]
    have h := abs_le.mp (RHTower.abs_bernoulliPeriodic_le y)
    dsimp [centeredBernoulli]
    constructor <;> linarith
  have h := intervalIntegral.norm_integral_le_of_norm_le_const hb
  rw [Real.norm_eq_abs, sub_zero, abs_of_nonneg (Int.fract_nonneg x)] at h
  exact h.trans (by nlinarith [Int.fract_lt_one x])

private theorem primitive_cpow_integrable {s:ℂ} (hs : -1<s.re) {N:ℕ} (hN:1≤N) :
    IntegrableOn (fun x:ℝ => (bernoulliCenteredPrimitive x:ℂ)*(x:ℂ)^(-s-3)) (Ioi (N:ℝ)) := by
  have hNp : (0:ℝ)<N := by exact_mod_cast (by omega : 0<N)
  have hi := integrableOn_Ioi_rpow_of_lt (by linarith : -s.re-3 < -1) hNp
  apply Integrable.mono hi
  · apply ContinuousOn.aestronglyMeasurable _ measurableSet_Ioi
    intro x hx
    apply ContinuousWithinAt.mul
    · exact (Complex.continuous_ofReal.comp primitive_continuous).continuousAt.continuousWithinAt
    · exact (hasDerivAt_ofReal_cpow_const (ne_of_gt (hNp.trans hx)) (by
        intro he
        have := congrArg Complex.re he
        simp at this
        linarith)).continuousAt.continuousWithinAt
  · rw [ae_restrict_iff' measurableSet_Ioi]
    filter_upwards with x hx
    have hxp := hNp.trans hx
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      Complex.norm_cpow_eq_rpow_re_of_pos hxp]
    have he : (-s-3).re = -s.re-3 := by simp
    rw [he, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hxp.le _)]
    exact mul_le_of_le_one_left (Real.rpow_nonneg hxp.le _)
      (abs_bernoulliCenteredPrimitive_le x)

/-- The cubic primitive tail after removing the Bernoulli mean. -/
def centeredPrimitiveTail (N:ℕ) (s:ℂ) : ℂ :=
  ∫ x in Ioi (N:ℝ), (bernoulliCenteredPrimitive x:ℂ)*(x:ℂ)^(-s-3)

/-- An explicit extra power of decay for the primitive tail. -/
theorem norm_centeredPrimitiveTail_le {s:ℂ} (hs:-1<s.re) {N:ℕ} (hN:1≤N) :
    ‖centeredPrimitiveTail N s‖ ≤ (N:ℝ)^(-s.re-2)/(s.re+2) := by
  have hNp : (0:ℝ)<N := by exact_mod_cast (by omega : 0<N)
  have hi := integrableOn_Ioi_rpow_of_lt (by linarith : -s.re-3 < -1) hNp
  have hb : ‖centeredPrimitiveTail N s‖ ≤ ∫ x in Ioi (N:ℝ), x^(-s.re-3) := by
    apply norm_integral_le_of_norm_le hi
    rw [ae_restrict_iff' measurableSet_Ioi]
    filter_upwards with x hx
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      Complex.norm_cpow_eq_rpow_re_of_pos (hNp.trans hx)]
    have he : (-s-3).re = -s.re-3 := by simp
    rw [he]
    exact mul_le_of_le_one_left (Real.rpow_nonneg (hNp.trans hx).le _)
      (abs_bernoulliCenteredPrimitive_le x)
  refine hb.trans_eq ?_
  rw [integral_Ioi_rpow_of_lt (by linarith : -s.re-3 < -1) hNp]
  rw [show -s.re-3+1 = -(s.re+2) by ring, neg_div_neg_eq]
  congr 2
  ring

private theorem centered_tail_eq {s:ℂ} (hs:-1<s.re) {N:ℕ} (hN:1≤N) :
    (∫ x in Ioi (N:ℝ), (centeredBernoulli x:ℂ)*(x:ℂ)^(-s-2)) =
      (s+2)*centeredPrimitiveTail N s := by
  have hNp : (0:ℝ)<N := by exact_mod_cast (by omega : 0<N)
  have hre : (-s-2).re < -1 := by simp; linarith
  have hrne : -s-2 ≠ 0 := by intro h; rw [h] at hre; norm_num at hre
  have hd (x:ℝ) (hx:0<x) : HasDerivAt (fun y:ℝ => (y:ℂ)^(-s-2))
      ((-s-2)*(x:ℂ)^(-s-3)) x := by
    simpa only [show -s-2-1 = -s-3 by ring] using
      hasDerivAt_ofReal_cpow_const hx.ne' hrne
  have hi : IntegrableOn (fun x:ℝ => (centeredBernoulli x:ℂ)*(x:ℂ)^(-s-2))
      (Ioi (N:ℝ)) := by
    have hb := RHTower.integrableOn_bernoulli_cpow hs hN
    have hc := (integrableOn_Ioi_cpow_of_lt hre hNp).const_mul (1/12:ℂ)
    refine (hb.add hc).congr_fun ?_ measurableSet_Ioi
    intro x _
    dsimp [centeredBernoulli]
    push_cast
    rw [show -s-1-1 = -s-2 by ring]
    ring
  have hprod0 : Tendsto (fun x:ℝ => (bernoulliCenteredPrimitive x:ℂ)*(x:ℂ)^(-s-2))
      (𝓝[>] (N:ℝ)) (𝓝 0) := by
    have hc := ((primitive_deriv (N:ℝ)).ofReal_comp.mul (hd N hNp)).continuousAt
    simpa [primitive_nat, Pi.mul_def] using hc.tendsto.mono_left nhdsWithin_le_nhds
  have hprodt : Tendsto (fun x:ℝ => (bernoulliCenteredPrimitive x:ℂ)*(x:ℂ)^(-s-2))
      atTop (𝓝 0) := by
    have ht := tendsto_rpow_neg_atTop (by linarith : 0<s.re+2)
    rw [show -(s.re+2) = -s.re-2 by ring] at ht
    apply squeeze_zero_norm' ?_ ht
    filter_upwards [eventually_gt_atTop (0:ℝ)] with x hx
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      Complex.norm_cpow_eq_rpow_re_of_pos hx]
    have he : (-s-2).re = -s.re-2 := by simp
    rw [he]
    exact mul_le_of_le_one_left (Real.rpow_nonneg hx.le _)
      (abs_bernoulliCenteredPrimitive_le x)
  have hip := (primitive_cpow_integrable hs hN).const_mul (-s-2)
  have hb := MeasureTheory.integral_Ioi_mul_deriv_eq_deriv_mul
    (u := fun x:ℝ => (x:ℂ)^(-s-2))
    (u' := fun x:ℝ => (-s-2)*(x:ℂ)^(-s-3))
    (v := fun x:ℝ => (bernoulliCenteredPrimitive x:ℂ))
    (v' := fun x:ℝ => (centeredBernoulli x:ℂ))
    (a := (N:ℝ)) (a' := (0:ℂ)) (b' := (0:ℂ))
    (fun x hx => hd x (hNp.trans hx)) (fun x _ => (primitive_deriv x).ofReal_comp)
    (by simpa [Pi.mul_def, mul_comm] using hi)
    (by simpa [IntegrableOn, Pi.mul_def, mul_assoc, mul_left_comm, mul_comm] using hip)
    (by simpa [Pi.mul_def, mul_comm] using hprod0)
    (by simpa [Pi.mul_def, mul_comm] using hprodt)
  simp only [zero_sub, sub_zero] at hb
  calc
    _ = ∫ x in Ioi (N:ℝ), (x:ℂ)^(-s-2)*(centeredBernoulli x:ℂ) := by
      apply integral_congr_ae; filter_upwards with x; ring
    _ = -(∫ x in Ioi (N:ℝ), ((-s-2)*(x:ℂ)^(-s-3))*(bernoulliCenteredPrimitive x:ℂ)) := hb
    _ = (s+2)*centeredPrimitiveTail N s := by
      rw [show (fun x:ℝ => ((-s-2)*(x:ℂ)^(-s-3))*(bernoulliCenteredPrimitive x:ℂ)) =
        (fun x:ℝ => (-s-2)*((bernoulliCenteredPrimitive x:ℂ)*(x:ℂ)^(-s-3))) by
          funext x; ring, integral_const_mul]
      dsimp [centeredPrimitiveTail]
      ring

/-- The Bernoulli mean and the full primitive correction, including integer endpoints. -/
theorem bernoulliTail_eq_mean_add_primitive {s:ℂ} (hs:-1<s.re) {N:ℕ} (hN:1≤N) :
    RHTower.zetaBernoulliTail N s =
      -(N:ℂ)^(-s-1)/(12*(s+1))+(s+2)*centeredPrimitiveTail N s := by
  have hNp : (0:ℝ)<N := by exact_mod_cast (by omega : 0<N)
  have hre : (-s-2).re < -1 := by simp; linarith
  have hs1 : s+1 ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  have hi := RHTower.integrableOn_bernoulli_cpow hs hN
  have hc := (integrableOn_Ioi_cpow_of_lt hre hNp).const_mul (1/12:ℂ)
  have he : (∫ x in Ioi (N:ℝ), (centeredBernoulli x:ℂ)*(x:ℂ)^(-s-2)) =
      RHTower.zetaBernoulliTail N s + (1/12:ℂ)*(∫ x in Ioi (N:ℝ), (x:ℂ)^(-s-2)) := by
    rw [RHTower.zetaBernoulliTail, ← integral_const_mul, ← integral_add hi hc]
    apply integral_congr_ae
    filter_upwards with x
    dsimp [centeredBernoulli]
    push_cast
    rw [show -s-1-1 = -s-2 by ring]
    ring
  rw [centered_tail_eq hs hN, integral_Ioi_cpow_of_lt hre hNp,
    show -s-2+1 = -s-1 by ring] at he
  have hden : -s-1 = -(s+1) := by ring
  rw [hden, neg_div_neg_eq] at he
  rw [hden]
  push_cast at he
  field_simp [hs1] at he ⊢
  linear_combination -he

/-- The first asymptotic coefficient of the actual ordinary power-sum remainder. -/
theorem powerSumRemainder_eq_mean_add_primitive {s:ℂ} (hs:-1<s.re) (hs1:s≠1)
    {N:ℕ} (hN:1≤N) :
    powerSumRemainder s N = -s/12*(N:ℂ)^(-s-1)+
      (s*(s+1)*(s+2))*centeredPrimitiveTail N s := by
  have hsp : s+1 ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  rw [powerSumRemainder_eq_bernoulli hs hs1 hN, bernoulliTail_eq_mean_add_primitive hs hN]
  field_simp

/-- An explicit error bound for the first coefficient, with no assumed asymptotic. -/
theorem norm_powerSumRemainder_sub_mean_le {s:ℂ} (hs:-1<s.re) (hs1:s≠1)
    {N:ℕ} (hN:1≤N) :
    ‖powerSumRemainder s N - (-s/12*(N:ℂ)^(-s-1))‖ ≤
      (‖s*(s+1)*(s+2)‖/(s.re+2))*(N:ℝ)^(-s.re-2) := by
  rw [powerSumRemainder_eq_mean_add_primitive hs hs1 hN, add_sub_cancel_left, norm_mul]
  exact (mul_le_mul_of_nonneg_left (norm_centeredPrimitiveTail_le hs hN)
    (norm_nonneg _)).trans_eq (by ring)

/-- Multiplying by the endpoint power recovers the exact first ordinary remainder coefficient. -/
theorem tendsto_powerSumRemainder_mul_endpoint {s:ℂ} (hs:-1<s.re) (hs1:s≠1) :
    Tendsto (fun N:ℕ => powerSumRemainder s N*(N:ℂ)^(s+1)) atTop (𝓝 (-s/12)) := by
  have ht : Tendsto (fun N:ℕ =>
      (‖s*(s+1)*(s+2)‖/(s.re+2))*(N:ℝ)^(-1:ℝ)) atTop (𝓝 0) := by
    simpa only [Function.comp_apply, mul_zero] using
      ((tendsto_rpow_neg_atTop (by norm_num : (0:ℝ)<1)).comp
        (tendsto_natCast_atTop_atTop (R:=ℝ))).const_mul (‖s*(s+1)*(s+2)‖/(s.re+2))
  have he : Tendsto (fun N:ℕ =>
      (powerSumRemainder s N-(-s/12*(N:ℂ)^(-s-1)))*(N:ℂ)^(s+1)) atTop (𝓝 0) := by
    apply squeeze_zero_norm' ?_ ht
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hNp : (0:ℝ)<N := by exact_mod_cast (by omega : 0<N)
    rw [norm_mul, Complex.norm_natCast_cpow_of_pos (by omega)]
    refine (mul_le_mul_of_nonneg_right (norm_powerSumRemainder_sub_mean_le hs hs1 hN)
      (Real.rpow_nonneg hNp.le _)).trans_eq ?_
    rw [mul_assoc, ← Real.rpow_add hNp]
    congr 2
    simp
    ring
  have hf := he.add_const (-s/12)
  simp only [zero_add] at hf
  apply hf.congr'
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hNc : (N:ℂ) ≠ 0 := by exact_mod_cast (by omega : N≠0)
  rw [sub_mul, mul_assoc, ← Complex.cpow_add _ _ hNc,
    show -s-1+(s+1) = 0 by ring, Complex.cpow_zero]
  ring

end RHTower.DeletionMixedRefinement
