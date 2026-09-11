import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

set_option backward.isDefEq.respectTransparency false
namespace RHTower
open MeasureTheory Set Filter Topology
noncomputable section

def pwGammaReciprocalMomentKernel (a : ℝ) (k : ℕ) (x : ℝ) : ℝ :=
  Real.exp (-x-a/x)/x^(k+3)

def pwGammaReciprocalMoment (a : ℝ) (k : ℕ) : ℝ :=
  ∫ x in Ioi (0:ℝ), pwGammaReciprocalMomentKernel a k x

def pwGammaReciprocalMomentRatio (a : ℝ) (k : ℕ) : ℝ :=
  pwGammaReciprocalMoment a k / ((k+1).factorial:ℝ)

private theorem pwGammaMoment_exp_bound (k : ℕ) {y : ℝ} (hy : 0<y) :
    Real.exp (-y) ≤ (k.factorial:ℝ)/y^k := by
  have hf : (0:ℝ)<k.factorial := by positivity
  have hb := Real.pow_div_factorial_le_exp y hy.le k
  rw [Real.exp_neg]
  apply (le_div_iff₀ (pow_pos hy k)).mpr
  rw [inv_mul_eq_div]
  exact (div_le_iff₀ (Real.exp_pos y)).mpr
    (by simpa only [mul_comm] using (div_le_iff₀ hf).mp hb)

theorem pwGammaReciprocalMomentKernel_pos (a : ℝ) (k : ℕ) {x : ℝ} (hx : 0<x) :
    0<pwGammaReciprocalMomentKernel a k x := div_pos (Real.exp_pos _) (pow_pos hx _)

theorem pwGammaReciprocalMomentKernel_bound (k : ℕ) {a x : ℝ}
    (ha : 0<a) (hx : 0<x) :
    pwGammaReciprocalMomentKernel a k x ≤
      (((k+3).factorial:ℝ)/a^(k+3))*Real.exp (-x) := by
  have he := pwGammaMoment_exp_bound (k+3) (div_pos ha hx)
  calc
    _ = Real.exp (-x)*Real.exp (-a/x)/x^(k+3) := by
      rw [pwGammaReciprocalMomentKernel, sub_eq_add_neg, Real.exp_add, neg_div]
    _ ≤ Real.exp (-x)*(((k+3).factorial:ℝ)/(a/x)^(k+3))/x^(k+3) := by
      gcongr
      simpa only [neg_div] using he
    _ = _ := by rw [div_pow]; field_simp

theorem pwGammaReciprocalMomentKernel_integrable (k : ℕ) {a : ℝ} (ha : 0<a) :
    IntegrableOn (pwGammaReciprocalMomentKernel a k) (Ioi 0) := by
  have hm : Measurable (pwGammaReciprocalMomentKernel a k) := by
    unfold pwGammaReciprocalMomentKernel
    fun_prop
  apply ((integrableOn_exp_neg_Ioi 0).const_mul
    (((k+3).factorial:ℝ)/a^(k+3))).mono' hm.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  rw [Real.norm_of_nonneg (pwGammaReciprocalMomentKernel_pos a k hx).le]
  exact pwGammaReciprocalMomentKernel_bound k ha hx

theorem pwGammaReciprocalMoment_pos (k : ℕ) {a : ℝ} (ha : 0<a) :
    0<pwGammaReciprocalMoment a k := by
  have hp : 0 ≤ᵐ[volume.restrict (Ioi (0:ℝ))] pwGammaReciprocalMomentKernel a k := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact (pwGammaReciprocalMomentKernel_pos a k hx).le
  unfold pwGammaReciprocalMoment
  rw [setIntegral_pos_iff_support_of_nonneg_ae hp (pwGammaReciprocalMomentKernel_integrable k ha)]
  have hs : Function.support (pwGammaReciprocalMomentKernel a k) ∩ Ioi (0:ℝ) = Ioi 0 := by
    apply inter_eq_right.mpr
    intro x hx
    exact (pwGammaReciprocalMomentKernel_pos a k hx).ne'
  rw [hs]
  simp

private theorem pwGammaMoment_involution {a : ℝ} (ha : 0<a) :
    Function.Involutive (fun x : ℝ => a/x) := by
  intro x
  simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
  field_simp

private theorem pwGammaMoment_image {a : ℝ} (ha : 0<a) :
    (fun x : ℝ => a/x) '' Ioi (0:ℝ) = Ioi 0 := by
  apply Set.Subset.antisymm
  · rintro y ⟨x,hx,rfl⟩
    exact div_pos ha hx
  · intro x hx
    exact ⟨a/x,div_pos ha hx,pwGammaMoment_involution ha x⟩

private theorem pwGammaMoment_deriv {a x : ℝ} (hx : 0<x) :
    HasDerivAt (fun y : ℝ => a/y) (-a/x^2) x := by
  simpa only [div_eq_mul_inv, mul_neg, neg_mul] using
    (hasDerivAt_inv hx.ne').const_mul a

theorem pwGammaReciprocalMoment_inversion (k : ℕ) {a : ℝ} (ha : 0<a) :
    pwGammaReciprocalMoment a k = (1/a^(k+2))*
      ∫ x in Ioi (0:ℝ), Real.exp (-x-a/x)*x^(k+1) := by
  have hs := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi
    (fun x (hx : x ∈ Ioi (0:ℝ)) =>
      (pwGammaMoment_deriv (a:=a) hx).hasDerivWithinAt)
    (pwGammaMoment_involution ha).injective.injOn
    (pwGammaReciprocalMomentKernel a k)
  rw [pwGammaMoment_image ha] at hs
  unfold pwGammaReciprocalMoment
  rw [hs, ← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x hx
  have hx0 : 0<x := hx
  dsimp only
  rw [smul_eq_mul, neg_div, abs_neg, abs_of_pos (div_pos ha (pow_pos hx0 2))]
  unfold pwGammaReciprocalMomentKernel
  have he : -(a/x)-a/(a/x) = -x-a/x := by field_simp; ring
  rw [he, div_pow]
  rw [show k+3=k+1+2 by omega, pow_add]
  field_simp
  ring

private theorem pwGammaMoment_weight_integrable (k : ℕ) :
    IntegrableOn (fun x : ℝ => Real.exp (-x)*x^k) (Ioi 0) := by
  simpa only [add_sub_cancel_right, Real.rpow_natCast] using
    (Real.GammaIntegral_convergent (s:=(k:ℝ)+1) (by positivity))

private theorem pwGammaMoment_weight_integral (k : ℕ) :
    (∫ x in Ioi (0:ℝ), Real.exp (-x)*x^k) = (k.factorial:ℝ) := by
  have hg := Real.Gamma_eq_integral (s:=(k:ℝ)+1) (by positivity)
  simpa only [add_sub_cancel_right, Real.rpow_natCast, Real.Gamma_nat_eq_factorial] using hg.symm

private theorem pwGammaMoment_transformed_integrable (k : ℕ) {a : ℝ} (ha : 0<a) :
    IntegrableOn (fun x : ℝ => Real.exp (-x-a/x)*x^(k+1)) (Ioi 0) := by
  have hm : Measurable (fun x : ℝ => Real.exp (-x-a/x)*x^(k+1)) := by fun_prop
  apply (pwGammaMoment_weight_integrable (k+1)).mono' hm.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  have hx0 : 0<x := hx
  rw [Real.norm_of_nonneg (by positivity)]
  gcongr
  exact sub_le_self _ (div_pos ha hx0).le

private theorem pwGammaMoment_transformed_upper (k : ℕ) {a : ℝ} (ha : 0<a) :
    (∫ x in Ioi (0:ℝ), Real.exp (-x-a/x)*x^(k+1)) ≤ ((k+1).factorial:ℝ) := by
  rw [← pwGammaMoment_weight_integral]
  apply integral_mono_ae (pwGammaMoment_transformed_integrable k ha)
    (pwGammaMoment_weight_integrable (k+1))
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  have hx0 : 0<x := hx
  gcongr
  exact sub_le_self _ (div_pos ha hx0).le

private theorem pwGammaMoment_transformed_lower (k : ℕ) {a : ℝ} (ha : 0<a) :
    ((k+1).factorial:ℝ)-a*(k.factorial:ℝ) ≤
      ∫ x in Ioi (0:ℝ), Real.exp (-x-a/x)*x^(k+1) := by
  rw [← pwGammaMoment_weight_integral (k+1), ← pwGammaMoment_weight_integral k,
    ← integral_const_mul, ← integral_sub (pwGammaMoment_weight_integrable (k+1))
      ((pwGammaMoment_weight_integrable k).const_mul a)]
  apply integral_mono_ae ((pwGammaMoment_weight_integrable (k+1)).sub
    ((pwGammaMoment_weight_integrable k).const_mul a))
    (pwGammaMoment_transformed_integrable k ha)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  have hx0 : 0<x := hx
  have he : 1-a/x ≤ Real.exp (-a/x) := by
    simpa only [sub_eq_add_neg, neg_div, add_comm] using Real.add_one_le_exp (-a/x)
  change Real.exp (-x)*x^(k+1)-a*(Real.exp (-x)*x^k) ≤ _
  calc
    _ = (Real.exp (-x)*x^(k+1))*(1-a/x) := by rw [pow_succ]; field_simp
    _ ≤ (Real.exp (-x)*x^(k+1))*Real.exp (-a/x) :=
      mul_le_mul_of_nonneg_left he (by positivity)
    _ = _ := by rw [sub_eq_add_neg, Real.exp_add, neg_div]; ring


theorem pwGammaReciprocalMomentRatio_pos (k : ℕ) {a : ℝ} (ha : 0<a) :
    0<pwGammaReciprocalMomentRatio a k :=
  div_pos (pwGammaReciprocalMoment_pos k ha) (by positivity)

theorem pwGammaReciprocalMomentRatio_upper (k : ℕ) {a : ℝ} (ha : 0<a) :
    pwGammaReciprocalMomentRatio a k ≤ 1/a^(k+2) := by
  unfold pwGammaReciprocalMomentRatio
  rw [pwGammaReciprocalMoment_inversion k ha]
  calc
    _ ≤ ((1/a^(k+2))*((k+1).factorial:ℝ))/((k+1).factorial:ℝ) := by
      gcongr
      exact pwGammaMoment_transformed_upper k ha
    _ = _ := by field_simp

theorem pwGammaReciprocalMomentRatio_lower (k : ℕ) {a : ℝ} (ha : 0<a) :
    (1/a^(k+2))*(1-a/((k:ℝ)+1)) ≤ pwGammaReciprocalMomentRatio a k := by
  unfold pwGammaReciprocalMomentRatio
  rw [pwGammaReciprocalMoment_inversion k ha]
  have hf : (0:ℝ)<(k.factorial:ℝ) := by positivity
  have hF : ((k+1).factorial:ℝ) = ((k:ℝ)+1)*(k.factorial:ℝ) := by
    rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  calc
    _ = ((1/a^(k+2))*(((k+1).factorial:ℝ)-a*(k.factorial:ℝ)))/((k+1).factorial:ℝ) := by
      rw [hF]
      field_simp
    _ ≤ _ := by
      gcongr
      exact pwGammaMoment_transformed_lower k ha

/-- The first reciprocal mode has a quantitative normalized Gamma limit. -/
theorem pwGammaReciprocalMomentRatio_one_error (k : ℕ) :
    |pwGammaReciprocalMomentRatio 1 k-1| ≤ 1/((k:ℝ)+1) := by
  have hl := pwGammaReciprocalMomentRatio_lower k (by positivity : (0:ℝ)<1)
  have hu := pwGammaReciprocalMomentRatio_upper k (by positivity : (0:ℝ)<1)
  simp only [one_pow, div_one, one_mul] at hl hu
  apply abs_le.mpr
  constructor
  · linarith
  · have h : (0:ℝ)≤1/((k:ℝ)+1) := by positivity
    linarith

theorem pwGammaReciprocalMomentRatio_one_tendsto :
    Tendsto (pwGammaReciprocalMomentRatio 1) atTop (𝓝 1) := by
  have hn : Tendsto (fun k : ℕ => (k:ℝ)+1) atTop atTop :=
    (tendsto_natCast_atTop_atTop (R:=ℝ)).atTop_add tendsto_const_nhds
  have hi : Tendsto (fun k : ℕ => 1/((k:ℝ)+1)) atTop (𝓝 (0:ℝ)) := by
    simpa only [one_div, Function.comp_def] using tendsto_inv_atTop_zero.comp hn
  have ht : Tendsto (fun k : ℕ => |pwGammaReciprocalMomentRatio 1 k-1|) atTop (𝓝 0) :=
    squeeze_zero (fun k => abs_nonneg _) pwGammaReciprocalMomentRatio_one_error hi
  have hz : Tendsto (fun k : ℕ => pwGammaReciprocalMomentRatio 1 k-1) atTop (𝓝 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr (by simpa only [Real.norm_eq_abs] using ht)
  simpa only [sub_add_cancel, zero_add] using hz.add_const 1


/-- Every later mode disappears under high-order Gamma normalization. -/
theorem pwGammaReciprocalMomentRatio_tendsto_zero {a : ℝ} (ha : 1<a) :
    Tendsto (pwGammaReciprocalMomentRatio a) atTop (𝓝 0) := by
  have ha0 : 0<a := lt_trans zero_lt_one ha
  have hp := tendsto_pow_atTop_nhds_zero_of_lt_one
    (show (0:ℝ)≤1/a by positivity) ((div_lt_one ha0).mpr ha)
  have ht : Tendsto (fun k : ℕ => 1/a^(k+2)) atTop (𝓝 (0:ℝ)) := by
    have he : ∀ k : ℕ, (1/a)^k*(1/a)^2=1/a^(k+2) := by
      intro k
      simp only [div_pow, one_pow, pow_add]
      field_simp
    have hp2 : Tendsto (fun k : ℕ => (1/a)^k*(1/a)^2) atTop (𝓝 (0:ℝ)) := by
      simpa only [zero_mul] using hp.mul_const ((1/a)^2)
    exact hp2.congr he
  exact squeeze_zero (fun k => (pwGammaReciprocalMomentRatio_pos k ha0).le)
    (fun k => pwGammaReciprocalMomentRatio_upper k ha0) ht

/-- Arbitrarily strong inverse-mode bounds also admit every fixed arithmetic moment. -/
theorem pwGammaReciprocalMomentKernel_pow_bound (k l : ℕ) {a x : ℝ}
    (ha : 0<a) (hx : 0<x) :
    pwGammaReciprocalMomentKernel a k x ≤
      (((k+3+l).factorial:ℝ)/a^(k+3+l))*Real.exp (-x)*x^l := by
  have he := pwGammaMoment_exp_bound (k+3+l) (div_pos ha hx)
  calc
    _ = Real.exp (-x)*Real.exp (-a/x)/x^(k+3) := by
      rw [pwGammaReciprocalMomentKernel, sub_eq_add_neg, Real.exp_add, neg_div]
    _ ≤ Real.exp (-x)*(((k+3+l).factorial:ℝ)/(a/x)^(k+3+l))/x^(k+3) := by
      gcongr
      simpa only [neg_div] using he
    _ = _ := by rw [div_pow, pow_add]; field_simp; ring

theorem pwGammaReciprocalMoment_pow_bound (k l : ℕ) {a : ℝ} (ha : 0<a) :
    pwGammaReciprocalMoment a k ≤
      (((k+3+l).factorial:ℝ)/a^(k+3+l))*(l.factorial:ℝ) := by
  unfold pwGammaReciprocalMoment
  rw [← pwGammaMoment_weight_integral l, ← integral_const_mul]
  apply integral_mono_ae (pwGammaReciprocalMomentKernel_integrable k ha)
    ((pwGammaMoment_weight_integrable l).const_mul _)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  simpa only [mul_assoc] using pwGammaReciprocalMomentKernel_pow_bound k l ha hx

end
end RHTower
