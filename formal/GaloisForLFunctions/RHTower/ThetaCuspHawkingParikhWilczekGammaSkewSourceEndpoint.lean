import GaloisForLFunctions.RHTower.ThetaCuspHawkingParikhWilczekGammaMobiusReciprocalEndpoint
import GaloisForLFunctions.RHTower.ThetaCuspHawkingParikhWilczekGammaAdjointSourceTest

set_option backward.isDefEq.respectTransparency false
namespace RHTower
open MeasureTheory Set Filter Topology ArithmeticFunction
noncomputable section

private theorem pwGammaSource_tail_limit (c : ℕ → ℂ) (h0 : c 0=0) (hs : Summable c) :
    Tendsto (fun x : ℝ => ∑' n, c n*(Real.exp (-((n:ℝ)-1)*(x-1)):ℂ)) atTop (𝓝 (c 1)) := by
  have hpt : ∀ n : ℕ, Tendsto (fun x : ℝ => c n*(Real.exp (-((n:ℝ)-1)*(x-1)):ℂ))
      atTop (𝓝 (if n=1 then c 1 else 0)) := by
    intro n
    by_cases hn1 : n=1
    · subst n
      simpa using (tendsto_const_nhds (x:=c 1) (f:=atTop))
    rw [if_neg hn1]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp only [h0, zero_mul]
      exact tendsto_const_nhds
    have hnR : (1:ℝ)<n := by exact_mod_cast (show 1<n by omega)
    have hshift : Tendsto (fun x : ℝ => x-1) atTop atTop := by
      simpa only [sub_eq_add_neg, id_eq] using
        (tendsto_id.atTop_add (tendsto_const_nhds (x:=(-1:ℝ))))
    have he := Real.tendsto_exp_atBot.comp
      (hshift.const_mul_atTop_of_neg (by linarith : -((n:ℝ)-1)<0))
    simpa only [Function.comp_apply, Complex.ofReal_zero, mul_zero] using he.ofReal.const_mul (c n)
  have hb : ∀ᶠ x : ℝ in atTop, ∀ n, ‖c n*(Real.exp (-((n:ℝ)-1)*(x-1)):ℂ)‖ ≤ ‖c n‖ := by
    filter_upwards [eventually_ge_atTop (1:ℝ)] with x hx n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [h0]
    have hnR : (1:ℝ)≤n := by exact_mod_cast hn
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
    have he : Real.exp (-((n:ℝ)-1)*(x-1)) ≤ 1 :=
      Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith))
    exact (mul_le_mul_of_nonneg_left he (norm_nonneg _)).trans_eq (mul_one _)
  have ht := tendsto_tsum_of_dominated_convergence hs.norm hpt hb
  simpa using ht

private theorem pwGammaSource_mode_shift (n : ℕ) (x : ℝ) :
    pwGammaNormalizedRayMode n x =
      pwGammaNormalizedRayMode n 1*Real.exp (-((n:ℝ)-1)*(x-1)) := by
  unfold pwGammaNormalizedRayMode
  rw [mul_assoc, ← Real.exp_add]
  congr 2
  ring

private theorem pwGammaSource_global_atom_ratio (z : ℂ) (n : ℕ) {x : ℝ} (hx : 0<x) :
    pwGammaMobiusGlobalAtom z n x/pwGammaRaySource x =
      (pwGammaMobiusGlobalAtom z n 1/pwGammaRaySource 1)*
        (Real.exp (-((n:ℝ)-1)*(x-1)):ℂ) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [pwGammaMobiusGlobalAtom]
  rw [pwGammaMobiusGlobalAtom, pwGammaMobiusGlobalAtom, mul_div_assoc, mul_div_assoc,
    pwGammaNormalizedRayMode_source_ratio hn hx,
    pwGammaNormalizedRayMode_source_ratio hn zero_lt_one,
    pwGammaSource_mode_shift n x, Complex.ofReal_mul]
  ring

theorem pwGammaMobiusTilt_normalized_tendsto_one (z : ℂ) :
    Tendsto (fun x : ℝ => pwGammaMobiusTilt z x/pwGammaRaySource x) atTop (𝓝 (1:ℂ)) := by
  have hs : Summable (fun n => pwGammaMobiusGlobalAtom z n 1/pwGammaRaySource 1) := by
    exact (pwGammaMobiusTilt_summable z zero_lt_one).div_const _
  have ht := pwGammaSource_tail_limit _ (by simp [pwGammaMobiusGlobalAtom]) hs
  have h1 : pwGammaMobiusGlobalAtom z 1 1/pwGammaRaySource 1=1 := by
    simp [pwGammaMobiusGlobalAtom, pwGammaRaySource_ne_zero]
  rw [h1] at ht
  apply ht.congr'
  filter_upwards [eventually_gt_atTop (0:ℝ)] with x hx
  rw [pwGammaMobiusTilt_eq_global_atoms, ← tsum_div_const]
  exact tsum_congr (fun n => (pwGammaSource_global_atom_ratio z n hx).symm)

theorem pwGammaMobiusTiltCurrent_normalized_tendsto_zero (z : ℂ) :
    Tendsto (fun x : ℝ => pwGammaMobiusTiltCurrent z x/pwGammaRaySource x) atTop (𝓝 (0:ℂ)) := by
  have hs : Summable (fun n => pwGammaMobiusGlobalCurrentAtom z n 1/pwGammaRaySource 1) := by
    exact (pwGammaMobiusTiltCurrent_summable z zero_lt_one).div_const _
  have ht := pwGammaSource_tail_limit _ (by simp [pwGammaMobiusGlobalCurrentAtom]) hs
  have h1 : pwGammaMobiusGlobalCurrentAtom z 1 1/pwGammaRaySource 1=0 := by
    simp [pwGammaMobiusGlobalCurrentAtom]
  rw [h1] at ht
  apply ht.congr'
  filter_upwards [eventually_gt_atTop (0:ℝ)] with x hx
  rw [pwGammaMobiusTiltCurrent_eq_global_atoms, ← tsum_div_const]
  apply tsum_congr
  intro n
  rw [pwGammaMobiusGlobalCurrentAtom, pwGammaMobiusGlobalCurrentAtom,
    mul_div_assoc, mul_div_assoc, pwGammaSource_global_atom_ratio z n hx]
  ring

theorem pwGammaMobiusSameSourceCurrent_reflection_endpoint (z : ℂ) :
    Tendsto (fun x : ℝ => pwGammaRayInverseReflection (pwGammaMobiusSameSourceCurrent z) x/
      pwGammaRaySource x) atTop (𝓝 (∑' n, pwGammaMobiusReciprocalEndpointAtom z n)) := by
  have ht := (pwGammaMobiusSameSourceCurrent_normalized_tendsto_endpoint z).comp
    (tendsto_inv_atTop_nhdsGT_zero (𝕜:=ℝ))
  apply ht.congr'
  apply Eventually.of_forall
  intro x
  dsimp [Function.comp_def, pwGammaRayInverseReflection]
  field_simp [pwGammaRaySource_ne_zero]

/-- Literal corrected skew candidate applied to the unchanged arithmetic field. -/
def pwGammaMobiusSkewSource (z : ℂ) (x : ℝ) : ℂ :=
  pwGammaMobiusTiltCurrent z x-
    pwGammaRayInverseReflection (pwGammaMobiusSameSourceCurrent z) x-
    (2*Real.log x:ℝ)*pwGammaMobiusTilt z x

theorem pwGammaMobiusSkewSource_normalized_log_limit (z : ℂ) :
    Tendsto (fun x : ℝ => pwGammaMobiusSkewSource z x/
      (pwGammaRaySource x*(Real.log x:ℂ))) atTop (𝓝 (-2:ℂ)) := by
  have hlog : Tendsto (fun x : ℝ => ((Real.log x)⁻¹:ℝ)) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp Real.tendsto_log_atTop
  have hsmall := ((pwGammaMobiusTiltCurrent_normalized_tendsto_zero z).sub
    (pwGammaMobiusSameSourceCurrent_reflection_endpoint z)).mul hlog.ofReal
  have ht := hsmall.sub ((pwGammaMobiusTilt_normalized_tendsto_one z).const_mul (2:ℂ))
  simp only [Complex.ofReal_zero, mul_zero, mul_one, zero_sub] at ht
  apply ht.congr'
  filter_upwards [eventually_gt_atTop (1:ℝ)] with x hx
  have hlog0 := (Real.log_pos hx).ne'
  dsimp [pwGammaMobiusSkewSource]
  push_cast
  field_simp [pwGammaRaySource_ne_zero, hlog0]

theorem pwGammaMobiusSkewSource_no_scalar_occurrence (z lam : ℂ) :
    ¬ (∀ x : ℝ, 0<x → pwGammaMobiusSkewSource z x=lam*pwGammaMobiusTilt z x) := by
  intro heq
  have hlog : Tendsto (fun x : ℝ => ((Real.log x)⁻¹:ℝ)) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp Real.tendsto_log_atTop
  have hz := ((pwGammaMobiusTilt_normalized_tendsto_one z).const_mul lam).mul hlog.ofReal
  simp only [Complex.ofReal_zero, mul_zero] at hz
  have hz' : Tendsto (fun x : ℝ => pwGammaMobiusSkewSource z x/
      (pwGammaRaySource x*(Real.log x:ℂ))) atTop (𝓝 (0:ℂ)) := by
    apply hz.congr'
    filter_upwards [eventually_gt_atTop (0:ℝ)] with x hx
    rw [heq x hx]
    push_cast
    ring
  have hf := tendsto_nhds_unique (pwGammaMobiusSkewSource_normalized_log_limit z) hz'
  exact (neg_ne_zero.mpr (two_ne_zero : (2:ℂ)≠0)) hf

/-- Exact leading effect of a logarithmic source correction. -/
theorem pwGammaMobiusSkewSource_correction_log_limit (z c : ℂ) :
    Tendsto (fun x : ℝ =>
      (pwGammaMobiusSkewSource z x+(2*Real.log x:ℝ)*c*pwGammaRaySource x)/
        (pwGammaRaySource x*(Real.log x:ℂ))) atTop (𝓝 (2*c-2)) := by
  have ht := (pwGammaMobiusSkewSource_normalized_log_limit z).add_const (2*c)
  have he : (-2:ℂ)+2*c=2*c-2 := by ring
  rw [he] at ht
  apply ht.congr'
  filter_upwards [eventually_gt_atTop (1:ℝ)] with x hx
  have hlog0 := (Real.log_pos hx).ne'
  push_cast
  field_simp [pwGammaRaySource_ne_zero, hlog0] <;> ring

/-- Only the unit ground correction can remove the logarithmic source obstruction. -/
theorem pwGammaMobiusSkewSource_ground_correction_required (z c lam : ℂ)
    (heq : ∀ x : ℝ, 0<x →
      pwGammaMobiusSkewSource z x+(2*Real.log x:ℝ)*c*pwGammaRaySource x=
        lam*(pwGammaMobiusTilt z x-c*pwGammaRaySource x)) : c=1 := by
  have hlog : Tendsto (fun x : ℝ => ((Real.log x)⁻¹:ℝ)) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp Real.tendsto_log_atTop
  have hz := (((pwGammaMobiusTilt_normalized_tendsto_one z).sub_const c).const_mul lam).mul hlog.ofReal
  simp only [Complex.ofReal_zero, mul_zero] at hz
  have hz' : Tendsto (fun x : ℝ =>
      (pwGammaMobiusSkewSource z x+(2*Real.log x:ℝ)*c*pwGammaRaySource x)/
        (pwGammaRaySource x*(Real.log x:ℂ))) atTop (𝓝 (0:ℂ)) := by
    apply hz.congr'
    filter_upwards [eventually_gt_atTop (1:ℝ)] with x hx
    rw [heq x (zero_lt_one.trans hx)]
    have hlog0 := (Real.log_pos hx).ne'
    push_cast
    field_simp [pwGammaRaySource_ne_zero, hlog0] <;> ring
  have he := sub_eq_zero.mp
    (tendsto_nhds_unique (pwGammaMobiusSkewSource_correction_log_limit z c) hz')
  exact (mul_left_cancel₀ (two_ne_zero : (2:ℂ)≠0)) (by simpa only [mul_one] using he)


end
end RHTower
