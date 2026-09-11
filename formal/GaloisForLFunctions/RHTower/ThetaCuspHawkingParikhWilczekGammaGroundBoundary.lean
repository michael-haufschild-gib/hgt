import GaloisForLFunctions.RHTower.ThetaCuspHawkingParikhWilczekGammaSkewSourceEndpoint

set_option backward.isDefEq.respectTransparency false
namespace RHTower
open MeasureTheory Set Filter Topology ArithmeticFunction
noncomputable section

private theorem pwGammaGround_atom_ratio (z : ℂ) (n : ℕ) {x : ℝ} (hx : 0<x) :
    pwGammaMobiusGlobalAtom z n x/pwGammaRaySource x =
      (pwGammaMobiusGlobalAtom z n 1/pwGammaRaySource 1)*
        (Real.exp (-((n:ℝ)-1)*(x-1)):ℂ) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [pwGammaMobiusGlobalAtom]
  rw [pwGammaMobiusGlobalAtom, pwGammaMobiusGlobalAtom, mul_div_assoc, mul_div_assoc,
    pwGammaNormalizedRayMode_source_ratio hn hx,
    pwGammaNormalizedRayMode_source_ratio hn zero_lt_one]
  have he : pwGammaNormalizedRayMode n x =
      pwGammaNormalizedRayMode n 1*Real.exp (-((n:ℝ)-1)*(x-1)) := by
    unfold pwGammaNormalizedRayMode
    rw [mul_assoc, ← Real.exp_add]
    congr 2
    ring
  rw [he, Complex.ofReal_mul]
  ring

private theorem pwGammaGround_tail_bound (c : ℕ → ℂ) (hs : Summable c)
    {x : ℝ} (hx : 1≤x) :
    ‖∑' n, c (n+2)*(Real.exp (-(((n+2:ℕ):ℝ)-1)*(x-1)):ℂ)‖ ≤
      (∑' n, ‖c (n+2)‖)*Real.exp (-(x-1)) := by
  have hs' : Summable (fun n => ‖c (n+2)‖) := (summable_nat_add_iff 2).mpr hs.norm
  apply tsum_of_norm_bounded (hs'.hasSum.mul_right _)
  intro n
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  apply Real.exp_le_exp.mpr
  have hn : (2:ℝ)≤(n+2:ℕ) := by exact_mod_cast (Nat.le_add_left 2 n)
  nlinarith

theorem pwGammaMobiusTilt_ground_tail_eq (z : ℂ) {x : ℝ} (hx : 0<x) :
    pwGammaMobiusTilt z x/pwGammaRaySource x-1 =
      ∑' n, (pwGammaMobiusGlobalAtom z (n+2) 1/pwGammaRaySource 1)*
        (Real.exp (-(((n+2:ℕ):ℝ)-1)*(x-1)):ℂ) := by
  have hs : Summable (fun n => pwGammaMobiusGlobalAtom z n x/pwGammaRaySource x) :=
    (pwGammaMobiusTilt_summable z hx).div_const _
  have ht := hs.sum_add_tsum_nat_add 2
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add] at ht
  have h0 : pwGammaMobiusGlobalAtom z 0 x/pwGammaRaySource x=0 := by
    simp [pwGammaMobiusGlobalAtom]
  have h1 : pwGammaMobiusGlobalAtom z 1 x/pwGammaRaySource x=1 := by
    simp [pwGammaMobiusGlobalAtom, pwGammaRaySource_ne_zero]
  rw [h0, h1, zero_add] at ht
  have hf : (∑' n, pwGammaMobiusGlobalAtom z n x/pwGammaRaySource x) =
      pwGammaMobiusTilt z x/pwGammaRaySource x := tsum_div_const
  rw [hf] at ht
  rw [← ht]
  have hh : (1:ℂ)+(∑' n, pwGammaMobiusGlobalAtom z (n+2) x/pwGammaRaySource x)-1 =
      ∑' n, pwGammaMobiusGlobalAtom z (n+2) x/pwGammaRaySource x := by ring
  rw [hh]
  exact tsum_congr (fun n => pwGammaGround_atom_ratio z (n+2) hx)

theorem pwGammaMobiusTilt_ground_tail_bound (z : ℂ) {x : ℝ} (hx : 1≤x) :
    ‖pwGammaMobiusTilt z x/pwGammaRaySource x-1‖ ≤
      (∑' n, ‖pwGammaMobiusGlobalAtom z (n+2) 1/pwGammaRaySource 1‖)*
        Real.exp (-(x-1)) := by
  rw [pwGammaMobiusTilt_ground_tail_eq z (zero_lt_one.trans_le hx)]
  exact pwGammaGround_tail_bound _ ((pwGammaMobiusTilt_summable z zero_lt_one).div_const _) hx

private theorem pwGammaGround_log_exp_limit :
    Tendsto (fun x : ℝ => Real.log x*Real.exp (-(x-1))) atTop (𝓝 0) := by
  have hshift : Tendsto (fun x : ℝ => x-1) atTop atTop := by
    simpa only [sub_eq_add_neg, id_eq] using
      (tendsto_id.atTop_add (tendsto_const_nhds (x:=(-1:ℝ))))
  have ht := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp hshift
  simp only [pow_one] at ht
  apply squeeze_zero' _ _ ht
  · filter_upwards [eventually_ge_atTop (1:ℝ)] with x hx
    exact mul_nonneg (Real.log_nonneg hx) (Real.exp_pos _).le
  · filter_upwards [eventually_ge_atTop (1:ℝ)] with x hx
    exact mul_le_mul_of_nonneg_right (Real.log_le_sub_one_of_pos (zero_lt_one.trans_le hx))
      (Real.exp_pos _).le

theorem pwGammaMobiusTilt_ground_tail_log_limit (z : ℂ) :
    Tendsto (fun x : ℝ => (Real.log x:ℂ)*(pwGammaMobiusTilt z x/pwGammaRaySource x-1))
      atTop (𝓝 (0:ℂ)) := by
  have ht := pwGammaGround_log_exp_limit.const_mul
    (∑' n, ‖pwGammaMobiusGlobalAtom z (n+2) 1/pwGammaRaySource 1‖)
  simp only [mul_zero] at ht
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) _ ht
  filter_upwards [eventually_ge_atTop (1:ℝ)] with x hx
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.log_nonneg hx)]
  calc
    _ ≤ Real.log x*((∑' n, ‖pwGammaMobiusGlobalAtom z (n+2) 1/pwGammaRaySource 1‖)*
        Real.exp (-(x-1))) :=
      mul_le_mul_of_nonneg_left (pwGammaMobiusTilt_ground_tail_bound z hx) (Real.log_nonneg hx)
    _ = _ := by ring

/-- The complete retained boundary after the forced unit ground correction. -/
theorem pwGammaMobiusSkewSource_ground_boundary_limit (z : ℂ) :
    Tendsto (fun x : ℝ =>
      (pwGammaMobiusSkewSource z x+(2*Real.log x:ℝ)*pwGammaRaySource x)/pwGammaRaySource x)
      atTop (𝓝 (-(∑' n, pwGammaMobiusReciprocalEndpointAtom z n))) := by
  have ht := ((pwGammaMobiusTiltCurrent_normalized_tendsto_zero z).sub
    (pwGammaMobiusSameSourceCurrent_reflection_endpoint z)).sub
    ((pwGammaMobiusTilt_ground_tail_log_limit z).const_mul (2:ℂ))
  simp only [zero_sub, mul_zero, sub_zero] at ht
  apply ht.congr'
  apply Eventually.of_forall
  intro x
  dsimp [pwGammaMobiusSkewSource]
  push_cast
  field_simp [pwGammaRaySource_ne_zero] <;> ring

/-- Scalar incidence for the unit-corrected source requires vanishing of its actual endpoint. -/
theorem pwGammaMobiusSkewSource_ground_boundary_required (z lam : ℂ)
    (heq : ∀ x : ℝ, 0<x →
      pwGammaMobiusSkewSource z x+(2*Real.log x:ℝ)*pwGammaRaySource x=
        lam*(pwGammaMobiusTilt z x-pwGammaRaySource x)) :
    (∑' n, pwGammaMobiusReciprocalEndpointAtom z n)=0 := by
  have ht := ((pwGammaMobiusTilt_normalized_tendsto_one z).sub_const (1:ℂ)).const_mul lam
  simp only [sub_self, mul_zero] at ht
  have ht' : Tendsto (fun x : ℝ =>
      (pwGammaMobiusSkewSource z x+(2*Real.log x:ℝ)*pwGammaRaySource x)/pwGammaRaySource x)
      atTop (𝓝 (0:ℂ)) := by
    apply ht.congr'
    filter_upwards [eventually_gt_atTop (0:ℝ)] with x hx
    rw [heq x hx]
    field_simp [pwGammaRaySource_ne_zero] <;> ring
  exact neg_eq_zero.mp (tendsto_nhds_unique (pwGammaMobiusSkewSource_ground_boundary_limit z) ht')

theorem pwGammaMobiusTiltCurrent_ground_tail_bound (z : ℂ) {x : ℝ} (hx : 1≤x) :
    ‖pwGammaMobiusTiltCurrent z x/pwGammaRaySource x‖ ≤
      (∑' n, ‖pwGammaMobiusGlobalCurrentAtom z (n+2) 1/pwGammaRaySource 1‖)*
        Real.exp (-(x-1)) := by
  have hx0 := zero_lt_one.trans_le hx
  have hs : Summable (fun n => pwGammaMobiusGlobalCurrentAtom z n x/pwGammaRaySource x) :=
    (pwGammaMobiusTiltCurrent_summable z hx0).div_const _
  have ht := hs.sum_add_tsum_nat_add 2
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add] at ht
  have h0 : pwGammaMobiusGlobalCurrentAtom z 0 x/pwGammaRaySource x=0 := by
    simp [pwGammaMobiusGlobalCurrentAtom]
  have h1 : pwGammaMobiusGlobalCurrentAtom z 1 x/pwGammaRaySource x=0 := by
    simp [pwGammaMobiusGlobalCurrentAtom]
  rw [h0, h1, zero_add, zero_add] at ht
  have hf : (∑' n, pwGammaMobiusGlobalCurrentAtom z n x/pwGammaRaySource x) =
      pwGammaMobiusTiltCurrent z x/pwGammaRaySource x := tsum_div_const
  rw [hf] at ht
  have he : pwGammaMobiusTiltCurrent z x/pwGammaRaySource x =
      ∑' n, (pwGammaMobiusGlobalCurrentAtom z (n+2) 1/pwGammaRaySource 1)*
        (Real.exp (-(((n+2:ℕ):ℝ)-1)*(x-1)):ℂ) := by
    rw [← ht]
    apply tsum_congr
    intro n
    rw [pwGammaMobiusGlobalCurrentAtom, pwGammaMobiusGlobalCurrentAtom,
      mul_div_assoc, mul_div_assoc, pwGammaGround_atom_ratio z (n+2) hx0]
    ring
  rw [he]
  exact pwGammaGround_tail_bound _
    ((pwGammaMobiusTiltCurrent_summable z zero_lt_one).div_const _) hx

private theorem pwGammaGround_pow_exp_limit (k : ℕ) :
    Tendsto (fun x : ℝ => x^k*Real.exp (-(x-1))) atTop (𝓝 0) := by
  have ht := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero k).const_mul (Real.exp 1)
  simp only [mul_zero] at ht
  apply ht.congr
  intro x
  have he : -(x-1) = 1+(-x) := by ring
  rw [he, Real.exp_add]
  ring

private theorem pwGammaGround_pow_log_exp_limit (k : ℕ) :
    Tendsto (fun x : ℝ => x^k*Real.log x*Real.exp (-(x-1))) atTop (𝓝 0) := by
  apply squeeze_zero' _ _ (pwGammaGround_pow_exp_limit (k+1))
  · filter_upwards [eventually_ge_atTop (1:ℝ)] with x hx
    exact mul_nonneg (mul_nonneg (pow_nonneg (zero_le_one.trans hx) _)
      (Real.log_nonneg hx)) (Real.exp_pos _).le
  · filter_upwards [eventually_ge_atTop (1:ℝ)] with x hx
    have hlog : Real.log x≤x := (Real.log_le_sub_one_of_pos (zero_lt_one.trans_le hx)).trans (by linarith)
    rw [pow_succ]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hlog (pow_nonneg (zero_le_one.trans hx) _)) (Real.exp_pos _).le

private theorem pwGammaGround_pow_decay (f : ℝ → ℂ) (C : ℝ)
    (hb : ∀ x : ℝ, 1≤x → ‖f x‖≤C*Real.exp (-(x-1))) (k : ℕ) :
    Tendsto (fun x : ℝ => (x^k:ℂ)*f x) atTop (𝓝 (0:ℂ)) := by
  have ht := (pwGammaGround_pow_exp_limit k).const_mul C
  simp only [mul_zero] at ht
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) _ ht
  filter_upwards [eventually_ge_atTop (1:ℝ)] with x hx
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg (zero_le_one.trans hx)]
  calc
    _ ≤ x^k*(C*Real.exp (-(x-1))) :=
      mul_le_mul_of_nonneg_left (hb x hx) (pow_nonneg (zero_le_one.trans hx) _)
    _ = _ := by ring

theorem pwGammaMobiusTilt_ground_tail_pow_limit (z : ℂ) (k : ℕ) :
    Tendsto (fun x : ℝ => (x^k:ℂ)*(pwGammaMobiusTilt z x/pwGammaRaySource x-1))
      atTop (𝓝 (0:ℂ)) :=
  pwGammaGround_pow_decay _ _ (fun _ hx => pwGammaMobiusTilt_ground_tail_bound z hx) k

theorem pwGammaMobiusTiltCurrent_ground_tail_pow_limit (z : ℂ) (k : ℕ) :
    Tendsto (fun x : ℝ => (x^k:ℂ)*(pwGammaMobiusTiltCurrent z x/pwGammaRaySource x))
      atTop (𝓝 (0:ℂ)) :=
  pwGammaGround_pow_decay _ _ (fun _ hx => pwGammaMobiusTiltCurrent_ground_tail_bound z hx) k

theorem pwGammaMobiusTilt_ground_tail_pow_log_limit (z : ℂ) (k : ℕ) :
    Tendsto (fun x : ℝ => (x^k:ℂ)*(Real.log x:ℂ)*
      (pwGammaMobiusTilt z x/pwGammaRaySource x-1)) atTop (𝓝 (0:ℂ)) := by
  have ht := (pwGammaGround_pow_log_exp_limit k).const_mul
    (∑' n, ‖pwGammaMobiusGlobalAtom z (n+2) 1/pwGammaRaySource 1‖)
  simp only [mul_zero] at ht
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) _ ht
  filter_upwards [eventually_ge_atTop (1:ℝ)] with x hx
  rw [norm_mul, norm_mul, norm_pow, Complex.norm_real, Complex.norm_real,
    Real.norm_of_nonneg (zero_le_one.trans hx), Real.norm_of_nonneg (Real.log_nonneg hx)]
  calc
    _ ≤ (x^k*Real.log x)*((∑' n, ‖pwGammaMobiusGlobalAtom z (n+2) 1/pwGammaRaySource 1‖)*
        Real.exp (-(x-1))) :=
      mul_le_mul_of_nonneg_left (pwGammaMobiusTilt_ground_tail_bound z hx)
        (mul_nonneg (pow_nonneg (zero_le_one.trans hx) _) (Real.log_nonneg hx))
    _ = _ := by ring

/-- The corrected scalar identity forces every polynomially normalized reciprocal current to vanish. -/
theorem pwGammaMobiusSkewSource_ground_current_flat_required (z lam : ℂ)
    (heq : ∀ x : ℝ, 0<x →
      pwGammaMobiusSkewSource z x+(2*Real.log x:ℝ)*pwGammaRaySource x=
        lam*(pwGammaMobiusTilt z x-pwGammaRaySource x)) (k : ℕ) :
    Tendsto (fun x : ℝ => (x^k:ℂ)*
      (pwGammaRayInverseReflection (pwGammaMobiusSameSourceCurrent z) x/pwGammaRaySource x))
      atTop (𝓝 (0:ℂ)) := by
  have ht := ((pwGammaMobiusTiltCurrent_ground_tail_pow_limit z k).sub
    ((pwGammaMobiusTilt_ground_tail_pow_log_limit z k).const_mul (2:ℂ))).sub
    ((pwGammaMobiusTilt_ground_tail_pow_limit z k).const_mul lam)
  simp only [mul_zero, sub_self] at ht
  apply ht.congr'
  filter_upwards [eventually_gt_atTop (0:ℝ)] with x hx
  have hh := heq x hx
  dsimp [pwGammaMobiusSkewSource] at hh
  push_cast at hh
  have hr : pwGammaRayInverseReflection (pwGammaMobiusSameSourceCurrent z) x =
      pwGammaMobiusTiltCurrent z x-(2:ℂ)*(Real.log x:ℂ)*
        (pwGammaMobiusTilt z x-pwGammaRaySource x)-
        lam*(pwGammaMobiusTilt z x-pwGammaRaySource x) := by linear_combination -hh
  rw [hr]
  field_simp [pwGammaRaySource_ne_zero] <;> ring

end
end RHTower
