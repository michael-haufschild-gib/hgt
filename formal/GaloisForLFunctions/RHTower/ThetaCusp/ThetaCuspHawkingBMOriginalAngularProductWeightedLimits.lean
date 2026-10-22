import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMOriginalAngularProductBounds

open Set Filter Topology MeasureTheory
namespace RHTower.D4BMOriginalAngularProducts
open D4BMJointSource D4BMJointWave D4BMModularCore
noncomputable section
set_option autoImplicit false

private theorem collar_exp_le_metric (L : ℝ) (hL : 0 < L) :
    Real.exp (-L) ≤ (tortoiseRadius (-L/2))^(2 : ℕ)-1 := by
  let R := tortoiseRadius (-L/2)
  have hR : 1 < R := tortoiseRadius_exterior (-L/2) (by linarith)
  have hR0 : R ≠ 0 := by linarith
  have h := radialUnit_one_sub (-L/2)
  rw [show 2*(-L/2)=-L by ring,radialUnit_inverse_radius] at h
  change 1-R⁻¹=Real.exp (-L)*(1+R⁻¹) at h
  have he : R-1=Real.exp (-L)*(R+1) := by
    have hh := congrArg (fun t : ℝ => t*R) h
    field_simp [hR0] at hh
    nlinarith
  calc
    _ ≤ Real.exp (-L)*(R+1)^(2 : ℕ) :=
      le_mul_of_one_le_right (Real.exp_nonneg _) (by nlinarith)
    _ = (Real.exp (-L)*(R+1))*(R+1) := by ring
    _ = R^(2 : ℕ)-1 := by rw [← he]; ring

private theorem iterated_period_norm_le {f : ℝ → ℝ → ℂ} {C T : ℝ}
    (hC : 0 ≤ C) (hT : 0 ≤ T)
    (h : ∀ p ∈ Ioc (0:ℝ) T, ∀ x : ℝ, ‖f p x‖ ≤ C*Real.exp (-p)) :
    ‖∫ p in (0:ℝ)..T, ∫ x in (-1/2:ℝ)..1/2, f p x‖ ≤ C := by
  have hx (p : ℝ) (hp : p ∈ Ioc (0:ℝ) T) :
      ‖∫ x in (-1/2:ℝ)..1/2, f p x‖ ≤ C*Real.exp (-p) := by
    have hi := intervalIntegral.norm_integral_le_of_norm_le_const
      (a:=(-1/2:ℝ)) (b:=(1/2:ℝ)) (fun x _ => h p hp x)
    simpa only [neg_div,sub_neg_eq_add,show (1/2:ℝ)+1/2=1 by norm_num,
      abs_one,mul_one] using hi
  have hi : IntervalIntegrable (fun p : ℝ => C*Real.exp (-p)) volume 0 T := by
    apply Continuous.intervalIntegrable
    fun_prop
  have ht := intervalIntegral.norm_integral_le_of_norm_le hT
    (Filter.Eventually.of_forall (fun p hp => hx p hp)) hi
  calc
    _ ≤ ∫ p in (0:ℝ)..T,C*Real.exp (-p) := ht
    _ = C*(1-Real.exp (-T)) := by
      rw [intervalIntegral.integral_const_mul,intervalIntegral.integral_comp_neg,
        integral_exp,neg_zero,Real.exp_zero]
    _ ≤ C := by nlinarith [Real.exp_nonneg (-T)]

/-- Every fixed exponential height weight is absorbed after both time and
horizontal integration, uniformly in independent cusp and horizon cutoffs. -/
theorem metric_angular_product_weighted_period_joint_limit
    (q : XiZeroCopy) (br : Bool) (amp : ℂ) (j : Fin 5) (d : Bool) (a : ℝ) :
    ∃ G : ℝ, 0 ≤ G ∧ ∀ w : ℂ, w.im ≠ 0 → G+1 ≤ w.re →
      ∀ T : ℝ × ℝ → Ici (0:ℝ),
      Tendsto (fun z : ℝ × ℝ => ∫ x in (-1/2:ℝ)..1/2,
        Complex.exp ((a:ℂ)*(z.2:ℂ))*
          ((∫ p in (0:ℝ)..(T z:ℝ),Complex.exp (-w*(p:ℂ))*
            (angularProduct q br amp w j d p z.1 x z.2-
              horizonAngularProduct q br amp w j d p x z.2))/
            ((tortoiseRadius (-z.1/2):ℂ)^(2 : ℕ)-1)))
        ((atTop : Filter ℝ) ×ˢ (atTop : Filter ℝ)) (𝓝 0) := by
  obtain ⟨N,hN⟩ := exists_nat_gt a
  obtain ⟨G,hG,h⟩ := metric_angular_product_time_error q br amp j d N
  refine ⟨G,hG,?_⟩
  intro w hwi hw T
  obtain ⟨B,hB,hb⟩ := h w hwi hw
  have hrate : a-(N:ℝ)<0 := sub_neg.mpr hN
  have hexp : Tendsto (fun k : ℝ => Real.exp ((a-(N:ℝ))*k)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp ((tendsto_const_mul_atBot_of_neg hrate).2 tendsto_id)
  have he : Tendsto (fun z : ℝ × ℝ => B*Real.exp ((a-(N:ℝ))*z.2))
      ((atTop : Filter ℝ) ×ˢ (atTop : Filter ℝ)) (𝓝 0) := by
    simpa only [Function.comp_def,mul_zero] using (hexp.const_mul B).comp tendsto_snd
  apply squeeze_zero_norm' _ he
  filter_upwards [hb.prod_mk (eventually_ge_atTop (0:ℝ))] with z hz
  have hx (x : ℝ) :
      ‖Complex.exp ((a:ℂ)*(z.2:ℂ))*
        ((∫ p in (0:ℝ)..(T z:ℝ),Complex.exp (-w*(p:ℂ))*
          (angularProduct q br amp w j d p z.1 x z.2-
            horizonAngularProduct q br amp w j d p x z.2))/
          ((tortoiseRadius (-z.1/2):ℂ)^(2 : ℕ)-1))‖ ≤
        B*Real.exp ((a-(N:ℝ))*z.2) := by
    rw [norm_mul,Complex.norm_exp]
    simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]
    calc
      _ ≤ Real.exp (a*z.2)*(B*Real.exp (-(N:ℝ)*z.2)) :=
        mul_le_mul_of_nonneg_left
          (hz.1 (T z) x z.2 (T z).property hz.2) (Real.exp_nonneg _)
      _ = B*Real.exp ((a-(N:ℝ))*z.2) := by
        rw [mul_left_comm,← Real.exp_add]
        congr 2
        ring
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const
    (a:=(-1/2:ℝ)) (b:=(1/2:ℝ)) (fun x _ => hx x)
  simpa only [neg_div,sub_neg_eq_add,show (1/2:ℝ)+1/2=1 by norm_num,
    abs_one,mul_one] using hi

/-- Weighted joint restoration in the same time-then-horizontal order as the
complete original boundary functional. -/
theorem metric_angular_product_weighted_time_period_joint_limit
    (q : XiZeroCopy) (br : Bool) (amp : ℂ) (j : Fin 5) (d : Bool) (a : ℝ) :
    ∃ G : ℝ, 0 ≤ G ∧ ∀ w : ℂ, w.im ≠ 0 → G+1 ≤ w.re →
      ∀ T : ℝ × ℝ → Ici (0:ℝ),
      Tendsto (fun z : ℝ × ℝ => Complex.exp ((a:ℂ)*(z.2:ℂ))*
        ((∫ p in (0:ℝ)..(T z:ℝ), ∫ x in (-1/2:ℝ)..1/2,
          Complex.exp (-w*(p:ℂ))*(angularProduct q br amp w j d p z.1 x z.2-
            horizonAngularProduct q br amp w j d p x z.2))/
          ((tortoiseRadius (-z.1/2):ℂ)^(2 : ℕ)-1)))
        ((atTop : Filter ℝ) ×ˢ (atTop : Filter ℝ)) (𝓝 0) := by
  obtain ⟨N,hN⟩ := exists_nat_gt a
  obtain ⟨G,hG,h⟩ := original_angular_product_error q br amp j d N
  refine ⟨G,hG,?_⟩
  intro w hwi hw T
  obtain ⟨B,hB,hb⟩ := h w hwi hw
  have hrate : a-(N:ℝ)<0 := sub_neg.mpr hN
  have hexp : Tendsto (fun k : ℝ => Real.exp ((a-(N:ℝ))*k)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp ((tendsto_const_mul_atBot_of_neg hrate).2 tendsto_id)
  have he : Tendsto (fun z : ℝ × ℝ => (2*B)*Real.exp ((a-(N:ℝ))*z.2))
      ((atTop : Filter ℝ) ×ˢ (atTop : Filter ℝ)) (𝓝 0) := by
    simpa only [Function.comp_def,mul_zero] using (hexp.const_mul (2*B)).comp tendsto_snd
  apply squeeze_zero_norm' _ he
  have hL := hb.and (eventually_gt_atTop (0:ℝ))
  filter_upwards [hL.prod_mk (eventually_ge_atTop (0:ℝ))] with z hz
  let R := tortoiseRadius (-z.1/2)
  let S := Real.exp (-z.1)+Real.exp (-w.re*z.1)
  let C := B*S*Real.exp (-(N:ℝ)*z.2)
  have hR : 1 < R := tortoiseRadius_exterior (-z.1/2) (by linarith)
  have hf : 0 < R^(2 : ℕ)-1 := by nlinarith
  have hgeo : Real.exp (-z.1) ≤ R^(2 : ℕ)-1 := collar_exp_le_metric z.1 hz.1.2
  have hdec : Real.exp (-w.re*z.1) ≤ Real.exp (-z.1) := by
    apply Real.exp_le_exp.mpr
    have hw1 : 1≤w.re := by linarith
    nlinarith
  have hS : S ≤ 2*(R^(2 : ℕ)-1) := by dsimp [S]; linarith
  have hC : 0 ≤ C := by dsimp [C,S]; positivity
  have ht : ‖∫ p in (0:ℝ)..(T z:ℝ), ∫ x in (-1/2:ℝ)..1/2,
      Complex.exp (-w*(p:ℂ))*(angularProduct q br amp w j d p z.1 x z.2-
        horizonAngularProduct q br amp w j d p x z.2)‖ ≤ C := by
    apply iterated_period_norm_le hC (T z).property
    intro p hp x
    simpa only [C,S,mul_assoc] using hz.1.1 p x z.2 hp.1 hz.2
  have hn : ‖(R:ℂ)^(2 : ℕ)-1‖=R^(2 : ℕ)-1 := by
    rw [← Complex.ofReal_pow,← Complex.ofReal_one,← Complex.ofReal_sub,
      Complex.norm_real,Real.norm_eq_abs,abs_of_pos hf]
  rw [norm_mul,Complex.norm_exp,norm_div,hn]
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]
  rw [← mul_div_assoc]
  apply (div_le_iff₀ hf).2
  calc
    _ ≤ Real.exp (a*z.2)*C := mul_le_mul_of_nonneg_left ht (Real.exp_nonneg _)
    _ = Real.exp (a*z.2)*(B*S*Real.exp (-(N:ℝ)*z.2)) := rfl
    _ ≤ Real.exp (a*z.2)*(B*(2*(R^(2 : ℕ)-1))*Real.exp (-(N:ℝ)*z.2)) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hS hB)
          (Real.exp_nonneg _)) (Real.exp_nonneg _)
    _ = (2*B)*Real.exp ((a-(N:ℝ))*z.2)*(R^(2 : ℕ)-1) := by
      have hexp_mul : Real.exp (a*z.2)*Real.exp (-(N:ℝ)*z.2) =
          Real.exp ((a-(N:ℝ))*z.2) := by
        rw [← Real.exp_add]
        congr 1
        ring
      calc
        _ = (2*B)*(Real.exp (a*z.2)*Real.exp (-(N:ℝ)*z.2))*(R^(2 : ℕ)-1) := by ring
        _ = _ := by rw [hexp_mul]

/-- The two actual temporal endpoint products obey the same weighted,
horizontal-period, independent cusp/horizon restoration law. -/
theorem metric_angular_product_weighted_endpoint_period_joint_limit
    (q : XiZeroCopy) (br : Bool) (amp : ℂ) (j : Fin 5) (d : Bool) (a : ℝ) :
    ∃ G : ℝ, 0 ≤ G ∧ ∀ w : ℂ, w.im ≠ 0 → G+1 ≤ w.re →
      ∀ P : ℝ × ℝ → Ioi (0:ℝ),
      Tendsto (fun z : ℝ × ℝ => ∫ x in (-1/2:ℝ)..1/2,
        Complex.exp ((a:ℂ)*(z.2:ℂ))*
          (Complex.exp (-w*((P z:ℝ):ℂ))*
            (angularProduct q br amp w j d (P z) z.1 x z.2-
              horizonAngularProduct q br amp w j d (P z) x z.2)/
            ((tortoiseRadius (-z.1/2):ℂ)^(2 : ℕ)-1)))
        ((atTop : Filter ℝ) ×ˢ (atTop : Filter ℝ)) (𝓝 0) := by
  obtain ⟨N,hN⟩ := exists_nat_gt a
  obtain ⟨G,hG,h⟩ := original_angular_product_error q br amp j d N
  refine ⟨G,hG,?_⟩
  intro w hwi hw P
  obtain ⟨B,hB,hb⟩ := h w hwi hw
  have hrate : a-(N:ℝ)<0 := sub_neg.mpr hN
  have hexp : Tendsto (fun k : ℝ => Real.exp ((a-(N:ℝ))*k)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp ((tendsto_const_mul_atBot_of_neg hrate).2 tendsto_id)
  have he : Tendsto (fun z : ℝ × ℝ => (2*B)*Real.exp ((a-(N:ℝ))*z.2))
      ((atTop : Filter ℝ) ×ˢ (atTop : Filter ℝ)) (𝓝 0) := by
    simpa only [Function.comp_def,mul_zero] using (hexp.const_mul (2*B)).comp tendsto_snd
  apply squeeze_zero_norm' _ he
  have hL := hb.and (eventually_gt_atTop (0:ℝ))
  filter_upwards [hL.prod_mk (eventually_ge_atTop (0:ℝ))] with z hz
  let R := tortoiseRadius (-z.1/2)
  have hR : 1 < R := tortoiseRadius_exterior (-z.1/2) (by linarith)
  have hf : 0 < R^(2 : ℕ)-1 := by nlinarith
  have hgeo : Real.exp (-z.1) ≤ R^(2 : ℕ)-1 := collar_exp_le_metric z.1 hz.1.2
  have hdec : Real.exp (-w.re*z.1) ≤ Real.exp (-z.1) := by
    apply Real.exp_le_exp.mpr
    have hw1 : 1≤w.re := by linarith
    nlinarith
  have hS : Real.exp (-z.1)+Real.exp (-w.re*z.1) ≤ 2*(R^(2 : ℕ)-1) := by linarith
  have hPexp : Real.exp (-(P z:ℝ)) ≤ 1 := by
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (neg_nonpos.mpr (P z).property.le)
  have hn : ‖(R:ℂ)^(2 : ℕ)-1‖=R^(2 : ℕ)-1 := by
    rw [← Complex.ofReal_pow,← Complex.ofReal_one,← Complex.ofReal_sub,
      Complex.norm_real,Real.norm_eq_abs,abs_of_pos hf]
  have hx (x : ℝ) :
      ‖Complex.exp ((a:ℂ)*(z.2:ℂ))*
        (Complex.exp (-w*((P z:ℝ):ℂ))*
          (angularProduct q br amp w j d (P z) z.1 x z.2-
            horizonAngularProduct q br amp w j d (P z) x z.2)/
          ((R:ℂ)^(2 : ℕ)-1))‖ ≤
        (2*B)*Real.exp ((a-(N:ℝ))*z.2) := by
    rw [norm_mul,Complex.norm_exp,norm_div,hn]
    simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]
    rw [← mul_div_assoc]
    apply (div_le_iff₀ hf).2
    calc
      _ ≤ Real.exp (a*z.2)*
          (B*(Real.exp (-z.1)+Real.exp (-w.re*z.1))*
            Real.exp (-(N:ℝ)*z.2)*Real.exp (-(P z:ℝ))) := by
        gcongr
        exact hz.1.1 (P z) x z.2 (P z).property hz.2
      _ ≤ Real.exp (a*z.2)*(B*(2*(R^(2 : ℕ)-1))*
            Real.exp (-(N:ℝ)*z.2)*Real.exp (-(P z:ℝ))) := by
        gcongr
      _ ≤ Real.exp (a*z.2)*(B*(2*(R^(2 : ℕ)-1))*
            Real.exp (-(N:ℝ)*z.2)*1) := by
        gcongr
      _ = (2*B)*Real.exp ((a-(N:ℝ))*z.2)*(R^(2 : ℕ)-1) := by
        have hexp_mul : Real.exp (a*z.2)*Real.exp (-(N:ℝ)*z.2) =
            Real.exp ((a-(N:ℝ))*z.2) := by
          rw [← Real.exp_add]
          congr 1
          ring
        calc
          _ = (2*B)*(Real.exp (a*z.2)*Real.exp (-(N:ℝ)*z.2))*(R^(2 : ℕ)-1) := by ring
          _ = _ := by rw [hexp_mul]
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const
    (a:=(-1/2:ℝ)) (b:=(1/2:ℝ)) (fun x _ => hx x)
  simpa only [R,neg_div,sub_neg_eq_add,show (1/2:ℝ)+1/2=1 by norm_num,
    abs_one,mul_one] using hi

end
end RHTower.D4BMOriginalAngularProducts
