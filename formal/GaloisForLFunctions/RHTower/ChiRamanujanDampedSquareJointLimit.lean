import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import GaloisForLFunctions.RHTower.ChiRamanujanDampedSquareTransfer

noncomputable section
open Filter Set MeasureTheory
open GaloisForLFunctions.RHTower
open scoped Topology
namespace RHTower.BAGTrace

private theorem normalize_source_bound (K A B C x y : ℝ) (hx : x ≠ 0) (hy : y ≠ 0) :
    K*(A+x*B+C)/(x*y) = K*(A/(x*y)+B/y+C/(x*y)) := by
  field_simp

private theorem square_left_error_tendsto {d : ℝ} (hd : 0 < d) :
    Tendsto (fun T : ℝ =>
      Real.exp (-(d/(1+T)^9)*T^18)*(1+T)^55*(1+2/(d/(1+T)^9)^2)/T^18)
      atTop (𝓝 0) := by
  let K := (1+2/d^2)*2^73
  have ht : Tendsto (fun T : ℝ => K*T^73*Real.exp (-(d/512)*T)) atTop (𝓝 0) := by
    have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (73 : ℕ) (d/512)
      (by positivity)).const_mul K
    simpa only [Real.rpow_natCast,mul_assoc,mul_zero] using h
  apply squeeze_zero' _ _ ht
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT
    positivity
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT
    have hT0 : 0 < T := by linarith
    have hS : 0 < 1+T := by linarith
    have hp9 : (1+T)^9 ≤ 512*T^9 := by
      calc (1+T)^9 ≤ (2*T)^9 := by gcongr; linarith
        _ = _ := by ring
    have hexp : (d/512)*T ≤ (d/(1+T)^9)*T^18 := by
      rw [show (d/(1+T)^9)*T^18 = d*T^18/(1+T)^9 by ring,
        le_div_iff₀ (pow_pos hS 9)]
      calc (d/512)*T*(1+T)^9 ≤ (d/512)*T*(512*T^9) := by gcongr
        _ = d*T^10 := by ring
        _ ≤ d*T^18 := mul_le_mul_of_nonneg_left
          (pow_le_pow_right₀ hT (show 10 ≤ 18 by omega)) hd.le
    have hinv : 1+2/(d/(1+T)^9)^2 ≤ (1+2/d^2)*(1+T)^18 := by
      have h1 : 1 ≤ (1+T)^18 := one_le_pow₀ (by linarith)
      have he : 2/(d/(1+T)^9)^2 = (2/d^2)*(1+T)^18 := by
        field_simp
      rw [he]
      nlinarith
    have hp73 : (1+T)^73 ≤ 2^73*T^73 := by
      calc (1+T)^73 ≤ (2*T)^73 := by gcongr; linarith
        _ = _ := mul_pow _ _ _
    have hden : 1 ≤ T^18 := one_le_pow₀ hT
    have he : Real.exp (-(d/(1+T)^9)*T^18) ≤ Real.exp (-(d/512)*T) :=
      Real.exp_le_exp.mpr (by nlinarith [hexp])
    calc _ ≤ Real.exp (-(d/(1+T)^9)*T^18)*(1+T)^55*(1+2/(d/(1+T)^9)^2) :=
          div_le_self (by positivity) hden
      _ ≤ Real.exp (-(d/512)*T)*(1+T)^55*((1+2/d^2)*(1+T)^18) := by
        exact mul_le_mul (mul_le_mul_of_nonneg_right he (by positivity)) hinv
          (by positivity) (by positivity)
      _ = (1+2/d^2)*(1+T)^73*Real.exp (-(d/512)*T) := by ring
      _ ≤ (1+2/d^2)*(2^73*T^73)*Real.exp (-(d/512)*T) := by gcongr
      _ = _ := by dsimp [K]; ring

private theorem square_right_scale {T : ℝ} (hT : 0 < T) :
    (Real.exp (T^18))^(1+1/T^18) = Real.exp (T^18)*Real.exp 1 := by
  rw [Real.rpow_def_of_pos (Real.exp_pos _),Real.log_exp,← Real.exp_add]
  congr 1
  field_simp

private theorem square_tail_error_tendsto :
    Tendsto (fun T : ℝ =>
      (Real.exp (T^18))^(1+1/T^18)/(1/T^18)^3 * (T^(-59 : ℝ)/59) /
        (Real.exp (T^18)*T^18)) atTop (𝓝 0) := by
  have ht : Tendsto (fun T : ℝ => (Real.exp 1/59)/T^23) atTop (𝓝 0) :=
    (tendsto_pow_atTop (by omega : 23 ≠ 0)).const_div_atTop _
  apply ht.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
  rw [square_right_scale hT,show (-59 : ℝ) = -(59 : ℕ) by norm_num,
    Real.rpow_neg hT.le,Real.rpow_natCast]
  field_simp

private theorem square_horizontal_error_tendsto :
    Tendsto (fun T : ℝ =>
      (Real.exp (T^18))^(1+1/T^18)*(1+T)^54/(1+T)^60 /
        (Real.exp (T^18)*T^18)) atTop (𝓝 0) := by
  have ht : Tendsto (fun T : ℝ => Real.exp 1/T^18) atTop (𝓝 0) :=
    (tendsto_pow_atTop (by omega : 18 ≠ 0)).const_div_atTop _
  apply squeeze_zero' _ _ ht
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT
    positivity
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT
    have hT0 : 0 < T := by linarith
    rw [square_right_scale hT0]
    have hpow : (1+T)^54 ≤ (1+T)^60 :=
      pow_le_pow_right₀ (by linarith) (by omega)
    calc _ = (Real.exp 1/T^18)*((1+T)^54/(1+T)^60) := by field_simp
      _ ≤ (Real.exp 1/T^18)*1 :=
        mul_le_mul_of_nonneg_left ((div_le_one (by positivity)).mpr hpow) (by positivity)
      _ = _ := mul_one _

private theorem square_parameters_eventually {d C η : ℝ}
    (hd : 0 < d) (hC : 0 < C) (hη : 0 < η) :
    ∀ᶠ T : ℝ in atTop, 1 ≤ T ∧
      0 < d/(1+T)^9 ∧ 0 < 1/T^18 ∧ 1/T^18 ≤ d/(1+T)^9 ∧
      ∀ c ∈ Ioc 0 C, 0 < c/T^18 ∧ c/T^18 < (d/(1+T)^9)/4 ∧ c/T^18 ≤ η := by
  have hsmall : ∀ᶠ T : ℝ in atTop, ((C+1)*512)/T^9 < d/4 :=
    ((tendsto_pow_atTop (by omega : 9 ≠ 0)).const_div_atTop ((C+1)*512)).eventually
      (gt_mem_nhds (by positivity))
  have hηsmall : ∀ᶠ T : ℝ in atTop, C/T^18 < η :=
    ((tendsto_pow_atTop (by omega : 18 ≠ 0)).const_div_atTop C).eventually (gt_mem_nhds hη)
  filter_upwards [eventually_ge_atTop (1 : ℝ),hsmall,hηsmall] with T hT hs hηT
  have hT0 : 0 < T := by linarith
  have hp : (1+T)^9 ≤ 512*T^9 := by
    calc (1+T)^9 ≤ (2*T)^9 := by gcongr; linarith
      _ = _ := by ring
  have hratio : ((C+1)/T^18)*(1+T)^9 < d/4 := by
    calc _ ≤ ((C+1)/T^18)*(512*T^9) := by gcongr
      _ = ((C+1)*512)/T^9 := by field_simp
      _ < _ := hs
  have hwidth : (C+1)/T^18 < (d/(1+T)^9)/4 := by
    rw [div_right_comm]
    exact (lt_div_iff₀ (by positivity)).mpr hratio
  have hδ : 0 < d/(1+T)^9 := by positivity
  refine ⟨hT,hδ,by positivity,?_,?_⟩
  · have h : 1/T^18 ≤ (C+1)/T^18 := by gcongr; linarith
    linarith
  · intro c hc
    refine ⟨div_pos hc.1 (pow_pos hT0 18),?_,?_⟩
    · exact (div_le_div_of_nonneg_right (by linarith [hc.2]) (by positivity)).trans_lt hwidth
    · exact ((div_le_div_of_nonneg_right hc.2 (by positivity)).trans_lt hηT).le

/-- Actual joint square law in a height parameter covering every sufficiently large height. -/
private theorem dampedSquareWindowEnergy_uniform_reparameterized {C : ℝ} (hC : 0 < C) :
    TendstoUniformlyOn
      (fun T c => dampedSquareWindowEnergy (c/T^18) (Real.exp (T^18)) -
        (dampedSquareCrossover c : ℂ)*dampedSquareWindowMellin 1)
      (fun _ => 0) atTop (Ioc 0 C) := by
  obtain ⟨d,hd,hrem⟩ := exists_dampedSquareWindowEnergy_remainder_bound
  obtain ⟨K,hK,hbound⟩ := hrem 60 (by omega)
  obtain ⟨η,hη,B,hB,hres⟩ := exists_dampedSquareResiduePacket_uniform_coalescence
  let tail : ℝ → ℝ := fun T =>
    (Real.exp (T^18))^(1+1/T^18)/(1/T^18)^3*(T^(-59 : ℝ)/59)/(Real.exp (T^18)*T^18)
  let left : ℝ → ℝ := fun T =>
    Real.exp (-(d/(1+T)^9)*T^18)*(1+T)^55*(1+2/(d/(1+T)^9)^2)/T^18
  let hor : ℝ → ℝ := fun T =>
    (Real.exp (T^18))^(1+1/T^18)*(1+T)^54/(1+T)^60/(Real.exp (T^18)*T^18)
  let E : ℝ → ℝ := fun T => K*(tail T+left T+hor T)+B/T^18
  have hE : Tendsto E atTop (𝓝 0) := by
    have hBlim : Tendsto (fun T : ℝ => B/T^18) atTop (𝓝 0) :=
      (tendsto_pow_atTop (by omega : 18 ≠ 0)).const_div_atTop B
    have h := (((square_tail_error_tendsto.add (square_left_error_tendsto hd.1)).add
      square_horizontal_error_tendsto).const_mul K).add hBlim
    simpa only [add_zero,mul_zero] using h
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro r hr
  filter_upwards [square_parameters_eventually hd.1 hC hη.1,hE.eventually (gt_mem_nhds hr)]
    with T hparams hEr
  obtain ⟨hT,hδ,hb,hbδ,hparams⟩ := hparams
  have hT0 : 0 < T := by linarith
  have hX : 1 < Real.exp (T^18) := Real.one_lt_exp_iff.mpr (pow_pos hT0 18)
  intro c hc
  obtain ⟨he,heδ,heη⟩ := hparams c hc
  have hsource := hbound hT hδ (le_refl (d/(1+T)^9)) he heδ hb hbδ hX
  have hpacket := hres he heη hX
  have hcscale : (c/T^18)*Real.log (Real.exp (T^18)) = c := by
    rw [Real.log_exp]
    field_simp
  rw [hcscale,Real.log_exp] at hpacket
  have hleftscale : (Real.exp (T^18))^(1-d/(1+T)^9) =
      Real.exp (T^18)*Real.exp (-(d/(1+T)^9)*T^18) := by
    rw [Real.rpow_def_of_pos (Real.exp_pos _),Real.log_exp,← Real.exp_add]
    congr 1
    ring
  have hsource' : ‖dampedSquareWindowEnergy (c/T^18) (Real.exp (T^18)) -
      dampedSquareResiduePacket (c/T^18) (Real.exp (T^18))‖ ≤ K*(tail T+left T+hor T) := by
    convert hsource using 1
    rw [Real.log_exp,hleftscale]
    dsimp [tail,left,hor]
    norm_num only [Nat.cast_ofNat,show (1-(60 : ℝ)) = -59 by norm_num,
      show ((60 : ℝ)-1) = 59 by norm_num]
    simpa only [mul_assoc] using (normalize_source_bound K
      ((Real.exp (T^18))^(1+1/T^18)/(1/T^18)^3*(T^(-59 : ℝ)/59))
      (Real.exp (-(d/(1+T)^9)*T^18)*((1+T)^55*(1+2/(d/(1+T)^9)^2)))
      ((Real.exp (T^18))^(1+1/T^18)*(1+T)^54/(1+T)^60)
      (Real.exp (T^18)) (T^18) (Real.exp_ne_zero _) (pow_ne_zero 18 hT0.ne')).symm
  have htotal : ‖dampedSquareWindowEnergy (c/T^18) (Real.exp (T^18)) -
      (dampedSquareCrossover c : ℂ)*dampedSquareWindowMellin 1‖ ≤ E T := by
    calc _ = ‖(dampedSquareWindowEnergy (c/T^18) (Real.exp (T^18)) -
          dampedSquareResiduePacket (c/T^18) (Real.exp (T^18))) +
        (dampedSquareResiduePacket (c/T^18) (Real.exp (T^18)) -
          (dampedSquareCrossover c : ℂ)*dampedSquareWindowMellin 1)‖ := by congr 1; ring
      _ ≤ _ := (norm_add_le _ _).trans (add_le_add hsource' hpacket)
  simpa only [dist_zero_left] using htotal.trans_lt hEr

theorem dampedSquareWindowEnergy_tendstoUniformlyOn {C : ℝ} (hC : 0 < C) :
    TendstoUniformlyOn
      (fun X c => dampedSquareWindowEnergy (c/Real.log X) X -
        (dampedSquareCrossover c : ℂ)*dampedSquareWindowMellin 1)
      (fun _ => 0) atTop (Ioc 0 C) := by
  have hroot : Tendsto (fun X : ℝ => (Real.log X)^((18 : ℝ)⁻¹)) atTop atTop :=
    (tendsto_rpow_atTop (by positivity : 0 < (18 : ℝ)⁻¹)).comp Real.tendsto_log_atTop
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro r hr
  have h := Metric.tendstoUniformlyOn_iff.mp
    (dampedSquareWindowEnergy_uniform_reparameterized hC) r hr
  filter_upwards [hroot.eventually h,eventually_gt_atTop (1 : ℝ)] with X hXr hX
  intro c hc
  have hp : ((Real.log X)^((18 : ℝ)⁻¹))^18 = Real.log X :=
    Real.rpow_inv_natCast_pow (Real.log_pos hX).le (by omega : 18 ≠ 0)
  simpa only [hp,Real.exp_log (show 0 < X by linarith)] using hXr c hc

/-- Uniformity on the shrinking damping interval, including ε log X → 0. -/
theorem dampedSquareWindowEnergy_uniform_joint_limit {C : ℝ} (hC : 0 < C) :
    ∀ r > 0, ∀ᶠ X : ℝ in atTop, ∀ ε : ℝ, 0 < ε → ε ≤ C/Real.log X →
      ‖dampedSquareWindowEnergy ε X -
        (dampedSquareCrossover (ε*Real.log X) : ℂ)*dampedSquareWindowMellin 1‖ < r := by
  intro r hr
  have h := Metric.tendstoUniformlyOn_iff.mp (dampedSquareWindowEnergy_tendstoUniformlyOn hC) r hr
  filter_upwards [h,eventually_gt_atTop (1 : ℝ)] with X hXr hX
  intro ε hε hεC
  have hL : 0 < Real.log X := Real.log_pos hX
  have hc : ε*Real.log X ∈ Ioc 0 C := ⟨mul_pos hε hL,(le_div_iff₀ hL).mp hεC⟩
  have he : (ε*Real.log X)/Real.log X = ε := by field_simp
  simpa only [he,dist_zero_left] using hXr (ε*Real.log X) hc

/-- The critical Mellin value is the mass of the literal physical window. -/
theorem dampedSquareWindowMellin_one :
    dampedSquareWindowMellin 1 =
      ((∫ x : ℝ,bagPhysicalHeightWindow x : ℝ) : ℂ) := by
  simp only [dampedSquareWindowMellin,mellin,sub_self,Complex.cpow_zero,one_smul]
  rw [MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero ?_,
    integral_complex_ofReal]
  intro x hx
  apply Complex.ofReal_eq_zero.mpr
  have hx0 : x ≤ 0 := le_of_not_gt hx
  by_contra hn
  have hm : x ∈ Metric.ball (3/2 : ℝ) bagPhysicalHeightWindow.rOut := by
    rw [← bagPhysicalHeightWindow.support_eq]
    exact hn
  have hb : |x-3/2| < (1/2 : ℝ) := by
    simpa only [Metric.mem_ball,Real.dist_eq,bagPhysicalHeightWindow] using hm
  linarith [(abs_lt.mp hb).1]

/-- Complete physical-window square law, uniform down to arbitrarily small positive damping. -/
theorem dampedSquare_physical_window_joint_limit {C : ℝ} (hC : 0 < C) :
    ∀ r > 0, ∀ᶠ X : ℝ in atTop, ∀ ε : ℝ, 0 < ε → ε ≤ C/Real.log X →
      ‖dampedSquareWindowEnergy ε X -
        (dampedSquareCrossover (ε*Real.log X) : ℂ)*
          ((∫ x : ℝ,bagPhysicalHeightWindow x : ℝ) : ℂ)‖ < r := by
  simpa only [dampedSquareWindowMellin_one] using dampedSquareWindowEnergy_uniform_joint_limit hC

end RHTower.BAGTrace
