import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import GaloisForLFunctions.RHTower.ChiRamanujanDampedSquareTestWindowBounds

/-!
# Uniform damping-height square law for an arbitrary smooth window

Let `W` be smooth with support in `[a,b]`, `0 < a ≤ b`, and `D_ε` the damped divisor
coefficient. The normalized energy `∑ D_ε(n)² W(n/X)/(X ε² log X)` differs from the two
normalized residues by the four rectangle edges and both original-line tails; all are bounded
uniformly in damping. With `T = (log X)^{1/18}`, `δ = d/(1+T)^9` and Mellin order `60`, the
total error tends to zero uniformly for `0 < ε ≤ C/log X`, so the energy tends to
`Ψ(ε log X) ∫ W`, `Ψ(c) = (1-e^{-2c})/(2c)`, including arbitrarily small `ε log X`.
-/

noncomputable section
open Complex Set Filter MeasureTheory
open scoped Topology
open GaloisForLFunctions.HTGeometry.TestFunctionPerron
open GaloisForLFunctions.RHTower
namespace RHTower.BAGTrace

variable {W : ℝ → ℂ} {a b : ℝ}


private theorem test_rectangle_solve (r l b u p : ℂ)
    (h : b-u+I*r-I*l = 2*Real.pi*I*p) :
    r-(2*Real.pi : ℂ)*p = l+I*(b-u) := by
  linear_combination (norm := (ring_nf; simp [I_sq])) -I*h

private theorem test_source_normalization (S P e x L : ℂ)
    (he : e ≠ 0) (hx : x ≠ 0) (hL : L ≠ 0) :
    S/(x*e^2*L)-P/(x*L) = ((2*Real.pi : ℂ)*S/e^2-(2*Real.pi : ℂ)*P) /
      ((2*Real.pi : ℂ)*x*L) := by
  have hp : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  field_simp

/-- The actual physical square energy at the joint damping-height normalization. -/
def dampedSquareTestWindowEnergy (W : ℝ → ℂ) (ε X : ℝ) : ℂ :=
  (∑' n : ℕ,(pmPowerDampedDivisorCoeff ε n : ℂ)^2*
    W (n/X))/((X : ℂ)*(ε : ℂ)^2*Real.log X)

/-- Exact transfer error: both original tails, left edge and both horizontal edges. -/
theorem exists_dampedSquareTestWindowEnergy_transfer (hW : IsTest W a b) :
    ∃ d ∈ Ioc (0 : ℝ) (1/128), ∀ {T δ ε b X : ℝ},
      0 < T → 0 < δ → δ ≤ d/(1+T)^9 → 0 < ε → ε < δ/4 →
      0 < b → b ≤ δ → 1 < X → 1 ≤ a*X →
      dampedSquareTestWindowEnergy W ε X-dampedSquareTestResiduePacket W ε X =
        (((∫ t : ℝ,dampedSquareTestContourIntegrand W ε X ((1+b : ℝ)+t*I)) -
           ∫ t in (-T)..T,dampedSquareTestContourIntegrand W ε X ((1+b : ℝ)+t*I)) +
         (∫ t in (-T)..T,dampedSquareTestContourIntegrand W ε X ((1-δ : ℝ)+t*I)) +
         I*((∫ x in (1-δ)..(1+b),dampedSquareTestContourIntegrand W ε X ((x : ℂ)+(-T)*I)) -
             ∫ x in (1-δ)..(1+b),dampedSquareTestContourIntegrand W ε X ((x : ℂ)+T*I))) /
          ((2*Real.pi*X*Real.log X : ℝ) : ℂ) := by
  obtain ⟨d,hd,hrect⟩ := exists_dampedSquareTestContour_rectangle hW
  refine ⟨d,hd,?_⟩
  intro T δ ε b X hT hδ hδd hε hεδ hb hbδ hX haX
  have hδsmall : δ ≤ d := hδd.trans (div_le_self hd.1.le (one_le_pow₀ (by linarith)))
  have hε1 : ε < 1/16 := by linarith [hd.2]
  have he := hrect hT hδ hδd hε hεδ hb hbδ (by linarith : 0 < X)
  simp only [rectIntegral,sub_re,add_re,ofReal_re,mul_re,ofReal_im,I_re,I_im,
    mul_zero,sub_zero,add_zero,sub_im,add_im,mul_im,mul_one,zero_sub,
    zero_add,smul_eq_mul,ofReal_neg] at he
  have hper := dampedSquareTest_weighted_sum_normalized_eq_integral hW hε.le hε1 hX.le haX
    (show 1 < 1+b by linarith)
  let P := dampedSquareTestMellinNumerator W ε X 1/(2*ε)+
    dampedSquareTestMellinNumerator W ε X (1-2*ε)/(-2*ε)
  have hline :
      (∫ t in (-T)..T,dampedSquareTestContourIntegrand W ε X ((1+b : ℝ)+t*I)) -
        (2*Real.pi : ℂ)*P =
      (∫ t in (-T)..T,dampedSquareTestContourIntegrand W ε X ((1-δ : ℝ)+t*I)) +
        I*((∫ x in (1-δ)..(1+b),dampedSquareTestContourIntegrand W ε X ((x : ℂ)+(-T)*I)) -
           ∫ x in (1-δ)..(1+b),dampedSquareTestContourIntegrand W ε X ((x : ℂ)+T*I)) := by
    exact test_rectangle_solve _ _ _ _ P he
  have hX0 : (X : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by linarith)
  have he0 : (ε : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hε.ne'
  have hL0 : (Real.log X : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.log_pos hX).ne'
  rw [add_assoc,← hline,← hper,sub_add_sub_cancel]
  simpa only [dampedSquareTestWindowEnergy,dampedSquareTestResiduePacket,P,ofReal_mul,
    ofReal_ofNat] using test_source_normalization
      (∑' n : ℕ,(pmPowerDampedDivisorCoeff ε n : ℂ)^2*W (n/X))
      P ε X (Real.log X) he0 hX0 hL0

private theorem test_transfer_numerator_norm_le (r l b u : ℂ) :
    ‖r+l+I*(b-u)‖ ≤ ‖r‖+‖l‖+‖b‖+‖u‖ := by
  calc _ ≤ ‖r+l‖+‖I*(b-u)‖ := norm_add_le _ _
    _ ≤ (‖r‖+‖l‖)+(‖b‖+‖u‖) := by
      rw [norm_mul,norm_I,one_mul]
      exact add_le_add (norm_add_le _ _) (norm_sub_le _ _)
    _ = _ := by ring

/-- Complete actual transfer error, uniform in damping and retaining every edge/tail. -/
theorem exists_dampedSquareTestWindowEnergy_remainder_bound (hW : IsTest W a b) :
    ∃ d ∈ Ioc (0 : ℝ) (1/128), ∀ j : ℕ, 2 ≤ j → ∃ K > 0,
    ∀ {T δ ε b X : ℝ}, 1 ≤ T → 0 < δ → δ ≤ d/(1+T)^9 →
      0 < ε → ε < δ/4 → 0 < b → b ≤ δ → 1 < X → 1 ≤ a*X →
      ‖dampedSquareTestWindowEnergy W ε X-dampedSquareTestResiduePacket W ε X‖ ≤
        K*(X^(1+b)/b^3*(T^(1-(j : ℝ))/((j : ℝ)-1)) +
          X^(1-δ)*(1+T)^55*(1+2/δ^2) +
          X^(1+b)*(1+T)^54/(1+T)^j)/(X*Real.log X) := by
  obtain ⟨d₁,hd₁,htransfer⟩ := exists_dampedSquareTestWindowEnergy_transfer hW
  obtain ⟨d₂,hd₂,C,hC,hedges⟩ := exists_dampedSquareTestContour_edge_bounds hW
  let d := min d₁ d₂
  have hd : d ∈ Ioc (0 : ℝ) (1/128) :=
    ⟨lt_min hd₁.1 hd₂.1,(min_le_left _ _).trans hd₁.2⟩
  refine ⟨d,hd,?_⟩
  intro j hj
  obtain ⟨A,hA,horiz⟩ := hedges j
  obtain ⟨B,hB,htails⟩ := exists_dampedSquareTestContour_two_tail_bound hW j hj
  let K := B+C+2*A
  have hK : 0 < K := by dsimp [K]; positivity
  refine ⟨K/(2*Real.pi),by positivity,?_⟩
  intro T δ ε b X hT hδ hδd hε hεδ hb hbδ hX haX
  have hX0 : 0 < X := by linarith
  have hlog : 0 < Real.log X := Real.log_pos hX
  have hδ₁ : δ ≤ d₁/(1+T)^9 := hδd.trans
    (div_le_div_of_nonneg_right (min_le_left _ _) (by positivity))
  have hδ₂ : δ ≤ d₂/(1+T)^9 := hδd.trans
    (div_le_div_of_nonneg_right (min_le_right _ _) (by positivity))
  have hδsmall : δ ≤ d := hδd.trans (div_le_self hd.1.le (one_le_pow₀ (by linarith)))
  have hε1 : ε < 1/16 := by linarith [hd.2]
  have hb1 : b ≤ 1 := by linarith [hd.2]
  have hT0 : 0 < T := by linarith
  have hjR : (1 : ℝ) < j := by exact_mod_cast (show 1 < j by omega)
  let D := X^(1+b)/b^3*(T^(1-(j : ℝ))/((j : ℝ)-1))
  let L := X^(1-δ)*(1+T)^55*(1+2/δ^2)
  let H := X^(1+b)*(1+T)^54/(1+T)^j
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hH : 0 ≤ H := by dsimp [H]; positivity
  have htail : ‖(∫ t : ℝ,dampedSquareTestContourIntegrand W ε X ((1+b : ℝ)+t*I)) -
      ∫ t in (-T)..T,dampedSquareTestContourIntegrand W ε X ((1+b : ℝ)+t*I)‖ ≤ B*D := by
    convert htails hε hε1 hb hb1 hX0 hT0 using 1
    dsimp [D]
    ring
  obtain ⟨hl,hh⟩ := horiz hT hδ hδ₂ hε hεδ hb hbδ hX.le
  have hleft : ‖∫ t in (-T)..T,dampedSquareTestContourIntegrand W ε X ((1-δ : ℝ)+t*I)‖ ≤ C*L := by
    convert hl using 1
    dsimp [L]
    ring
  have hbottom : ‖∫ x in (1-δ)..(1+b),dampedSquareTestContourIntegrand W ε X ((x : ℂ)+(-T)*I)‖ ≤ A*H := by
    simpa only [H,ofReal_neg,mul_div_assoc,mul_assoc] using hh (-T) (by rw [abs_neg,abs_of_pos hT0])
  have htop : ‖∫ x in (1-δ)..(1+b),dampedSquareTestContourIntegrand W ε X ((x : ℂ)+T*I)‖ ≤ A*H := by
    convert hh T (abs_of_pos hT0) using 1
    dsimp [H]
    ring
  rw [htransfer hT0 hδ hδ₁ hε hεδ hb hbδ hX haX,norm_div,Complex.norm_real,
    Real.norm_of_nonneg (by positivity : 0 ≤ 2*Real.pi*X*Real.log X)]
  have htriangle := test_transfer_numerator_norm_le
    ((∫ t : ℝ,dampedSquareTestContourIntegrand W ε X ((1+b : ℝ)+t*I)) -
      ∫ t in (-T)..T,dampedSquareTestContourIntegrand W ε X ((1+b : ℝ)+t*I))
    (∫ t in (-T)..T,dampedSquareTestContourIntegrand W ε X ((1-δ : ℝ)+t*I))
    (∫ x in (1-δ)..(1+b),dampedSquareTestContourIntegrand W ε X ((x : ℂ)+(-T)*I))
    (∫ x in (1-δ)..(1+b),dampedSquareTestContourIntegrand W ε X ((x : ℂ)+T*I))
  have hnum : B*D+C*L+A*H+A*H ≤ K*(D+L+H) := by
    have hBK : B ≤ K := by dsimp [K]; linarith
    have hCK : C ≤ K := by dsimp [K]; linarith
    have hAK : 2*A ≤ K := by dsimp [K]; linarith
    calc _ = B*D+C*L+(2*A)*H := by ring
      _ ≤ K*D+K*L+K*H := by gcongr
      _ = _ := by ring
  calc _ ≤ (B*D+C*L+A*H+A*H)/(2*Real.pi*X*Real.log X) := by
        gcongr
        exact htriangle.trans (by gcongr)
    _ ≤ K*(D+L+H)/(2*Real.pi*X*Real.log X) := by gcongr
    _ = _ := by dsimp [D,L,H]; ring



private theorem test_normalize_source_bound (K A B C x y : ℝ) (hx : x ≠ 0) (hy : y ≠ 0) :
    K*(A+x*B+C)/(x*y) = K*(A/(x*y)+B/y+C/(x*y)) := by
  field_simp

private theorem test_square_left_error_tendsto {d : ℝ} (hd : 0 < d) :
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

private theorem test_square_right_scale {T : ℝ} (hT : 0 < T) :
    (Real.exp (T^18))^(1+1/T^18) = Real.exp (T^18)*Real.exp 1 := by
  rw [Real.rpow_def_of_pos (Real.exp_pos _),Real.log_exp,← Real.exp_add]
  congr 1
  field_simp

private theorem test_square_tail_error_tendsto :
    Tendsto (fun T : ℝ =>
      (Real.exp (T^18))^(1+1/T^18)/(1/T^18)^3 * (T^(-59 : ℝ)/59) /
        (Real.exp (T^18)*T^18)) atTop (𝓝 0) := by
  have ht : Tendsto (fun T : ℝ => (Real.exp 1/59)/T^23) atTop (𝓝 0) :=
    (tendsto_pow_atTop (by omega : 23 ≠ 0)).const_div_atTop _
  apply ht.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
  rw [test_square_right_scale hT,show (-59 : ℝ) = -(59 : ℕ) by norm_num,
    Real.rpow_neg hT.le,Real.rpow_natCast]
  field_simp

private theorem test_square_horizontal_error_tendsto :
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
    rw [test_square_right_scale hT0]
    have hpow : (1+T)^54 ≤ (1+T)^60 :=
      pow_le_pow_right₀ (by linarith) (by omega)
    calc _ = (Real.exp 1/T^18)*((1+T)^54/(1+T)^60) := by field_simp
      _ ≤ (Real.exp 1/T^18)*1 :=
        mul_le_mul_of_nonneg_left ((div_le_one (by positivity)).mpr hpow) (by positivity)
      _ = _ := mul_one _

private theorem test_square_parameters_eventually {d C η : ℝ}
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
private theorem dampedSquareTestWindowEnergy_uniform_reparameterized (hW : IsTest W a b) {C : ℝ} (hC : 0 < C) :
    TendstoUniformlyOn
      (fun T c => dampedSquareTestWindowEnergy W (c/T^18) (Real.exp (T^18)) -
        (dampedSquareCrossover c : ℂ)*dampedSquareTestMellin W 1)
      (fun _ => 0) atTop (Ioc 0 C) := by
  obtain ⟨d,hd,hrem⟩ := exists_dampedSquareTestWindowEnergy_remainder_bound hW
  obtain ⟨K,hK,hbound⟩ := hrem 60 (by omega)
  obtain ⟨η,hη,B,hB,hres⟩ := exists_dampedSquareTestResiduePacket_uniform_coalescence hW
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
    have h := (((test_square_tail_error_tendsto.add (test_square_left_error_tendsto hd.1)).add
      test_square_horizontal_error_tendsto).const_mul K).add hBlim
    simpa only [add_zero,mul_zero] using h
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro r hr
  have haT : ∀ᶠ T : ℝ in atTop, 1 ≤ a*Real.exp (T^18) :=
    ((Real.tendsto_exp_atTop.comp (tendsto_pow_atTop (by norm_num : 18 ≠ 0))).const_mul_atTop
      hW.pos).eventually_ge_atTop 1
  filter_upwards [test_square_parameters_eventually hd.1 hC hη.1,hE.eventually (gt_mem_nhds hr),haT]
    with T hparams hEr haX
  obtain ⟨hT,hδ,hb,hbδ,hparams⟩ := hparams
  have hT0 : 0 < T := by linarith
  have hX : 1 < Real.exp (T^18) := Real.one_lt_exp_iff.mpr (pow_pos hT0 18)
  intro c hc
  obtain ⟨he,heδ,heη⟩ := hparams c hc
  have hsource := hbound hT hδ (le_refl (d/(1+T)^9)) he heδ hb hbδ hX haX
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
  have hsource' : ‖dampedSquareTestWindowEnergy W (c/T^18) (Real.exp (T^18)) -
      dampedSquareTestResiduePacket W (c/T^18) (Real.exp (T^18))‖ ≤ K*(tail T+left T+hor T) := by
    convert hsource using 1
    rw [Real.log_exp,hleftscale]
    dsimp [tail,left,hor]
    norm_num only [Nat.cast_ofNat,show (1-(60 : ℝ)) = -59 by norm_num,
      show ((60 : ℝ)-1) = 59 by norm_num]
    simpa only [mul_assoc] using (test_normalize_source_bound K
      ((Real.exp (T^18))^(1+1/T^18)/(1/T^18)^3*(T^(-59 : ℝ)/59))
      (Real.exp (-(d/(1+T)^9)*T^18)*((1+T)^55*(1+2/(d/(1+T)^9)^2)))
      ((Real.exp (T^18))^(1+1/T^18)*(1+T)^54/(1+T)^60)
      (Real.exp (T^18)) (T^18) (Real.exp_ne_zero _) (pow_ne_zero 18 hT0.ne')).symm
  have htotal : ‖dampedSquareTestWindowEnergy W (c/T^18) (Real.exp (T^18)) -
      (dampedSquareCrossover c : ℂ)*dampedSquareTestMellin W 1‖ ≤ E T := by
    calc _ = ‖(dampedSquareTestWindowEnergy W (c/T^18) (Real.exp (T^18)) -
          dampedSquareTestResiduePacket W (c/T^18) (Real.exp (T^18))) +
        (dampedSquareTestResiduePacket W (c/T^18) (Real.exp (T^18)) -
          (dampedSquareCrossover c : ℂ)*dampedSquareTestMellin W 1)‖ := by congr 1; ring
      _ ≤ _ := (norm_add_le _ _).trans (add_le_add hsource' hpacket)
  simpa only [dist_zero_left] using htotal.trans_lt hEr

theorem dampedSquareTestWindowEnergy_tendstoUniformlyOn (hW : IsTest W a b) {C : ℝ} (hC : 0 < C) :
    TendstoUniformlyOn
      (fun X c => dampedSquareTestWindowEnergy W (c/Real.log X) X -
        (dampedSquareCrossover c : ℂ)*dampedSquareTestMellin W 1)
      (fun _ => 0) atTop (Ioc 0 C) := by
  have hroot : Tendsto (fun X : ℝ => (Real.log X)^((18 : ℝ)⁻¹)) atTop atTop :=
    (tendsto_rpow_atTop (by positivity : 0 < (18 : ℝ)⁻¹)).comp Real.tendsto_log_atTop
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro r hr
  have h := Metric.tendstoUniformlyOn_iff.mp
    (dampedSquareTestWindowEnergy_uniform_reparameterized hW hC) r hr
  filter_upwards [hroot.eventually h,eventually_gt_atTop (1 : ℝ)] with X hXr hX
  intro c hc
  have hp : ((Real.log X)^((18 : ℝ)⁻¹))^18 = Real.log X :=
    Real.rpow_inv_natCast_pow (Real.log_pos hX).le (by omega : 18 ≠ 0)
  simpa only [hp,Real.exp_log (show 0 < X by linarith)] using hXr c hc

/-- Uniformity on the shrinking damping interval, including ε log X → 0. -/
theorem dampedSquareTestWindowEnergy_uniform_joint_limit (hW : IsTest W a b) {C : ℝ} (hC : 0 < C) :
    ∀ r > 0, ∀ᶠ X : ℝ in atTop, ∀ ε : ℝ, 0 < ε → ε ≤ C/Real.log X →
      ‖dampedSquareTestWindowEnergy W ε X -
        (dampedSquareCrossover (ε*Real.log X) : ℂ)*dampedSquareTestMellin W 1‖ < r := by
  intro r hr
  have h := Metric.tendstoUniformlyOn_iff.mp (dampedSquareTestWindowEnergy_tendstoUniformlyOn hW hC) r hr
  filter_upwards [h,eventually_gt_atTop (1 : ℝ)] with X hXr hX
  intro ε hε hεC
  have hL : 0 < Real.log X := Real.log_pos hX
  have hc : ε*Real.log X ∈ Ioc 0 C := ⟨mul_pos hε hL,(le_div_iff₀ hL).mp hεC⟩
  have he : (ε*Real.log X)/Real.log X = ε := by field_simp
  simpa only [he,dist_zero_left] using hXr (ε*Real.log X) hc

/-- **Uniform damping-height square law for every smooth positive-axis window.**  For `W` smooth
with support in `[a,b]`, `0 < a ≤ b`, and every `C > 0`, uniformly in `0 < ε ≤ C/log X`,
`∑ D_ε(n)² W(n/X)/(X ε² log X) - Ψ(ε log X) ∫ W → 0`, `Ψ(c) = (1-e^{-2c})/(2c)`. -/
theorem dampedSquare_testWindow_joint_limit (hW : IsTest W a b) {C : ℝ} (hC : 0 < C) :
    ∀ r > 0, ∀ᶠ X : ℝ in atTop, ∀ ε : ℝ, 0 < ε → ε ≤ C/Real.log X →
      ‖dampedSquareTestWindowEnergy W ε X -
        (dampedSquareCrossover (ε*Real.log X) : ℂ)*(∫ x : ℝ, W x)‖ < r := by
  simpa only [dampedSquareTestMellin_one hW] using
    dampedSquareTestWindowEnergy_uniform_joint_limit hW hC

/-- At fixed `c > 0`, `(log X/X) ∑ D_{c/log X}(n)² W(n/X) → (c/2)(1-e^{-2c}) ∫ W`. -/
theorem tendsto_dampedSquare_testWindow_fixed_damping (hW : IsTest W a b) {c : ℝ} (hc : 0 < c) :
    Tendsto (fun X : ℝ => (Real.log X/X : ℂ)*∑' n : ℕ,
        (pmPowerDampedDivisorCoeff (c/Real.log X) n : ℂ)^2*W (n/X)) atTop
      (𝓝 ((c/2*(1-Real.exp (-2*c)) : ℝ)*(∫ x : ℝ, W x))) := by
  have hlim := dampedSquare_testWindow_joint_limit hW (C := c) hc
  have heq : ∀ᶠ X : ℝ in atTop, (Real.log X/X : ℂ)*∑' n : ℕ,
      (pmPowerDampedDivisorCoeff (c/Real.log X) n : ℂ)^2*W (n/X) =
      (c^2 : ℂ)*dampedSquareTestWindowEnergy W (c/Real.log X) X := by
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with X hX
    have hL : (Real.log X : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.log_pos hX).ne'
    have hX0 : (X : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by linarith)
    have hc0 : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc.ne'
    unfold dampedSquareTestWindowEnergy
    push_cast
    field_simp
  have hval : ((c/2*(1-Real.exp (-2*c)) : ℝ) : ℂ)*(∫ x : ℝ, W x) =
      (c^2 : ℂ)*((dampedSquareCrossover c : ℂ)*(∫ x : ℝ, W x)) := by
    unfold dampedSquareCrossover
    push_cast
    field_simp
  rw [hval]
  have hE : Tendsto (fun X : ℝ => dampedSquareTestWindowEnergy W (c/Real.log X) X) atTop
      (𝓝 ((dampedSquareCrossover c : ℂ)*(∫ x : ℝ, W x))) := by
    rw [tendsto_iff_norm_sub_tendsto_zero, Metric.tendsto_nhds]
    intro r hr
    filter_upwards [hlim r hr, eventually_gt_atTop (1 : ℝ)] with X hX hX1
    have hL : 0 < Real.log X := Real.log_pos hX1
    have h := hX (c/Real.log X) (div_pos hc hL) le_rfl
    have he : c/Real.log X*Real.log X = c := by field_simp
    rw [he] at h
    simpa only [Real.dist_eq, sub_zero, abs_norm] using h
  exact Tendsto.congr' (EventuallyEq.symm heq) (hE.const_mul _)

end RHTower.BAGTrace
