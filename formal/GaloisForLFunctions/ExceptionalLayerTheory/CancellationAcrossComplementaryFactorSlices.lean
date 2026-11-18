import GaloisForLFunctions.ExceptionalLayerTheory.CancellationOnRepeatedPrimeFactors
import GaloisForLFunctions.ExceptionalLayerTheory.OrdinaryPrimeCancellationInTheSquareRootBand
import GaloisForLFunctions.PrimeExponentialSums.FractionalPartsOnIntegerReciprocalBlocks

/-!
# Cancellation across complementary-factor slices

Below a short power cutoff use the interval length. Above the reciprocal
cutoff use the number of quotient fibres. Between them the two stencils
reduce to centered reciprocal fractional parts on ordinary integer blocks.
-/

noncomputable section
open Finset ArithmeticFunction RHTower
namespace GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval

private theorem middle_divisor_block :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {T e d A B : ℕ}, 1 ≤ T → 1 ≤ e → 1 ≤ d → 1 ≤ A → A < B → B ≤ 2*A →
      (T : ℝ)^(49/100 : ℝ) ≤ e*(A : ℝ) → (A : ℝ) ≤ (T : ℝ)^(51/100 : ℝ) →
      |∑ t ∈ Ico A B, centeredQuotient T (e*t) d| ≤ C*(d*e : ℕ)*(T : ℝ)^(47/100 : ℝ) := by
  obtain ⟨C,hC,h⟩ := PrimeExponentialSums.centered_fractional_reciprocal_integer_block
  refine ⟨4*C,by positivity,?_⟩
  intro T e d A B hT he hd hA hAB hB hlo hhi
  have hx : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have hx₀ := zero_lt_one.trans_le hx
  have hA₀ : (0 : ℝ) < A := by exact_mod_cast hA
  have he₁ : (1 : ℝ) ≤ e := by exact_mod_cast he
  have hd₁ : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hde := one_le_mul_of_one_le_of_one_le hd₁ he₁
  have hde₀ := zero_lt_one.trans_le hde
  let P (b : ℝ) := (T : ℝ)^b
  have pos (b : ℝ) : 0 < P b := Real.rpow_pos_of_pos hx₀ _
  have mul (a b : ℝ) : P a*P b=P (a+b) := (Real.rpow_add hx₀ _ _).symm
  have powr (a b : ℝ) : (P a)^b = P (a*b) := (Real.rpow_mul hx₀.le _ _).symm
  have mono {a b : ℝ} (hz : a ≤ b) : P a ≤ P b := Real.rpow_le_rpow_of_exponent_le hx hz
  have one : P 1 = T := Real.rpow_one _
  let Z := (T : ℝ)/((d : ℝ)*e)
  let λ₀ := 2*Z/(2*(A : ℝ))^3
  let δ := P (-(4/100))
  have hZ : 0 < Z := div_pos hx₀ hde₀
  have hλ : 0 < λ₀ := by dsimp [λ₀]; positivity
  have hδ : 0 < δ := pos _
  have hλid : λ₀*(4*((d : ℝ)*e)*(A : ℝ)^3)=T := by dsimp [λ₀,Z]; field_simp <;> ring
  have sqrt_sq := Real.sq_sqrt hλ.le
  have first : (A : ℝ)*Real.sqrt λ₀ ≤ P (255/1000) := by
    have hlower : (T : ℝ) ≤ (P (255/1000))^2*(4*((d : ℝ)*e)*A) := by
      calc (T : ℝ) = (P (255/1000))^2*P (49/100) := by
              rw [←Real.rpow_natCast _ 2,powr,mul]; norm_num [P]
           _ ≤ _ := mul_le_mul_of_nonneg_left
              (hlo.trans (by nlinarith only [mul_le_mul_of_nonneg_right hd₁ (mul_nonneg (Nat.cast_nonneg e) hA₀.le),
                mul_nonneg (Nat.cast_nonneg e) hA₀.le])) (sq_nonneg _)
    have hs : ((A : ℝ)*Real.sqrt λ₀)^2*(4*((d : ℝ)*e)*A)=T := by
      rw [mul_pow,sqrt_sq,←hλid]; ring
    have hh := le_of_mul_le_mul_right (hs.trans_le hlower) (by positivity : 0 < 4*((d : ℝ)*e)*A)
    nlinarith only [hh,(pos (255/1000)).le,mul_nonneg hA₀.le (Real.sqrt_nonneg λ₀)]
  have second : 1/Real.sqrt λ₀ ≤ 2*((d : ℝ)*e)*P (265/1000) := by
    have hcube := pow_le_pow_left₀ hA₀.le hhi 3
    change (A : ℝ)^3 ≤ (P (51/100))^3 at hcube
    have ht : (P (265/1000))^2*T = (P (51/100))^3 := by
      rw [←Real.rpow_natCast _ 2,←Real.rpow_natCast _ 3,powr,powr,←one,mul]; norm_num
    have hs : (2*((d : ℝ)*e)*P (265/1000)*Real.sqrt λ₀)^2*(A : ℝ)^3 =
        ((d : ℝ)*e)*((P (265/1000))^2*T) := by
      rw [mul_pow,sqrt_sq,←hλid]; ring
    have hl := hcube.trans (le_mul_of_one_le_left (by positivity) hde)
    rw [←ht,←hs] at hl
    have hh := le_of_mul_le_mul_right (by simpa only [one_mul] using hl :
      1*(A : ℝ)^3 ≤ (2*((d : ℝ)*e)*P (265/1000)*Real.sqrt λ₀)^2*(A : ℝ)^3) (pow_pos hA₀ 3)
    apply (div_le_iff₀ (Real.sqrt_pos.mpr hλ)).mpr
    nlinarith only [hh,show 0 ≤ 2*((d : ℝ)*e)*P (265/1000)*Real.sqrt λ₀ by positivity]
  have small : δ*(A : ℝ) ≤ P (47/100) := by
    apply (mul_le_mul_of_nonneg_left hhi hδ.le).trans_eq
    dsimp only [δ]; rw [mul]; norm_num
  have large : ((A : ℝ)*Real.sqrt λ₀+1/Real.sqrt λ₀)/δ ≤ 3*((d : ℝ)*e)*P (47/100) := by
    apply (div_le_iff₀ hδ).mpr
    have hb : P (265/1000) ≤ P (47/100)*δ := by
      dsimp only [δ]; rw [mul]; apply mono; norm_num
    have hh := (first.trans (mono (by norm_num : (255/1000:ℝ) ≤ 265/1000))).trans
      (le_mul_of_one_le_left (pos _).le hde)
    have hm := mul_le_mul_of_nonneg_left hb (by positivity : 0 ≤ 3*((d : ℝ)*e))
    linarith only [hh,second,hm]
  have hsum := h hA le_rfl hAB.le hB hZ hδ
  have ht : (∑ t ∈ Ico A B, centeredQuotient T (e*t) d) =
      ∑ t ∈ Ico A B, (Int.fract (Z/t)-1/2) := by
    apply sum_congr rfl
    intro t _
    dsimp only [centeredQuotient,Z]
    rw [Nat.cast_mul,div_mul_eq_div_div,div_mul_eq_div_div]
  rw [ht,Nat.cast_mul]
  apply hsum.trans
  have hsmall := small.trans (le_mul_of_one_le_left (pos _).le hde)
  exact (mul_le_mul_of_nonneg_left (add_le_add hsmall large) hC).trans_eq (by dsimp [P]; ring)

private theorem middle_divisor_interval :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {T L U e d : ℕ}, 1 ≤ T → 1 ≤ e → 1 ≤ d →
      (T : ℝ)^(49/100 : ℝ) < (L : ℝ)+1 → (U : ℝ) ≤ (T : ℝ)^(51/100 : ℝ) →
      |∑ t ∈ Ioc (L/e) (U/e), centeredQuotient T (e*t) d| ≤
        C*(d*e : ℕ)*(1+Real.log T)*(T : ℝ)^(47/100 : ℝ) := by
  obtain ⟨C,hC,h⟩ := middle_divisor_block
  refine ⟨4*C,by positivity,?_⟩
  intro T L U e d hT he hd hlo hhi
  let lo := L/e+1
  let hi := U/e+1
  have hx : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have hlog := Real.log_natCast_nonneg T
  have huT : U ≤ T := by exact_mod_cast hhi.trans ((Real.rpow_le_rpow_of_exponent_le hx
    (by norm_num : (51/100 : ℝ) ≤ 1)).trans_eq (Real.rpow_one _))
  have heq : Ioc (L/e) (U/e) = Ico lo hi := by ext t; simp only [mem_Ioc,mem_Ico,lo,hi]; omega
  rw [heq]
  by_cases hhh : lo ≤ hi
  swap
  · rw [Ico_eq_empty (by omega),sum_empty,abs_zero]
    positivity
  let M := C*(d*e : ℕ)*(T : ℝ)^(47/100 : ℝ)
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hdya := Sieve.norm_sum_Ico_le_of_blocks (fun t => centeredQuotient T (e*t) d) M hhh
    (Nat.succ_pos _) hM (fun A B hA hAB hB hl hu => by
      rw [Real.norm_eq_abs]
      rcases hAB.eq_or_lt with rfl | hlt
      · simpa only [Ico_self,sum_empty,abs_zero] using hM
      · have hmul := (Nat.div_lt_iff_lt_mul he).mp (show L/e < A by exact hl)
        have hAl : (L : ℝ)+1 ≤ e*(A : ℝ) := by
          exact_mod_cast (by simpa only [Nat.mul_comm] using hmul : L+1 ≤ e*A)
        have hAu : A ≤ U := (show A ≤ U/e by dsimp [hi] at hu; omega).trans (Nat.div_le_self ..)
        exact h hT he hd hA hlt hB (hlo.le.trans hAl) ((by exact_mod_cast hAu : (A : ℝ) ≤ U).trans hhi))
  have hhi' : (hi : ℝ) ≤ 2*T := by
    have hh : hi ≤ T+1 := Nat.succ_le_succ ((Nat.div_le_self ..).trans huT)
    exact_mod_cast (by omega : hi ≤ 2*T)
  have hl := Real.log_le_log (by dsimp [hi]; positivity : (0 : ℝ) < hi) hhi'
  rw [Real.log_mul (by norm_num) (zero_lt_one.trans_le hx).ne'] at hl
  have hloghi : 1+Real.log hi ≤ 2*(1+Real.log T) := by
    linarith only [hl,hlog,Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hh := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hloghi (by norm_num : (0 : ℝ) ≤ 2)) hM
  rw [Real.norm_eq_abs] at hdya
  exact hdya.trans (hh.trans_eq (by dsimp [M]; ring))

private theorem middle_slice_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {D R T L U : ℕ}, 1 ≤ R → 1 ≤ T → 1 ≤ L →
      (T : ℝ)^(49/100 : ℝ) < (L : ℝ)+1 → (U : ℝ) ≤ (T : ℝ)^(51/100 : ℝ) →
      |∑ v ∈ Ioc L U, innerJump D v*centeredPrimeWeight R (T/v)| ≤
        C*((D+1 : ℕ) : ℝ)^2*(R : ℝ)^3*(1+Real.log T)*(T : ℝ)^(47/100 : ℝ) := by
  obtain ⟨C,hC,h⟩ := middle_divisor_interval
  obtain ⟨M,hM,hm⟩ := mass_uniform
  refine ⟨33024000*(1+M)*M*C,by positivity,?_⟩
  intro D R T L U hR hT hL hlo hhi
  let S := Ioc L U
  let J := 128*(128*R^2+1)
  let F := (1+Real.log T)*(T : ℝ)^(47/100 : ℝ)
  have hlog := Real.log_natCast_nonneg T
  have hF : 0 ≤ F := by dsimp [F]; positivity
  have hd₁ : 0 ≤ mass (D+1) := (abs_nonneg _).trans (abs_prefix_le_mass (Nat.succ_pos D) 0)
  have hr₁ : 0 ≤ mass R := (abs_nonneg _).trans (abs_prefix_le_mass hR 0)
  have inner (d : ℕ) (hd : d ∈ Icc 1 J) :
      |∑ v ∈ S, innerJump D v*centeredQuotient T v d| ≤
        mass (D+1)*(C*(J : ℝ)*(2*((D+1 : ℕ) : ℝ))*F) := by
    let z (v : ℕ) := centeredQuotient T v d
    let test (v e : ℕ) : ℝ := if e ∣ v then 1 else 0
    have id : (∑ v ∈ S, innerJump D v*z v) =
        -(stencil (D+1) fun e => ∑ v ∈ S, z v*test v e) := by
      rw [←stencil_weighted_sum,←sum_neg_distrib]
      apply sum_congr rfl
      intro v hv
      have hv₂ : 2 ≤ v := by have := (mem_Ioc.mp hv).1; omega
      rw [innerJump_divisor_stencil hv₂]
      dsimp only [test]
      ring
    change |∑ v ∈ S, innerJump D v*z v| ≤ _
    rw [id,abs_neg]
    apply abs_stencil_le (Nat.succ_pos D)
    intro e he
    have eqsum : (∑ v ∈ S, z v*test v e) = ∑ t ∈ Ioc (L/e) (U/e), z (e*t) := by
      rw [←sum_divisible_Ioc (mem_Icc.mp he).1, sum_filter]
      apply sum_congr rfl
      intro v _
      by_cases hv : e ∣ v <;> simp only [test,hv,if_true,if_false,mul_one,mul_zero]
    rw [eqsum]
    have ht := h hT (mem_Icc.mp he).1 (mem_Icc.mp hd).1 hlo hhi
    have hh : ((d*e : ℕ) : ℝ) ≤ (J : ℝ)*(2*((D+1 : ℕ) : ℝ)) := by
      exact_mod_cast Nat.mul_le_mul (mem_Icc.mp hd).2 (mem_Icc.mp he).2
    have hprod := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hh hC) hF
    apply ht.trans
    dsimp only [F] at hprod ⊢
    linarith only [hprod]
  have ht := abs_centered_block hR T S (innerJump D) (by positivity) inner
  have hr : (1 : ℝ) ≤ R := by exact_mod_cast hR
  have hR₂ : (1 : ℝ) ≤ (R : ℝ)^2 := one_le_pow₀ hr
  have hJ : (J : ℝ) ≤ 16512*(R : ℝ)^2 := by dsimp only [J]; push_cast; linarith only [hR₂]
  have hmR : 1+mass R ≤ (1+M)*R := by linarith only [hm R hR,hr]
  have hmul := mul_le_mul (mul_le_mul hmR (hm (D+1) (Nat.succ_pos D)) hd₁ (by positivity)) hJ
    (Nat.cast_nonneg J) (by positivity)
  have hh := mul_le_mul_of_nonneg_right hmul (by positivity : 0 ≤ 2000*C*((D+1 : ℕ) : ℝ)*F)
  apply ht.trans
  dsimp only [F] at hh ⊢
  linarith only [hh]

/-- Every complementary-factor slice saves a fixed power below one half
at its own horizon, uniformly in the lower product endpoint. -/
theorem complementary_slice_power_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {D R T : ℕ}, 1 ≤ R → 1 ≤ T → ∀ L : ℕ,
      |∑ v ∈ Ioc L T, innerJump D v*centeredPrimeWeight R (T/v)| ≤
        C*((D+1 : ℕ) : ℝ)^2*(R : ℝ)^3*(1+Real.log T)*(T : ℝ)^(49/100 : ℝ) := by
  obtain ⟨C,hC,hmiddle⟩ := middle_slice_bound
  obtain ⟨M,hM,hm⟩ := mass_uniform
  obtain ⟨F,hF,hw⟩ := centeredPrimeWeight_uniform
  let K := 2*(1+M)*F
  have hK : 0 ≤ K := by dsimp [K]; positivity
  refine ⟨K+C+K,by positivity,?_⟩
  intro D R T hR hT L
  have hx : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have hx₀ := zero_lt_one.trans_le hx
  have hlog := Real.log_natCast_nonneg T
  let P (b : ℝ) := (T : ℝ)^b
  have pos (b : ℝ) : 0 < P b := Real.rpow_pos_of_pos hx₀ _
  have mono {a b : ℝ} (h : a ≤ b) : P a ≤ P b := Real.rpow_le_rpow_of_exponent_le hx h
  let lo := max L ⌊P (49/100)⌋₊
  let mid := max L ⌊P (51/100)⌋₊
  let g := fun v : ℕ => innerJump D v*centeredPrimeWeight R (T/v)
  let H := ((D+1 : ℕ) : ℝ)^2*(R : ℝ)^3*(1+Real.log T)
  have hH : 0 ≤ H := by dsimp [H]; positivity
  have hd : (1 : ℝ) ≤ ((D+1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos D
  have hr : (1 : ℝ) ≤ R := by exact_mod_cast hR
  have hscale : ((D+1 : ℕ) : ℝ)*R ≤ H := by
    have hd₂ := pow_le_pow_right₀ hd (by norm_num : 1 ≤ 2)
    have hr₃ := pow_le_pow_right₀ hr (by norm_num : 1 ≤ 3)
    rw [pow_one] at hd₂ hr₃
    exact (mul_le_mul hd₂ hr₃ (Nat.cast_nonneg R) (sq_nonneg _)).trans
      (le_mul_of_one_le_right (by positivity) (le_add_of_nonneg_right hlog))
  have hmass : 1+mass (D+1) ≤ (1+M)*((D+1 : ℕ) : ℝ) := by
    linarith only [hm (D+1) (Nat.succ_pos D),hd]
  have hmass₀ : 0 ≤ 1+mass (D+1) := (abs_nonneg _).trans (innerJump_prefix_bound D 0)
  have hcoef : 2*(1+mass (D+1))*(F*(R : ℝ)) ≤ K*H := by
    have hh := mul_le_mul_of_nonneg_right hmass (by positivity : 0 ≤ 2*F*(R : ℝ))
    have hs := mul_le_mul_of_nonneg_left hscale hK
    dsimp only [K] at hs ⊢
    linarith only [hh,hs]
  by_cases hLT : L ≤ T
  swap
  · rw [Ioc_eq_empty_of_le (by omega),sum_empty,abs_zero]; positivity
  have lim (a : ℝ) (ha : a ≤ 1) : ⌊P a⌋₊ ≤ T := Nat.floor_le_of_le
    ((mono ha).trans_eq (Real.rpow_one _))
  have hLlo : L ≤ lo := le_max_left ..
  have hsplit : lo ≤ mid := max_le_max_left _ (Nat.floor_mono (mono (by norm_num)))
  have hmid : mid ≤ T := max_le hLT (lim _ (by norm_num))
  have hcount : ((lo-L : ℕ) : ℝ) ≤ P (49/100) :=
    (by exact_mod_cast (by dsimp [lo]; omega : lo-L ≤ ⌊P (49/100)⌋₊) :
      ((lo-L : ℕ) : ℝ) ≤ (⌊P (49/100)⌋₊ : ℕ)).trans (Nat.floor_le (pos _).le)
  have low : |∑ v ∈ Ioc L lo, g v| ≤ K*H*P (49/100) := by
    apply (abs_sum_le_sum_abs _ _).trans
    calc _ ≤ ∑ _v ∈ Ioc L lo, K*H := by
              apply sum_le_sum
              intro v _
              rw [show g v = _ from rfl,abs_mul]
              exact (mul_le_mul (innerJump_pointwise_bound D v) (hw hR _) (abs_nonneg _)
                (mul_nonneg (by norm_num) hmass₀)).trans hcoef
         _ ≤ _ := by
              rw [sum_const,Nat.card_Ioc,nsmul_eq_mul,mul_comm]
              exact mul_le_mul_of_nonneg_left hcount (mul_nonneg hK hH)
  have middle : |∑ v ∈ Ioc lo mid, g v| ≤ C*H*P (49/100) := by
    by_cases hl : L ≤ ⌊P (51/100)⌋₊
    · have h₁ : 1 ≤ lo := (Nat.one_le_floor_iff _).mpr (Real.one_le_rpow hx (by norm_num)) |>.trans (le_max_right ..)
      have h₂ : P (49/100) < (lo : ℝ)+1 := (Nat.lt_floor_add_one _).trans_le (by
        exact_mod_cast Nat.succ_le_succ (le_max_right L ⌊P (49/100)⌋₊))
      have h₃ : (mid : ℝ) ≤ P (51/100) := by dsimp [mid]; rw [max_eq_right hl]; exact Nat.floor_le (pos _).le
      have hh := hmiddle (D := D) hR hT h₁ h₂ h₃
      change |∑ v ∈ Ioc lo mid, g v| ≤ _ at hh
      apply hh.trans
      calc _ = C*H*P (47/100) := by dsimp [H,P]; ring
           _ ≤ _ := mul_le_mul_of_nonneg_left (mono (by norm_num)) (mul_nonneg hC hH)
    · have he : mid ≤ lo := by dsimp [mid,lo]; omega
      rw [Ioc_eq_empty_of_le he,sum_empty,abs_zero]; positivity
  have top : |∑ v ∈ Ioc mid T, g v| ≤ K*H*P (49/100) := by
    have hpre (t : ℕ) (_ : t ≤ T) : |∑ v ∈ Ioc 0 t, innerJump D v| ≤ 1+mass (D+1) := by
      rw [show Ioc 0 t = Icc 1 t by ext v; simp only [mem_Ioc,mem_Icc]; omega]
      exact innerJump_prefix_bound D t
    have hh := abs_quotient_tail_le mid (innerJump D) (centeredPrimeWeight R) hmass₀ (mul_nonneg hF (Nat.cast_nonneg R))
      hpre (hw hR)
    have hn : P (51/100) ≤ ((mid+1 : ℕ) : ℝ) := by
      have hh := Nat.succ_le_succ (le_max_right L ⌊P (51/100)⌋₊)
      push_cast
      exact (Nat.lt_floor_add_one _).le.trans (by exact_mod_cast hh)
    have ht : ((T/(mid+1) : ℕ) : ℝ) ≤ P (49/100) := by
      apply (Nat.cast_div_le (m := T) (n := mid+1)).trans
      apply (div_le_iff₀ (by positivity)).mpr
      apply le_trans _ (mul_le_mul_of_nonneg_left hn (pos _).le)
      dsimp only [P]
      rw [←Real.rpow_add hx₀,show (49/100+51/100 : ℝ)=1 by norm_num,Real.rpow_one]
    exact hh.trans (mul_le_mul hcoef ht (Nat.cast_nonneg _) (mul_nonneg hK hH))
  change |∑ v ∈ Ioc L T, g v| ≤ _
  rw [←sum_Ioc_consecutive g (hLlo.trans hsplit) hmid,←sum_Ioc_consecutive g hLlo hsplit]
  apply (abs_add_le _ _).trans ((add_le_add (abs_add_le _ _) le_rfl).trans _)
  apply (add_le_add (add_le_add low middle) top).trans_eq
  dsimp [H,P]; ring

#print axioms complementary_slice_power_bound
end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
