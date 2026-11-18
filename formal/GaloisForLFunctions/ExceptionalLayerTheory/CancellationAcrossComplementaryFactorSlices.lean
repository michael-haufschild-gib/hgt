import GaloisForLFunctions.ExceptionalLayerTheory.CancellationOnRepeatedPrimeFactors
import GaloisForLFunctions.ExceptionalLayerTheory.OrdinaryPrimeCancellationInTheSquareRootBand
import GaloisForLFunctions.ExceptionalLayerTheory.IntegerCancellationOnMiddleDivisorIntervals

/-!
# Cancellation across complementary-factor slices

Below a short power cutoff use the interval length. Above the reciprocal
cutoff use the number of quotient fibres. Between them the two stencils
reduce to centered reciprocal fractional parts on ordinary integer blocks.
-/

noncomputable section
open Finset ArithmeticFunction RHTower
namespace GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval

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
              change |innerJump D v*centeredPrimeWeight R (T/v)| ≤ K*H
              rw [abs_mul]
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
    have hh := abs_quotient_tail_le mid (innerJump D) (centeredPrimeWeight R) hmass₀ hpre (hw hR)
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

end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
