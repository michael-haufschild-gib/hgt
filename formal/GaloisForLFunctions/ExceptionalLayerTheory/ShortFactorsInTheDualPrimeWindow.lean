import GaloisForLFunctions.ExceptionalLayerTheory.ShortComplementsInTheSquareRootProductWindow

/-!
# Bare reciprocal divisor tests at short complementary factors

A sharp prime interval in the product window lies in the reciprocal
prime cancellation range for every short divisor dilation, before the
divisor tests are combined into a particular factorial weight.
-/

noncomputable section
open Finset RHTower
namespace GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval

private theorem prime_window_interval :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {X L U : ℕ} {Z : ℝ}, 1 ≤ X → 1 ≤ L →
      (X : ℝ)^(9999/10000 : ℝ) ≤ Z → Z ≤ X →
      (X : ℝ)^(4999/10000 : ℝ) ≤ L → (U : ℝ) ≤ (X : ℝ)^(5001/10000 : ℝ)+1 →
      |∑ p ∈ (Ico L U).filter Nat.Prime, Real.log p*(Int.fract (Z/p)-1/2)| ≤
        K*(1+Real.log X)*(X : ℝ)^(4997/10000 : ℝ) := by
  obtain ⟨K,hK,h⟩ := PrimeExponentialSums.centered_fractional_reciprocal_prime_block
  refine ⟨4*K,by positivity,?_⟩
  intro X L U Z hX hL hzlo hzhi hlo hhi
  have hx : (1 : ℝ) ≤ X := by exact_mod_cast hX
  let P (s : ℝ) := (X : ℝ)^s
  have powr (a b : ℝ) : (P a)^b=P (a*b) := (Real.rpow_mul (Nat.cast_nonneg X) _ _).symm
  have mono {s t : ℝ} (h : s ≤ t) : P s ≤ P t := Real.rpow_le_rpow_of_exponent_le hx h
  let f (p : ℕ) := if p.Prime then Real.log p*(Int.fract (Z/p)-1/2) else 0
  let M := K*P (4997/10000)
  have hM : 0 ≤ M := by dsimp [M,P]; positivity
  have hlx := Real.log_natCast_nonneg X
  by_cases hlu : L ≤ U
  swap
  · rw [Ico_eq_empty (by omega),filter_empty,sum_empty,abs_zero]; positivity
  have hsum := Sieve.norm_sum_Ico_le_of_blocks f M hlu hL hM (fun A B hA hAB hB hl hu => by
    rw [Real.norm_eq_abs]
    rcases hAB.eq_or_lt with rfl | hlt
    · simpa only [Ico_self,sum_empty,abs_zero] using hM
    · have ha : P (4999/10000) ≤ A := hlo.trans (by exact_mod_cast hl)
      have hh : (A : ℝ)+1 ≤ U := by exact_mod_cast (show A+1 ≤ U from hlt.trans_le hu)
      have hb : (A : ℝ) ≤ P (5001/10000) := by linarith only [hh,hhi]
      have hz₁ : (A : ℝ)^(999/500 : ℝ) ≤ Z := by
        apply (Real.rpow_le_rpow (Nat.cast_nonneg A) hb (by norm_num : (0 : ℝ) ≤ 999/500)).trans
        rw [powr]; exact (mono (by norm_num)).trans hzlo
      have hz₂ : Z ≤ (A : ℝ)^(1001/500 : ℝ) := by
        apply hzhi.trans
        have ht : P 1 ≤ (P (4999/10000))^(1001/500 : ℝ) := by rw [powr]; exact mono (by norm_num)
        rw [show P 1=X from Real.rpow_one _] at ht
        exact ht.trans (Real.rpow_le_rpow (by dsimp [P]; positivity) ha (by norm_num))
      have hA' : (A : ℝ)^(999/1000 : ℝ) ≤ P (4997/10000) := by
        apply (Real.rpow_le_rpow (Nat.cast_nonneg A) hb (by norm_num : (0 : ℝ) ≤ 999/1000)).trans
        rw [powr]; exact mono (by norm_num)
      have ht := h A B Z hA hlt.le hB hz₁ hz₂
      rw [sum_filter] at ht
      exact ht.trans (mul_le_mul_of_nonneg_left hA' hK))
  have hu₁ : (0 : ℝ) < U := by exact_mod_cast hL.trans hlu
  have hu₂ : (U : ℝ) ≤ 2*X := by
    have hp := (mono (by norm_num : (5001/10000 : ℝ) ≤ 1)).trans_eq (show P 1=X from Real.rpow_one _)
    linarith only [hhi,hp,hx]
  have hlog := Real.log_le_log hu₁ hu₂
  rw [Real.log_mul (by norm_num) (zero_lt_one.trans_le hx).ne'] at hlog
  have hh : 1+Real.log U ≤ 2*(1+Real.log X) := by
    linarith only [hlog,hlx,Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ)<2)]
  rw [sum_filter]
  rw [Real.norm_eq_abs] at hsum
  exact hsum.trans ((mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hh (by norm_num : (0 : ℝ) ≤ 2)) hM).trans_eq
    (by dsimp [M,P]; ring))

/-- Every short complementary factor is allowed with an arbitrary
bounded coefficient, uniformly in the divisor dilation and both endpoints. -/
theorem short_factor_prime_divisor_window :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {X e F L U : ℕ}, 1 ≤ X → 1 ≤ e →
      (e : ℝ) ≤ (X : ℝ)^(1/100000 : ℝ) → Real.sqrt X ≤ (L : ℝ)+1 →
      (U : ℝ) ≤ (X : ℝ)^(500000001/1000000000 : ℝ) →
      ∀ (β : ℕ → ℝ) {B : ℝ}, 0 ≤ B →
      (∀ j ∈ Icc 1 ⌊(X : ℝ)^(1/1000000 : ℝ)⌋₊, |β j| ≤ B) →
      |∑ j ∈ Icc 1 ⌊(X : ℝ)^(1/1000000 : ℝ)⌋₊, β j*
        ∑ p ∈ squareRootWindowPrimes F L U j, Real.log p*centeredQuotient X (p*j) e| ≤
        K*B*(1+Real.log X)*Real.sqrt X := by
  obtain ⟨K,hK,h⟩ := prime_window_interval
  refine ⟨K,hK,?_⟩
  intro X e F L U hx he he' hL hU β B hB hβ
  have hX : (1 : ℝ) ≤ X := by exact_mod_cast hx
  let P (s : ℝ) := (X : ℝ)^s
  have pos (s : ℝ) : 0 < P s := Real.rpow_pos_of_pos (zero_lt_one.trans_le hX) _
  have mono {s t : ℝ} (h : s ≤ t) : P s ≤ P t := Real.rpow_le_rpow_of_exponent_le hX h
  have mul (s t : ℝ) : P s*P t=P (s+t) := (Real.rpow_add (zero_lt_one.trans_le hX) _ _).symm
  let Q := ⌊P (1/1000000)⌋₊
  let M := K*(1+Real.log X)*P (4997/10000)
  have hl := Real.log_natCast_nonneg X
  have hM : 0 ≤ M := by dsimp [M,P]; positivity
  have hq : (Q : ℝ) ≤ P (1/1000000) := Nat.floor_le (pos _).le
  have term (j : ℕ) (hj : j ∈ Icc 1 Q) :
      |β j*∑ p ∈ squareRootWindowPrimes F L U j, Real.log p*centeredQuotient X (p*j) e| ≤ B*M := by
    obtain ⟨hj₁,hjq⟩ := mem_Icc.mp hj
    have hj' : (j : ℝ) ≤ P (1/1000000) := (by exact_mod_cast hjq : (j : ℝ) ≤ Q).trans hq
    have he₁ : (1 : ℝ) ≤ e := by exact_mod_cast he
    have hj₁' : (1 : ℝ) ≤ j := by exact_mod_cast hj₁
    have hj₀ := zero_lt_one.trans_le hj₁'
    let Z := ((X : ℝ)/e)/j
    have hz₁ : P (9999/10000) ≤ Z := by
      apply (le_div_iff₀ hj₀).mpr
      apply (le_div_iff₀ (zero_lt_one.trans_le he₁)).mpr
      have hh := mul_le_mul (mul_le_mul_of_nonneg_left hj' (pos (9999/10000)).le) he'
        (Nat.cast_nonneg e) (mul_nonneg (pos (9999/10000)).le (pos (1/1000000)).le)
      apply hh.trans
      change (P (9999/10000)*P (1/1000000))*P (1/100000) ≤ X
      rw [mul,mul]
      exact (mono (by norm_num : (9999/10000 : ℝ)+1/1000000+1/100000 ≤ 1)).trans_eq (Real.rpow_one _)
    have hz₂ : Z ≤ X := (div_le_self (div_nonneg (Nat.cast_nonneg X) (Nat.cast_nonneg e)) hj₁').trans
      (div_le_self (Nat.cast_nonneg X) he₁)
    have hlo : P (4999/10000) ≤ (L/j+1 : ℕ) := by
      refine le_of_mul_le_mul_right (show P (4999/10000)*(j : ℝ) ≤ ((L/j+1 : ℕ) : ℝ)*j from ?_) hj₀
      have hh : L+1 ≤ (L/j+1)*j := (Nat.lt_mul_div_succ L hj₁).trans_eq (Nat.mul_comm ..)
      have hh' : (L : ℝ)+1 ≤ ((L/j+1 : ℕ) : ℝ)*j := by exact_mod_cast hh
      apply (mul_le_mul_of_nonneg_left hj' (pos (4999/10000)).le).trans
      rw [mul]; exact ((mono (by norm_num : (4999/10000 : ℝ)+1/1000000 ≤ 1/2)).trans_eq
        (Real.sqrt_eq_rpow _).symm).trans (hL.trans hh')
    have hhi : ((U/j+1 : ℕ) : ℝ) ≤ P (5001/10000)+1 := by
      push_cast
      exact add_le_add ((by exact_mod_cast Nat.div_le_self U j : ((U/j : ℕ) : ℝ) ≤ U).trans
        (hU.trans (mono (by norm_num)))) (le_refl (1 : ℝ))
    have ht := h hx (show 1 ≤ max (F+1) (L/j+1) from (show 1 ≤ F+1 from Nat.succ_pos F).trans (le_max_left ..))
      hz₁ hz₂ (hlo.trans (by exact_mod_cast le_max_right (F+1) (L/j+1))) hhi
    have eq (p : ℕ) : centeredQuotient X (p*j) e=Int.fract (Z/p)-1/2 := by
      dsimp only [centeredQuotient,Z]
      rw [Nat.cast_mul,mul_comm (p : ℝ) j,div_mul_eq_div_div]
    rw [abs_mul]
    apply mul_le_mul (hβ j hj) _ (abs_nonneg _) hB
    simpa only [squareRootWindowPrimes,eq] using ht
  apply (abs_sum_le_sum_abs _ _).trans
  apply (sum_le_sum term).trans
  rw [sum_const,Nat.card_Icc,nsmul_eq_mul,show Q+1-1=Q by omega]
  have hh := mul_le_mul_of_nonneg_right hq (mul_nonneg hB hM)
  apply hh.trans
  have hroot : P (1/1000000)*P (4997/10000) ≤ Real.sqrt X := by
    rw [mul,Real.sqrt_eq_rpow]; exact mono (by norm_num)
  have hcost := mul_le_mul_of_nonneg_left hroot (by positivity : 0 ≤ K*B*(1+Real.log X))
  dsimp only [M]; linarith only [hcost]

#print axioms short_factor_prime_divisor_window
end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
