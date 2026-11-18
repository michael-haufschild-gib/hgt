import GaloisForLFunctions.PrimeExponentialSums.FractionalPartsAcrossAReciprocalProductWindow

/-!
# Divisor dilations in square-root product windows

One integral correlation length works for all short divisor dilations
of the reciprocal phase. The fourth-root saving pays for the whole
product interval beyond the square root.
-/

noncomputable section
open Finset RHTower
namespace GaloisForLFunctions.PrimeExponentialSums

/-- A common integral correlation length fits every divisor up to `J` and
pays for the excess of the product above the square root. -/
theorem square_root_product_scales {X a c J L U : ℕ} (hX : 1 ≤ X)
    (hlarge : 64 ≤ (X : ℝ)^(1/25000000 : ℝ)) (hstencil : (J : ℝ) ≤ (X : ℝ)^(1/25000000 : ℝ))
    (ha : (X : ℝ)^(1/1000000 : ℝ) ≤ a) (hc : (X : ℝ)^(1/1000000 : ℝ) ≤ c)
    (hL : Real.sqrt X ≤ (L : ℝ)+1) (hU : (U : ℝ) ≤ (X : ℝ)^(500000001/1000000000 : ℝ)) :
    ∃ H : ℕ, 1 ≤ H ∧ H^4 ≤ a ∧ H ≤ c ∧ (J : ℝ)*(U : ℝ)^2 ≤ H*X ∧
      16*(X : ℝ) ≤ H*(L : ℝ)^2 ∧ (U : ℝ) ≤ Real.sqrt X*Real.sqrt (Real.sqrt H) := by
  have hx : (1 : ℝ) ≤ X := by exact_mod_cast hX
  let P (s : ℝ) := (X : ℝ)^s
  have pos (s : ℝ) : 0 < P s := Real.rpow_pos_of_pos (zero_lt_one.trans_le hx) _
  have mono {s t : ℝ} (h : s ≤ t) : P s ≤ P t := Real.rpow_le_rpow_of_exponent_le hx h
  have mul (s t : ℝ) : P s*P t=P (s+t) := (Real.rpow_add (zero_lt_one.trans_le hx) _ _).symm
  have power (s : ℝ) (k : ℕ) : (P s)^k=P (s*k) := by
    rw [←Real.rpow_natCast _ k]; exact (Real.rpow_mul (Nat.cast_nonneg X) _ _).symm
  let r := P (1/25000000)
  let H := ⌊P (1/5000000)⌋₊
  have hr : 64 ≤ r := hlarge
  have Hr : P (1/5000000)=r^5 := by
    dsimp only [r]; rw [power]; norm_num
  have h₁ : 1 ≤ r := by linarith only [hr]
  have hr₀ : 0 ≤ r := zero_le_one.trans h₁
  have hr₄ : r^4 ≤ (H : ℝ) := by
    have hh := Nat.lt_floor_add_one (P (1/5000000))
    change P (1/5000000) < (H : ℝ)+1 at hh
    rw [Hr,pow_succ] at hh
    have hbig := one_le_pow₀ h₁ (n := 4)
    have hg := mul_le_mul_of_nonneg_right (show 2 ≤ r by linarith only [hr]) (pow_nonneg hr₀ 4)
    change 2*r^4 ≤ r*r^4 at hg
    linarith only [hh,hbig,hg]
  have h₁₄ : r ≤ r^4 := by simpa only [pow_one] using (pow_le_pow_right₀ h₁ (by norm_num : 1 ≤ 4))
  have hrH := h₁₄.trans hr₄
  have hH₁ : 1 ≤ H := by exact_mod_cast h₁.trans hrH
  have hHmx : (H : ℝ) ≤ P (1/5000000) := Nat.floor_le (pos _).le
  have hHa : H^4 ≤ a := by
    have hh := pow_le_pow_left₀ (Nat.cast_nonneg H) hHmx 4
    rw [power] at hh
    exact_mod_cast hh.trans ((mono (by norm_num : (1/5000000 : ℝ)*(4 : ℕ) ≤ 1/1000000)).trans ha)
  have hHc : H ≤ c := by exact_mod_cast hHmx.trans ((mono (by norm_num : (1/5000000 : ℝ) ≤ 1/1000000)).trans hc)
  have hr2 : (2 : ℝ) ≤ Real.sqrt X := by
    exact (show 2 ≤ r by linarith only [hr]).trans ((mono (by norm_num : (1/25000000 : ℝ) ≤ 1/2)).trans_eq
      (Real.sqrt_eq_rpow _).symm)
  have hLL : Real.sqrt X ≤ 2*(L : ℝ) := by linarith only [hL,hr2]
  have ht : 16*(X : ℝ) ≤ H*(L : ℝ)^2 := by
    have hs := pow_le_pow_left₀ (Real.sqrt_nonneg (X : ℝ)) hLL 2
    rw [Real.sq_sqrt (Nat.cast_nonneg X)] at hs
    have hh := mul_le_mul_of_nonneg_right (hr.trans hrH) (sq_nonneg (L : ℝ))
    linarith only [hs,hh]
  have hu : (J : ℝ)*(U : ℝ)^2 ≤ H*X := by
    have hh := mul_le_mul hstencil (pow_le_pow_left₀ (Nat.cast_nonneg U) hU 2) (sq_nonneg _) hr₀
    apply hh.trans
    change P (1/25000000)*(P (500000001/1000000000))^2 ≤ H*X
    have he : P (1/25000000)*(P (500000001/1000000000))^2 ≤ r^4*X := by
      calc _ = P (1/25000000+(500000001/1000000000)*2) := by rw [power,mul]; norm_num
           _ ≤ P ((1/25000000)*4+1) := mono (by norm_num)
           _ = r^4*X := by rw [←mul,show r^4=P ((1/25000000)*4) from power _ 4,show P 1=X from Real.rpow_one _]
    exact he.trans (mul_le_mul_of_nonneg_right hr₄ (Nat.cast_nonneg X))
  have hroot : r ≤ Real.sqrt (Real.sqrt H) := by
    apply (Real.le_sqrt hr₀ (Real.sqrt_nonneg _)).mpr
    apply (Real.le_sqrt (sq_nonneg _) (Nat.cast_nonneg _)).mpr
    exact (show (r^2)^2=r^4 by ring).le.trans hr₄
  have hprod : (U : ℝ) ≤ Real.sqrt X*Real.sqrt (Real.sqrt H) := by
    apply hU.trans
    apply le_trans _ (mul_le_mul_of_nonneg_left hroot (Real.sqrt_nonneg (X : ℝ)))
    rw [Real.sqrt_eq_rpow]
    change P _ ≤ P (1/2)*P (1/25000000)
    rw [mul]; exact mono (by norm_num)
  exact ⟨H,hH₁,hHa,hHc,hu,ht,hprod⟩

/-- A single divisor test over both long factor intervals has square-root
cost with only the two dyadic logarithms and the coefficient bounds. -/
theorem square_root_fractional_divisor_window :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {a b c d L U e X : ℕ}, 1 ≤ e → 1 ≤ X →
      64 ≤ (X : ℝ)^(1/25000000 : ℝ) → (e : ℝ) ≤ (X : ℝ)^(1/25000000 : ℝ) →
      (X : ℝ)^(1/1000000 : ℝ) ≤ a → (X : ℝ)^(1/1000000 : ℝ) ≤ c → a ≤ b → c ≤ d →
      Real.sqrt X ≤ (L : ℝ)+1 → (U : ℝ) ≤ (X : ℝ)^(500000001/1000000000 : ℝ) →
      ∀ (α β : ℕ → ℂ) {A B : ℝ}, 0 ≤ A → 0 ≤ B →
        (∀ p ∈ Ico a b, ‖α p‖ ≤ A) → (∀ m ∈ Ico c d, ‖β m‖ ≤ B) →
      ‖∑ p ∈ Ico a b, ∑ m ∈ Ico c d, fractionalProductTerm ((X : ℝ)/e) L U α β p m‖ ≤
        K*(1+Real.log b)*(1+Real.log d)*(A*B)*Real.sqrt X := by
  obtain ⟨K,hK,h⟩ := centered_fractional_reciprocal_product_window
  refine ⟨K,hK,?_⟩
  intro a b c d L U e X he hX hlarge hdiv ha hc hab hcd hL hU α β A B hA hB hα hβ
  obtain ⟨H,hH,hHa,hHc,hu,ht,hprod⟩ := square_root_product_scales hX hlarge hdiv ha hc hL hU
  have he₁ : (1 : ℝ) ≤ e := by exact_mod_cast he
  have he₀ := zero_lt_one.trans_le he₁
  have hlo : (U : ℝ)^2 ≤ H*((X : ℝ)/e) := by
    rw [←mul_div_assoc]; apply (le_div_iff₀ he₀).mpr
    simpa only [mul_comm (e : ℝ)] using hu
  have hhi : 16*((X : ℝ)/e) ≤ H*(L : ℝ)^2 :=
    (mul_le_mul_of_nonneg_left (div_le_self (Nat.cast_nonneg X) he₁) (by norm_num)).trans ht
  have hh := h hH hHa hHc hab hcd (div_pos (by exact_mod_cast hX) he₀) hlo hhi α β hA hB hα hβ
  apply hh.trans
  apply (div_le_iff₀ (Real.sqrt_pos.mpr (Real.sqrt_pos.mpr (by exact_mod_cast hH)))).mpr
  have hl := Real.log_natCast_nonneg b
  have hr := Real.log_natCast_nonneg d
  have hfin := mul_le_mul_of_nonneg_left hprod
    (by positivity : 0 ≤ K*(1+Real.log b)*(1+Real.log d)*(A*B))
  linarith only [hfin]

#print axioms square_root_fractional_divisor_window
end GaloisForLFunctions.PrimeExponentialSums
