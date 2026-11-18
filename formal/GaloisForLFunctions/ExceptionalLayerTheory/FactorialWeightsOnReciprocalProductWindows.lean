import GaloisForLFunctions.ExceptionalLayerTheory.CenteringTheFactorialPrimeWeight
import GaloisForLFunctions.PrimeExponentialSums.FractionalPartsAcrossAReciprocalProductWindow

/-!
# Factorial weights on reciprocal product windows

Pushing a bilinear weight forward under multiplication groups pairs with
the same quotient. The finite divisor stencil then transfers the reciprocal
fractional-part estimate to the original factorial weight.
-/

noncomputable section
open Finset RHTower
open GaloisForLFunctions.PrimeExponentialSums GaloisForLFunctions.HTGeometry.SmoothedSawtooth
namespace GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval

/-- The centered factorial stencil on an arbitrary finite list of denominators. -/
theorem abs_centered_image_block {ι : Type*} (s : Finset ι) (q : ι → ℕ) (z : ι → ℝ)
    {R X : ℕ} (hR : 1 ≤ R) {M : ℝ} (hM : 0 ≤ M)
    (hs : ∀ t ∈ Icc 1 (128*(128*R^2+1)), |∑ i ∈ s, z i*centeredQuotient X (q i) t| ≤ M) :
    |∑ i ∈ s, z i*centeredPrimeWeight R (X/q i)| ≤ 1000*(1+mass R)*M := by
  classical
  let w (n : ℕ) := ∑ i ∈ s, if q i=n then z i else 0
  have lift (f : ℕ → ℝ) : (∑ n ∈ s.image q, w n*f n) = ∑ i ∈ s, z i*f (q i) := by
    simp only [w,sum_mul]
    rw [sum_comm]
    refine sum_congr rfl fun i hi => ?_
    simp only [ite_mul,zero_mul,sum_ite_eq,if_pos (mem_image_of_mem q hi)]
  simpa only [lift] using abs_centered_block hR X (s.image q) w hM
    (fun t ht => (congrArg abs (lift (fun n => centeredQuotient X n t))).le.trans (hs t ht))

/-- Across both full factor intervals the centered factorial prime weight
saves a fourth root of the short correlation length. -/
theorem centered_weight_product_window :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {a b c d H L U R X : ℕ}, 1 ≤ R → 1 ≤ X → 1 ≤ H → H^4 ≤ a → H ≤ c →
      a ≤ b → c ≤ d → ((128*(128*R^2+1) : ℕ) : ℝ)*(U : ℝ)^2 ≤ H*X →
      16*(X : ℝ) ≤ H*(L : ℝ)^2 →
      ∀ (α β : ℕ → ℝ) {A B : ℝ}, 0 ≤ A → 0 ≤ B →
        (∀ p ∈ Ico a b, |α p| ≤ A) → (∀ m ∈ Ico c d, |β m| ≤ B) →
      |∑ q ∈ (Ico a b ×ˢ Ico c d) with L<q.1*q.2 ∧ q.1*q.2≤U,
        (α q.1*β q.2)*centeredPrimeWeight R (X/(q.1*q.2))| ≤
        K*(1+mass R)*(1+Real.log b)*(1+Real.log d)*(A*B*U)/Real.sqrt (Real.sqrt H) := by
  obtain ⟨K,hK,hwindow⟩ := centered_fractional_reciprocal_product_window
  refine ⟨1000*K,by positivity,?_⟩
  intro a b c d H L U R X hR hX hH ha hc hab hcd hlow hhigh α β A B hA hB hα hβ
  let s := (Ico a b ×ˢ Ico c d).filter (fun q => L<q.1*q.2 ∧ q.1*q.2≤U)
  let M := K*(1+Real.log b)*(1+Real.log d)*(A*B*U)/Real.sqrt (Real.sqrt H)
  have hM : 0 ≤ M := by
    have := Real.log_natCast_nonneg b
    have := Real.log_natCast_nonneg d
    dsimp [M]; positivity
  have tests (t : ℕ) (ht : t ∈ Icc 1 (128*(128*R^2+1))) :
      |∑ q ∈ s, (α q.1*β q.2)*centeredQuotient X (q.1*q.2) t| ≤ M := by
    obtain ⟨hl,hu⟩ := mem_Icc.mp ht
    have ht₁ : (1 : ℝ) ≤ t := by exact_mod_cast hl
    have ht₀ := zero_lt_one.trans_le ht₁
    let Z := (X : ℝ)/t
    have hZ : 0 < Z := div_pos (by exact_mod_cast hX) ht₀
    have hlo : (U : ℝ)^2 ≤ H*Z := by
      dsimp [Z]; rw [←mul_div_assoc]
      apply (le_div_iff₀ ht₀).mpr
      rw [mul_comm]
      exact (mul_le_mul_of_nonneg_right (by exact_mod_cast hu) (sq_nonneg _)).trans hlow
    have hhi : 16*Z ≤ H*(L : ℝ)^2 :=
      (mul_le_mul_of_nonneg_left (div_le_self (Nat.cast_nonneg X) ht₁) (by norm_num)).trans hhigh
    let f := fractionalProductTerm Z L U (fun p => (α p : ℂ)) (fun m => (β m : ℂ))
    have bound := hwindow hH ha hc hab hcd hZ hlo hhi (fun p => (α p : ℂ)) (fun m => (β m : ℂ)) hA hB
      (fun p hp => by simpa only [Complex.norm_real,Real.norm_eq_abs] using hα p hp)
      (fun m hm => by simpa only [Complex.norm_real,Real.norm_eq_abs] using hβ m hm)
    have eq : ((∑ q ∈ s, (α q.1*β q.2)*centeredQuotient X (q.1*q.2) t : ℝ) : ℂ) =
        ∑ p ∈ Ico a b, ∑ m ∈ Ico c d, f p m := by
      rw [Complex.ofReal_sum]
      dsimp only [s]
      rw [sum_filter,sum_product]
      apply sum_congr rfl
      intro p _
      apply sum_congr rfl
      intro m _
      by_cases hcut : L<p*m ∧ p*m≤U
      · simp [f,fractionalProductTerm,hcut,centeredQuotient,saw,Z,
          Nat.cast_mul,div_mul_eq_div_div,div_right_comm (X/t : ℝ) p m]
      · simp [f,fractionalProductTerm,hcut]
    rw [←eq,Complex.norm_real,Real.norm_eq_abs] at bound
    exact bound
  exact (abs_centered_image_block s (fun q => q.1*q.2) (fun q => α q.1*β q.2) hR hM tests).trans_eq
    (by dsimp [M]; ring)

#print axioms centered_weight_product_window

/-- On the fixed window through the square-root product, both long-variable
intervals together cost square-root error up to the two logarithms and the
factorial stencil mass. -/
theorem square_root_window_power_bound :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {a b c d L U R X : ℕ}, 1 ≤ R → 1 ≤ X →
      64 ≤ (X : ℝ)^(1/25000000 : ℝ) →
      ((128*(128*R^2+1) : ℕ) : ℝ) ≤ (X : ℝ)^(1/25000000 : ℝ) →
      (X : ℝ)^(1/1000000 : ℝ) ≤ a → (X : ℝ)^(1/1000000 : ℝ) ≤ c →
      a ≤ b → c ≤ d → Real.sqrt X ≤ (L : ℝ)+1 →
      (U : ℝ) ≤ (X : ℝ)^(500000001/1000000000 : ℝ) →
      ∀ (α β : ℕ → ℝ) {A B : ℝ}, 0 ≤ A → 0 ≤ B →
        (∀ p ∈ Ico a b, |α p| ≤ A) → (∀ m ∈ Ico c d, |β m| ≤ B) →
      |∑ q ∈ (Ico a b ×ˢ Ico c d) with L<q.1*q.2 ∧ q.1*q.2≤U,
        (α q.1*β q.2)*centeredPrimeWeight R (X/(q.1*q.2))| ≤
        K*(1+mass R)*(1+Real.log b)*(1+Real.log d)*(A*B)*Real.sqrt X := by
  obtain ⟨K,hK,hwindow⟩ := centered_weight_product_window
  refine ⟨K,hK,?_⟩
  intro a b c d L U R X hR hX hlarge hstencil ha hc hab hcd hL hU α β A B hA hB hα hβ
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
  have hu : ((128*(128*R^2+1) : ℕ) : ℝ)*(U : ℝ)^2 ≤ H*X := by
    have hh := mul_le_mul hstencil (pow_le_pow_left₀ (Nat.cast_nonneg U) hU 2) (sq_nonneg _) hr₀
    apply hh.trans
    change P (1/25000000)*(P (500000001/1000000000))^2 ≤ H*X
    have he : P (1/25000000)*(P (500000001/1000000000))^2 ≤ r^4*X := by
      calc _ = P (1/25000000+(500000001/1000000000)*2) := by rw [power,mul]; norm_num
           _ ≤ P ((1/25000000)*4+1) := mono (by norm_num)
           _ = r^4*X := by rw [←mul,show r^4=P ((1/25000000)*4) from power _ 4,show P 1=X from Real.rpow_one _]
    exact he.trans (mul_le_mul_of_nonneg_right hr₄ (Nat.cast_nonneg X))
  have hh := hwindow hR hX hH₁ hHa hHc hab hcd hu ht α β hA hB hα hβ
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
  let T := K*(1+mass R)*(1+Real.log b)*(1+Real.log d)*(A*B)
  have hT : 0 ≤ T := by
    have hm := (abs_nonneg _).trans (abs_prefix_le_mass hR 0)
    have hb := Real.log_natCast_nonneg b
    have hd := Real.log_natCast_nonneg d
    dsimp [T]; positivity
  apply hh.trans
  apply (div_le_iff₀ (Real.sqrt_pos.mpr (Real.sqrt_pos.mpr (by exact_mod_cast hH₁)))).mpr
  have hfinal := mul_le_mul_of_nonneg_left hprod hT
  dsimp only [T] at hfinal
  linarith only [hfinal]

#print axioms square_root_window_power_bound

end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
