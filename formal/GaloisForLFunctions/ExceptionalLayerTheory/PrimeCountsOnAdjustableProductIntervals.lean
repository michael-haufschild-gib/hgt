import GaloisForLFunctions.ExceptionalLayerTheory.CancellationOnTruncatedQuotientIntervals
import GaloisForLFunctions.ExceptionalLayerTheory.BalancedProductsInTheLargePrimeCells

/-!
# Prime counts on a product interval with independently chosen cutoffs

The deviation of the Mangoldt measure from the balanced convolution and
unit density has small prefixes. Quotient intervals absorb that deviation;
the harmonic divisor moments absorb unit density.
-/

noncomputable section
open Finset ArithmeticFunction RHTower
namespace GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval

/-- The lower endpoint of the product interval at inner cutoff D. -/
def productLower (D X : ℕ) : ℕ := min X ((D+1)*⌊Real.sqrt X⌋₊)

/-- Pair the two-factor convolution with the centered quotient weight
above the moving square-root cutoff. -/
def adjustableProductRow (D R X : ℕ) : ℝ :=
  ∑ n ∈ Ioc (productLower D X) X, balancedProduct D n*centeredPrimeWeight R (X/n)

private theorem lower_bounds {D X : ℕ} {H : ℝ} (hX : 1 ≤ X) (hH : 1 ≤ H) (hd : (D : ℝ) ≤ H) :
    let Y := productLower D X
    Y ≤ X ∧ Real.sqrt X ≤ ((Y+1 : ℕ) : ℝ) ∧ ((Y+1 : ℕ) : ℝ) ≤ 3*H*Real.sqrt X := by
  intro Y
  have hx : (1 : ℝ) ≤ X := by exact_mod_cast hX
  have hr : 1 ≤ Real.sqrt X := by simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hx
  have hrX : Real.sqrt X ≤ X := by nlinarith only [Real.sq_sqrt (Nat.cast_nonneg X),hr,mul_nonneg (sub_nonneg.mpr hr) (Real.sqrt_nonneg (X : ℝ))]
  have hmin : ⌊Real.sqrt X⌋₊ ≤ Y := le_min (Nat.floor_le_of_le hrX) (Nat.le_mul_of_pos_left _ (Nat.succ_pos D))
  have hy : (Y : ℝ) ≤ ((D+1 : ℕ) : ℝ) * (⌊Real.sqrt X⌋₊ : ℕ) := by
    exact_mod_cast (min_le_right X ((D+1)*⌊Real.sqrt X⌋₊))
  have hbase := (Nat.lt_floor_add_one (Real.sqrt X)).le
  have hm := mul_le_mul (show ((D+1 : ℕ) : ℝ) ≤ 2*H by push_cast; linarith only [hd,hH])
    (Nat.floor_le (Real.sqrt_nonneg (X : ℝ))) (Nat.cast_nonneg _) (by positivity)
  refine ⟨min_le_left ..,?_,?_⟩
  · push_cast
    exact hbase.trans (add_le_add (by exact_mod_cast hmin : (⌊Real.sqrt X⌋₊ : ℝ) ≤ Y) (le_refl 1))
  · push_cast
    linarith only [hy,hm,one_le_mul_of_one_le_of_one_le hH hr]

private theorem prefix_bound :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ {D X : ℕ} {H : ℝ}, 1 ≤ H → (D : ℝ) ≤ H → Real.log X ≤ H →
      ∀ t ≤ X, |∑ n ∈ Ioc 0 t, (vonMangoldt n-balancedProduct D n-1)| ≤ B*H^2 := by
  obtain ⟨C,hC,h⟩ := mass_uniform
  refine ⟨18*C+7*(1+2*C),by positivity,?_⟩
  intro D X H hH hd hl t ht
  rcases Nat.eq_zero_or_pos t with rfl | ht₁
  · rw [Ioc_self,sum_empty,abs_zero]; positivity
  have hI : Ioc 0 t = Icc 1 t := by ext; simp only [mem_Ioc,mem_Icc]; omega
  have hp : (∑ n ∈ Icc 1 t, vonMangoldt n) = Chebyshev.psi t := by
    unfold Chebyshev.psi; rw [Nat.floor_natCast]; rfl
  simp only [hI,sum_sub_distrib,hp,sum_balancedProduct,sum_const,Nat.card_Icc,Nat.add_sub_cancel,nsmul_eq_mul,mul_one]
  rw [sub_right_comm]
  apply (abs_error_sub_middle (Nat.succ_pos D) ht₁ D).trans
  have hm := h (D+1) (Nat.succ_pos D)
  have hd₁ : ((D+1 : ℕ) : ℝ) ≤ 2*H := by push_cast; linarith only [hd,hH]
  have hm' := hm.trans (mul_le_mul_of_nonneg_left hd₁ hC)
  have htlog := (Real.log_le_log (by exact_mod_cast ht₁) (by exact_mod_cast ht : (t : ℝ) ≤ X)).trans hl
  have hlog := Real.log_le_sub_one_of_pos (show 0 < ((2*(D+1) : ℕ) : ℝ) by positivity)
  have hlen : ((2*(D+1) : ℕ) : ℝ) ≤ 4*H := by push_cast at hd₁ ⊢; linarith only [hd₁]
  have hlog' : 3+Real.log (2*(D+1) : ℕ)+2*Real.log t ≤ 9*H := by
    linarith only [htlog,hlog,hlen,hH]
  have ha := mul_le_mul hm' hlog' (by have := Real.log_natCast_nonneg (2*(D+1)); have := Real.log_natCast_nonneg t; positivity)
    (by positivity)
  have hb := mul_le_mul (show 1+mass (D+1) ≤ (1+2*C)*H by linarith only [hH,hm'])
    (mul_le_mul_of_nonneg_left hd (by norm_num : (0 : ℝ) ≤ 7)) (by positivity) (by positivity)
  linarith only [ha,hb]

private theorem unit_density_bound :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {D R X : ℕ} {H : ℝ}, 1 ≤ X → 1 ≤ R → 1 ≤ H → (D : ℝ) ≤ H → (R : ℝ) ≤ H →
      |∑ n ∈ Ioc (productLower D X) X, centeredPrimeWeight R (X/n)| ≤ K*H^5*Real.sqrt X := by
  obtain ⟨C,hC,h⟩ := abs_truncated_density
  refine ⟨1+40*C,by positivity,?_⟩
  intro D R X H hx hr hH hd hR
  let Y := productLower D X
  let Z : ℝ := (Y+1 : ℕ)
  obtain ⟨hy,hz,hZ⟩ := lower_bounds hx hH hd
  have hx0 : 0 < (X : ℝ) := by exact_mod_cast hx
  have hs := Real.sqrt_pos.mpr hx0
  have hs₁ : 1 ≤ Real.sqrt X := by simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt (show (1 : ℝ) ≤ X by exact_mod_cast hx)
  have bound := h X Y R hx hy hr (fun _ => 1) 0 le_rfl (fun l u hlu => by
    simp only [sum_const,Nat.card_Ioc,nsmul_eq_mul,mul_one,Nat.cast_sub hlu,sub_self,abs_zero,le_refl])
  simp only [one_mul,zero_add] at bound
  apply bound.trans
  change 1+C*((R : ℝ)^3*(4*Z^2/X)+(1+Real.log R)*(2*X/Z)) ≤ _
  have hsq := Real.sq_sqrt (Nat.cast_nonneg X)
  have hzz := pow_le_pow_left₀ (show 0 ≤ Z by dsimp [Z]; positivity) hZ 2
  have hhZ : 4*Z^2/(X : ℝ) ≤ 36*H^2 := by
    rw [div_le_iff₀ hx0]
    calc 4*Z^2 ≤ 4*((3*H*Real.sqrt X)^2) := mul_le_mul_of_nonneg_left hzz (by norm_num)
         _ = _ := by rw [mul_pow,hsq]; ring
  have hbulk := mul_le_mul (pow_le_pow_left₀ (Nat.cast_nonneg R) hR 3) hhZ (by positivity) (by positivity)
  have hrec : 2*(X : ℝ)/Z ≤ 2*Real.sqrt X := by
    rw [div_le_iff₀ (hs.trans_le hz)]
    have hh := mul_le_mul_of_nonneg_left hz hs.le
    nlinarith only [hh,hsq]
  have hlog := Real.log_le_sub_one_of_pos (show 0 < (R : ℝ) by exact_mod_cast hr)
  have htail := mul_le_mul (show 1+Real.log R ≤ 2*H by linarith only [hlog,hR,hH]) hrec
    (by dsimp [Z]; positivity) (by positivity)
  have hh₁ : 1 ≤ H^5*Real.sqrt X := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hH) hs₁
  have hh₂ : H^5 ≤ H^5*Real.sqrt X := le_mul_of_one_le_right (by positivity) hs₁
  have hh₃ : H*Real.sqrt X ≤ H^5*Real.sqrt X := mul_le_mul_of_nonneg_right
    (by simpa only [pow_one] using pow_le_pow_right₀ hH (by norm_num : 1 ≤ 5)) hs.le
  have hboth : (R : ℝ)^3*(4*Z^2/X)+(1+Real.log R)*(2*X/Z) ≤ 40*(H^5*Real.sqrt X) := by
    linarith only [hbulk,htail,hh₂,hh₃]
  linarith only [hh₁,mul_le_mul_of_nonneg_left hboth hC]

/-- The cutoffs may vary independently, allowing both complementary factors
to grow at a power chosen for the target exponent. -/
theorem adjustable_product_bound :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {D R X : ℕ} {H : ℝ}, 1 ≤ X → 1 ≤ R → 1 ≤ H →
      (D : ℝ) ≤ H → (R : ℝ) ≤ H → Real.log X ≤ H →
      |(Chebyshev.psi X-X)-adjustableProductRow D R X| ≤ K*H^5*Real.sqrt X := by
  obtain ⟨C,hC,hm⟩ := mass_uniform
  obtain ⟨F,hF,hw⟩ := centeredPrimeWeight_uniform
  obtain ⟨B,hB,hprefix⟩ := prefix_bound
  obtain ⟨K,hK,hunit⟩ := unit_density_bound
  refine ⟨420*(1+C)*16517+21*F+4*B*F+K,by positivity,?_⟩
  intro D R X H hx hr hH hd hR hlog
  let Y := productLower D X
  let w := fun n => centeredPrimeWeight R (X/n)
  let a := fun n => vonMangoldt n-balancedProduct D n-1
  obtain ⟨hy,_,hZ⟩ := lower_bounds hx hH hd
  have h₁ : 1 ≤ Real.sqrt X := by simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt (show (1 : ℝ) ≤ X by exact_mod_cast hx)
  have h₂ := pow_le_pow_right₀ hH (by norm_num : 1 ≤ 2)
  simp only [pow_one] at h₂
  have hR₂ := pow_le_pow_left₀ (Nat.cast_nonneg R) hR 2
  have he := Real.log_le_sub_one_of_pos (show (0 : ℝ) < (128*(128*R^2+1) : ℕ) by positivity)
  have hlen : ((128*(128*R^2+1) : ℕ) : ℝ) ≤ 16512*H^2 := by
    push_cast; linarith only [hR₂,one_le_pow₀ (n := 2) hH]
  have hscale : 3+Real.log (128*(128*R^2+1) : ℕ)+2*Real.log X ≤ 16517*H^2 := by
    linarith only [he,hlen,hlog,h₂,one_le_pow₀ (n := 2) hH]
  have hm' : 1+mass R ≤ (1+C)*H := by
    linarith only [hH,(hm R hr).trans (mul_le_mul_of_nonneg_left hR hC)]
  have hf := (centeredPrimeWeight_factorial hr hx).trans (mul_le_mul
    (mul_le_mul_of_nonneg_left hm' (by norm_num : (0 : ℝ) ≤ 420)) hscale
    (by have := Real.log_natCast_nonneg (128*(128*R^2+1)); have := Real.log_natCast_nonneg X; positivity) (by positivity))
  have hlow : |∑ n ∈ Ioc 0 Y, vonMangoldt n*w n| ≤ 21*F*H^2*Real.sqrt X := by
    have hI : Ioc 0 Y = Icc 1 Y := by ext; simp only [mem_Ioc,mem_Icc]; omega
    calc _ ≤ ∑ n ∈ Ioc 0 Y, (F*H)*vonMangoldt n := by
              apply (abs_sum_le_sum_abs _ _).trans
              apply sum_le_sum
              intro n _
              rw [abs_mul,abs_of_nonneg vonMangoldt_nonneg,mul_comm]
              exact mul_le_mul_of_nonneg_right ((hw hr _).trans (mul_le_mul_of_nonneg_left hR hF)) vonMangoldt_nonneg
         _ ≤ (F*H)*(7*Y) := by
              rw [←mul_sum,hI]
              exact mul_le_mul_of_nonneg_left (chebyshevPsi_le_seven _) (by positivity)
         _ ≤ _ := by
              have hy' : (Y : ℝ) ≤ 3*H*Real.sqrt X := (by exact_mod_cast Nat.le_succ Y : (Y : ℝ) ≤ (Y+1 : ℕ)).trans hZ
              linarith only [mul_le_mul_of_nonneg_left hy' (mul_nonneg hF (zero_le_one.trans hH))]
  have hres := abs_truncated_quotient_pair (N := X) Y a (centeredPrimeWeight R) (show 0 ≤ B*H^2 by positivity)
    (mul_nonneg hF (Nat.cast_nonneg R)) (hprefix hH hd hlog) (hw hr)
  have hroot : ((Nat.sqrt X : ℕ) : ℝ) ≤ Real.sqrt X := (Real.le_sqrt (Nat.cast_nonneg _) (Nat.cast_nonneg _)).mpr
    (by rw [sq]; exact_mod_cast Nat.sqrt_le X)
  have hres' : |∑ n ∈ Ioc Y X, a n*w n| ≤ 4*B*F*H^3*Real.sqrt X := by
    apply hres.trans
    have hh := mul_le_mul hR hroot (Nat.cast_nonneg _) (zero_le_one.trans hH)
    linarith only [mul_le_mul_of_nonneg_left hh (show 0 ≤ 4*(B*H^2)*F by positivity)]
  let T := H^5*Real.sqrt X
  have h3 : H^3 ≤ T := (pow_le_pow_right₀ hH (by norm_num : 3 ≤ 5)).trans (le_mul_of_one_le_right (by positivity) h₁)
  have h2r : H^2*Real.sqrt X ≤ T := mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hH (by norm_num : 2 ≤ 5)) (Real.sqrt_nonneg _)
  have h3r : H^3*Real.sqrt X ≤ T := mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hH (by norm_num : 3 ≤ 5)) (Real.sqrt_nonneg _)
  have hfull : |(Chebyshev.psi X-X)-∑ n ∈ Icc 1 X, vonMangoldt n*w n| ≤ (420*(1+C)*16517)*T :=
    hf.trans (by linarith only [mul_le_mul_of_nonneg_left h3 (show 0 ≤ 420*(1+C)*16517 by positivity)])
  have hi : Icc 1 X = Ioc 0 X := by ext; simp only [mem_Ioc,mem_Icc]; omega
  rw [hi,←sum_Ioc_consecutive (fun n => vonMangoldt n*w n) (Nat.zero_le Y) hy] at hfull
  have hdif : (∑ n ∈ Ioc Y X, vonMangoldt n*w n) - adjustableProductRow D R X =
      (∑ n ∈ Ioc Y X, a n*w n)+(∑ n ∈ Ioc Y X, w n) := by
    unfold adjustableProductRow
    rw [←sum_sub_distrib,←sum_add_distrib]
    exact sum_congr rfl fun n _ => by dsimp [a,w]; ring
  have hu : |∑ n ∈ Ioc Y X, w n| ≤ K*T := by
    simpa only [T,mul_assoc] using hunit hx hr hH hd hR
  have hdiff := (abs_add_le _ _).trans (add_le_add hres' hu)
  rw [←hdif] at hdiff
  have ht : (Chebyshev.psi X-X)-adjustableProductRow D R X =
      ((Chebyshev.psi X-X)-((∑ n ∈ Ioc 0 Y, vonMangoldt n*w n)+(∑ n ∈ Ioc Y X, vonMangoldt n*w n)))+
      (∑ n ∈ Ioc 0 Y, vonMangoldt n*w n)+((∑ n ∈ Ioc Y X, vonMangoldt n*w n)-adjustableProductRow D R X) := by ring
  rw [ht]
  apply (abs_add_le _ _).trans ((add_le_add (abs_add_le _ _) le_rfl).trans ?_)
  rw [mul_assoc (420*(1+C)*16517+21*F+4*B*F+K)]
  change _ ≤ (420*(1+C)*16517+21*F+4*B*F+K)*T
  linarith only [hfull,hlow,hdiff,mul_le_mul_of_nonneg_left h2r (show 0 ≤ 21*F by positivity),
    mul_le_mul_of_nonneg_left h3r (show 0 ≤ 4*B*F by positivity)]

#print axioms adjustable_product_bound
end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
