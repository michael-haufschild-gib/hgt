import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.TheThreeQuarterProductWindow
import GaloisForLFunctions.ExceptionalLayerTheory.LargeComplementsInTheCoprimeProduct

/-!
# The complete upper product tail of the signed spline

At unit stencil cutoffs the product q occurs precisely at horizons k
from q up to, but excluding, ceil(q/2)². Thus a single clipped product
estimate removes the entire lower range, including the short
complements. No cutoff term is discarded at either end.
-/

noncomputable section
open Finset ArithmeticFunction
open GaloisForLFunctions.CountingHolography.Sections
namespace GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval

/-- First horizon where the unit-stencil lower bound reaches q, once k ≥ q. -/
def unitProductHorizonEnd (q : ℕ) := ((q+1)/2)^2

private theorem product_cell {k q : ℕ} (h : q≤k) :
    productLower 1 k < q ↔ k < unitProductHorizonEnd q := by
  rw [productLower,Real.nat_floor_real_sqrt_eq_nat_sqrt,min_lt_iff,unitProductHorizonEnd,←Nat.sqrt_lt']
  omega

private def smallCell (U k p : ℕ) : ℝ :=
  ∑ v ∈ (Icc 1 (U/p)).filter (p.Coprime ·), innerJump 1 v *
    (if p*v≤k ∧ k<unitProductHorizonEnd (p*v) then centeredPrimeWeight 1 (k/(p*v)) else 0)

private theorem slice_partition {p : ℕ} (hp : 0<p) (U k : ℕ) :
    coprimeSlice 1 1 k (productLower 1 k) p =
      smallCell U k p + coprimeSlice 1 1 k (max (productLower 1 k) U) p := by
  let Y := productLower 1 k
  let S := (Ioc (Y/p) (k/p)).filter (p.Coprime ·)
  let w (v : ℕ) := innerJump 1 v*centeredPrimeWeight 1 (k/(p*v))
  let low := (Icc 1 (U/p)).filter (p.Coprime ·)
  have hv (v : ℕ) : p*v≤k ↔ v≤k/p := by rw [Nat.le_div_iff_mul_le hp,Nat.mul_comm v p]
  have hlo (v : ℕ) : Y<p*v ↔ Y/p<v := by rw [Nat.div_lt_iff_lt_mul hp,Nat.mul_comm v p]
  have h₁ : low.filter (fun v => p*v≤k ∧ k<unitProductHorizonEnd (p*v)) = S.filter (fun v => v≤U/p) := by
    ext v
    simp only [low,S,mem_filter,mem_Icc,mem_Ioc]
    constructor
    · rintro ⟨⟨⟨_,hu⟩,hc⟩,hk,he⟩
      exact ⟨⟨⟨(hlo v).mp ((product_cell hk).mpr he),(hv v).mp hk⟩,hc⟩,hu⟩
    · rintro ⟨⟨⟨hl,hk⟩,hc⟩,hu⟩
      exact ⟨⟨⟨by omega,hu⟩,hc⟩,(hv v).mpr hk,(product_cell ((hv v).mpr hk)).mp ((hlo v).mpr hl)⟩
  have h₂ : S.filter (fun v => ¬v≤U/p) = (Ioc (max Y U/p) (k/p)).filter (p.Coprime ·) := by
    have he : max Y U/p = max (Y/p) (U/p) := by
      rcases le_total Y U with h|h
      · rw [max_eq_right h,max_eq_right (Nat.div_le_div_right h)]
      · rw [max_eq_left h,max_eq_left (Nat.div_le_div_right h)]
    ext v
    simp only [S,mem_filter,mem_Ioc,he,max_lt_iff,not_le]; tauto
  have hc : smallCell U k p = ∑ v ∈ S.filter (fun v => v≤U/p), w v := by
    unfold smallCell
    simp only [mul_ite,mul_zero,←sum_filter]
    exact sum_congr h₁ fun _ _ => rfl
  rw [hc]
  have hh := sum_filter_add_sum_filter_not S (fun v => v≤U/p) w
  rw [h₂] at hh
  simpa only [Y,S,w,coprimeSlice,Nat.div_div_eq_div_mul] using hh.symm

private theorem cell_zero {U k p : ℕ} (hp : U<p ∨ k<p) : smallCell U k p=0 := by
  unfold smallCell
  apply sum_eq_zero; intro v hv
  obtain ⟨hv₁,hvU⟩ := mem_Icc.mp (mem_filter.mp hv).1
  rcases hp with hp|hp
  · rw [Nat.div_eq_of_lt hp] at hvU
    omega
  · have h : ¬(p*v≤k ∧ k<unitProductHorizonEnd (p*v)) :=
      fun h => hp.not_ge ((Nat.le_mul_of_pos_right p hv₁).trans h.1)
    rw [if_neg h,mul_zero]

private theorem prime_padding {a b : ℕ} (hab : a≤b) (f : ℕ → ℝ)
    (hz : ∀ p : ℕ, a<p → f p=0) : ordinaryFactorTail 4 a f=ordinaryFactorTail 4 b f := by
  unfold ordinaryFactorTail
  apply sum_subset
  · intro p hp
    obtain ⟨hh,prime⟩ := mem_filter.mp hp
    exact mem_filter.mpr ⟨Ioc_subset_Ioc_right hab hh,prime⟩
  · intro p hp hn
    obtain ⟨hi,prime⟩ := mem_filter.mp hp
    have ha : a<p := lt_of_not_ge fun h => hn (mem_filter.mpr ⟨mem_Ioc.mpr ⟨(mem_Ioc.mp hi).1,h⟩,prime⟩)
    rw [hz p ha,mul_zero]

/-- Exact split at any prescribed product cutoff U, for every horizon
including those at which the moving lower endpoint crosses a product. -/
theorem unit_stencil_product_partition (U k : ℕ) :
    coprimePrimeRow 1 1 k (productLower 1 k) =
      clippedPrimeProducts 1 1 4 U (fun p v => p*v) (fun p v => unitProductHorizonEnd (p*v)) k+
        coprimePrimeRow 1 1 k (max (productLower 1 k) U) := by
  have h : ordinaryFactorTail 4 U (smallCell U k) = ordinaryFactorTail 4 k (smallCell U k) := by
    rcases le_total U k with h|h
    · exact prime_padding h _ fun _ hp => cell_zero (Or.inl hp)
    · exact (prime_padding h _ fun _ hp => cell_zero (Or.inr hp)).symm
  change _ = ordinaryFactorTail 4 U (smallCell U k)+_
  rw [h]
  unfold ordinaryFactorTail coprimePrimeRow
  rw [←sum_add_distrib]
  apply sum_congr rfl; intro p hp
  rw [←mul_add,slice_partition (mem_filter.mp hp).2.pos]

/-- The actual sum of all products above U, with ordinary first primes
and coprimality imposed in the original row. -/
def upperProductReading (U n : ℕ) :=
  splineCountReading n (fun k => coprimePrimeRow 1 1 k (max (productLower 1 k) U))

/-- Full-range approximation at arbitrary U. At x=n² the price of
raising the product cutoff is U²(1+log U)/x^(3/2). -/
theorem dyadicPrimeContact_upper_product_tail :
    ∃ A B : ℝ, 0≤A ∧ 0≤B ∧ ∀ {n U : ℕ}, 0<n → 1≤U →
      |dyadicPrimeContact n-upperProductReading U n| ≤
        A*(1+Real.log (splineHorizon n))^6+B*(1+Real.log U)*(U:ℝ)^2/(n:ℝ)^3 := by
  obtain ⟨A,hA,ha⟩ := dyadicPrimeContact_unit_stencils
  obtain ⟨C,hC,h⟩ := spline_clipped_product_bound
  let B := C*(2*(1+mass (1+1)))*(125*(1+mass 1)*(128*(128*(1:ℝ)^2+1)))
  have h₁ := (abs_nonneg _).trans (abs_prefix_le_mass (R := 1) le_rfl 0)
  have h₂ := (abs_nonneg _).trans (innerJump_pointwise_bound 1 0)
  refine ⟨A,B,hA,by dsimp [B]; positivity,fun {n U} hn hu => ?_⟩
  let head := clippedPrimeProducts 1 1 4 U (fun p v => p*v) (fun p v => unitProductHorizonEnd (p*v))
  have he : splineCountReading n (fun k => coprimePrimeRow 1 1 k (productLower 1 k)) =
      splineCountReading n head+upperProductReading U n := by
    simp only [upperProductReading,splineCountReading,unit_stencil_product_partition U,add_mul,
      sum_add_distrib,head]
  have hb := h hn (R := 1) le_rfl hu 1 4 (fun p v => p*v) (fun p v => unitProductHorizonEnd (p*v))
  have id : dyadicPrimeContact n-upperProductReading U n =
      (dyadicPrimeContact n-splineCountReading n (fun k => coprimePrimeRow 1 1 k (productLower 1 k)))+
        splineCountReading n head := by rw [he]; ring
  rw [id]
  exact (abs_add_le _ _).trans (add_le_add (ha hn) (by simpa only [B,head,Nat.cast_one] using hb))

/-- Complete signed reading with both the lower product and upper
complementary-factor cutoffs imposed on the same prime window. -/
def cappedUpperProductReading (U M n : ℕ) :=
  splineCountReading n (fun k => ordinaryFactorTail 4 k
    (cappedCoprimeSlice 1 1 k (max (productLower 1 k) U) M))

/-- Every remaining first prime exceeds U/M and every outer quotient
is at most k/(U+1), including the integer rounding of the product cut. -/
theorem capped_upper_ranges {k p v U M : ℕ} (hp : 0<p)
    (hv : v ∈ Ioc (max (productLower 1 k) U /p) (min (k/p) M)) :
    U<p*v ∧ U/M<p ∧ k/p/v≤k/(U+1) := by
  obtain ⟨hl,hu⟩ := mem_Ioc.mp hv
  have hprod : U<p*v := (le_max_right ..).trans_lt (by
    simpa only [Nat.mul_comm v p] using (Nat.div_lt_iff_lt_mul hp).mp hl)
  have hM := hu.trans (min_le_right ..)
  have hvpos : 0<v := (Nat.zero_le _).trans_lt hl
  refine ⟨hprod,(Nat.div_lt_iff_lt_mul (hvpos.trans_le hM)).mpr
    (hprod.trans_le (Nat.mul_le_mul_left p hM)),?_⟩
  rw [Nat.div_div_eq_div_mul]
  exact Nat.div_le_div_left hprod (Nat.succ_pos U)

/-- Both cutoffs have explicit costs. For x=n² the additional price for
v≤M is O(√x (1+log L)/(M+1)), uniformly in the product cutoff. -/
theorem dyadicPrimeContact_capped_upper_product_tail :
    ∃ A B C : ℝ, 0≤A ∧ 0≤B ∧ 0≤C ∧ ∀ {n U : ℕ}, 0<n → 1≤U → ∀ M : ℕ,
      |dyadicPrimeContact n-cappedUpperProductReading U M n| ≤
        A*(1+Real.log (splineHorizon n))^6+B*(1+Real.log U)*(U:ℝ)^2/(n:ℝ)^3+
          C*n*(1+Real.log (splineHorizon n))/(M+1:ℕ) := by
  obtain ⟨A,B,hA,hB,hupper⟩ := dyadicPrimeContact_upper_product_tail
  obtain ⟨K,hK,hlarge⟩ := large_complement_bound
  obtain ⟨J,_,hJ,_,hdiff⟩ := sampledSpline_differences
  obtain ⟨T,hT,hwin⟩ := successorSquare_window_bound
  have hT₀ := zero_le_one.trans hT
  refine ⟨A,B,2*K*J*T^4,hA,hB,by positivity,fun {n U} hn hU M => ?_⟩
  let L := splineHorizon n
  let H := 1+Real.log L
  let head (k : ℕ) := coprimePrimeRow 1 1 k (max (productLower 1 k) U)
  let cap (k : ℕ) := ordinaryFactorTail 4 k (cappedCoprimeSlice 1 1 k (max (productLower 1 k) U) M)
  have hn' : (0:ℝ)<n := Nat.cast_pos.mpr hn
  have hm : (0:ℝ)<(M+1:ℕ) := Nat.cast_pos.mpr (Nat.succ_pos M)
  have hH : 0≤H := by dsimp [H]; have := Real.log_natCast_nonneg L; positivity
  have hbound : (L:ℝ) ≤ (T*n)^2 := hwin hn
  have hrow (k : ℕ) (hk : k ∈ Icc 1 L) :
      |head k-cap k| ≤ (2*K)*((T*n)^2/(M+1:ℕ))*H := by
    obtain ⟨hk₁,hkL⟩ := mem_Icc.mp hk
    have h := hlarge (D := 1) (R := 1) (F := 4) le_rfl le_rfl hk₁ (by decide) (max (productLower 1 k) U) M
    change |head k-cap k| ≤ _ at h
    have hdiv : ((k/(M+1):ℕ):ℝ) ≤ (T*n)^2/(M+1:ℕ) :=
      (Nat.cast_div_le ..).trans (div_le_div_of_nonneg_right
        ((by exact_mod_cast hkL : (k:ℝ)≤L).trans hbound) hm.le)
    have hlog := Real.log_le_log (by exact_mod_cast hk₁ : (0:ℝ)<k) (by exact_mod_cast hkL : (k:ℝ)≤L)
    apply h.trans
    have hprod := mul_le_mul (mul_le_mul_of_nonneg_left hdiv (by positivity : 0≤2*K))
      (add_le_add (le_refl (1:ℝ)) hlog) (by have := Real.log_natCast_nonneg k; positivity) (by positivity)
    calc _ = (2*K)*((k/(M+1):ℕ):ℝ)*(1+Real.log k) := by norm_num <;> ring
         _ ≤ _ := hprod
  have hdiff' : |upperProductReading U n-cappedUpperProductReading U M n| ≤
      (2*K*J*T^4)*n*H/(M+1:ℕ) := by
    change |(∑ k ∈ Icc 1 L, head k*(sampledSpline n k-sampledSpline n (k+1)))-
      (∑ k ∈ Icc 1 L, cap k*(sampledSpline n k-sampledSpline n (k+1)))| ≤ _
    rw [←sum_sub_distrib]
    simp_rw [←sub_mul]
    apply (abs_sum_le_sum_abs _ _).trans
    calc _ ≤ ∑ _k ∈ Icc 1 L, ((2*K)*((T*n)^2/(M+1:ℕ))*H)*(J/(n:ℝ)^3) := by
            apply sum_le_sum; intro k hk
            rw [abs_mul]
            exact mul_le_mul (hrow k hk) ((hdiff hn k).1) (abs_nonneg _) (by positivity)
         _ ≤ (T*n)^2*(((2*K)*((T*n)^2/(M+1:ℕ))*H)*(J/(n:ℝ)^3)) := by
            rw [sum_const,nsmul_eq_mul,Nat.card_Icc,Nat.add_sub_cancel]
            exact mul_le_mul_of_nonneg_right hbound (by positivity)
         _ = _ := by field_simp <;> ring
  have he : dyadicPrimeContact n-cappedUpperProductReading U M n =
      (dyadicPrimeContact n-upperProductReading U n)+(upperProductReading U n-cappedUpperProductReading U M n) := by ring
  rw [he]
  exact (abs_add_le _ _).trans (add_le_add (hupper hn hU) hdiff')

#print axioms unit_stencil_product_partition
#print axioms dyadicPrimeContact_upper_product_tail
#print axioms capped_upper_ranges
#print axioms dyadicPrimeContact_capped_upper_product_tail
end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
