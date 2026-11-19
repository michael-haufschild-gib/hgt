import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.ThePrimeSignalAtASquareComplement
import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.TheCompleteUpperProductTail

/-!
# The square complement after the conductor cutoffs

At a fixed prime square the discarded lower product range is one column
of clipped horizon intervals. Its spline reading costs one logarithm.
-/

noncomputable section
open Finset ArithmeticFunction
open GaloisForLFunctions.CountingHolography.Sections
namespace GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval

/-- The square fibre of the actual capped coprime row. -/
def cappedSquareComplementRow (ℓ U M k : ℕ) : ℝ :=
  if ℓ^2≤M then ∑ p ∈ Icc 1 (k/ℓ^2),
    if (p.Prime ∧ 4<p ∧ p.Coprime (ℓ^2) ∧ productLower 1 k<p*ℓ^2) ∧ U<p*ℓ^2 then
      innerJump 1 (ℓ^2)*(vonMangoldt p*centeredPrimeWeight 1 (k/ℓ^2/p)) else 0
  else 0

/-- Closing all other cofactor intervals isolates the chosen column. -/
def cofactorColumnHorizonEnd (v p t : ℕ) := if t=v then unitProductHorizonEnd (p*t) else 0

private theorem column_cell {k q : ℕ} (h : q≤k) :
    productLower 1 k<q ↔ k<unitProductHorizonEnd q := by
  rw [productLower,Real.nat_floor_real_sqrt_eq_nat_sqrt,min_lt_iff,unitProductHorizonEnd,←Nat.sqrt_lt']
  omega

/-- Exact effect of the lower cutoff on one retained square complement. -/
theorem squareComplementRow_sub_capped {ℓ U M : ℕ} (hℓ : 0<ℓ) (hM : ℓ^2≤M) (k : ℕ) :
    squareComplementRow ℓ k-cappedSquareComplementRow ℓ U M k =
      clippedPrimeProducts 1 1 4 U (fun p t => p*t) (cofactorColumnHorizonEnd (ℓ^2)) k := by
  let v := ℓ^2
  have hv : 0<v := pow_pos hℓ 2
  let good (p : ℕ) := p.Prime ∧ 4<p ∧ p.Coprime v ∧ productLower 1 k<p*v
  let a (p : ℕ) := innerJump 1 v*(vonMangoldt p*centeredPrimeWeight 1 (k/v/p))
  let S := (Icc 1 (k/v)).filter (fun p => good p ∧ p*v≤U)
  have hleft : squareComplementRow ℓ k-cappedSquareComplementRow ℓ U M k = ∑ p ∈ S, a p := by
    unfold squareComplementRow cappedSquareComplementRow
    rw [if_pos hM,←sum_sub_distrib]
    dsimp only [S]; rw [sum_filter]
    apply sum_congr rfl; intro p _
    change (if good p then a p else 0)-(if good p ∧ U<p*v then a p else 0)=_
    by_cases hg : good p
    · by_cases hu : p*v≤U
      · simp [hg,hu,not_lt.mpr hu]
      · simp [hg,hu,lt_of_not_ge hu]
    · simp [hg]
  let T := ((Ioc 4 U).filter Nat.Prime).filter fun p =>
    v∈(Icc 1 (U/p)).filter (p.Coprime ·) ∧ p*v≤k ∧ productLower 1 k<p*v
  have hST : S=T := by
    ext p
    simp only [S,T,good,mem_filter,mem_Icc,mem_Ioc,Nat.le_div_iff_mul_le hv]
    constructor
    · rintro ⟨⟨_,hk⟩,⟨hp,hp₄,hcop,hy⟩,hu⟩
      exact ⟨⟨⟨hp₄,(Nat.le_mul_of_pos_right p hv).trans hu⟩,hp⟩,
        ⟨⟨hv,(Nat.le_div_iff_mul_le hp.pos).mpr (by simpa only [Nat.mul_comm v p] using hu)⟩,hcop⟩,hk,hy⟩
    · rintro ⟨⟨⟨h₄,_⟩,hp⟩,⟨⟨_,hvU⟩,hc⟩,hk,hy⟩
      exact ⟨⟨hp.pos,hk⟩,⟨hp,h₄,hc,hy⟩,by simpa only [Nat.mul_comm v p] using (Nat.le_div_iff_mul_le hp.pos).mp hvU⟩
  have hterm (p t : ℕ) : innerJump 1 t*(if p*t≤k ∧ k<cofactorColumnHorizonEnd v p t then
      centeredPrimeWeight 1 (k/(p*t)) else 0) =
      if t=v then (if p*v≤k ∧ productLower 1 k<p*v then innerJump 1 v*centeredPrimeWeight 1 (k/(p*v)) else 0) else 0 := by
    by_cases he : t=v
    · subst t; by_cases hk : p*v≤k
      · simp only [cofactorColumnHorizonEnd,↓reduceIte,hk,true_and,column_cell hk,mul_ite,mul_zero]
      · simp [hk,cofactorColumnHorizonEnd]
    · simp [cofactorColumnHorizonEnd,he]
  rw [hleft,hST]
  dsimp only [T]; rw [sum_filter]
  unfold clippedPrimeProducts ordinaryFactorTail
  apply sum_congr rfl; intro p _
  change _ = vonMangoldt p*∑ t ∈ (Icc 1 (U/p)).filter (p.Coprime ·),
    innerJump 1 t*(if p*t≤k ∧ k<cofactorColumnHorizonEnd v p t then centeredPrimeWeight 1 (k/(p*t)) else 0)
  simp_rw [hterm]; rw [sum_ite_eq']
  by_cases hm : v∈(Icc 1 (U/p)).filter (p.Coprime ·) <;>
    by_cases hc : p*v≤k ∧ productLower 1 k<p*v <;>
    simp only [hm,hc,true_and,false_and,if_true,if_false,mul_zero,a,Nat.div_div_eq_div_mul,Nat.mul_comm v p] <;> ring

/-- A retained square fibre pays at most one logarithm for every product
cutoff through n floor(√n), including the incomplete quotient cells. -/
theorem squareComplementRow_clip_cost : ∃ C : ℝ, 0≤C ∧
    ∀ {ℓ n U M : ℕ}, 0<ℓ → 0<n → 0<U → U≤n*n.sqrt → ℓ^2≤M →
      |splineCountReading n (squareComplementRow ℓ)-
        splineCountReading n (cappedSquareComplementRow ℓ U M)|≤C*(1+Real.log U) := by
  obtain ⟨C,hC,h⟩ := spline_three_quarter_product_bound
  let A := 2*(1+mass (1+1))
  let B := 125*(1+mass 1)*(128*(128*(1:ℝ)^2+1))
  have hA : 0≤A := (abs_nonneg _).trans (innerJump_pointwise_bound 1 0)
  have hm := (abs_nonneg _).trans (abs_prefix_le_mass (R := 1) le_rfl 0)
  have hB : 0≤B := by dsimp [B]; positivity
  refine ⟨C*A*B,by positivity,fun {ℓ n U M} hℓ hn hu hU hM => ?_⟩
  have he : splineCountReading n (squareComplementRow ℓ)-splineCountReading n (cappedSquareComplementRow ℓ U M) =
      splineCountReading n (clippedPrimeProducts 1 1 4 U (fun p t => p*t) (cofactorColumnHorizonEnd (ℓ^2))) := by
    unfold splineCountReading
    rw [←sum_sub_distrib]
    exact sum_congr rfl fun k _ => by rw [←sub_mul,squareComplementRow_sub_capped hℓ hM]
  rw [he]
  simpa only [A,B,Nat.cast_one] using h hn (R := 1) le_rfl hu hU 1 4 (fun p t => p*t) (cofactorColumnHorizonEnd (ℓ^2))

/-- All multiples of the chosen square at one first prime, with the
same sharp product and cofactor endpoints as the capped row. -/
def squareMultipleSlice (ℓ k Y M p : ℕ) :=
  ∑ v ∈ Ioc (Y/p) (min (k/p) M) with ℓ^2 ∣ v,
    if p.Coprime v then innerJump 1 v*centeredPrimeWeight 1 (k/p/v) else 0

/-- Every dilation coprime to the unit stencil's divisor moduli has the
same solitary defect at t = 1, independently of its prime factors. -/
theorem innerJump_rough_multiple {r t : ℕ} (hr : 1<r) (hc : r.Coprime 12) (ht : 0<t) :
    innerJump 1 (r*t)=innerJump 1 t-(if t=1 then 1 else 0) := by
  let f (v d : ℕ) : ℝ := if d ∣ v then 1 else 0
  have test (d : ℕ) (hd : d∈Icc 1 (2*2)) : f (r*t) d=f (5*t) d := by
    obtain ⟨hd₁,hd₄⟩ := mem_Icc.mp hd
    have hdv : d ∣ 12 := by norm_num1 at hd₄; interval_cases d <;> decide
    have h₁ := Nat.Coprime.of_dvd_left hdv hc.symm
    have h₂ := Nat.Coprime.of_dvd_left hdv (show Nat.Coprime 12 5 by decide)
    simp only [f,h₁.dvd_mul_left,h₂.dvd_mul_left]
  have hs := abs_stencil_le (R := 2) (by decide) (fun d => f (r*t) d-f (5*t) d) (M := 0)
    (fun d hd => by rw [test d hd,sub_self,abs_zero])
  rw [mul_zero,abs_nonpos_iff,stencil_sub,sub_eq_zero] at hs
  have hrt : 2≤r*t := hr.trans_le (Nat.le_mul_of_pos_right r ht)
  have h5t : 2≤5*t := (by decide : 2≤5).trans (Nat.le_mul_of_pos_right 5 ht)
  calc innerJump 1 (r*t) = innerJump 1 (5*t) := by
         rw [innerJump_divisor_stencil hrt,innerJump_divisor_stencil h5t]
         exact congrArg Neg.neg hs
       _ = _ := innerJump_prime_multiple le_rfl (by decide : Nat.Prime 5) (by decide) ht

/-- Dividing every complementary factor by ℓ² produces the same capped
coprime slice and subtracts its unit quotient. Both terms have the
same divided endpoints, including the last incomplete quotient. -/
theorem squareMultipleSlice_divided {ℓ p : ℕ} (hℓ : ℓ.Prime) (h₄ : 4<ℓ) (hp : p.Prime)
    (k Y M : ℕ) :
    squareMultipleSlice ℓ k Y M p = if p.Coprime (ℓ^2) then
      cappedCoprimeSlice 1 1 (k/ℓ^2) (Y/ℓ^2) (M/ℓ^2) p-
        (if 1∈Ioc (Y/ℓ^2/p) (min (k/ℓ^2/p) (M/ℓ^2)) then centeredPrimeWeight 1 (k/ℓ^2/p) else 0)
      else 0 := by
  let d := ℓ^2
  have hd : 0<d := pow_pos hℓ.pos 2
  have hdiv (x : ℕ) : x/p/d=x/d/p := by simp only [Nat.div_div_eq_div_mul,Nat.mul_comm p d]
  have hmin (a b : ℕ) : min a b/d=min (a/d) (b/d) := by
    rcases le_total a b with h|h
    · rw [min_eq_left h,min_eq_left (Nat.div_le_div_right h)]
    · rw [min_eq_right h,min_eq_right (Nat.div_le_div_right h)]
  have hcop (t : ℕ) : p.Coprime (d*t) ↔ p.Coprime d ∧ p.Coprime t := by
    simp only [hp.coprime_iff_not_dvd,hp.dvd_mul,not_or]
  have hjump (t : ℕ) (ht : 0<t) : innerJump 1 (d*t)=innerJump 1 t-(if t=1 then 1 else 0) := by
    have hlarge := Nat.le_mul_of_pos_right ℓ ht
    have hne : ℓ*t≠1 := by omega
    dsimp only [d]; rw [sq,Nat.mul_assoc,innerJump_prime_multiple le_rfl hℓ h₄ (Nat.mul_pos hℓ.pos ht),
      if_neg hne,sub_zero,innerJump_prime_multiple le_rfl hℓ h₄ ht]
  unfold squareMultipleSlice
  rw [sum_divisible_Ioc hd,hmin,hdiv,hdiv]
  let S := Ioc (Y/d/p) (min (k/d/p) (M/d))
  by_cases hc : p.Coprime d
  swap
  · rw [if_neg hc]; exact sum_eq_zero fun t _ => if_neg (fun h => hc ((hcop t).mp h).1)
  rw [if_pos hc]
  have he (t : ℕ) (ht : t∈S) :
      (if p.Coprime (d*t) then innerJump 1 (d*t)*centeredPrimeWeight 1 (k/p/(d*t)) else 0) =
        (if p.Coprime t then innerJump 1 t*centeredPrimeWeight 1 (k/d/p/t) else 0)-
        (if t=1 then centeredPrimeWeight 1 (k/d/p) else 0) := by
    have ht₀ := (Nat.zero_le _).trans_lt (mem_Ioc.mp ht).1
    rw [←Nat.div_div_eq_div_mul (k/p) d t,hdiv,hjump t ht₀]
    by_cases hut : t=1
    · subst t; simp [hc,sub_mul]
    · have hct : p.Coprime (d*t) ↔ p.Coprime t := (hcop t).trans (and_iff_right hc)
      simp only [hct,hut,↓reduceIte,sub_zero]
  rw [sum_congr (s₁ := S) rfl he,sum_sub_distrib,sum_ite_eq']
  simp only [cappedCoprimeSlice,sum_filter,S,d]

#print axioms squareComplementRow_sub_capped
#print axioms squareComplementRow_clip_cost
#print axioms innerJump_rough_multiple
#print axioms squareMultipleSlice_divided

end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
