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

private def squareColumnEnd (v p t : ℕ) := if t=v then unitProductHorizonEnd (p*t) else 0

private theorem column_cell {k q : ℕ} (h : q≤k) :
    productLower 1 k<q ↔ k<unitProductHorizonEnd q := by
  rw [productLower,Real.nat_floor_real_sqrt_eq_nat_sqrt,min_lt_iff,unitProductHorizonEnd,←Nat.sqrt_lt']
  omega

/-- Exact effect of the lower cutoff on one retained square complement. -/
theorem squareComplementRow_sub_capped {ℓ U M : ℕ} (hℓ : 0<ℓ) (hM : ℓ^2≤M) (k : ℕ) :
    squareComplementRow ℓ k-cappedSquareComplementRow ℓ U M k =
      clippedPrimeProducts 1 1 4 U (fun p t => p*t) (squareColumnEnd (ℓ^2)) k := by
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
  have hterm (p t : ℕ) : innerJump 1 t*(if p*t≤k ∧ k<squareColumnEnd v p t then
      centeredPrimeWeight 1 (k/(p*t)) else 0) =
      if t=v then (if p*v≤k ∧ productLower 1 k<p*v then innerJump 1 v*centeredPrimeWeight 1 (k/(p*v)) else 0) else 0 := by
    by_cases he : t=v
    · subst t; by_cases hk : p*v≤k
      · simp only [squareColumnEnd,if_pos rfl,hk,true_and,column_cell hk,mul_ite,mul_zero]
      · simp [hk,squareColumnEnd]
    · simp [squareColumnEnd,he]
  rw [hleft,hST]
  dsimp only [T]; rw [sum_filter]
  unfold clippedPrimeProducts ordinaryFactorTail
  apply sum_congr rfl; intro p _
  change _ = vonMangoldt p*∑ t ∈ (Icc 1 (U/p)).filter (p.Coprime ·),
    innerJump 1 t*(if p*t≤k ∧ k<squareColumnEnd v p t then centeredPrimeWeight 1 (k/(p*t)) else 0)
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
      splineCountReading n (clippedPrimeProducts 1 1 4 U (fun p t => p*t) (squareColumnEnd (ℓ^2))) := by
    unfold splineCountReading
    rw [←sum_sub_distrib]
    exact sum_congr rfl fun k _ => by rw [←sub_mul,squareComplementRow_sub_capped hℓ hM]
  rw [he]
  simpa only [A,B,Nat.cast_one] using h hn (R := 1) le_rfl hu hU 1 4 (fun p t => p*t) (squareColumnEnd (ℓ^2))

#print axioms squareComplementRow_sub_capped
#print axioms squareComplementRow_clip_cost

end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
