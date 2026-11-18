import GaloisForLFunctions.ExceptionalLayerTheory.LargeComplementsInTheCoprimeProduct
import GaloisForLFunctions.ExceptionalLayerTheory.TheUpperBoundaryOfTheTransposedPrimeRow

/-!
# Averaging the complementary cutoff in the ordinary coprime row

The lower boundary is averaged before taking absolute values. The upper
boundary is the entire dual product head. Repeated primes have a
reciprocal-prime bound at each cutoff.
-/

noncomputable section
open Finset ArithmeticFunction RHTower
namespace GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval

/-- Complete ordinary-prime slices above a complementary lower cutoff. -/
def ordinaryComplementTail (D R X F a : ℕ) : ℝ :=
  ordinaryFactorTail F X (fun p => factorSlice D R X (a*p) p)

private def complementaryLowerBoundary (D R X F a : ℕ) :=
  ordinaryFactorTail F X (fun p => factorialBoundary (D+1) a*
    ∑ j ∈ Icc 1 (X/p/(a+1)), outerJump R j)

private theorem transpose (D R X F : ℕ) {a : ℕ} (ha : 1≤a) :
    ordinaryComplementTail D R X F a=dualBoundaryHead X (D+1) F (X/(a+1)) (outerJump R)-complementaryLowerBoundary D R X F a := by
  unfold ordinaryComplementTail dualBoundaryHead complementaryLowerBoundary ordinaryFactorTail
  rw [←sum_sub_distrib]
  apply sum_congr rfl
  intro p hp
  have hp₀ := (mem_filter.mp hp).2.pos
  rw [←mul_sub,factorSlice,Nat.mul_div_cancel _ hp₀,complementary_tail_transpose D R _ ha]
  simp only [Nat.div_div_eq_div_mul,Nat.mul_comm (a+1) p]

/-- Ordinary prime row with a fixed cap on its complementary factor. -/
def cappedComplementaryRow (D R X F Y a : ℕ) :=
  ordinaryFactorTail F X (cappedCoprimeSlice D R X Y a)

/-- At cutoffs beyond the lower product edge the coprime tail differs
from the unrestricted tail by a uniform square-root error. -/
theorem complement_tail_coprime_comparison :
    ∃ K : ℝ, 0≤K ∧ ∀ {D R X F Y a : ℕ}, 1≤D → 1≤R → 1≤X → 2*(D+1)≤F → Y/(F+1)≤a →
      |ordinaryFactorTail F X (coprimeSlice D R X Y)-cappedComplementaryRow D R X F Y a-ordinaryComplementTail D R X F a|≤
        K*((D+1 : ℕ) : ℝ)*R*Real.sqrt X*(1+Real.log X) := by
  obtain ⟨K,hK,h⟩ := factor_slice_bounds
  let E := Real.log 4+4
  have hE : 0≤E := by dsimp [E]; linarith only [Real.log_nonneg (by norm_num : (1 : ℝ)≤4)]
  refine ⟨K*E,by positivity,?_⟩
  intro D R X F Y a hD hR hx hF hY
  let f (p : ℕ) := coprimeSlice D R X (a*p) p-factorSlice D R X (a*p) p
  have heq : ordinaryFactorTail F X (coprimeSlice D R X Y)-cappedComplementaryRow D R X F Y a-ordinaryComplementTail D R X F a =
      ordinaryFactorTail F X f := by
    unfold cappedComplementaryRow ordinaryComplementTail ordinaryFactorTail
    rw [←sum_sub_distrib,←sum_sub_distrib]
    apply sum_congr rfl; intro p hp
    obtain ⟨hi,hp'⟩ := mem_filter.mp hp
    have hle : Y/p≤a := ((Nat.le_div_iff_mul_le (Nat.succ_pos F)).mpr
      ((Nat.mul_le_mul_left (Y/p) (mem_Ioc.mp hi).1).trans (Nat.div_mul_le_self Y p))).trans hY
    have hc : coprimeSlice D R X Y p-cappedCoprimeSlice D R X Y a p=coprimeSlice D R X (a*p) p := by
      rw [coprimeSlice_sub_capped,max_eq_right hle,coprimeSlice,Nat.mul_div_cancel _ hp'.pos,sum_filter]
      apply sum_congr rfl; intro v _
      by_cases h : p.Coprime v <;> simp [h]
    rw [←mul_sub,←mul_sub,hc]
  rw [heq]
  let C := K*((D+1 : ℕ) : ℝ)*R*Real.sqrt X
  have hf (p : ℕ) (hp : p ∈ (Ioc F X).filter Nat.Prime) : |f p|≤C/p := by
    obtain ⟨hi,hp'⟩ := mem_filter.mp hp
    dsimp only [f]; rw [abs_sub_comm]
    exact (h hD hR X (a*p)).2 p hp' (hF.trans_lt (mem_Ioc.mp hi).1)
  exact (ordinaryFactorTail_reciprocal hx (by dsimp [C]; positivity) hf).trans_eq (by dsimp [E,C]; ring)

/-- Mean over consecutive complementary cutoffs. -/
def complementAverage (A S : ℕ) (f : ℕ → ℝ) := (∑ a ∈ Ico A (A+S), f a)/(S : ℝ)

private theorem average_le {A S : ℕ} (hS : 0<S) {f : ℕ → ℝ} {M : ℝ}
    (h : ∀ a ∈ Ico A (A+S), |f a|≤M) : |complementAverage A S f|≤M := by
  unfold complementAverage
  have hs : (0 : ℝ)<S := by exact_mod_cast hS
  rw [abs_div,abs_of_nonneg hs.le]
  apply (div_le_iff₀ hs).mpr
  apply (abs_sum_le_sum_abs _ _).trans ((sum_le_sum h).trans_eq _)
  rw [sum_const,Nat.card_Ico,Nat.add_sub_cancel_left,nsmul_eq_mul,mul_comm]

/-- Starting at any positive complement whose dual horizon lies below
the product-window endpoint, tapering the coprime row costs square-root
error at all logarithmic stencil scales. -/
theorem averaged_coprime_tail :
    ∃ K : ℝ, 0≤K ∧ ∀ {D R X F Y A : ℕ}, 1≤D → 1≤R → 1≤X → 2*(D+1)≤F →
      64≤(X : ℝ)^(1/25000000 : ℝ) → ((2*(D+1) : ℕ) : ℝ)≤(X : ℝ)^(1/25000000 : ℝ) →
      ⌊(X : ℝ)^(1/1000000 : ℝ)⌋₊≤F → 1≤A → Y/(F+1)≤A →
      ((X/(A+1) : ℕ) : ℝ)≤(X : ℝ)^(500000001/1000000000 : ℝ) →
      let S := ⌊Real.sqrt X/(A+1 : ℕ)⌋₊+1
      |ordinaryFactorTail F X (coprimeSlice D R X Y)-complementAverage A S (cappedComplementaryRow D R X F Y)|≤
        K*((D+1 : ℕ) : ℝ)^2*R*(1+Real.log X)^3*Real.sqrt X := by
  obtain ⟨C,hC,hcap⟩ := complement_tail_coprime_comparison
  obtain ⟨B,hB,hβ⟩ := outerJump_uniform
  obtain ⟨M,hM,hmass⟩ := mass_uniform
  obtain ⟨K,hK,hhead⟩ := dualBoundaryHead_bound
  let E := Real.log 4+4
  have hE : 0≤E := by dsimp [E]; linarith only [Real.log_nonneg (by norm_num : (1 : ℝ)≤4)]
  refine ⟨C+K*M*B+M*B*E,by positivity,?_⟩
  intro D R X F Y A hD hR hx hF hbig hd hcut hA hY hU S
  let J := 1+Real.log X
  let d : ℝ := (D+1 : ℕ)
  let base := ordinaryFactorTail F X (coprimeSlice D R X Y)
  let cap := cappedComplementaryRow D R X F Y
  let raw := ordinaryComplementTail D R X F
  let top (a : ℕ) := dualBoundaryHead X (D+1) F (X/(a+1)) (outerJump R)
  let bot := complementaryLowerBoundary D R X F
  let gap (a : ℕ) := base-cap a-raw a
  have hs : 0<S := Nat.succ_pos _
  have hs' : (S : ℝ)≠0 := by exact_mod_cast Nat.ne_of_gt hs
  have hJ : 1≤J := le_add_of_nonneg_right (Real.log_natCast_nonneg X)
  have hj := zero_le_one.trans hJ
  have hd₁ : 1≤d := by exact_mod_cast Nat.succ_pos D
  have hd₀ := zero_le_one.trans hd₁
  have hj₃ : J≤J^3 := by simpa only [pow_one] using pow_le_pow_right₀ hJ (by norm_num : 1≤3)
  have hd₂ : d≤d^2 := by simpa only [pow_one] using pow_le_pow_right₀ hd₁ (by norm_num : 1≤2)
  have hΔ : |complementAverage A S gap|≤C*d*R*Real.sqrt X*J :=
    average_le hs fun a ha => hcap hD hR hx hF (hY.trans (mem_Ico.mp ha).1)
  have hm := hmass (D+1) (Nat.succ_pos D)
  have htop : |complementAverage A S top|≤K*(M*d)*(B*R)*J^3*Real.sqrt X := by
    apply average_le hs; intro a ha
    have hq : X/(a+1)≤X/(A+1) := (Nat.le_div_iff_mul_le (Nat.succ_pos A)).mpr
      ((Nat.mul_le_mul_left (X/(a+1)) (Nat.succ_le_succ (mem_Ico.mp ha).1)).trans (Nat.div_mul_le_self ..))
    apply (hhead hx (Nat.succ_pos D) hbig hd hcut ((by exact_mod_cast hq :
      ((X/(a+1) : ℕ) : ℝ)≤(X/(A+1) : ℕ)).trans hU) _ (by positivity) (hβ hR)).trans
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hm hK) (by positivity)) (by positivity)) (Real.sqrt_nonneg _)
  have hbot : |complementAverage A S bot|≤M*d*(d/4)*(B*R)*Real.sqrt X*(E*J) := by
    apply (averaged_ordinary_complementary_boundary (F := F) (A := A) hx (Nat.succ_pos D)
      (outerJump R) (by positivity) (hβ hR)).trans
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hm (by positivity)) (by positivity)) (Real.sqrt_nonneg _)) (mul_nonneg hE hj)
  have eq : base-complementAverage A S cap =
      (complementAverage A S gap+complementAverage A S top)-complementAverage A S bot := by
    have heq (a : ℕ) (ha : a ∈ Ico A (A+S)) : base-cap a=gap a+top a-bot a := by
      have hh : raw a=top a-bot a := transpose D R X F (hA.trans (mem_Ico.mp ha).1)
      dsimp only [gap]; rw [hh]; ring
    have hh := sum_congr rfl heq
    simp only [sum_sub_distrib,sum_add_distrib,sum_const,Nat.card_Ico,Nat.add_sub_cancel_left,nsmul_eq_mul] at hh
    unfold complementAverage
    calc _ = ((S : ℝ)*base-(∑ a ∈ Ico A (A+S), cap a))/S := by
             rw [sub_div,mul_div_cancel_left₀ base hs']
         _ = _ := by rw [hh,sub_div,add_div]
  rw [eq]
  apply (abs_sub _ _).trans ((add_le_add_right (abs_add_le _ _) _).trans ((add_le_add (add_le_add hΔ htop) hbot).trans _))
  have h1 := mul_le_mul_of_nonneg_right (mul_le_mul hd₂ hj₃ hj (sq_nonneg d))
    (by positivity : 0≤C*R*Real.sqrt X)
  have h2 := mul_le_mul_of_nonneg_right hd₂ (by positivity : 0≤K*M*(B*R)*J^3*Real.sqrt X)
  have h3 := mul_le_mul_of_nonneg_right hj₃ (by positivity : 0≤M*d^2*(B*R)*Real.sqrt X*E)
  have h4 : 0≤M*d^2*(B*R)*Real.sqrt X*E*J := by positivity
  change _≤(C+K*M*B+M*B*E)*d^2*R*J^3*Real.sqrt X
  linarith only [h1,h2,h3,h4]

end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
