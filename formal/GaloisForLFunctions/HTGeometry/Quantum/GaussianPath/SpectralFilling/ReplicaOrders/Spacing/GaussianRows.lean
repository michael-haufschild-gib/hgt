import GaloisForLFunctions.HTGeometry.SeparatedOffDiagonalBound

/-! # Gaussian observation of separated real frequencies -/
open Finset Real
namespace GaloisForLFunctions.HTGeometry.SpectralFilling.ReplicaOrders
noncomputable section

private theorem dyadic_integer_sum : HasSum (fun z : ℤ => (1/2:ℝ)^z.natAbs) 3 := by
  rw [show (3:ℝ)=2+1 by norm_num]
  let f (z : ℤ) := (1/2:ℝ)^z.natAbs
  have hp : HasSum (fun n : ℕ => f n) 2 := hasSum_geometric_two
  have hn : HasSum (fun n : ℕ => f (-((n:ℤ)+1))) 1 := by
    change HasSum (fun n : ℕ => (1/2:ℝ)^(n+1)) 1
    have h : HasSum (fun n : ℕ => (1/2:ℝ)^n*(1/2)) (2*(1/2):ℝ) :=
      hasSum_geometric_two.mul_right (1/2:ℝ)
    rw [show (2:ℝ)*(1/2)=1 by norm_num] at h
    simpa only [pow_succ] using h
  exact HasSum.of_nat_of_neg_add_one (f:=f) hp hn

private theorem gaussian_floor_weight (a : ℝ) :
    exp (-a^2/2) ≤ 4*(1/2:ℝ)^⌊a⌋.natAbs := by
  let w := ⌊a⌋.natAbs
  have habs : (w:ℝ) = |(⌊a⌋:ℝ)| := by
    simp only [w,←Int.cast_abs,←Int.natCast_natAbs,Int.cast_natCast]
  have hw : (w:ℝ) ≤ |a|+1 := by
    rw [habs,abs_le]
    constructor
    · linarith only [Int.lt_floor_add_one a,neg_abs_le a]
    · linarith only [Int.floor_le a,le_abs_self a]
  have hlog : log 2 ≤ 1 := by linarith only [log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)]
  have hexp : (w:ℝ)*log 2-2*log 2 ≤ a^2/2 := by
    by_cases h : (w:ℝ) ≤ 2
    · linarith only [mul_le_mul_of_nonneg_right h (log_nonneg (by norm_num : (1:ℝ)≤2)),sq_nonneg a]
    · have hmul := mul_le_mul_of_nonneg_left hlog (sub_nonneg.mpr (le_of_not_ge h))
      nlinarith only [hmul,hw,sq_nonneg (|a|-1),sq_abs a]
  calc _ ≤ exp (2*log 2-(w:ℝ)*log 2) := exp_le_exp.mpr (by linarith only [hexp])
       _ = _ := by
         rw [exp_sub,show 2*log 2=((2:ℕ):ℝ)*log 2 by norm_num,exp_nat_mul,exp_nat_mul,
           exp_log (by norm_num),one_div,inv_pow]
         norm_num only [Nat.reducePow]
         ring

/-- Each unit interval contains at most one of the frequencies. Summing
the dyadic majorant over occupied integer bins costs at most 12 per row. -/
theorem separated_gaussian_row {I : Type*} [Fintype I] (F : I → ℝ)
    (hsep : ∀ i j, i≠j → 1 ≤ |F i-F j|) (r : I) :
    ∑ j, exp (-(F r-F j)^2/2) ≤ 12 := by
  classical
  let code (j : I) := ⌊F r-F j⌋
  have hinj : Function.Injective code := by
    intro i j he
    by_contra hij
    have hl (s : I) : (code s:ℝ) ≤ F r-F s := Int.floor_le _
    have hu (s : I) : F r-F s < (code s:ℝ)+1 := Int.lt_floor_add_one _
    have hcast := congrArg (fun z : ℤ => (z:ℝ)) he
    have hclose : |F i-F j| < 1 := abs_lt.mpr
      ⟨by linarith only [hl j,hu i,hcast],by linarith only [hl i,hu j,hcast]⟩
    exact (hsep i j hij).not_gt hclose
  let b (z : ℤ) := (1/2:ℝ)^z.natAbs
  calc _ ≤ ∑ j, 4*b (code j) := sum_le_sum fun j _ => gaussian_floor_weight _
       _ = 4*∑ z ∈ univ.image code, b z := by rw [←Finset.mul_sum,Finset.sum_image hinj.injOn]
       _ ≤ 4*3 := mul_le_mul_of_nonneg_left ((dyadic_integer_sum.summable.sum_le_tsum _
         (fun _ _ => pow_nonneg (by norm_num) _)).trans_eq dyadic_integer_sum.tsum_eq) (by norm_num)
       _ = _ := by norm_num

/-- Gaussian averaging at inverse spacing bounds the entire weighted
second moment by twelve times its diagonal, for any number of frequencies. -/
theorem separated_gaussian_energy {I : Type*} [Fintype I] (F b : I → ℝ)
    (hsep : ∀ i j, i≠j → 1 ≤ |F i-F j|) :
    ∑ i, ∑ j, |b i| * |b j| * exp (-(F i-F j)^2/2) ≤ 12*∑ i, (b i)^2 := by
  apply weighted_double_sum_le_rowBound (K:=fun i j => exp (-(F i-F j)^2/2))
  · intro i j
    rw [sub_sq_comm]
  · exact fun _ _ => (exp_pos _).le
  · exact separated_gaussian_row F hsep

#print axioms separated_gaussian_energy
end
end GaloisForLFunctions.HTGeometry.SpectralFilling.ReplicaOrders
