import GaloisForLFunctions.ExceptionalLayerTheory.CenteringTheFactorialPrimeWeight
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# The first quotient cell in the ordinary prime price

The square-root moment fixes the sign of the first cell. At resolution one
the factorial stencil is a parity weight. Its correction at indices 64
through 127 outweighs the total mass on the even cells.
-/

noncomputable section
open Finset ArithmeticFunction
namespace GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval

private theorem factorialPrefix_unit_parity (j : ℕ) :
    factorialPrefix 1 j = (1/Real.log 2)*((j%2:ℕ):ℝ) := by
  have h (w : ℕ → ℝ) : stencil 1 w = (1/Real.log 2)*(w 1-2*w 2) := by
    let a := stencil 1 (fun d => if d=1 then 1 else 0)
    let b := stencil 1 (fun d => if d=2 then 1 else 0)
    have basis (f : ℕ → ℝ) : stencil 1 f = a*f 1+b*f 2 := by
      dsimp only [a,b,stencil]
      simp only [Icc_self,sum_singleton,if_true,if_neg (by decide : (1:ℕ)≠2),
        if_neg (by decide : (2:ℕ)≠1),mul_zero,mul_one,zero_add,sub_zero]
      ring
    have hz := basis (fun d => 1/d)
    have hs := basis (fun d => (1/d)*(0-Real.log d))
    rw [stencil_linear_quotient (by decide : 1≤1) 1] at hz
    rw [stencil_log_quotient (by decide : 1≤1) 1 0] at hs
    norm_num only [Nat.cast_one,Nat.cast_ofNat,Real.log_one,div_one,sub_zero,
      mul_zero,mul_one,zero_add] at hz hs
    have ha : a=1/Real.log 2 := (eq_div_iff (Real.log_pos (by norm_num : (1:ℝ)<2)).ne').mpr (by
      linear_combination -(Real.log 2)*hz-hs)
    have hb : b= -2*a := by linarith only [hz]
    rw [basis,hb,ha]; ring
  rw [factorialPrefix,h,Nat.div_one]
  have ht : ((j%2:ℕ):ℝ)+2*((j/2:ℕ):ℝ)=j := by exact_mod_cast Nat.mod_add_div j 2
  congr 1
  linarith only [ht]

private theorem quotient_cell_mass {a b : ℕ} (hab : a ≤ b) :
    ∑ j ∈ Ico a b, cellSize j = edge a-edge b := by
  simpa only [cellSize,neg_sub_neg] using
    (_root_.RHTower.Sieve.sum_Ico_telescope (fun j => -edge j) hab)

private theorem quotient_outer_band_mass :
    (2:ℝ) ≤ 64*(edge 64-edge 128) := by
  have h : (32/3:ℝ) ≤ Real.sqrt 128 := Real.le_sqrt_of_sq_le (by norm_num)
  have hi := inv_anti₀ (by norm_num : (0:ℝ)<32/3) h
  unfold edge
  norm_num only [Nat.cast_ofNat,show Real.sqrt 64=8 by norm_num]
  norm_num at hi
  linarith only [hi]

/-- The first positive outer quotient has a strictly negative coefficient. -/
theorem first_centered_quotient_negative : centeredPrimeWeight 1 1 < 0 := by
  let A := 1/Real.log 2
  let u (j : ℕ) : ℝ := ((j%2:ℕ):ℝ)
  let I : Finset ℕ := Ico 1 129
  let J : Finset ℕ := Ico 64 128
  let S := ∑ j ∈ I, u j*cellSize j
  let E := ∑ j ∈ I, (1-u j)*cellSize j
  let D := 64*(edge 64-edge 128)
  let m := momentRatio 1
  let w := 1-A-m
  have hu (j : ℕ) : 0≤u j ∧ u j≤1 :=
    ⟨Nat.cast_nonneg _,by dsimp only [u]; exact_mod_cast (show j%2≤1 by omega)⟩
  have hparity (j : ℕ) (hj : j∈I) :
      parityCorrection 1 j=u j-64*(if j∈J then 1 else 0) := by
    have hi := (mem_Ico.mp hj).2
    change ((j/1%2:ℕ):ℝ)-64*((j/(64*1)%2:ℕ):ℝ)=_
    simp only [Nat.div_one,Nat.mul_one]
    have he : j/64%2 = if j∈J then 1 else 0 := by
      dsimp only [I,J] at *
      simp only [mem_Ico]
      split <;> omega
    rw [he]
    split <;> simp only [u,Nat.cast_one,Nat.cast_zero]
  have band : ∑ j ∈ I, (if j∈J then (1:ℝ) else 0)*cellSize j = edge 64-edge 128 := by
    have hsub : J ⊆ I := by
      intro j hj
      obtain ⟨hl,hu'⟩ := mem_Ico.mp hj
      exact mem_Ico.mpr ⟨by omega,by omega⟩
    have he : I.filter (· ∈ J) = J := by
      ext j
      exact ⟨fun hj => (mem_filter.mp hj).2,fun hj => mem_filter.mpr ⟨hsub hj,hj⟩⟩
    simp only [ite_mul,one_mul,zero_mul,←sum_filter,he,J,quotient_cell_mass (by decide : 64≤128)]
  have hS : S≤1 := by
    apply (sum_le_sum (s := I) (g := cellSize) (fun j hj =>
      mul_le_of_le_one_left (cellSize_nonneg (mem_Ico.mp hj).1) (hu j).2)).trans
    rw [show I=Ico 1 129 from rfl,quotient_cell_mass (by decide : 1≤129)]
    calc edge 1-edge 129 ≤ edge 1 := sub_le_self _ (by dsimp only [edge]; positivity)
         _ = 1 := by norm_num [edge]
  have hE : E≤3/4 := by
    have hI : Ico 1 129 = insert 1 (Ico 2 129) := by ext j; simp only [mem_Ico,mem_insert]; omega
    dsimp only [E,I]
    rw [hI,sum_insert (by decide : 1∉Ico 2 129)]
    simp only [show u 1=1 by norm_num [u],sub_self,zero_mul,zero_add]
    apply (sum_le_sum (s := Ico 2 129) (g := cellSize) (fun j hj =>
      mul_le_of_le_one_left (cellSize_nonneg (by have := (mem_Ico.mp hj).1; omega))
        (sub_le_self _ (hu j).1))).trans
    rw [quotient_cell_mass (by decide : 2≤129)]
    apply (sub_le_self _ (by dsimp only [edge]; positivity : 0≤edge 129)).trans
    have hr : (4/3:ℝ)≤Real.sqrt 2 := Real.le_sqrt_of_sq_le (by norm_num)
    have hi := inv_anti₀ (by norm_num : (0:ℝ)<4/3) hr
    simpa [edge] using hi
  have hD : 2≤D := quotient_outer_band_mass
  have hA : 3/8 < A-1 := by
    have hlog : 0<Real.log 2 := Real.log_pos (by norm_num)
    have ht : 11/8 < A := (lt_div_iff₀ hlog).mpr (by linarith only [Real.log_two_lt_d9])
    linarith only [ht]
  have hm := primeWeight_moment (by decide : 1≤1)
  change (∑ j ∈ I, primeWeight 1 j*cellSize j)=0 at hm
  have he (j : ℕ) (hj : j∈I) :
      primeWeight 1 j*cellSize j=(1-u j)*cellSize j+w*(u j*cellSize j)+
        (64*m)*((if j∈J then 1 else 0)*cellSize j) := by
    rw [primeWeight,factorialPrefix_unit_parity,hparity j hj]
    dsimp only [A,w,m,u]
    ring
  rw [sum_congr rfl he,sum_add_distrib,sum_add_distrib,←mul_sum,←mul_sum,band] at hm
  change E+w*S+(64*m)*(edge 64-edge 128)=0 at hm
  have hnum : w*(S-D) = (A-1)*D-E := by
    dsimp only [w,D] at hm ⊢
    linarith only [hm]
  have hpos : 0<(A-1)*D-E := by
    have h := (mul_lt_mul_of_pos_right hA (by norm_num : (0:ℝ)<2)).trans_le
      (mul_le_mul_of_nonneg_left hD (by linarith only [hA]))
    linarith only [h,hE]
  have hw : w<0 := by
    by_contra! hw
    have hh := mul_nonpos_of_nonneg_of_nonpos hw (by linarith only [hS,hD] : S-D≤0)
    rw [hnum] at hh
    exact hpos.not_ge hh
  have h1 := hparity 1 (by decide)
  have h129 := parityCorrection_small (by decide : 1<128*1^2+1)
  simpa only [centeredPrimeWeight,primeWeight,factorialPrefix_unit_parity,h1,h129,
    show 1∉J by decide,if_false,mul_zero,add_zero,sub_zero,show u 1=1 by norm_num [u],mul_one,
    show ((1%2:ℕ):ℝ)=1 by norm_num,A,w,m] using hw

/-- The second outer quotient has unit coefficient. Both parity corrections
and the factorial stencil vanish on this even input. -/
theorem second_centered_quotient_unit : centeredPrimeWeight 1 2=1 := by
  rw [centeredPrimeWeight,primeWeight,factorialPrefix_unit_parity,parityCorrection_floors,
    parityCorrection_small (by decide : 2<128*1^2+1)]
  norm_num

#print axioms second_centered_quotient_unit
#print axioms first_centered_quotient_negative

end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
