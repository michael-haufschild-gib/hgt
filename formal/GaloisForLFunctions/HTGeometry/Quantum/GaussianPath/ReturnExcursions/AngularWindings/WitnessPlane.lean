import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic

/-! # A winding test from two orthogonal field responses -/

open Finset
namespace GaloisForLFunctions.HTGeometry.ReturnExcursions.AngularWindings
noncomputable section

private theorem combination_sq {I : Type*} [Fintype I] (u v : I → ℝ) (a c : ℝ)
    (huv : (∑ i, u i*v i)=0) :
    (∑ i, (a*u i+c*v i)^2)=a^2*(∑ i, u i^2)+c^2*(∑ i, v i^2) := by
  have h (i) : (a*u i+c*v i)^2=a^2*u i^2+c^2*v i^2+(2*a*c)*(u i*v i) := by ring
  simp only [h,sum_add_distrib,←mul_sum,huv,mul_zero,add_zero]

/-- For every lifted circuit target there is a centered test perpendicular to it.
Two orthogonal field inputs and their orthogonal outputs give a lower bound on
the standard deviation of that test divided by its total absolute weight. -/
theorem winding_witness {I J : Type*} [Fintype I] [Fintype J] [Nonempty J]
    (Q : I → J → ℝ) (p f : I → ℝ) (b : J → ℝ) (d : ℝ) (hd : 0<d)
    (hp : (∑ i, p i^2)≤1) (hf : (∑ i, f i^2)≤1) (hpf : (∑ i, p i*f i)=0) :
    let u (j : J) := ∑ i, p i*Q i j
    let v (j : J) := ∑ i, f i*Q i j
    let N := (Fintype.card J:ℝ)
    (∑ j, u j)=0 → (∑ j, v j)=0 → (∑ j, u j*v j)=0 →
    N*d^2≤∑ j, u j^2 → N*d^2≤∑ j, v j^2 →
    ∃ w : J → ℝ, (∑ j, w j)=0 ∧ (∑ j, w j*b j)=0 ∧
      0<(∑ i, (∑ j, w j*Q i j)^2) ∧ d^2*(∑ j, |w j|)^2 ≤ ∑ i, (∑ j, w j*Q i j)^2 := by
  intro u v N hu hv huv hU hV
  let B := ∑ j, u j*b j
  let C := ∑ j, v j*b j
  obtain ⟨a,c,hpos,hcancel⟩ : ∃ a c : ℝ, 0<a^2+c^2 ∧ a*B+c*C=0 := by
    by_cases hB : B=0
    · exact ⟨1,0,by norm_num,by simp only [hB,mul_zero,zero_mul,add_zero]⟩
    · refine ⟨-C,B,add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_ne_zero hB),by ring⟩
  let w (j : J) := a*u j+c*v j
  let k (i : I) := a*p i+c*f i
  let m (i : I) := ∑ j, w j*Q i j
  let S := ∑ j, w j^2
  let M := ∑ i, m i^2
  have hN : 0<N := Nat.cast_pos.mpr Fintype.card_pos
  have hS : N*d^2*(a^2+c^2)≤S := by
    rw [show S=a^2*(∑ j, u j^2)+c^2*(∑ j, v j^2) from combination_sq u v a c huv]
    calc
      _ = a^2*(N*d^2)+c^2*(N*d^2) := by ring
      _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left hU (sq_nonneg _)) (mul_le_mul_of_nonneg_left hV (sq_nonneg _))
  have hs : 0<S := (mul_pos (mul_pos hN (sq_pos_of_pos hd)) hpos).trans_le hS
  have hk : (∑ i, k i^2)≤a^2+c^2 := by
    rw [show (∑ i, k i^2)=_ from combination_sq p f a c hpf]
    simpa only [mul_one] using add_le_add (mul_le_mul_of_nonneg_left hp (sq_nonneg a)) (mul_le_mul_of_nonneg_left hf (sq_nonneg c))
  have hw (j : J) : (∑ i, k i*Q i j)=w j := by
    simp only [w,u,v,k,add_mul,mul_assoc,sum_add_distrib,←mul_sum]
  have hkm : (∑ i, k i*m i)=S := by
    simp only [m,mul_sum]
    rw [sum_comm]
    apply sum_congr rfl
    intro j _
    calc
      _ = w j*∑ i, k i*Q i j := by
        rw [mul_sum]
        exact sum_congr rfl fun i _ => by ring
      _ = _ := by rw [hw j,sq]
  have hM : 0≤M := sum_nonneg fun _ _ => sq_nonneg _
  have hcs := sum_mul_sq_le_sq_mul_sq univ k m
  rw [hkm] at hcs
  have hbound : N*d^2*S ≤ M := by
    apply le_of_mul_le_mul_left (a:=a^2+c^2) _ hpos
    calc
      _ = (N*d^2*(a^2+c^2))*S := by ring
      _ ≤ S^2 := by simpa only [sq] using mul_le_mul_of_nonneg_right hS hs.le
      _ ≤ _ := hcs.trans (mul_le_mul_of_nonneg_right hk hM)
  refine ⟨w,?_,?_,(mul_pos (mul_pos hN (sq_pos_of_pos hd)) hs).trans_le hbound,?_⟩
  · simp only [w,sum_add_distrib,←mul_sum,hu,hv,mul_zero,add_zero]
  · simpa only [w,add_mul,mul_assoc,sum_add_distrib,←mul_sum] using hcancel
  · have habs := sum_mul_sq_le_sq_mul_sq univ (fun _ : J => (1:ℝ)) (fun j => |w j|)
    simp only [one_mul,one_pow,sum_const,card_univ,nsmul_eq_mul,mul_one,sq_abs] at habs
    calc
      _ ≤ d^2*(N*S) := mul_le_mul_of_nonneg_left habs (sq_nonneg _)
      _ = N*d^2*S := by ring
      _ ≤ _ := hbound

#print axioms winding_witness
end
end GaloisForLFunctions.HTGeometry.ReturnExcursions.AngularWindings
