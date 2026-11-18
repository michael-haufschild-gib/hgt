import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.PeriodicQuotientCancellation

/-!
# Square dilation on the prime mesh

Dividing the count horizon by r² at conductor rn divides its reading by
r at conductor n. The floor is constant on each block of r² integers
and all intermediate spline differences telescope.
-/

noncomputable section
open Finset
open GaloisForLFunctions.CountingHolography.Sections
namespace GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval

private theorem reading_padded {n T : ℕ} (hn : 0<n) (hT : splineHorizon n<T)
    (f : ℕ → ℝ) (hz : f 0=0) :
    splineCountReading n f = ∑ k ∈ range T, f k*(sampledSpline n k-sampledSpline n (k+1)) := by
  unfold splineCountReading
  apply sum_subset
  · intro k hk
    exact mem_range.mpr ((mem_Icc.mp hk).2.trans_lt hT)
  · intro k _ hk
    rcases Nat.eq_zero_or_pos k with rfl | hp
    · rw [hz,zero_mul]
    · have h : splineHorizon n<k := lt_of_not_ge (fun he => hk (mem_Icc.mpr ⟨hp,he⟩))
      rw [sampledSpline_eq_zero_after hn h,sampledSpline_eq_zero_after hn (h.trans (Nat.lt_succ_self k)),sub_self,mul_zero]

private theorem quotient_blocks {d : ℕ} (hd : 0<d) (f w : ℕ → ℝ) (M : ℕ) :
    (∑ k ∈ range (d*M), f (k/d)*(w k-w (k+1))) =
    ∑ j ∈ range M, f j*(w (d*j)-w (d*(j+1))) := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [Nat.mul_succ,sum_range_add,ih,sum_range_succ]
    congr 1
    have hb (i : ℕ) (hi : i ∈ range d) : (d*M+i)/d=M := by
      rw [Nat.mul_add_div hd,Nat.div_eq_of_lt (mem_range.mp hi),Nat.add_zero]
    calc _ = ∑ i ∈ range d, f M*(w (d*M+i)-w (d*M+i+1)) := by
              exact sum_congr rfl fun i hi => by rw [hb i hi]
         _ = _ := by
              rw [←mul_sum]
              congr 1
              have ht := sum_range_sub (fun i : ℕ => -w (d*M+i)) d
              simpa only [neg_sub_neg,Nat.add_assoc,Nat.add_zero,Nat.mul_succ] using ht

/-- On the submesh of multiples of r², the whole two-dilation spline
agrees with its reading at the smaller conductor, up to the factor 1/r. -/
theorem sampledSpline_square_dilation {n r : ℕ} (hn : 0<n) (hr : 0<r) (j : ℕ) :
    sampledSpline (r*n) (r^2*j)=sampledSpline n j/r := by
  have hr' : (0:ℝ)<r := Nat.cast_pos.mpr hr
  have hn' : (0:ℝ)<n := Nat.cast_pos.mpr hn
  unfold sampledSpline
  push_cast
  rw [show (r:ℝ)^2*j/((r:ℝ)*n)^2=(j:ℝ)/(n:ℝ)^2 by field_simp <;> ring]
  rw [div_div,mul_comm (n:ℝ) (r:ℝ)]

/-- Exact square dilation for any count vanishing at the empty horizon.
The original finite cutoffs at both conductors are included. -/
theorem splineCountReading_square_dilation {n r : ℕ} (hn : 0<n) (hr : 0<r)
    (f : ℕ → ℝ) (hf : f 0=0) :
    splineCountReading (r*n) (fun k => f (k/r^2))=splineCountReading n f/r := by
  let M := max (splineHorizon (r*n)) (splineHorizon n)+1
  have hd : 0<r^2 := pow_pos hr 2
  have hT : splineHorizon (r*n)<r^2*M :=
    (Nat.lt_succ_of_le (le_max_left ..)).trans_le (Nat.le_mul_of_pos_left M hd)
  have hM : splineHorizon n<M := Nat.lt_succ_of_le (le_max_right ..)
  rw [reading_padded (Nat.mul_pos hr hn) hT (fun k => f (k/r^2)) (by simpa only [Nat.zero_div] using hf),
    quotient_blocks hd,reading_padded hn hM f hf,sum_div]
  apply sum_congr rfl
  intro j _
  rw [sampledSpline_square_dilation hn hr,sampledSpline_square_dilation hn hr]
  ring

#print axioms splineCountReading_square_dilation
end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
