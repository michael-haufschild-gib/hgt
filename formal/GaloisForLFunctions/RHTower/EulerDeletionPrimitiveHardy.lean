import GaloisForLFunctions.RHTower.GaussSpikeMass
import GaloisForLFunctions.HTGeometry.PowerSeriesTailBound
import GaloisForLFunctions.HTGeometry.RectangularSchurBound

/-!
# Critical discrete Hardy transfer for deletion primitives

The triangular tail kernel has a weighted Schur bound at the exact critical
square-energy weight. Both finite cutoffs and the genuine infinite tail are
controlled without discarding any part of the input energy.
-/
noncomputable section
open Filter Topology
open scoped BigOperators
namespace RHTower.DeletionPrimitiveHardy

/-- Critical triangular kernel acting on normalized arithmetic primitives. -/
def tailKernel (sigma : ℝ) (k n : ℕ) : ℝ :=
  if k ≤ n then ((k : ℝ)+1)^(sigma-1)*((n : ℝ)+1)^(-sigma) else 0

/-- Explicit Schur constant; the only singularity is the critical exponent. -/
def schurConstant (sigma : ℝ) : ℝ := 1+1/(sigma-1/2)

private theorem rectangular_schur (I J : Finset ℕ) (T : ℕ → ℕ → ℝ)
    (w b : ℕ → ℝ) {C : ℝ} (hC : 0 ≤ C) (hw : ∀ n, 0 < w n)
    (hT : ∀ k n, 0 ≤ T k n)
    (hrow : ∀ k ∈ I, ∑ n ∈ J, T k n*w n ≤ C*w k)
    (hcol : ∀ n ∈ J, ∑ k ∈ I, T k n*w k ≤ C*w n) :
    (∑ k ∈ I, (∑ n ∈ J, T k n*b n)^2)  ≤  C^2*∑ n ∈ J, b n^2 := by
  exact GaloisForLFunctions.weighted_rectangular_sum_sq_le I J T w w b hC hw hT hrow hcol

private theorem power_head {delta : ℝ} (hd : 0 < delta) (hd' : delta < 1) (n : ℕ) :
    (∑ k ∈ Finset.range (n+1), ((k : ℝ)+1)^(delta-1))  ≤
      (1+1/delta)*((n : ℝ)+1)^delta := by
  have h := sum_rpow_neg_head_le (c := 1-delta) (by linarith) (by linarith) (n+1)
  have heq : (∑ k ∈ Finset.range (n+1), ((k : ℝ)+1)^(delta-1)) =
      ∑ k ∈ Finset.Icc 1 (n+1), (k : ℝ)^(-(1-delta)) := by
    rw [show Finset.Icc 1 (n+1)=Finset.Ico 1 (n+2) by ext k; simp; omega,
      Finset.sum_Ico_eq_sum_range]
    simp only [Nat.cast_add, Nat.cast_one]
    apply Finset.sum_congr rfl
    intro k hk
    congr 1 <;> ring
  have hp : 1 ≤ ((n : ℝ)+1)^delta := Real.one_le_rpow
    (by have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith) hd.le
  rw [heq]
  have he : 1-(1-delta)=delta := by ring
  rw [he] at h
  push_cast at h
  calc _ ≤ 1+((n : ℝ)+1)^delta/delta := h
       _ ≤ ((n : ℝ)+1)^delta+((n : ℝ)+1)^delta/delta := add_le_add hp le_rfl
       _ = _ := by ring

private theorem power_tail {delta : ℝ} (hd : 0 < delta) (k M : ℕ) :
    (∑ n ∈ (Finset.range M).filter (fun n => k ≤ n), ((n : ℝ)+1)^(-delta-1))  ≤
      (1+1/delta)*((k : ℝ)+1)^(-delta) := by
  have hsub : (Finset.range M).filter (fun n => k ≤ n) ⊆
      (Finset.range (M+1)).image (fun j => k+j) := by
    intro n hn
    simp only [Finset.mem_filter, Finset.mem_range] at hn
    exact Finset.mem_image.mpr ⟨n-k,Finset.mem_range.mpr (by omega),by omega⟩
  have hle := Finset.sum_le_sum_of_subset_of_nonneg
    (f := fun n : ℕ => ((n : ℝ)+1)^(-delta-1)) hsub (fun n _ _ => by positivity)
  rw [Finset.sum_image (by intro a ha b hb h; exact Nat.add_left_cancel h), Finset.sum_range_succ'] at hle
  have ht := GaloisForLFunctions.sum_shift_rpow_tail_le
    (s := delta+1) (by linarith) k M
  have heq : (∑ j ∈ Finset.range M, (((k+(j+1) : ℕ) : ℝ)+1)^(-delta-1)) =
      ∑ j ∈ Finset.range M, (((k : ℝ)+1+j)+1)^(-(delta+1)) := by
    apply Finset.sum_congr rfl
    intro j hj
    push_cast
    congr 1 <;> ring
  rw [heq] at hle
  have hp : ((k : ℝ)+1)^(-delta-1) ≤ ((k : ℝ)+1)^(-delta) :=
    Real.rpow_le_rpow_of_exponent_le
      (by have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k; linarith) (by linarith)
  have he1 : 1-(delta+1)= -delta := by ring
  have he2 : delta+1-1=delta := by ring
  rw [he1,he2] at ht
  simp only [Nat.add_zero] at hle
  calc _ ≤ (∑ j ∈ Finset.range M, (((k : ℝ)+1+j)+1)^(-(delta+1))) +
          ((k : ℝ)+1)^(-delta-1) := hle
       _ ≤ ((k : ℝ)+1)^(-delta)/delta+((k : ℝ)+1)^(-delta) := add_le_add ht hp
       _ = _ := by ring

private theorem kernel_nonneg (sigma : ℝ) (k n : ℕ) : 0 ≤ tailKernel sigma k n := by
  unfold tailKernel
  split_ifs <;> positivity

private theorem row_bound {sigma : ℝ} (hs : 1/2 < sigma) (k M : ℕ) :
    (∑ n ∈ Finset.range M, tailKernel sigma k n*((n : ℝ)+1)^(-(1/2 : ℝ)))  ≤
      schurConstant sigma*((k : ℝ)+1)^(-(1/2 : ℝ)) := by
  have heq : (∑ n ∈ Finset.range M, tailKernel sigma k n*((n : ℝ)+1)^(-(1/2 : ℝ))) =
      ((k : ℝ)+1)^(sigma-1)*
        ∑ n ∈ (Finset.range M).filter (fun n => k ≤ n), ((n : ℝ)+1)^(-(sigma-1/2)-1) := by
    rw [Finset.mul_sum, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro n hn
    by_cases hkn : k ≤ n
    · simp only [tailKernel,hkn,if_true,mul_assoc,← Real.rpow_add (show (0 : ℝ) < n+1 by positivity)]
      congr 2
      ring
    · simp [tailKernel,hkn]
  rw [heq]
  have h := mul_le_mul_of_nonneg_left (power_tail (by linarith : 0 < sigma-1/2) k M)
    (Real.rpow_nonneg (show (0 : ℝ) ≤ (k : ℝ)+1 by positivity) (sigma-1))
  calc _ ≤ ((k : ℝ)+1)^(sigma-1)*
           ((1+1/(sigma-1/2))*((k : ℝ)+1)^(-(sigma-1/2))) := h
       _ = _ := by
         rw [mul_left_comm,← Real.rpow_add (show (0 : ℝ) < (k : ℝ)+1 by positivity)]
         have he : sigma-1 + (-(sigma-1/2)) = -(1/2 : ℝ) := by ring
         rw [he]
         rfl

private theorem column_bound {sigma : ℝ} (hs : 1/2 < sigma) (hs' : sigma < 1) (n L : ℕ) :
    (∑ k ∈ Finset.range L, tailKernel sigma k n*((k : ℝ)+1)^(-(1/2 : ℝ)))  ≤
      schurConstant sigma*((n : ℝ)+1)^(-(1/2 : ℝ)) := by
  have heq : (∑ k ∈ Finset.range L, tailKernel sigma k n*((k : ℝ)+1)^(-(1/2 : ℝ))) =
      ((n : ℝ)+1)^(-sigma)*
        ∑ k ∈ (Finset.range L).filter (fun k => k ≤ n), ((k : ℝ)+1)^((sigma-1/2)-1) := by
    rw [Finset.mul_sum, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro k hk
    by_cases hkn : k ≤ n
    · simp only [tailKernel,hkn,if_true]
      rw [mul_right_comm,← Real.rpow_add (show (0 : ℝ) < k+1 by positivity)]
      rw [mul_comm]
      congr 1
      congr 1
      ring
    · simp [tailKernel,hkn]
  have hsub : (Finset.range L).filter (fun k => k ≤ n) ⊆ Finset.range (n+1) := by
    intro k hk
    simp only [Finset.mem_filter, Finset.mem_range] at *
    omega
  have hhead := (Finset.sum_le_sum_of_subset_of_nonneg
    (f := fun k : ℕ => ((k : ℝ)+1)^((sigma-1/2)-1)) hsub (fun k _ _ => by positivity)).trans
      (power_head (by linarith : 0 < sigma-1/2) (by linarith) n)
  rw [heq]
  have h := mul_le_mul_of_nonneg_left hhead (Real.rpow_nonneg (show (0 : ℝ) ≤ (n : ℝ)+1 by positivity) (-sigma))
  calc _ ≤ ((n : ℝ)+1)^(-sigma)*
           ((1+1/(sigma-1/2))*((n : ℝ)+1)^(sigma-1/2)) := h
       _ = _ := by
         rw [mul_left_comm,← Real.rpow_add (show (0 : ℝ) < (n : ℝ)+1 by positivity)]
         have he : -sigma + (sigma-1/2) = -(1/2 : ℝ) := by ring
         rw [he]
         rfl

/-- Every finite triangular section has one critical square-energy bound, independent of both cutoffs. -/
theorem finite_tail_energy_le {sigma : ℝ} (hs : 1/2 < sigma) (hs' : sigma < 1)
    (b : ℕ → ℝ) (L M : ℕ) :
    (∑ k ∈ Finset.range L, (∑ n ∈ Finset.range M, tailKernel sigma k n*b n)^2)  ≤
      schurConstant sigma^2*∑ n ∈ Finset.range M, b n^2 := by
  apply rectangular_schur (Finset.range L) (Finset.range M) (tailKernel sigma)
    (fun n : ℕ => ((n : ℝ)+1)^(-(1/2 : ℝ))) b
  · unfold schurConstant
    have : 0 < sigma-1/2 := by linarith
    positivity
  · intro n
    positivity
  · exact kernel_nonneg sigma
  · intro k hk
    exact row_bound hs k M
  · intro n hn
    exact column_bound hs hs' n L

/-- The actual positive triangular tail, not a finite-section surrogate. -/
def tailTransform (sigma : ℝ) (b : ℕ → ℝ) (k : ℕ) : ℝ :=
  ∑' n : ℕ, tailKernel sigma k n*b n

/-- Square-summable nonnegative input gives ordinary summability of every complete tail row. -/
theorem summable_tail_row {sigma : ℝ} (hs : 1/2 < sigma) (hs' : sigma < 1)
    {b : ℕ → ℝ} (hb : ∀ n, 0 ≤ b n) (hbs : Summable (fun n => b n^2)) (k : ℕ) :
    Summable (fun n => tailKernel sigma k n*b n) := by
  have hC : 0 ≤ schurConstant sigma^2 := sq_nonneg _
  apply summable_of_sum_range_le (fun n => mul_nonneg (kernel_nonneg _ _ _) (hb n))
    (c := 1+schurConstant sigma^2*(∑' n, b n^2))
  intro M
  have hpoint : (∑ n ∈ Finset.range M, tailKernel sigma k n*b n)^2  ≤
      ∑ j ∈ Finset.range (k+1), (∑ n ∈ Finset.range M, tailKernel sigma j n*b n)^2 :=
    Finset.single_le_sum (fun j _ => sq_nonneg (∑ n ∈ Finset.range M, tailKernel sigma j n*b n))
      (Finset.mem_range.mpr (Nat.lt_succ_self k))
  have h := hpoint.trans ((finite_tail_energy_le hs hs' b (k+1) M).trans
    (mul_le_mul_of_nonneg_left (hbs.sum_le_tsum (Finset.range M) (fun n _ => sq_nonneg _)) hC))
  nlinarith [sq_nonneg ((∑ n ∈ Finset.range M, tailKernel sigma k n*b n)-1)]

/-- Full critical Hardy estimate with genuine tail summability and all output energy retained. -/
theorem tail_energy_summable_le {sigma : ℝ} (hs : 1/2 < sigma) (hs' : sigma < 1)
    {b : ℕ → ℝ} (hb : ∀ n, 0 ≤ b n) (hbs : Summable (fun n => b n^2)) :
    Summable (fun k => tailTransform sigma b k^2) ∧
      (∑' k, tailTransform sigma b k^2) ≤ schurConstant sigma^2*(∑' n, b n^2) := by
  have hfinite (L : ℕ) : (∑ k ∈ Finset.range L, tailTransform sigma b k^2)  ≤
      schurConstant sigma^2*(∑' n, b n^2) := by
    have ht := tendsto_finsetSum (Finset.range L) (fun k _ =>
      ((summable_tail_row hs hs' hb hbs k).hasSum.tendsto_sum_nat).pow 2)
    apply le_of_tendsto ht
    exact Filter.Eventually.of_forall (fun M => (finite_tail_energy_le hs hs' b L M).trans
      (mul_le_mul_of_nonneg_left (hbs.sum_le_tsum (Finset.range M) (fun n _ => sq_nonneg _))
        (sq_nonneg _)))
  have hsummable := summable_of_sum_range_le (fun k => sq_nonneg (tailTransform sigma b k)) hfinite
  exact ⟨hsummable,hsummable.tsum_le_of_sum_range_le hfinite⟩

end RHTower.DeletionPrimitiveHardy
end
