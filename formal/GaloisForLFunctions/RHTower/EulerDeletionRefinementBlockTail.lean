import GaloisForLFunctions.RHTower.EulerDeletionRefinementBlockDifference

noncomputable section

open Finset

namespace RHTower.DeletionResidueMartingale

/-- The complete parent refinement aggregate is exactly its canonical finite
Euler-deletion kernel. -/
theorem canonicalRefinementAggregateKernel_eq_canonical_finite_kernel
    (N l r : ℕ) (hlN : l < N) (x : ℝ) :
    canonicalRefinementAggregateKernel N l r x =
      (1 - x) * x ^ r *
        (∑ s ∈ range (canonicalClockRatio N l),
          (x ^ (s * clock l) * pairedMoebiusSource N (r + s * clock l)) *
            (1 - x ^ (canonicalClockRatio N l * clock l))⁻¹) := by
  unfold canonicalRefinementAggregateKernel
  rw [canonicalClockRatio_eq_refinement_mul l N hlN]
  have hclock : (clock (l + 1) / clock l) * clock l = clock (l + 1) :=
    Nat.div_mul_cancel (clock_dvd (Nat.le_succ l))
  rw [Nat.mul_assoc, hclock]
  congr 1
  rw [← Fin.sum_univ_eq_sum_range]
  symm
  calc
    (∑ s : Fin (canonicalClockRatio N (l + 1) * (clock (l + 1) / clock l)),
        (x ^ (s * clock l) * pairedMoebiusSource N (r + s * clock l)) *
          (1 - x ^ (canonicalClockRatio N (l + 1) * clock (l + 1)))⁻¹) =
        ∑ qs : Fin (canonicalClockRatio N (l + 1)) × Fin (clock (l + 1) / clock l),
          (x ^ ((qs.2 + (clock (l + 1) / clock l) * qs.1) * clock l) *
            pairedMoebiusSource N
              (r + (qs.2 + (clock (l + 1) / clock l) * qs.1) * clock l)) *
            (1 - x ^ (canonicalClockRatio N (l + 1) * clock (l + 1)))⁻¹ := by
      simpa using
        (sum_fin_block_decomposition (clock (l + 1) / clock l)
          (canonicalClockRatio N (l + 1))
          (fun s : ℕ =>
            (x ^ (s * clock l) * pairedMoebiusSource N (r + s * clock l)) *
              (1 - x ^ (canonicalClockRatio N (l + 1) * clock (l + 1)))⁻¹))
    _ = _ := by rw [Fintype.sum_prod_type]

/-- Scaling the literal parent refinement aggregate gives the exact signed
unprocessed Euler-deletion tail from level `l` onward. -/
theorem scaled_canonicalRefinementAggregateKernel_eq_unprocessed_tail
    (N l r : ℕ) (hlN : l < N) (x : ℝ) :
    (∑ a ∈ range (clock l), x ^ a) * canonicalRefinementAggregateKernel N l r x =
      x ^ r *
        (((1 - x ^ clock N) * pairedMoebiusSource N r +
          x ^ clock l * ∑ s ∈ range (canonicalClockRatio N l), x ^ (s * clock l) *
            (∑ i ∈ range N, if l ≤ i then
              ((ArithmeticFunction.moebius (i + 1) : ℤ) : ℝ) *
                (residue (i + 1) (r + (s + 1) * clock l) -
                  residue (i + 1) (r + s * clock l)) else 0)) *
          (1 - x ^ clock N)⁻¹) := by
  rw [canonicalRefinementAggregateKernel_eq_canonical_finite_kernel N l r hlN x]
  have hlN' : l ≤ N := Nat.le_of_lt hlN
  have hK : canonicalClockRatio N l * clock l = clock N := by
    rw [canonicalClockRatio_eq_div_of_le N l hlN']
    exact Nat.div_mul_cancel (clock_dvd hlN')
  have hkernel :
      (1 - x) * x ^ r *
          (∑ s ∈ range (canonicalClockRatio N l),
            (x ^ (s * clock l) * pairedMoebiusSource N (r + s * clock l)) *
              (1 - x ^ clock N)⁻¹) =
        ((1 - x) * x ^ r *
          ∑ s ∈ range (canonicalClockRatio N l),
            x ^ (s * clock l) * pairedMoebiusSource N (r + s * clock l)) *
          (1 - x ^ clock N)⁻¹ := by
    rw [← Finset.sum_mul]
    ring
  rw [hK, hkernel]
  simpa only [hK] using
    pairedMoebiusSource_scaled_finite_joint_kernel_eq_unprocessed_tail N l r
      (canonicalClockRatio N l) x hK

end RHTower.DeletionResidueMartingale
