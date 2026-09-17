import GaloisForLFunctions.RHTower.EulerDeletionRefinementBlockTail

noncomputable section

open Finset

namespace RHTower.DeletionResidueMartingale

/-- The one selected child refinement block is its canonical finite
Euler-deletion kernel at the child clock. -/
theorem canonicalRefinementBlockKernel_eq_canonical_finite_kernel
    (N l u b : ℕ) (x : ℝ) :
    canonicalRefinementBlockKernel N l u b x =
      (1 - x) * x ^ (u + b * clock l) *
        ∑ a : Fin (canonicalClockRatio N (l + 1)),
          (x ^ (a * clock (l + 1)) *
            pairedMoebiusSource N (u + b * clock l + a * clock (l + 1))) *
            (1 - x ^ (canonicalClockRatio N (l + 1) * clock (l + 1)))⁻¹ := by
  unfold canonicalRefinementBlockKernel
  have hclock : (clock (l + 1) / clock l) * clock l = clock (l + 1) :=
    Nat.div_mul_cancel (clock_dvd (Nat.le_succ l))
  calc
    (1 - x) * x ^ u *
        ∑ a : Fin (canonicalClockRatio N (l + 1)),
          (x ^ ((b + (clock (l + 1) / clock l) * a) * clock l) *
            pairedMoebiusSource N
              (u + (b + (clock (l + 1) / clock l) * a) * clock l)) *
            (1 - x ^ (canonicalClockRatio N (l + 1) * clock (l + 1)))⁻¹ =
        (1 - x) * x ^ u *
          ∑ a : Fin (canonicalClockRatio N (l + 1)),
            (x ^ (b * clock l) *
              (x ^ (a * clock (l + 1)) *
                pairedMoebiusSource N (u + b * clock l + a * clock (l + 1)))) *
              (1 - x ^ (canonicalClockRatio N (l + 1) * clock (l + 1)))⁻¹ := by
      congr 1
      apply Finset.sum_congr rfl
      intro a ha
      have hpow : b * clock l + a * clock (l + 1) =
          (b + (clock (l + 1) / clock l) * a) * clock l := by
        calc
          b * clock l + a * clock (l + 1) =
              b * clock l + a * ((clock (l + 1) / clock l) * clock l) := by
                rw [hclock]
          _ = _ := by ring
      rw [← hpow, ← Nat.add_assoc, pow_add]
      ring
    _ =
        (1 - x) * x ^ (u + b * clock l) *
          ∑ a : Fin (canonicalClockRatio N (l + 1)),
            (x ^ (a * clock (l + 1)) *
              pairedMoebiusSource N (u + b * clock l + a * clock (l + 1))) *
              (1 - x ^ (canonicalClockRatio N (l + 1) * clock (l + 1)))⁻¹ := by
      calc
        (1 - x) * x ^ u *
            ∑ a : Fin (canonicalClockRatio N (l + 1)),
              (x ^ (b * clock l) *
                (x ^ (a * clock (l + 1)) *
                  pairedMoebiusSource N (u + b * clock l + a * clock (l + 1)))) *
                (1 - x ^ (canonicalClockRatio N (l + 1) * clock (l + 1)))⁻¹ =
            (1 - x) * x ^ u *
              ∑ a : Fin (canonicalClockRatio N (l + 1)), x ^ (b * clock l) *
                ((x ^ (a * clock (l + 1)) *
                  pairedMoebiusSource N (u + b * clock l + a * clock (l + 1))) *
                  (1 - x ^ (canonicalClockRatio N (l + 1) * clock (l + 1)))⁻¹) := by
          congr 1
          apply Finset.sum_congr rfl
          intro a ha
          ring
        _ = (1 - x) * x ^ u *
            (x ^ (b * clock l) *
              ∑ a : Fin (canonicalClockRatio N (l + 1)),
                (x ^ (a * clock (l + 1)) *
                  pairedMoebiusSource N (u + b * clock l + a * clock (l + 1))) *
                  (1 - x ^ (canonicalClockRatio N (l + 1) * clock (l + 1)))⁻¹) := by
          congr 1
          symm
          apply Finset.mul_sum
        _ = _ := by
          rw [pow_add]
          ring

/-- Scaling a selected child block gives the exact signed unprocessed
Euler-deletion tail beginning at the child level. -/
theorem scaled_canonicalRefinementBlockKernel_eq_unprocessed_tail
    (N l u b : ℕ) (hlN : l < N) (x : ℝ) :
    (∑ a ∈ range (clock (l + 1)), x ^ a) * canonicalRefinementBlockKernel N l u b x =
      x ^ (u + b * clock l) *
        (((1 - x ^ clock N) * pairedMoebiusSource N (u + b * clock l) +
          x ^ clock (l + 1) *
            ∑ s ∈ range (canonicalClockRatio N (l + 1)), x ^ (s * clock (l + 1)) *
              (∑ i ∈ range N, if l + 1 ≤ i then
                ((ArithmeticFunction.moebius (i + 1) : ℤ) : ℝ) *
                  (residue (i + 1) (u + b * clock l + (s + 1) * clock (l + 1)) -
                    residue (i + 1) (u + b * clock l + s * clock (l + 1))) else 0)) *
          (1 - x ^ clock N)⁻¹) := by
  rw [canonicalRefinementBlockKernel_eq_canonical_finite_kernel]
  have hsuccN : l + 1 ≤ N := Nat.succ_le_iff.mpr hlN
  have hK : canonicalClockRatio N (l + 1) * clock (l + 1) = clock N := by
    rw [canonicalClockRatio_eq_div_of_le N (l + 1) hsuccN]
    exact Nat.div_mul_cancel (clock_dvd hsuccN)
  have hkernel :
      (1 - x) * x ^ (u + b * clock l) *
          (∑ s : Fin (canonicalClockRatio N (l + 1)),
            (x ^ (s * clock (l + 1)) *
              pairedMoebiusSource N (u + b * clock l + s * clock (l + 1))) *
              (1 - x ^ clock N)⁻¹) =
        ((1 - x) * x ^ (u + b * clock l) *
          ∑ s : Fin (canonicalClockRatio N (l + 1)),
            x ^ (s * clock (l + 1)) *
              pairedMoebiusSource N (u + b * clock l + s * clock (l + 1))) *
          (1 - x ^ clock N)⁻¹ := by
    rw [← Finset.sum_mul]
    ring
  have hfin :
      (∑ s : Fin (canonicalClockRatio N (l + 1)),
        x ^ (s * clock (l + 1)) *
          pairedMoebiusSource N (u + b * clock l + s * clock (l + 1))) =
        ∑ s ∈ range (canonicalClockRatio N (l + 1)),
          x ^ (s * clock (l + 1)) *
            pairedMoebiusSource N (u + b * clock l + s * clock (l + 1)) := by
    simpa using
      (Fin.sum_univ_eq_sum_range
        (fun s : ℕ => x ^ (s * clock (l + 1)) *
          pairedMoebiusSource N (u + b * clock l + s * clock (l + 1)))
        (canonicalClockRatio N (l + 1)))
  rw [hK, hkernel, hfin]
  simpa only [hK] using
    pairedMoebiusSource_scaled_finite_joint_kernel_eq_unprocessed_tail N (l + 1)
      (u + b * clock l) (canonicalClockRatio N (l + 1)) x hK

end RHTower.DeletionResidueMartingale
