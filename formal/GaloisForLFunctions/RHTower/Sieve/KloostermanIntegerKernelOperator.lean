import GaloisForLFunctions.RHTower.Sieve.KloostermanIntegerModulusKernel

/-!
# Finite operator carried by the signed integer Kloosterman kernel

This file separates exact Hilbert-space bookkeeping from the missing spectral estimate.  The
kernel acts on ordinary coefficient sequences over finite supports; Cauchy--Schwarz reduces every
bilinear estimate to its output square energy.  An unconditional Hilbert--Schmidt baseline is
proved without taking absolute values inside the modulus sum.
-/

open scoped BigOperators
open Complex Finset

namespace RHTower.Sieve

noncomputable section

/-- Finite transform defined by the signed modulus kernel. -/
def kloostermanIntegerKernelTransform
    (Q : Finset ℕ) (w : ℕ → ℂ) (B : Finset ℕ)
    (b : ℕ → ℂ) (m : ℕ) : ℂ :=
  ∑ n ∈ B, b n * kloostermanIntegerModulusKernel Q w (m : ℤ) (n : ℤ)

/-- Finite bilinear form of the signed modulus-kernel transform. -/
def kloostermanIntegerKernelBilinear
    (Q : Finset ℕ) (w : ℕ → ℂ) (A B : Finset ℕ)
    (a b : ℕ → ℂ) : ℂ :=
  ∑ m ∈ A, a m * kloostermanIntegerKernelTransform Q w B b m

/-- Cauchy receiver: a bilinear estimate reduces exactly to output square energy of the kernel
transform. -/
theorem norm_kloostermanIntegerKernelBilinear_sq_le
    (Q : Finset ℕ) (w : ℕ → ℂ) (A B : Finset ℕ)
    (a b : ℕ → ℂ) :
    ‖kloostermanIntegerKernelBilinear Q w A B a b‖ ^ 2 ≤
      (∑ m ∈ A, ‖a m‖ ^ 2) *
        ∑ m ∈ A, ‖kloostermanIntegerKernelTransform Q w B b m‖ ^ 2 := by
  have htri : ‖kloostermanIntegerKernelBilinear Q w A B a b‖ ≤
      ∑ m ∈ A, ‖a m‖ * ‖kloostermanIntegerKernelTransform Q w B b m‖ := by
    unfold kloostermanIntegerKernelBilinear
    refine (norm_sum_le _ _).trans ?_
    apply Finset.sum_le_sum
    intro m _hm
    rw [norm_mul]
  have hsum0 : 0 ≤ ∑ m ∈ A,
      ‖a m‖ * ‖kloostermanIntegerKernelTransform Q w B b m‖ :=
    Finset.sum_nonneg fun m _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have hsq : ‖kloostermanIntegerKernelBilinear Q w A B a b‖ ^ 2 ≤
      (∑ m ∈ A, ‖a m‖ * ‖kloostermanIntegerKernelTransform Q w B b m‖) ^ 2 := by
    nlinarith [norm_nonneg (kloostermanIntegerKernelBilinear Q w A B a b)]
  exact hsq.trans (Finset.sum_mul_sq_le_sq_mul_sq A
    (fun m => ‖a m‖) (fun m => ‖kloostermanIntegerKernelTransform Q w B b m‖))

/-- Pointwise Hilbert--Schmidt row bound for the signed kernel transform. -/
theorem norm_kloostermanIntegerKernelTransform_sq_le
    (Q : Finset ℕ) (w : ℕ → ℂ) (B : Finset ℕ)
    (b : ℕ → ℂ) (m : ℕ) :
    ‖kloostermanIntegerKernelTransform Q w B b m‖ ^ 2 ≤
      (∑ n ∈ B, ‖b n‖ ^ 2) *
        ∑ n ∈ B, ‖kloostermanIntegerModulusKernel Q w (m : ℤ) (n : ℤ)‖ ^ 2 := by
  have htri : ‖kloostermanIntegerKernelTransform Q w B b m‖ ≤
      ∑ n ∈ B, ‖b n‖ *
        ‖kloostermanIntegerModulusKernel Q w (m : ℤ) (n : ℤ)‖ := by
    unfold kloostermanIntegerKernelTransform
    refine (norm_sum_le _ _).trans ?_
    apply Finset.sum_le_sum
    intro n _hn
    rw [norm_mul]
  have hsum0 : 0 ≤ ∑ n ∈ B, ‖b n‖ *
      ‖kloostermanIntegerModulusKernel Q w (m : ℤ) (n : ℤ)‖ :=
    Finset.sum_nonneg fun n _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have hsq : ‖kloostermanIntegerKernelTransform Q w B b m‖ ^ 2 ≤
      (∑ n ∈ B, ‖b n‖ *
        ‖kloostermanIntegerModulusKernel Q w (m : ℤ) (n : ℤ)‖) ^ 2 := by
    nlinarith [norm_nonneg (kloostermanIntegerKernelTransform Q w B b m)]
  exact hsq.trans (Finset.sum_mul_sq_le_sq_mul_sq B
    (fun n => ‖b n‖)
    (fun n => ‖kloostermanIntegerModulusKernel Q w (m : ℤ) (n : ℤ)‖))

/-- Output square energy is bounded by coefficient energy times the Hilbert--Schmidt energy of the
signed kernel. -/
theorem sum_norm_kloostermanIntegerKernelTransform_sq_le
    (Q : Finset ℕ) (w : ℕ → ℂ) (A B : Finset ℕ) (b : ℕ → ℂ) :
    (∑ m ∈ A, ‖kloostermanIntegerKernelTransform Q w B b m‖ ^ 2) ≤
      (∑ n ∈ B, ‖b n‖ ^ 2) *
        ∑ m ∈ A, ∑ n ∈ B,
          ‖kloostermanIntegerModulusKernel Q w (m : ℤ) (n : ℤ)‖ ^ 2 := by
  calc
    _ ≤ ∑ m ∈ A, (∑ n ∈ B, ‖b n‖ ^ 2) *
        ∑ n ∈ B,
          ‖kloostermanIntegerModulusKernel Q w (m : ℤ) (n : ℤ)‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro m _hm
      exact norm_kloostermanIntegerKernelTransform_sq_le Q w B b m
    _ = _ := by rw [Finset.mul_sum]

/-- Complete unconditional Hilbert--Schmidt bilinear baseline. -/
theorem norm_kloostermanIntegerKernelBilinear_sq_le_hilbertSchmidt
    (Q : Finset ℕ) (w : ℕ → ℂ) (A B : Finset ℕ)
    (a b : ℕ → ℂ) :
    ‖kloostermanIntegerKernelBilinear Q w A B a b‖ ^ 2 ≤
      (∑ m ∈ A, ‖a m‖ ^ 2) * (∑ n ∈ B, ‖b n‖ ^ 2) *
        ∑ m ∈ A, ∑ n ∈ B,
          ‖kloostermanIntegerModulusKernel Q w (m : ℤ) (n : ℤ)‖ ^ 2 := by
  have hA : 0 ≤ ∑ m ∈ A, ‖a m‖ ^ 2 :=
    Finset.sum_nonneg fun m _ => sq_nonneg _
  calc
    _ ≤ (∑ m ∈ A, ‖a m‖ ^ 2) *
        ∑ m ∈ A, ‖kloostermanIntegerKernelTransform Q w B b m‖ ^ 2 :=
      norm_kloostermanIntegerKernelBilinear_sq_le Q w A B a b
    _ ≤ (∑ m ∈ A, ‖a m‖ ^ 2) *
        ((∑ n ∈ B, ‖b n‖ ^ 2) *
          ∑ m ∈ A, ∑ n ∈ B,
            ‖kloostermanIntegerModulusKernel Q w (m : ℤ) (n : ℤ)‖ ^ 2) :=
      mul_le_mul_of_nonneg_left
        (sum_norm_kloostermanIntegerKernelTransform_sq_le Q w A B b) hA
    _ = _ := by ring

/-- Hilbert--Schmidt energy under the elementary per-entry totient baseline. -/
theorem sum_norm_kloostermanIntegerModulusKernel_sq_le_totient
    (Q : Finset ℕ) (w : ℕ → ℂ) (A B : Finset ℕ) :
    (∑ m ∈ A, ∑ n ∈ B,
        ‖kloostermanIntegerModulusKernel Q w (m : ℤ) (n : ℤ)‖ ^ 2) ≤
      (A.card : ℝ) * (B.card : ℝ) *
        (∑ q ∈ Q, ‖w q‖ * (Nat.totient (q + 1) : ℝ)) ^ 2 := by
  let W : ℝ := ∑ q ∈ Q, ‖w q‖ * (Nat.totient (q + 1) : ℝ)
  have hW : 0 ≤ W := Finset.sum_nonneg fun q _ => mul_nonneg (norm_nonneg _) (by positivity)
  calc
    _ ≤ ∑ m ∈ A, ∑ n ∈ B, W ^ 2 := by
      apply Finset.sum_le_sum
      intro m _hm
      apply Finset.sum_le_sum
      intro n _hn
      have h := norm_kloostermanIntegerModulusKernel_le_totient
        Q w (m : ℤ) (n : ℤ)
      change ‖kloostermanIntegerModulusKernel Q w (m : ℤ) (n : ℤ)‖ ≤ W at h
      nlinarith [norm_nonneg (kloostermanIntegerModulusKernel Q w (m : ℤ) (n : ℤ))]
    _ = (A.card : ℝ) * (B.card : ℝ) * W ^ 2 := by simp; ring
    _ = _ := rfl

/-- Fully scalar elementary baseline for the signed kernel bilinear form.  A spectral large sieve
must replace the cardinality/totient factor while retaining the two coefficient energies. -/
theorem norm_kloostermanIntegerKernelBilinear_sq_le_totient
    (Q : Finset ℕ) (w : ℕ → ℂ) (A B : Finset ℕ)
    (a b : ℕ → ℂ) :
    ‖kloostermanIntegerKernelBilinear Q w A B a b‖ ^ 2 ≤
      (∑ m ∈ A, ‖a m‖ ^ 2) * (∑ n ∈ B, ‖b n‖ ^ 2) *
        ((A.card : ℝ) * (B.card : ℝ) *
          (∑ q ∈ Q, ‖w q‖ * (Nat.totient (q + 1) : ℝ)) ^ 2) := by
  have hAB : 0 ≤ (∑ m ∈ A, ‖a m‖ ^ 2) * (∑ n ∈ B, ‖b n‖ ^ 2) := by positivity
  exact (norm_kloostermanIntegerKernelBilinear_sq_le_hilbertSchmidt Q w A B a b).trans
    (mul_le_mul_of_nonneg_left
      (sum_norm_kloostermanIntegerModulusKernel_sq_le_totient Q w A B) hAB)

/-- The physical-height carrier is literally the kernel bilinear form on the two dyadic interval
supports. -/
theorem kloostermanPhysicalResidueModulusBilinear_eq_kernelBilinear
    (Q : Finset ℕ) (w : ℕ → ℂ) (N M : ℕ)
    (a b : ℕ → ℂ) (t : ℝ) :
    kloostermanPhysicalResidueModulusBilinear Q w N M a b t =
      kloostermanIntegerKernelBilinear Q w (Finset.Icc 1 N) (Finset.Icc 1 M)
        (fun m => physicalDirichletTerm a m t)
        (fun n => physicalDirichletTerm b n t) := by
  rw [kloostermanPhysicalResidueModulusBilinear_eq_integerKernel]
  rfl

end

end RHTower.Sieve
