import GaloisForLFunctions.RHTower.Sieve.KloostermanPhysicalResidueModulusBilinear

/-!
# Signed Kloosterman modulus kernel on ordinary integer indices

The modulus sum is isolated as a kernel on ordinary integer coefficient indices.  The shared
physical-residue carrier is exactly the resulting finite bilinear form.  Any genuine spectral
saving must improve this signed kernel or its operator norm before absolute values are taken.
-/

open scoped BigOperators ComplexConjugate
open Complex Finset

namespace RHTower.Sieve

noncomputable section

/-- Signed complete Kloosterman kernel across a finite modulus family, evaluated on ordinary
integer indices. -/
def kloostermanIntegerModulusKernel
    (Q : Finset ℕ) (w : ℕ → ℂ) (m n : ℤ) : ℂ :=
  ∑ q ∈ Q, w q * kloostermanSum (q + 1) (Int.cast m) (Int.cast n)

/-- Symmetry in the two ordinary integer frequencies. -/
theorem kloostermanIntegerModulusKernel_comm
    (Q : Finset ℕ) (w : ℕ → ℂ) (m n : ℤ) :
    kloostermanIntegerModulusKernel Q w m n =
      kloostermanIntegerModulusKernel Q w n m := by
  unfold kloostermanIntegerModulusKernel
  apply Finset.sum_congr rfl
  intro q _hq
  rw [kloostermanSum_comm]

/-- Conjugation negates both integer frequencies and conjugates the modulus weights. -/
theorem star_kloostermanIntegerModulusKernel
    (Q : Finset ℕ) (w : ℕ → ℂ) (m n : ℤ) :
    star (kloostermanIntegerModulusKernel Q w m n) =
      kloostermanIntegerModulusKernel Q (fun q => star (w q)) (-m) (-n) := by
  unfold kloostermanIntegerModulusKernel
  change (starRingEnd ℂ)
    (∑ q ∈ Q, w q * kloostermanSum (q + 1) (Int.cast m) (Int.cast n)) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro q _hq
  rw [map_mul]
  change star (w q) * star (kloostermanSum (q + 1) (Int.cast m) (Int.cast n)) = _
  rw [star_kloostermanSum]
  simp

/-- Elementary triangle/totient baseline.  A spectral estimate must improve this signed modulus
sum by retaining cancellation on the left. -/
theorem norm_kloostermanIntegerModulusKernel_le_totient
    (Q : Finset ℕ) (w : ℕ → ℂ) (m n : ℤ) :
    ‖kloostermanIntegerModulusKernel Q w m n‖ ≤
      ∑ q ∈ Q, ‖w q‖ * (Nat.totient (q + 1) : ℝ) := by
  unfold kloostermanIntegerModulusKernel
  calc
    ‖∑ q ∈ Q, w q * kloostermanSum (q + 1) (Int.cast m) (Int.cast n)‖ ≤
        ∑ q ∈ Q, ‖w q * kloostermanSum (q + 1) (Int.cast m) (Int.cast n)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ q ∈ Q, ‖w q‖ * (Nat.totient (q + 1) : ℝ) := by
      apply Finset.sum_le_sum
      intro q _hq
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left
        (norm_kloostermanSum_le_totient (q + 1) (Int.cast m) (Int.cast n))
        (norm_nonneg _)

/-- The shared physical-residue modulus carrier is the finite ordinary-index bilinear form of the
signed integer Kloosterman kernel. -/
theorem kloostermanPhysicalResidueModulusBilinear_eq_integerKernel
    (Q : Finset ℕ) (w : ℕ → ℂ) (N M : ℕ)
    (a b : ℕ → ℂ) (t : ℝ) :
    kloostermanPhysicalResidueModulusBilinear Q w N M a b t =
      ∑ m ∈ Finset.Icc 1 N, physicalDirichletTerm a m t *
        ∑ n ∈ Finset.Icc 1 M, physicalDirichletTerm b n t *
          kloostermanIntegerModulusKernel Q w (m : ℤ) (n : ℤ) := by
  rw [kloostermanPhysicalResidueModulusBilinear_eq]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro m _hm
  rw [← Finset.mul_sum]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n _hn
  unfold kloostermanIntegerModulusKernel
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q _hq
  have hmcast : (Int.cast (m : ℤ) : ZMod (q + 1)) = Nat.cast m := by norm_cast
  have hncast : (Int.cast (n : ℤ) : ZMod (q + 1)) = Nat.cast n := by norm_cast
  rw [hmcast, hncast]
  ring

end

end RHTower.Sieve
