/-
# Chen--Gupta--Li class-I dyadic detector large values

Chen--Gupta--Li class-I zeros lead, after dyadic subdivision, to large values
of a Dirichlet polynomial with truncated Möbius-convolution coefficients.
This module connects the literal class-I detector block to the existing finite
character large-value matrix and exposes its exact coefficient energy.

No RH, GRH, zero-density, zero-detection, or large-value premise is used.
-/

import GaloisForLFunctions.RHTower.ChenGuptaLiClassIBlock

open Complex

noncomputable section

namespace RHTower

/-- Rows whose literal class-I dyadic detector block exceeds a nonnegative
threshold. -/
def cglClassIDyadicDetectorLargeValues (X N q R : ℕ)
    (w : Fin R → CGLCharacterDyadicRowData q) (V : NNReal) : Finset (Fin R) :=
  cglCharacterDyadicLargeValues N q R w (cglClassIDyadicDetectorCoefficients X N) V

/-- Membership in the finite class-I large-value packet is exactly the source
dyadic detector threshold. -/
theorem mem_cglClassIDyadicDetectorLargeValues_iff (X N q R : ℕ)
    (w : Fin R → CGLCharacterDyadicRowData q) (V : NNReal) (r : Fin R) :
    r ∈ cglClassIDyadicDetectorLargeValues X N q R w V ↔
      (V : ℝ) ≤ ‖cglClassIDyadicDetectorPolynomial X N q (w r)‖ := by
  simp only [cglClassIDyadicDetectorLargeValues, cglCharacterDyadicLargeValues,
    Finset.mem_filter, Finset.mem_univ, true_and]
  rw [show cglCharacterDyadicPolynomial N q (w r) (cglClassIDyadicDetectorCoefficients X N) =
    cglClassIDyadicDetectorPolynomial X N q (w r) by rfl]

/-- Closed finite class-I large-value reduction to the exact coefficient
energy of the dyadic detector block. -/
theorem card_cglClassIDyadicDetectorLargeValues_mul_sq_le (X N q R : ℕ)
    (w : Fin R → CGLCharacterDyadicRowData q) (V : NNReal) :
    ((cglClassIDyadicDetectorLargeValues X N q R w V).card : ℝ) * (V : ℝ) ^ 2 ≤
      (R : ℝ) * (N : ℝ) * ‖cglClassIDyadicDetectorCoefficients X N‖ ^ 2 := by
  exact card_cglCharacterDyadicLargeValues_mul_sq_le N q R w
    (cglClassIDyadicDetectorCoefficients X N) V

/-- Exact finite coefficient energy in the class-I dyadic detector block. -/
theorem norm_cglClassIDyadicDetectorCoefficients_sq_eq (X N : ℕ) :
    ‖cglClassIDyadicDetectorCoefficients X N‖ ^ 2 =
      ∑ j : Fin N, ‖(zeroDetectionMobiusCoefficient X (N + j.1 + 1) : ℂ)‖ ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
  simp only [cglClassIDyadicDetectorCoefficients]

/-- The exact class-I detector coefficient energy is bounded by the ordinary
divisor-square energy over its literal dyadic support. -/
theorem cglClassIDyadicDetectorCoefficient_divisorEnergy_le (X N : ℕ) :
    ∑ j : Fin N, ‖(zeroDetectionMobiusCoefficient X (N + j.1 + 1) : ℂ)‖ ^ 2 ≤
      ∑ n ∈ Finset.Icc 1 (2 * N), (n.divisors.card : ℝ) ^ 2 := by
  let f : Fin N → ℕ := fun j => N + j.1 + 1
  let S : Finset ℕ := Finset.univ.image f
  have hf : Set.InjOn f (↑(Finset.univ : Finset (Fin N))) := by
    intro j hj k hk hjk
    dsimp [f] at hjk
    omega
  have hsum : (∑ j : Fin N, ((f j).divisors.card : ℝ) ^ 2) =
      ∑ n ∈ S, (n.divisors.card : ℝ) ^ 2 := by
    symm
    exact Finset.sum_image hf
  have hsub : S ⊆ Finset.Icc 1 (2 * N) := by
    intro n hn
    rcases Finset.mem_image.mp hn with ⟨j, hj, rfl⟩
    simp only [Finset.mem_Icc]
    dsimp [f]
    omega
  calc
    ∑ j : Fin N, ‖(zeroDetectionMobiusCoefficient X (N + j.1 + 1) : ℂ)‖ ^ 2 ≤
        ∑ j : Fin N, ((N + j.1 + 1).divisors.card : ℝ) ^ 2 := by
      apply Finset.sum_le_sum
      intro j hj
      exact pow_le_pow_left₀ (norm_nonneg _)
        (norm_zeroDetectionMobiusCoefficient_le_card_divisors X _) 2
    _ = ∑ j : Fin N, ((f j).divisors.card : ℝ) ^ 2 := by rfl
    _ = ∑ n ∈ S, (n.divisors.card : ℝ) ^ 2 := hsum
    _ ≤ ∑ n ∈ Finset.Icc 1 (2 * N), (n.divisors.card : ℝ) ^ 2 := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsub
      intro n hn hns
      positivity

/-- Closed class-I large-value bound in terms of the ordinary divisor-square
energy on the source dyadic interval. -/
theorem card_cglClassIDyadicDetectorLargeValues_mul_sq_le_divisorEnergy (X N q R : ℕ)
    (w : Fin R → CGLCharacterDyadicRowData q) (V : NNReal) :
    ((cglClassIDyadicDetectorLargeValues X N q R w V).card : ℝ) * (V : ℝ) ^ 2 ≤
      (R : ℝ) * (N : ℝ) * ∑ n ∈ Finset.Icc 1 (2 * N), (n.divisors.card : ℝ) ^ 2 := by
  calc
    ((cglClassIDyadicDetectorLargeValues X N q R w V).card : ℝ) * (V : ℝ) ^ 2 ≤
        (R : ℝ) * (N : ℝ) * ‖cglClassIDyadicDetectorCoefficients X N‖ ^ 2 :=
      card_cglClassIDyadicDetectorLargeValues_mul_sq_le X N q R w V
    _ = (R : ℝ) * (N : ℝ) *
        ∑ j : Fin N, ‖(zeroDetectionMobiusCoefficient X (N + j.1 + 1) : ℂ)‖ ^ 2 := by
      rw [norm_cglClassIDyadicDetectorCoefficients_sq_eq]
    _ ≤ (R : ℝ) * (N : ℝ) *
        ∑ n ∈ Finset.Icc 1 (2 * N), (n.divisors.card : ℝ) ^ 2 := by
      gcongr
      exact cglClassIDyadicDetectorCoefficient_divisorEnergy_le X N

end RHTower
