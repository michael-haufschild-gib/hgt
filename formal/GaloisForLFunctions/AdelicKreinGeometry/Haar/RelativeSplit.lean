import GaloisForLFunctions.AdelicKreinGeometry.Haar.PositiveSlopeSplit
import GaloisForLFunctions.AdelicKreinGeometry.Haar.PolynomialCorrection

/-!
# Canonical splitting modulo zero-axis polynomial kernels

The polynomial period correction and the positive moving form give a unique positive Haar, slope, and finite-rank polynomial decomposition.
-/

open Module
open GaloisForLFunctions.ArithmeticPositiveDuality
open GaloisForLFunctions.BiarithmeticGeometry
open GaloisForLFunctions.HeckeKreinToeplitz
noncomputable section
namespace GaloisForLFunctions.AdelicKreinGeometry

/-- A positive Haar carrier is invariant under right integer translation. -/
theorem positive_haar_right_integer_invariant {p : AffineGroupQ → ℂ}
    (hp : IsPosDefKernel p) (hs : HasIntegerSuccessor p) (g : AffineGroupQ) :
    p (g * translation 1) = p g := by
  have h1 : p (translation 1) = p 1 := by
    simpa only [Int.cast_one] using hasIntegerSuccessor_int hs (1 : ℤ)
  exact (isPosDefKernel_iff_isPosDefOnGroup.mp hp).mul_right_eq h1 g

/-- In a positive-plus-slope decomposition, the finite correction carries exactly the period defect. -/
theorem haar_split_correction_difference {k p q : AffineGroupQ → ℂ} {ψ : ℚˣ → ℂ}
    (hp : IsPosDefKernel p) (hs : HasIntegerSuccessor p)
    (he : ∀ g, k g = p g + ψ (slopeUnit g) + q g) (g : AffineGroupQ) :
    q (g * translation 1) - q g = k (g * translation 1) - k g := by
  have h1 : slopeUnit (translation 1) = 1 := Units.ext (affSlope_translation 1)
  have hnext := he (g * translation 1)
  rw [positive_haar_right_integer_invariant hp hs, map_mul, h1, mul_one] at hnext
  linear_combination -hnext + he g

/-- Finite column rank and zero dilation values make the polynomial correction canonical. -/
theorem haar_split_correction_unique {k p p' q q' : AffineGroupQ → ℂ} {ψ ψ' : ℚˣ → ℂ}
    [Module.Finite ℂ (kernelColumnSpan q)] [Module.Finite ℂ (kernelColumnSpan q')]
    (hp : IsPosDefKernel p) (hp' : IsPosDefKernel p')
    (hs : HasIntegerSuccessor p) (hs' : HasIntegerSuccessor p')
    (hd : ∀ u : ℚˣ, q (dilation u) = 0) (hd' : ∀ u : ℚˣ, q' (dilation u) = 0)
    (he : ∀ g, k g = p g + ψ (slopeUnit g) + q g)
    (he' : ∀ g, k g = p' g + ψ' (slopeUnit g) + q' g) : q = q' := by
  apply polynomial_period_correction_unique
    (hasPolynomialTranslationFibres_of_finite_columns q)
    (hasPolynomialTranslationFibres_of_finite_columns q') hd hd'
  intro g
  exact (haar_split_correction_difference hp hs he g).trans
    (haar_split_correction_difference hp' hs' he' g).symm

/-- Every finite-index Haar kernel has a unique positive, slope, and zero-axis polynomial split. -/
theorem exists_unique_haar_relative_split {k : AffineGroupQ → ℂ}
    (hk : IsHermKernel k) {r : ℕ} (hi : negIndex k ≤ r) (hs : HasIntegerSuccessor k) :
    ∃ p : AffineGroupQ → ℂ, ∃ ψ : ℚˣ → ℂ, ∃ q : AffineGroupQ → ℂ,
      IsPosDefKernel p ∧ HasIntegerSuccessor p ∧ IsHermKernel ψ ∧
      Module.Finite ℂ (kernelColumnSpan q) ∧ HasPolynomialTranslationFibres q ∧ IsHermKernel q ∧
      (∀ b : ℚ, q (translation b) = 0) ∧ (∀ u : ℚˣ, q (dilation u) = 0) ∧
      (∀ g, k g = p g + ψ (slopeUnit g) + q g) ∧
      negIndex ψ = negIndex (fun g => k g - q g) ∧
      negIndex ψ ≤ (r : ℕ∞) + finrank ℂ (kernelColumnSpan q) ∧
      ∀ (p' : AffineGroupQ → ℂ) (ψ' : ℚˣ → ℂ) (q' : AffineGroupQ → ℂ),
        IsPosDefKernel p' → HasIntegerSuccessor p' → IsHermKernel ψ' →
        Module.Finite ℂ (kernelColumnSpan q') → (∀ u : ℚˣ, q' (dilation u) = 0) →
        (∀ g, k g = p' g + ψ' (slopeUnit g) + q' g) → p' = p ∧ ψ' = ψ ∧ q' = q := by
  obtain ⟨q, hfinite, hqpoly, hqHerm, hqt, hqd, hrem, hindex, hperiod, _⟩ :=
    exists_zero_axis_polynomial_correction hk hi (hasIntegerSuccessor_translation_periodic hs)
  letI := hfinite
  have hsrem : HasIntegerSuccessor (fun g => k g - q g) := by
    intro b
    change k (translation b) - q (translation b) = _
    rw [hqt, sub_zero]
    exact hs b
  have hib : negIndex (fun g => k g - q g) ≤ ((r + finrank ℂ (kernelColumnSpan q) : ℕ) : ℕ∞) := by
    simpa only [Nat.cast_add] using hindex
  obtain ⟨p, ψ, hp, hps, hψ, he, hiψ, _⟩ :=
    exists_unique_positive_haar_slope_split hrem hib hsrem hperiod
  have hsplit (g : AffineGroupQ) : k g = p g + ψ (slopeUnit g) + q g := by
    linear_combination he g
  refine ⟨p, ψ, q, hp, hps, hψ, hfinite, hqpoly, hqHerm, hqt, hqd, hsplit, hiψ,
    hiψ.le.trans hindex, ?_⟩
  intro p' ψ' q' hp' hs' hψ' hfinite' hd' he'
  letI := hfinite'
  have hqeq : q' = q := haar_split_correction_unique hp' hp hs' hps hd' hqd he' hsplit
  have hpair : p' = p ∧ ψ' = ψ := by
    apply positive_haar_slope_split_unique hp' hp hs' hps hψ' hψ
    intro g
    have h := (he' g).symm.trans (hsplit g)
    rw [hqeq] at h
    exact add_right_cancel h
  exact ⟨hpair.1, hpair.2, hqeq⟩

#print axioms haar_split_correction_unique
#print axioms exists_unique_haar_relative_split
end GaloisForLFunctions.AdelicKreinGeometry
