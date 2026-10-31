import GaloisForLFunctions.AdelicKreinGeometry.Haar.RelativeSplit
import GaloisForLFunctions.HeckeKreinToeplitz.Index.FiniteRankStability
import GaloisForLFunctions.AdelicKreinGeometry.Haar.PolynomialIndexPreservation

/-!
# Classification of finite-index Haar kernels

A positive Haar part and a finite-rank zero-axis correction leave precisely the finite-index
condition on the slope part. Polynomial quadrature removes the positive part without changing index;
normalization at identity gives the converse to the canonical split.
-/

open Module
open GaloisForLFunctions.ArithmeticPositiveDuality
open GaloisForLFunctions.BiarithmeticGeometry
open GaloisForLFunctions.HeckeKreinToeplitz
noncomputable section
namespace GaloisForLFunctions.AdelicKreinGeometry

/-- The slope index differs from the full index by at most the correction's column dimension. -/
theorem haar_relative_split_index_bounds {k p q : AffineGroupQ → ℂ} {ψ : ℚˣ → ℂ}
    [Module.Finite ℂ (kernelColumnSpan q)] (hp : IsPosDefKernel p)
    (hs : HasIntegerSuccessor p) (hψ : IsHermKernel ψ)
    (he : ∀ g, k g = p g + ψ (slopeUnit g) + q g) :
    negIndex k ≤ negIndex ψ + finrank ℂ (kernelColumnSpan q) ∧
      negIndex ψ ≤ negIndex k + finrank ℂ (kernelColumnSpan q) := by
  have he' : (fun g => k g - q g) = (fun g => p g + ψ (slopeUnit g)) := by
    funext g
    rw [he, add_sub_cancel_right]
  have hi : negIndex (fun g => k g - q g) = negIndex ψ := by
    rw [he']
    exact negIndex_add_slope_of_integer_successor hp hs ψ hψ
  constructor
  · simpa only [hi] using negIndex_le_sub_add_finrank k q
  · simpa only [hi] using negIndex_sub_le_add_finrank k q

/-- The positive Haar part contributes no negative index to a polynomial relative split. -/
theorem haar_relative_split_index_eq_polynomial_residual
    {k p q : AffineGroupQ → ℂ} {ψ : ℚˣ → ℂ}
    (hp : IsPosDefKernel p) (hs : HasIntegerSuccessor p) (hψ : IsHermKernel ψ)
    (hq : IsHermKernel q) (hpoly : HasPolynomialTranslationFibres q)
    (he : ∀ g, k g = p g + ψ (slopeUnit g) + q g) :
    negIndex k = negIndex (fun g => ψ (slopeUnit g) + q g) := by
  have he' : k = (fun g => p g + ψ (slopeUnit g) + q g) := funext he
  rw [he']
  exact negIndex_positive_haar_slope_polynomial_eq hp hs hψ hq hpoly

/-- Zero-axis polynomial corrections cannot reduce the slope's negative index. -/
theorem haar_relative_split_slope_index_le
    {k p q : AffineGroupQ → ℂ} {ψ : ℚˣ → ℂ}
    (hp : IsPosDefKernel p) (hs : HasIntegerSuccessor p) (hψ : IsHermKernel ψ)
    (hq : IsHermKernel q) (hpoly : HasPolynomialTranslationFibres q)
    (hd : ∀ u : ℚˣ, q (dilation u) = 0)
    (he : ∀ g, k g = p g + ψ (slopeUnit g) + q g) : negIndex ψ ≤ negIndex k := by
  have he' : k = (fun g => p g + ψ (slopeUnit g) + q g) := funext he
  rw [he']
  exact negIndex_slope_le_positive_haar_polynomial hp hs hψ hq hpoly hd

/-- Finite index of a relative Haar split is equivalent to finite index of its slope part. -/
theorem haar_relative_split_finite_index_iff {k p q : AffineGroupQ → ℂ} {ψ : ℚˣ → ℂ}
    [Module.Finite ℂ (kernelColumnSpan q)] (hp : IsPosDefKernel p)
    (hs : HasIntegerSuccessor p) (hψ : IsHermKernel ψ)
    (he : ∀ g, k g = p g + ψ (slopeUnit g) + q g) :
    negIndex k < ⊤ ↔ negIndex ψ < ⊤ := by
  have hb := haar_relative_split_index_bounds hp hs hψ he
  constructor
  · intro h
    exact lt_of_le_of_lt hb.2
      (by simpa only [ENat.add_lt_top, ENat.coe_lt_top, and_true] using h)
  · intro h
    exact lt_of_le_of_lt hb.1
      (by simpa only [ENat.add_lt_top, ENat.coe_lt_top, and_true] using h)

/-- Finite-index Haar kernels are exactly normalized positive, slope, and polynomial sums. -/
theorem finite_index_haar_iff_relative_split (k : AffineGroupQ → ℂ) :
    (IsHermKernel k ∧ HasIntegerSuccessor k ∧ negIndex k < ⊤) ↔
      ∃ p : AffineGroupQ → ℂ, ∃ ψ : ℚˣ → ℂ, ∃ q : AffineGroupQ → ℂ,
        IsPosDefKernel p ∧ HasIntegerSuccessor p ∧ IsHermKernel ψ ∧ ψ 1 = 0 ∧
        negIndex ψ < ⊤ ∧ Module.Finite ℂ (kernelColumnSpan q) ∧
        HasPolynomialTranslationFibres q ∧ IsHermKernel q ∧
        (∀ b : ℚ, q (translation b) = 0) ∧ (∀ u : ℚˣ, q (dilation u) = 0) ∧
        (∀ g, k g = p g + ψ (slopeUnit g) + q g) ∧
        negIndex k = negIndex (fun g => ψ (slopeUnit g) + q g) ∧
        negIndex ψ ≤ negIndex k := by
  constructor
  · rintro ⟨hk, hs, hfin⟩
    obtain ⟨r, hr⟩ := ENat.ne_top_iff_exists.mp (ne_of_lt hfin)
    obtain ⟨p, ψ, q, hp, hps, hψ, hfinite, hpoly, hq, hqt, hqd, he, _, _, _⟩ :=
      exists_unique_haar_relative_split hk hr.ge hs
    letI := hfinite
    have hqone : q 1 = 0 := by simpa only [map_one] using hqd 1
    have hzero : ψ 1 = 0 := by
      have h := he 1
      rw [hasIntegerSuccessor_one hs, hasIntegerSuccessor_one hps, map_one,
        hqone, add_zero] at h
      linear_combination -h
    exact ⟨p, ψ, q, hp, hps, hψ, hzero,
      (haar_relative_split_finite_index_iff hp hps hψ he).mp hfin,
      hfinite, hpoly, hq, hqt, hqd, he,
      haar_relative_split_index_eq_polynomial_residual hp hps hψ hq hpoly he,
      haar_relative_split_slope_index_le hp hps hψ hq hpoly hqd he⟩
  · rintro ⟨p, ψ, q, hp, hps, hψ, hzero, hfin, hfinite, _, hq, hqt, _, he, _, _⟩
    letI := hfinite
    have hk : IsHermKernel k := by
      intro g
      rw [he g⁻¹, he g, map_inv, hp.1 g, hψ (slopeUnit g), hq g, map_add, map_add]
    have hs : HasIntegerSuccessor k := by
      intro b
      have ht : slopeUnit (translation b) = 1 := Units.ext (affSlope_translation b)
      rw [he, hqt, add_zero, ht, hzero, add_zero]
      exact hps b
    exact ⟨hk, hs, (haar_relative_split_finite_index_iff hp hps hψ he).mpr hfin⟩

#print axioms haar_relative_split_index_bounds
#print axioms haar_relative_split_index_eq_polynomial_residual
#print axioms haar_relative_split_slope_index_le
#print axioms haar_relative_split_finite_index_iff
#print axioms finite_index_haar_iff_relative_split
end GaloisForLFunctions.AdelicKreinGeometry
