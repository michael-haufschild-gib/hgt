import GaloisForLFunctions.RHTower.XiHedenmalmDeBrangesSeam
import GaloisForLFunctions.RHTower.XiWeilOneCauchyGate

/-!
# Hermitian diagonal orientation gate for the Hedenmalm Bezoutian

On the centered upper half-strip, the Hermitian specialization of the Hedenmalm--de Branges
Bezoutian is the one-Cauchy prime--archimedean source diagonal multiplied by the strictly positive
factor `‖XiC z‖²`.  Consequently nonnegativity of these scalar Bezoutian diagonals is already
equivalent to RH.  Full kernel positivity is not needed for the implication to RH, although it is
needed for a positive de Branges Hilbert-space realization.

This module proves only the exact equivalence.  It supplies no source sign theorem.
-/

open Complex Filter Topology

namespace RHTower

noncomputable section

/-- The Hermitian Xi Bezoutian diagonal is the prime--archimedean one-Cauchy diagonal times the
strictly positive Xi norm square. -/
theorem xiHedenmalmBezoutian_conj_eq_normSq_mul_sourceDiagonal
    {z : ℂ} (hzpos : 0 < z.im) (hzhalf : z.im < 1 / 2)
    (hzeta : riemannZeta (1 / 2 + z * I) ≠ 0) :
    xiHedenmalmBezoutian z ((starRingEnd ℂ) z) =
      (normSq (XiC z) : ℂ) *
        ((continuedPrimeArchSourceRelativeTrace ((starRingEnd ℂ) z) -
          continuedPrimeArchSourceRelativeTrace z) /
            (z - (starRingEnd ℂ) z)) := by
  have hspos : 0 < (1 / 2 + z * I).re := by simp [mul_re]; linarith
  have hs1 : 1 / 2 + z * I ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    simp [mul_re] at hre
    linarith
  have hzXi : XiC z ≠ 0 :=
    XiC_ne_zero_of_continuedPrimeArch_domain hspos hs1 hzeta
  obtain ⟨hcpos, hc1, hczeta⟩ :=
    continuedPrimeArch_conj_domain_of_upperHalfStrip hzpos hzhalf hzeta
  have hcXi : XiC ((starRingEnd ℂ) z) ≠ 0 :=
    XiC_ne_zero_of_continuedPrimeArch_domain hcpos hc1 hczeta
  have hTz : continuedPrimeArchSourceRelativeTrace z = logDeriv XiC z := by
    rw [continuedPrimeArchSourceRelativeTrace_eq_xiRelativeResolventTrace
      hspos hs1 hzeta, ← logDeriv_XiC_eq_relativeResolventTrace hzXi]
  have hTc : continuedPrimeArchSourceRelativeTrace ((starRingEnd ℂ) z) =
      logDeriv XiC ((starRingEnd ℂ) z) := by
    rw [continuedPrimeArchSourceRelativeTrace_eq_xiRelativeResolventTrace
      hcpos hc1 hczeta, ← logDeriv_XiC_eq_relativeResolventTrace hcXi]
  rw [logDeriv_apply] at hTz hTc
  have hDz : deriv XiC z = continuedPrimeArchSourceRelativeTrace z * XiC z := by
    rw [hTz]
    field_simp
  have hDc : deriv XiC ((starRingEnd ℂ) z) =
      continuedPrimeArchSourceRelativeTrace ((starRingEnd ℂ) z) *
        XiC ((starRingEnd ℂ) z) := by
    rw [hTc]
    field_simp
  have hne : (starRingEnd ℂ) z ≠ z := by
    intro h
    have him := congrArg Complex.im h
    simp at him
    linarith
  have hcz0 : (starRingEnd ℂ) z - z ≠ 0 := sub_ne_zero.mpr hne
  have hzc0 : z - (starRingEnd ℂ) z ≠ 0 := sub_ne_zero.mpr hne.symm
  rw [xiHedenmalmBezoutian_eq_div hne, hDz, hDc,
    xiHedenmalm_XiC_conj]
  have hnormc : XiC z * (starRingEnd ℂ) (XiC z) = (normSq (XiC z) : ℂ) := by
    apply Complex.ext
    · simp [Complex.normSq_apply]
    · simp [Complex.normSq_apply]
      ring
  calc
    (continuedPrimeArchSourceRelativeTrace z * XiC z *
          (starRingEnd ℂ) (XiC z) -
        XiC z * (continuedPrimeArchSourceRelativeTrace ((starRingEnd ℂ) z) *
          (starRingEnd ℂ) (XiC z))) /
          ((starRingEnd ℂ) z - z) =
        (XiC z * (starRingEnd ℂ) (XiC z)) *
          ((continuedPrimeArchSourceRelativeTrace ((starRingEnd ℂ) z) -
            continuedPrimeArchSourceRelativeTrace z) /
              (z - (starRingEnd ℂ) z)) := by
        field_simp [hcz0, hzc0]
        ring
    _ = _ := by rw [hnormc]

/-- Scalar Hermitian-diagonal orientation of the Hedenmalm Bezoutian on the centered upper
half-strip. -/
def XiHedenmalmUpperHermitianDiagonalNonnegative : Prop :=
  ∀ z : ℂ, 0 < z.im → z.im < 1 / 2 →
    riemannZeta (1 / 2 + z * I) ≠ 0 →
      0 ≤ (xiHedenmalmBezoutian z ((starRingEnd ℂ) z)).re

/-- Hedenmalm Hermitian-diagonal orientation is exactly the continued prime--archimedean
one-Cauchy source sign. -/
theorem xiHedenmalmUpperHermitianDiagonalNonnegative_iff_source :
    XiHedenmalmUpperHermitianDiagonalNonnegative ↔
      ContinuedPrimeArchUpperCauchyDiagonalNonnegative := by
  constructor
  · intro h z hzpos hzhalf hzeta
    have hspos : 0 < (1 / 2 + z * I).re := by simp [mul_re]; linarith
    have hs1 : 1 / 2 + z * I ≠ 1 := by
      intro heq
      have hre := congrArg Complex.re heq
      simp [mul_re] at hre
      linarith
    have hzXi : XiC z ≠ 0 :=
      XiC_ne_zero_of_continuedPrimeArch_domain hspos hs1 hzeta
    have hnorm : 0 < normSq (XiC z) := normSq_pos.mpr hzXi
    have hB := h z hzpos hzhalf hzeta
    rw [xiHedenmalmBezoutian_conj_eq_normSq_mul_sourceDiagonal
      hzpos hzhalf hzeta, mul_re] at hB
    simp only [ofReal_re, ofReal_im, zero_mul, sub_zero] at hB
    nlinarith
  · intro h z hzpos hzhalf hzeta
    have hspos : 0 < (1 / 2 + z * I).re := by simp [mul_re]; linarith
    have hs1 : 1 / 2 + z * I ≠ 1 := by
      intro heq
      have hre := congrArg Complex.re heq
      simp [mul_re] at hre
      linarith
    have hzXi : XiC z ≠ 0 :=
      XiC_ne_zero_of_continuedPrimeArch_domain hspos hs1 hzeta
    have hnorm : 0 < normSq (XiC z) := normSq_pos.mpr hzXi
    have hsource := h z hzpos hzhalf hzeta
    rw [xiHedenmalmBezoutian_conj_eq_normSq_mul_sourceDiagonal
      hzpos hzhalf hzeta, mul_re]
    simp only [ofReal_re, ofReal_im, zero_mul, sub_zero]
    exact mul_nonneg hnorm.le hsource

/-- Exact scalar Hermitian-diagonal Hedenmalm criterion for RH. -/
theorem xiHedenmalmUpperHermitianDiagonalNonnegative_iff_riemannHypothesis :
    XiHedenmalmUpperHermitianDiagonalNonnegative ↔ RiemannHypothesis := by
  rw [xiHedenmalmUpperHermitianDiagonalNonnegative_iff_source,
    continuedPrimeArchUpperCauchyDiagonalNonnegative_iff_riemannHypothesis]

end

end RHTower
