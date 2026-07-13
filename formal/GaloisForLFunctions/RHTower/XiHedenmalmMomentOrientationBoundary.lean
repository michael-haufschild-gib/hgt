import GaloisForLFunctions.RHTower.XiHedenmalmMomentDeterminacy
import GaloisForLFunctions.RHTower.XiHedenmalmOrientationGate

/-!
# Exact boundary between Hedenmalm moment determinacy and orientation

The pointed analytic moment germ reconstructs the Euler--Gamma trace, the centered Xi function,
and its Bezoutian.  This module identifies the sign still missing after that reconstruction.
On every admissible Hermitian diagonal, the pointed-moment Bezoutian is the continued
prime--archimedean source diagonal multiplied by `‖XiC z‖²`.  Its nonnegativity is therefore
equivalent to the Riemann hypothesis.

This is an unconditional boundary theorem, not a sign theorem: determinacy selects the unique
Bezoutian whose orientation must be proved, but supplies no proof of that orientation.
-/

open Complex

namespace RHTower

noncomputable section

/-- Nonnegativity of the Bezoutian reconstructed from the pointed Hedenmalm moment germ on the
centered upper half-strip. -/
def XiHedenmalmPointedMomentUpperHermitianDiagonalNonnegative : Prop :=
  ∀ z : ℂ, 0 < z.im → z.im < 1 / 2 →
    riemannZeta (1 / 2 + z * I) ≠ 0 →
      0 ≤ (xiHedenmalmPointedMomentBezoutian z ((starRingEnd ℂ) z)).re

/-- The globally defined pointed-moment Bezoutian has exactly the continued
prime--archimedean one-Cauchy diagonal, multiplied by the Xi norm square.  This identity uses
source recovery from the analytic moment germ, not a local Taylor approximation. -/
theorem xiHedenmalmPointedMomentBezoutian_conj_eq_normSq_mul_sourceDiagonal
    {z : ℂ} (hzpos : 0 < z.im) :
    xiHedenmalmPointedMomentBezoutian z ((starRingEnd ℂ) z) =
      (normSq (XiC z) : ℂ) *
        ((continuedPrimeArchSourceRelativeTrace ((starRingEnd ℂ) z) -
          continuedPrimeArchSourceRelativeTrace z) /
            (z - (starRingEnd ℂ) z)) := by
  have hne : (starRingEnd ℂ) z ≠ z := by
    intro h
    have him := congrArg Complex.im h
    simp at him
    linarith
  have hnormc : XiC z * XiC ((starRingEnd ℂ) z) = (normSq (XiC z) : ℂ) := by
    rw [xiHedenmalm_XiC_conj]
    exact Complex.mul_conj (XiC z)
  rw [xiHedenmalmPointedMomentBezoutian, dslope_of_ne _ hne,
    slope_def_module,
    ← neg_eq_iff_eq_neg.mpr
      (continuedPrimeArchSourceRelativeTrace_eq_neg_pointedMomentFlux z),
    ← neg_eq_iff_eq_neg.mpr
      (continuedPrimeArchSourceRelativeTrace_eq_neg_pointedMomentFlux
        ((starRingEnd ℂ) z)), hnormc]
  simp only [smul_eq_mul]
  field_simp [sub_ne_zero.mpr hne, sub_ne_zero.mpr hne.symm]
  ring

/-- The orientation of the uniquely reconstructed pointed-moment Bezoutian is exactly the
continued prime--archimedean source sign. -/
theorem xiHedenmalmPointedMomentUpperHermitianDiagonalNonnegative_iff_source :
    XiHedenmalmPointedMomentUpperHermitianDiagonalNonnegative ↔
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
    rw [xiHedenmalmPointedMomentBezoutian_conj_eq_normSq_mul_sourceDiagonal
      hzpos, mul_re] at hB
    simp only [ofReal_re, ofReal_im, zero_mul, sub_zero] at hB
    nlinarith
  · intro h z hzpos hzhalf hzeta
    have hsource := h z hzpos hzhalf hzeta
    rw [xiHedenmalmPointedMomentBezoutian_conj_eq_normSq_mul_sourceDiagonal
      hzpos, mul_re]
    simp only [ofReal_re, ofReal_im, zero_mul, sub_zero]
    exact mul_nonneg (normSq_nonneg _) hsource

/-- Exact endpoint of the moment module: the missing sign of its uniquely reconstructed
Hermitian Bezoutian is equivalent to RH. -/
theorem xiHedenmalmPointedMomentUpperHermitianDiagonalNonnegative_iff_riemannHypothesis :
    XiHedenmalmPointedMomentUpperHermitianDiagonalNonnegative ↔ RiemannHypothesis := by
  rw [xiHedenmalmPointedMomentUpperHermitianDiagonalNonnegative_iff_source,
    continuedPrimeArchUpperCauchyDiagonalNonnegative_iff_riemannHypothesis]

end

end RHTower
