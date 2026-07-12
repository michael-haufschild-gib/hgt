import GaloisForLFunctions.RHTower.XiHurwitzOrientationHilbert
import GaloisForLFunctions.RHTower.XiWeilLineConjHilbert
import GaloisForLFunctions.RHTower.XiWeilPositivityCriterion

/-!
# The canonical negative Weil sector carried by Hurwitz orientation

Functional-equation reflection negates the Xi--Hurwitz orientation vector.  The vector therefore
lies in the negative eigenspace of the unconditional Weil reflection, and its Weil Hilbert square
is exactly the negative scalar orientation energy.
-/

open Complex

namespace RHTower

noncomputable section

open HurwitzOrbit

/-- Critical-line reflection negates each signed Hurwitz orientation coordinate. -/
theorem xiHurwitzOrientationCoordinate_lineConj (q : XiZeroCopy) :
    xiHurwitzOrientationCoordinate (xiZeroCopyLineConjEquiv q) =
      -xiHurwitzOrientationCoordinate q := by
  have hval : ((xiZeroCopyLineConjEquiv q).1 : ℂ) =
      1 - (starRingEnd ℂ) (q.1 : ℂ) := rfl
  have hchar :
      xiHurwitzMonodromyCharacter (xiZeroCopyLineConjEquiv q).1 =
        (starRingEnd ℂ) (xiHurwitzMonodromyCharacter q.1) := by
    change monoScalar ((xiZeroCopyLineConjEquiv q).1 : ℂ) =
      (starRingEnd ℂ) (monoScalar (q.1 : ℂ))
    rw [hval, monoScalar_feReflection]
  have hcenter : ‖((xiZeroCopyLineConjEquiv q).1 : ℂ) - 1 / 2‖ =
      ‖(q.1 : ℂ) - 1 / 2‖ := by
    rw [← norm_xiSpectralPoint (xiZeroCopyLineConjEquiv q),
      xiSpectralPoint_lineConj, Complex.norm_conj, norm_xiSpectralPoint]
  rw [xiHurwitzOrientationCoordinate, xiHurwitzOrientationCoordinate,
    hchar, Complex.conj_im, Complex.norm_conj, hcenter]
  push_cast
  ring

/-- **Canonical negative-sector law.**  The Xi--Hurwitz orientation vector is an exact
`(-1)`-eigenvector of the unconditional Xi Weil reflection. -/
theorem xiWeilLineConjLp_xiHurwitzOrientationVector :
    xiWeilLineConjLp xiHurwitzOrientationVector =
      -xiHurwitzOrientationVector := by
  apply Subtype.ext
  funext q
  rw [xiWeilLineConjLp_apply]
  exact xiHurwitzOrientationCoordinate_lineConj q

/-- **Weil-energy identity.**  The canonical orientation vector has Weil Hilbert square exactly
equal to minus the scalar orientation energy. -/
theorem xiWeilHilbertQuadratic_xiHurwitzOrientationVector :
    xiWeilHilbertQuadratic xiHurwitzOrientationVector =
      -xiHurwitzOrientationEnergy := by
  rw [xiWeilHilbertQuadratic, xiWeilLineConjLinearIsometry_apply,
    xiWeilLineConjLp_xiHurwitzOrientationVector, inner_neg_left,
    neg_re]
  congr 1
  exact (inner_self_eq_norm_sq (𝕜 := ℂ) xiHurwitzOrientationVector).trans
    norm_sq_xiHurwitzOrientationVector

/-- **One-vector Weil criterion.**  RH is equivalent to nonnegativity of the unconditional Weil
Hilbert form on the single canonical Xi--Hurwitz orientation vector. -/
theorem riemannHypothesis_iff_xiHurwitzOrientationVector_weil_nonneg :
    RiemannHypothesis ↔
      0 ≤ xiWeilHilbertQuadratic xiHurwitzOrientationVector := by
  rw [xiWeilHilbertQuadratic_xiHurwitzOrientationVector]
  constructor
  · intro hRH
    have hzero :=
      riemannHypothesis_iff_xiHurwitzOrientationEnergy_eq_zero.mp hRH
    rw [hzero]
    norm_num
  · intro hnonneg
    apply riemannHypothesis_iff_xiHurwitzOrientationEnergy_eq_zero.mpr
    linarith [xiHurwitzOrientationEnergy_nonneg]

/-- Positivity of the Weil form on the single canonical orientation vector is equivalent to
positivity on its complete square-summable domain. -/
theorem xiHurwitzOrientationVector_weil_nonneg_iff_fullWeil_nonneg :
    0 ≤ xiWeilHilbertQuadratic xiHurwitzOrientationVector ↔
      ∀ F : ℂ → ℂ, XiWeilSquareSummable F →
        0 ≤ (xiWeilPolarization F F).re :=
  riemannHypothesis_iff_xiHurwitzOrientationVector_weil_nonneg.symm.trans
    riemannHypothesis_iff_xiWeilPolarization_nonneg

/-- Source-closure discharge.  Positivity on the algebraic regular-Cauchy source core proves RH as
soon as the single canonical orientation vector is shown to belong to its Hilbert closure. -/
theorem riemannHypothesis_of_cauchyCore_nonneg_of_orientationVector_mem
    (hpos : ∀ v ∈ xiWeilCauchyAlgebraicSubspace,
      0 ≤ xiWeilHilbertQuadratic v)
    (hmem : xiHurwitzOrientationVector ∈ xiWeilCauchyHilbertSubspace) :
    RiemannHypothesis := by
  apply riemannHypothesis_iff_xiHurwitzOrientationVector_weil_nonneg.mpr
  exact xiWeilHilbertQuadratic_nonneg_on_cauchyHilbertSubspace hpos
    xiHurwitzOrientationVector hmem

/-- Failure of RH is equivalent to strict negativity on the same canonical vector. -/
theorem not_riemannHypothesis_iff_xiHurwitzOrientationVector_weil_neg :
    ¬RiemannHypothesis ↔
      xiWeilHilbertQuadratic xiHurwitzOrientationVector < 0 := by
  rw [xiWeilHilbertQuadratic_xiHurwitzOrientationVector,
    neg_lt_zero, xiHurwitzOrientationEnergy_pos_iff_not_riemannHypothesis]

end

end RHTower
