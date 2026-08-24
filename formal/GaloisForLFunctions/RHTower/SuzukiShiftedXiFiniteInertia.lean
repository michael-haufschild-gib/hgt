import GaloisForLFunctions.HTGeometry.FiniteBlaschkeAdjointFaithfulness
import GaloisForLFunctions.RHTower.SuzukiShiftedXiFiniteDiskFactor

open Complex Set
open GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

theorem xiShiftFiniteSchurNumerator_fn_poleDiskCoordinate_ne_zero
    {omega : ℝ} (homega : 0 ≤ omega)
    [Fintype (XiShiftRightZeroCopy omega)]
    (hnon : SuzukiShiftNonexceptional omega)
    (q : XiShiftRightZeroCopy omega) :
    (xiShiftFiniteSchurNumerator omega homega).fn
        (xiShiftPoleDiskCoordinate omega q) ≠ 0 := by
  let p := xiShiftPoleCoordinate omega q
  have hp : 0 < p.im := xiShiftPoleCoordinate_im_pos omega q
  have hsource : suzukiCanonicalE omega (-p) ≠ 0 := hnon q
  rw [suzukiCanonicalE_eq_center_mul_extremeE_mul_coreE] at hsource
  have hparts := mul_ne_zero_iff.mp hsource
  have hextNum : xiShiftExtremeE omega (-p) ≠ 0 :=
    (mul_ne_zero_iff.mp hparts.1).2
  have hcoreNum : xiShiftCoreE omega (-p) ≠ 0 := hparts.2
  have hextCanonical :
      xiShiftExtremeCanonicalProduct omega
        (p - (omega : ℂ) * I) ≠ 0 := by
    simpa only [xiShiftExtremeE, neg_neg] using hextNum
  have hfact := xiShiftExtremeCanonicalProduct_numerator_shift_factorization
    omega homega p
  rw [hfact] at hextCanonical
  have hnumProd : xiShiftFiniteNumeratorProduct omega p ≠ 0 :=
    (mul_ne_zero_iff.mp hextCanonical).2
  have hconjNumProd : xiShiftFiniteConjNumeratorProduct omega p ≠ 0 := by
    rw [xiShiftFiniteConjNumeratorProduct]
    apply Finset.prod_ne_zero_iff.mpr
    intro r _
    apply sub_ne_zero.mpr
    intro heq
    have him := congrArg Complex.im heq
    have hr := xiShiftNumeratorCoordinate_im_pos homega r
    norm_num at him
    linarith
  have hhalfNum : xiShiftFiniteNumeratorHalfPlaneBlaschke omega p ≠ 0 := by
    rw [xiShiftFiniteNumeratorHalfPlaneBlaschke]
    exact div_ne_zero hnumProd hconjNumProd
  have hnumUnit : xiShiftFiniteNumeratorCayleyUnit omega ≠ 0 :=
    norm_ne_zero_iff.mp (by
      rw [norm_xiShiftFiniteNumeratorCayleyUnit_eq_one homega]
      norm_num)
  have hBnum :
      (xiShiftFiniteNumeratorBlaschke omega homega).fn
        (upperToDiskCayley p) ≠ 0 := by
    rw [xiShiftFiniteNumeratorBlaschke_cayley homega hp]
    exact mul_ne_zero hnumUnit hhalfNum
  have hcoreTheta : xiShiftCoreTheta omega p ≠ 0 := by
    rw [xiShiftCoreTheta]
    exact div_ne_zero hcoreNum (xiShiftCoreE_ne_zero_upperHalfPlane hp)
  have hunit : xiShiftFiniteCayleyUnit omega ≠ 0 :=
    norm_ne_zero_iff.mp (by
      rw [norm_xiShiftFiniteCayleyUnit_eq_one homega]
      norm_num)
  rw [xiShiftFiniteSchurNumerator_fn]
  have hcoord : xiShiftPoleDiskCoordinate omega q = lineCayley p := rfl
  rw [hcoord,
    GaloisForLFunctions.RHTower.suzukiUpperCayleyInv_lineCayley]
  · exact mul_ne_zero (mul_ne_zero hunit hBnum) hcoreTheta
  · intro hzero
    have him := congrArg Complex.im hzero
    norm_num at him
    linarith

theorem xiShiftFiniteSchurNumerator_nonzero_on_poleBlaschkeZeros
    {omega : ℝ} (homega : 0 ≤ omega)
    [Fintype (XiShiftRightZeroCopy omega)]
    (hnon : SuzukiShiftNonexceptional omega) :
    ∀ j : Fin (xiShiftFinitePoleBlaschke omega).deg,
      (xiShiftFiniteSchurNumerator omega homega).fn
        ((xiShiftFinitePoleBlaschke omega).zeros j) ≠ 0 := by
  intro j
  change (xiShiftFiniteSchurNumerator omega homega).fn
    (xiShiftPoleDiskCoordinate omega
      ((Fintype.equivFin (XiShiftRightZeroCopy omega)).symm j)) ≠ 0
  exact xiShiftFiniteSchurNumerator_fn_poleDiskCoordinate_ne_zero
    homega hnon _

/-- Exact multiplicity-aware disk negative squares for every finite nonexceptional shifted-Xi
tail. -/
theorem xiShiftFiniteGeneralizedSchur_exactNegativeSquares
    {omega : ℝ} (homega : 0 ≤ omega)
    [Fintype (XiShiftRightZeroCopy omega)]
    (hnon : SuzukiShiftNonexceptional omega) :
    (finiteBlaschkeGeneralizedSchurRealization
        (xiShiftFiniteSchurNumerator omega homega)
        (xiShiftFinitePoleBlaschke omega)).HasFiniteGramNegativeDimensionOn
          (Metric.ball 0 1) (Fintype.card (XiShiftRightZeroCopy omega)) ∧
      ∀ r : ℕ,
        (finiteBlaschkeGeneralizedSchurRealization
          (xiShiftFiniteSchurNumerator omega homega)
          (xiShiftFinitePoleBlaschke omega)).HasFiniteGramNegativeDimensionOn
            (Metric.ball 0 1) r →
          r ≤ Fintype.card (XiShiftRightZeroCopy omega) := by
  simpa only [xiShiftFinitePoleBlaschke_deg] using
    finiteBlaschkeGeneralizedSchurKernel_exactNegativeSquares_of_nonzero
      (xiShiftFiniteSchurNumerator omega homega)
      (xiShiftFinitePoleBlaschke omega)
      (by rw [xiShiftFiniteSchurNumerator_bd])
      (xiShiftFiniteSchurNumerator_nonzero_on_poleBlaschkeZeros homega hnon)

end

end RHTower
