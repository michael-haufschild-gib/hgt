import GaloisForLFunctions.HTGeometry.RestrictedAdjointCancellationQuotient
import GaloisForLFunctions.RHTower.SuzukiShiftedXiInfiniteKernelIdentification

/-!
# Literal common-divisor cancellation for the infinite shifted-Xi kernel

A denominator pole of the shifted-Xi quotient is a common source zero exactly when the full Hardy
numerator vanishes at its disk coordinate.  Such a common zero supplies an explicit nonzero Szegő-
kernel direction in the restricted-adjoint cancellation space.  Quotienting the complete pole
model space by all these common directions gives an intrinsic uncancelled divisor quotient; every
finite negative dimension of the literal regular shifted-Xi kernel is exactly a finite independent
dimension of that quotient, including exceptional and infinite-tail shifts.
-/

open Complex Set
open GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section
open scoped Classical

/-- A common source zero forces the complete infinite Schur numerator to vanish at the matching
pole disk coordinate. -/
theorem xiShiftInfiniteSchurNumerator_fn_poleDiskCoordinate_eq_zero_of_common
    {omega : ℝ} (homega : 0 ≤ omega)
    (q : XiShiftRightZeroCopy omega)
    (hcommon : suzukiCanonicalE omega (-xiShiftPoleCoordinate omega q) = 0) :
    (xiShiftInfiniteSchurNumerator homega).fn
      (xiShiftPoleDiskCoordinate omega q) = 0 := by
  let p := xiShiftPoleCoordinate omega q
  have hp : 0 < p.im := xiShiftPoleCoordinate_im_pos omega q
  have hpI : p + I ≠ 0 := by
    intro hzero
    have him := congrArg Complex.im hzero
    norm_num at him
    linarith
  have hsource : suzukiCanonicalE omega (-p) = 0 := hcommon
  rw [suzukiCanonicalE_eq_center_mul_extremeE_mul_coreE] at hsource
  rcases mul_eq_zero.mp hsource with hcenterext | hcore
  · have hext : xiShiftExtremeE omega (-p) = 0 :=
      (mul_eq_zero.mp hcenterext).resolve_left XiC_zero_ne
    have hprod : xiShiftExtremeCanonicalProduct omega
        (p - (omega : ℂ) * I) = 0 := by
      simpa only [xiShiftExtremeE, neg_neg] using hext
    have hex : ∃ r : XiShiftExtremeZeroCopy omega,
        p - (omega : ℂ) * I = xiSpectralPoint r.1 := by
      by_contra hnone
      push Not at hnone
      exact (canonicalProductE1IndexedSelected_ne_zero
        xiSpectralPoint
        (fun r => omega < |(I * xiSpectralPoint r).re|)
        xiSpectralPoint_ne_zero xiSpectralPoint_inv_sq_summable
        (p - (omega : ℂ) * I) hnone) hprod
    obtain ⟨r, hr⟩ := hex
    have hdelta : (I * xiSpectralPoint r.1).re =
        2 * omega - (I * xiSpectralPoint q.1).re := by
      rw [← hr]
      dsimp only [p, xiShiftPoleCoordinate]
      norm_num [mul_re]
      ring
    have hright : omega <
        (I * xiSpectralPoint (xiZeroCopyReflectEquiv r.1)).re := by
      rw [xiSpectralPoint_reflect]
      have hnegdelta : (I * -xiSpectralPoint r.1).re =
          -(I * xiSpectralPoint r.1).re := by
        norm_num [mul_re]
      rw [hnegdelta, hdelta]
      rcases lt_abs.mp r.2 with hrpos | hrneg
      · rw [hdelta] at hrpos
        exfalso
        linarith [q.2]
      · rw [hdelta] at hrneg
        linarith
    let rRight : XiShiftRightZeroCopy omega :=
      ⟨xiZeroCopyReflectEquiv r.1, hright⟩
    have hcoord : xiShiftPoleDiskCoordinate omega q =
        xiShiftNumeratorDiskCoordinate omega rRight := by
      change lineCayley p = lineCayley (xiShiftNumeratorCoordinate omega rRight)
      congr 1
      change p = -xiSpectralPoint rRight.1 + (omega : ℂ) * I
      dsimp only [p, xiShiftPoleCoordinate] at hr ⊢
      dsimp only [rRight]
      rw [xiSpectralPoint_reflect, ← hr]
      ring
    have hnum : (xiShiftNumeratorBlaschkeMultiplier homega).fn
        (xiShiftPoleDiskCoordinate omega q) = 0 := by
      rw [hcoord]
      exact indexedBlaschkeMultiplier_apply_zero
        (xiShiftNumeratorDiskCoordinate omega)
        (norm_xiShiftNumeratorDiskCoordinate_lt_one homega)
        (summable_one_sub_norm_xiShiftNumeratorDiskCoordinate homega) rRight
    change (xiShiftNumeratorBlaschkeMultiplier homega).fn
        (xiShiftPoleDiskCoordinate omega q) *
      (xiShiftCoreDiskMultiplier omega).fn
        (xiShiftPoleDiskCoordinate omega q) = 0
    rw [hnum, zero_mul]
  · have hcoreTheta : xiShiftCoreTheta omega p = 0 := by
      rw [xiShiftCoreTheta, hcore]
      simp
    have hcoreDisk : (xiShiftCoreDiskMultiplier omega).fn
        (xiShiftPoleDiskCoordinate omega q) = 0 := by
      change xiShiftCoreTheta omega
        (GaloisForLFunctions.RHTower.suzukiUpperCayleyInv (lineCayley p)) = 0
      rw [GaloisForLFunctions.RHTower.suzukiUpperCayleyInv_lineCayley hpI]
      exact hcoreTheta
    change (xiShiftNumeratorBlaschkeMultiplier homega).fn
        (xiShiftPoleDiskCoordinate omega q) *
      (xiShiftCoreDiskMultiplier omega).fn
        (xiShiftPoleDiskCoordinate omega q) = 0
    rw [hcoreDisk, mul_zero]

/-- Exact pointwise common-divisor criterion: source numerator and Hardy numerator have the same
common zeros on the complete shifted-Xi pole divisor. -/
theorem xiShiftInfiniteSchurNumerator_fn_poleDiskCoordinate_eq_zero_iff
    {omega : ℝ} (homega : 0 ≤ omega)
    (q : XiShiftRightZeroCopy omega) :
    (xiShiftInfiniteSchurNumerator homega).fn
        (xiShiftPoleDiskCoordinate omega q) = 0 ↔
      suzukiCanonicalE omega (-xiShiftPoleCoordinate omega q) = 0 := by
  constructor
  · intro hnum
    by_contra hsource
    exact (xiShiftInfiniteSchurNumerator_fn_poleDiskCoordinate_ne_zero_of_source
      homega q hsource) hnum
  · exact xiShiftInfiniteSchurNumerator_fn_poleDiskCoordinate_eq_zero_of_common homega q

/-- Full pole model space after deleting the exact common numerator-adjoint kernel. -/
abbrev XiShiftUncancelledDivisorQuotient
    {omega : ℝ} (homega : 0 ≤ omega) :=
  RestrictedAdjointUncancelledQuotient
    (hardyMultiplierModelSpace (xiShiftPoleBlaschkeMultiplier homega))
    (hardyMul (xiShiftInfiniteSchurNumerator homega))

/-- Explicit model-space direction attached to one exceptional common shifted-Xi zero. -/
def xiShiftCommonZeroCancellationVector
    {omega : ℝ} (homega : 0 ≤ omega)
    (q : XiShiftRightZeroCopy omega) :
    hardyMultiplierModelSpace (xiShiftPoleBlaschkeMultiplier homega) :=
  commonZeroCancellationVector
    (xiShiftPoleBlaschkeMultiplier homega)
    (norm_xiShiftPoleDiskCoordinate_lt_one omega q)
    (xiShiftPoleBlaschkeMultiplier_apply_zero homega q)

theorem xiShiftCommonZeroCancellationVector_ne_zero
    {omega : ℝ} (homega : 0 ≤ omega)
    (q : XiShiftRightZeroCopy omega) :
    xiShiftCommonZeroCancellationVector homega q ≠ 0 :=
  commonZeroCancellationVector_ne_zero
    (xiShiftPoleBlaschkeMultiplier homega)
    (norm_xiShiftPoleDiskCoordinate_lt_one omega q)
    (xiShiftPoleBlaschkeMultiplier_apply_zero homega q)

/-- Every literal common shifted-Xi source zero lies in the exact cancellation kernel. -/
theorem xiShiftCommonZeroCancellationVector_mem
    {omega : ℝ} (homega : 0 ≤ omega)
    (q : XiShiftRightZeroCopy omega)
    (hcommon : suzukiCanonicalE omega (-xiShiftPoleCoordinate omega q) = 0) :
    xiShiftCommonZeroCancellationVector homega q ∈
      restrictedAdjointCancellationSpace
        (hardyMultiplierModelSpace (xiShiftPoleBlaschkeMultiplier homega))
        (hardyMul (xiShiftInfiniteSchurNumerator homega)) := by
  exact commonZeroCancellationVector_mem
    (xiShiftInfiniteSchurNumerator homega)
    (xiShiftPoleBlaschkeMultiplier homega)
    (norm_xiShiftPoleDiskCoordinate_lt_one omega q)
    ((xiShiftInfiniteSchurNumerator_fn_poleDiskCoordinate_eq_zero_iff homega q).2 hcommon)
    (xiShiftPoleBlaschkeMultiplier_apply_zero homega q)

/-- An exceptional shift produces a genuine nonzero common-divisor cancellation direction. -/
theorem exists_nonzero_xiShiftCommonCancellation_of_exceptional
    {omega : ℝ} (homega : 0 ≤ omega)
    (hexceptional : ¬ SuzukiShiftNonexceptional omega) :
    ∃ x : hardyMultiplierModelSpace (xiShiftPoleBlaschkeMultiplier homega),
      x ≠ 0 ∧
        x ∈ restrictedAdjointCancellationSpace
          (hardyMultiplierModelSpace (xiShiftPoleBlaschkeMultiplier homega))
          (hardyMul (xiShiftInfiniteSchurNumerator homega)) := by
  rw [SuzukiShiftNonexceptional] at hexceptional
  push Not at hexceptional
  obtain ⟨q, hcommon⟩ := hexceptional
  exact ⟨xiShiftCommonZeroCancellationVector homega q,
    xiShiftCommonZeroCancellationVector_ne_zero homega q,
    xiShiftCommonZeroCancellationVector_mem homega q hcommon⟩

/-- Literal regular shifted-Xi negative dimensions are exactly finite dimensions of the complete
pole divisor after common-factor quotient, for every shift including exceptional and infinite
tails. -/
theorem xiShiftRegularUpperKernel_negativeDimension_iff_uncancelledDivisorQuotient
    {omega : ℝ} (homega : 0 ≤ omega) (r : ℕ) :
    HasFiniteKernelNegativeDimension (xiShiftRegularUpperKernel omega) r ↔
      HasIndependentDimensionAtLeast (XiShiftUncancelledDivisorQuotient homega) r := by
  rw [xiShiftRegularUpperKernel_negativeDimension_iff_rankAtLeast homega r]
  exact restrictedAdjointRankAtLeast_iff_uncancelledQuotient
    (hardyMultiplierModelSpace (xiShiftPoleBlaschkeMultiplier homega))
    (hardyMul (xiShiftInfiniteSchurNumerator homega)) r

end
end RHTower
