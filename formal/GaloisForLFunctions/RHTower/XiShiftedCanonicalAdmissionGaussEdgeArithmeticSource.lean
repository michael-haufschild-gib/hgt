import GaloisForLFunctions.HTGeometry.AdaptiveOrthogonalSourceGaussDecomposition
import GaloisForLFunctions.RHTower.XiShiftedAdaptiveOrthogonalSourceJacobiEnergy
import GaloisForLFunctions.RHTower.XiShiftedCanonicalAdmissionScaleCompletedArithmeticSource

/-!
# Shifted-Xi adaptive arithmetic source: Gauss bulk plus universal Christoffel edge

The completed `P^sharp` source is formed before observation.  Its current-admission Gaussian rule
then sees a strictly positive nonlinear bulk and misses exactly one next-norm coordinate.  After
current Christoffel-scale completion that invisible coordinate is the universal scalar `(n+1)/16`.
-/

open Matrix Polynomial
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Source-selected Gaussian bulk of the literal completed adaptive mixed amplitude. -/
def xiShiftedAdaptiveGaussArithmeticBulk (w : ℝ) (n : ℕ) : ℝ :=
  2 * HTGeometry.adaptiveOrthoGaussAggregate (xiShiftedRealMomentSequence w) n

/-- **Literal completed `P^sharp` source law.**  Current admission is performed first; current
Gaussian nodes and Christoffel weights then capture all but the exact next-norm edge. -/
theorem xiShiftedAdaptiveMixedCompletedArithmeticSource_eq_gaussBulk_add_nextEdge
    {w : ℝ} (hw : 1 / 2 < w) {n : ℕ} (hn : 0 < n)
    (hH : (HTGeometry.momentHankelMatrix
      (xiShiftedRealMomentSequence w) (n + 2)).PosDef) :
    xiShiftedAdaptiveMixedCompletedArithmeticSource w
        (HTGeometry.monicOrtho (xiShiftedRealMomentSequence w) n) =
      xiShiftedAdaptiveGaussArithmeticBulk w n +
        2 * (n + 1 : ℝ) *
          HTGeometry.monicOrthoNormSq (xiShiftedRealMomentSequence w) (n + 1) := by
  let s := xiShiftedRealMomentSequence w
  let hbelow := HTGeometry.positiveMomentFormBelow_of_hankelPosDef hH
  have hliteral :=
    xiShiftedAdaptiveMixedCompletedArithmeticSource_monicOrtho_eq_jacobiEnergy_of_hankelPosDef
      hw hn hH
  have hsource :=
    HTGeometry.momentFunctional_adaptiveOrthoSourcePolynomial_eq_jacobiEnergy_below
      hbelow hn (le_refl (n + 2))
  have hdefect :=
    HTGeometry.momentFunctional_adaptiveOrthoSourcePolynomial_sub_gaussAggregate_eq_nextNorm
      hbelow hn (le_refl (n + 2))
  unfold xiShiftedAdaptiveGaussArithmeticBulk
  linear_combination hliteral - 2 * hsource + 2 * hdefect

theorem xiShiftedAdaptiveGaussArithmeticBulk_pos
    {w : ℝ} {n : ℕ} (hn : 0 < n)
    (hH : (HTGeometry.momentHankelMatrix
      (xiShiftedRealMomentSequence w) (n + 2)).PosDef) :
    0 < xiShiftedAdaptiveGaussArithmeticBulk w n := by
  unfold xiShiftedAdaptiveGaussArithmeticBulk
  exact mul_pos (by norm_num)
    (HTGeometry.adaptiveOrthoGaussAggregate_pos
      (HTGeometry.positiveMomentFormBelow_of_hankelPosDef hH)
      hn (le_refl (n + 2)))

namespace XiShiftedCanonicalAdmission

/-- Dimensionless source-selected bulk after amplitude normalization and current Christoffel-scale
completion.  This is adaptive in nodes, weights, amplitude, and scale. -/
def scaleCompletedAdmissionGaussBulk (w : ℝ) (n : ℕ) : ℝ :=
  let s := xiShiftedFarRightNormalizedMoment w
  HTGeometry.adaptiveOrthoGaussAggregate s n /
    (16 * HTGeometry.monicOrthoNormSq s n *
      HTGeometry.monicOrthoBeta s (n + 1))

theorem scaleCompletedAdmissionGaussBulk_pos
    {w : ℝ} {n : ℕ} (hn : 0 < n)
    (hH : (HTGeometry.momentHankelMatrix
      (xiShiftedFarRightNormalizedMoment w) (n + 2)).PosDef) :
    0 < scaleCompletedAdmissionGaussBulk w n := by
  let s := xiShiftedFarRightNormalizedMoment w
  let hbelow := HTGeometry.positiveMomentFormBelow_of_hankelPosDef hH
  have haggregate : 0 < HTGeometry.adaptiveOrthoGaussAggregate s n :=
    HTGeometry.adaptiveOrthoGaussAggregate_pos hbelow hn (le_refl (n + 2))
  have hnorm : 0 < HTGeometry.monicOrthoNormSq
      (xiShiftedFarRightNormalizedMoment w) n :=
    HTGeometry.monicOrtho_inner_self_pos_below hbelow (by omega)
  have hbeta : 0 < HTGeometry.monicOrthoBeta
      (xiShiftedFarRightNormalizedMoment w) (n + 1) :=
    HTGeometry.monicOrthoBeta_pos_below hbelow (by omega) (by omega)
  unfold scaleCompletedAdmissionGaussBulk
  dsimp only [s]
  exact div_pos haggregate (mul_pos (mul_pos (by norm_num) hnorm) hbeta)

/-- **Adaptive Gauss-edge completion law.**  The scale-completed literal arithmetic source is a
universal next-edge term plus a strictly positive source-selected bulk.  No orientation map and no
fixed linear reporter occurs. -/
theorem scaleCompletedRelativeArithmeticSource_eq_universalEdge_add_gaussBulk
    {w : ℝ} (hw : 1 < w) {n : ℕ} (hn : 0 < n)
    (hH : (HTGeometry.momentHankelMatrix
      (xiShiftedFarRightNormalizedMoment w) (n + 2)).PosDef) :
    scaleCompletedRelativeArithmeticSource w n =
      (n + 1 : ℝ) / 16 + scaleCompletedAdmissionGaussBulk w n := by
  let s := xiShiftedFarRightNormalizedMoment w
  let hbelow := HTGeometry.positiveMomentFormBelow_of_hankelPosDef hH
  have hsource :=
    scaleCompletedRelativeArithmeticSource_eq_jacobiEnergy_div_christoffel hw hn hH
  have haggregate :=
    HTGeometry.adaptiveOrthoGaussAggregate_eq_visibleJacobiEnergy
      hbelow hn (le_refl (n + 2))
  have hnorm : 0 < HTGeometry.monicOrthoNormSq
      (xiShiftedFarRightNormalizedMoment w) n :=
    HTGeometry.monicOrtho_inner_self_pos_below hbelow (by omega)
  have hbeta : 0 < HTGeometry.monicOrthoBeta
      (xiShiftedFarRightNormalizedMoment w) (n + 1) :=
    HTGeometry.monicOrthoBeta_pos_below hbelow (by omega) (by omega)
  rw [hsource]
  unfold scaleCompletedAdmissionGaussBulk
  dsimp only [s]
  rw [haggregate]
  field_simp [ne_of_gt hnorm, ne_of_gt hbeta]
  ring

/-- The formerly unexplained strict excess over `(n+1)/16` is exactly the positive adaptive
Gaussian bulk. -/
theorem scaleCompletedRelativeArithmeticSource_sub_universalEdge_eq_gaussBulk
    {w : ℝ} (hw : 1 < w) {n : ℕ} (hn : 0 < n)
    (hH : (HTGeometry.momentHankelMatrix
      (xiShiftedFarRightNormalizedMoment w) (n + 2)).PosDef) :
    scaleCompletedRelativeArithmeticSource w n - (n + 1 : ℝ) / 16 =
      scaleCompletedAdmissionGaussBulk w n := by
  rw [scaleCompletedRelativeArithmeticSource_eq_universalEdge_add_gaussBulk hw hn hH]
  ring

end XiShiftedCanonicalAdmission

end

end RHTower
