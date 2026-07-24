import GaloisForLFunctions.HilbertMetric.ThreePointCorrelationAngle
import GaloisForLFunctions.HTGeometry.PSDMatrixSpectralHankel
import GaloisForLFunctions.RHTower.HedenmalmCenterMixedThreePoint
import GaloisForLFunctions.RHTower.ThetaCuspReflectedRiccatiAngle
import GaloisForLFunctions.RHTower.ThetaCuspLikelihoodGapCumulantRiccati
import GaloisForLFunctions.RHTower.ThetaCuspAtomLikelihoodCrossDomination
import GaloisForLFunctions.RHTower.ThetaCuspGlobalReflectedRiccati

/-!
# Correlation-angle producer for Hedenmalm three-point positivity

Correlation-angle subadditivity of every reflected completed-source fibre makes its ordered
three-point matrix positive semidefinite.  The existing continuum matrix-kernel theorem then
passes this positivity through Hedenmalm's positive center mixture and discharges the named
near-center wall.
-/

open MeasureTheory Set

namespace RHTower

noncomputable section

/-- Reflected product of the completed theta source at center `u`. -/
def thetaCuspReflectedSourceProduct (u t : ℝ) : ℝ :=
  thetaCuspFullSource (u + t) * thetaCuspFullSource (u - t)

/-- Center-normalized reflected completed-source correlation. -/
def thetaCuspReflectedSourceCorrelation (u t : ℝ) : ℝ :=
  thetaCuspReflectedSourceProduct u t / thetaCuspReflectedSourceProduct u 0

/-- Correlation angle of the normalized reflected completed-source fibre. -/
def thetaCuspReflectedSourceCorrelationAngle (u t : ℝ) : ℝ :=
  Real.arccos (thetaCuspReflectedSourceCorrelation u t)

/-- **Unconditional global source angle law.**  Every completed-source reflected fibre obeys
the correlation-angle triangle inequality, including packets crossing the modular seam. -/
theorem thetaCuspReflectedSourceCorrelationAngle_subadditive_global
    {u x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    thetaCuspReflectedSourceCorrelationAngle u (x + y) ≤
      thetaCuspReflectedSourceCorrelationAngle u x +
        thetaCuspReflectedSourceCorrelationAngle u y := by
  simpa [thetaCuspReflectedSourceCorrelationAngle,
    thetaCuspReflectedSourceCorrelation,
    thetaCuspReflectedSourceProduct, pow_two] using
      thetaCuspFullSource_reflectedCorrelationAngle_subadditive_global
        (u := u) hx hy

/-- Ordered three-node matrix of one unnormalized reflected source fibre. -/
def thetaCuspReflectedSourceThreePointMatrix
    (u x y : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  HilbertMetric.threePointCorrelationMatrix
    (thetaCuspReflectedSourceProduct u 0)
    (thetaCuspReflectedSourceProduct u x)
    (thetaCuspReflectedSourceProduct u y)
    (thetaCuspReflectedSourceProduct u (x + y))

/-- Correlation-angle subadditivity makes each completed-source fibre positive semidefinite. -/
theorem thetaCuspReflectedSourceThreePointMatrix_posSemidef_of_angle_subadditive
    {u x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hangle :
      thetaCuspReflectedSourceCorrelationAngle u (x + y) ≤
        thetaCuspReflectedSourceCorrelationAngle u x +
          thetaCuspReflectedSourceCorrelationAngle u y) :
    Matrix.PosSemidef (thetaCuspReflectedSourceThreePointMatrix u x y) := by
  let d := thetaCuspReflectedSourceProduct u 0
  let p := thetaCuspReflectedSourceCorrelation u x
  let q := thetaCuspReflectedSourceCorrelation u y
  let r := thetaCuspReflectedSourceCorrelation u (x + y)
  have hd : 0 < d := by
    dsimp [d, thetaCuspReflectedSourceProduct]
    exact mul_pos (thetaCuspFullSource_pos_all _) (thetaCuspFullSource_pos_all _)
  have hprodPos (t : ℝ) : 0 < thetaCuspReflectedSourceProduct u t := by
    unfold thetaCuspReflectedSourceProduct
    exact mul_pos (thetaCuspFullSource_pos_all _) (thetaCuspFullSource_pos_all _)
  have hxle :
      thetaCuspReflectedSourceProduct u x ≤
        thetaCuspReflectedSourceProduct u 0 := by
    exact (strictAntiOn_thetaCuspFullSource_mul_reflect u).antitoneOn
      (by simp) hx hx
  have hyle :
      thetaCuspReflectedSourceProduct u y ≤
        thetaCuspReflectedSourceProduct u 0 := by
    exact (strictAntiOn_thetaCuspFullSource_mul_reflect u).antitoneOn
      (by simp) hy hy
  have hxy : 0 ≤ x + y := add_nonneg hx hy
  have hrpRaw :
      thetaCuspReflectedSourceProduct u (x + y) ≤
        thetaCuspReflectedSourceProduct u x := by
    exact (strictAntiOn_thetaCuspFullSource_mul_reflect u).antitoneOn
      hx hxy (by linarith)
  have hrqRaw :
      thetaCuspReflectedSourceProduct u (x + y) ≤
        thetaCuspReflectedSourceProduct u y := by
    exact (strictAntiOn_thetaCuspFullSource_mul_reflect u).antitoneOn
      hy hxy (by linarith)
  have hp0 : 0 ≤ p := by
    dsimp [p, thetaCuspReflectedSourceCorrelation]
    exact (div_pos (hprodPos x) hd).le
  have hp1 : p ≤ 1 := by
    dsimp [p, thetaCuspReflectedSourceCorrelation]
    exact (div_le_one hd).mpr hxle
  have hq0 : 0 ≤ q := by
    dsimp [q, thetaCuspReflectedSourceCorrelation]
    exact (div_pos (hprodPos y) hd).le
  have hq1 : q ≤ 1 := by
    dsimp [q, thetaCuspReflectedSourceCorrelation]
    exact (div_le_one hd).mpr hyle
  have hr0 : 0 ≤ r := by
    dsimp [r, thetaCuspReflectedSourceCorrelation]
    exact (div_pos (hprodPos (x + y)) hd).le
  have hrp : r ≤ p := by
    dsimp [r, p, thetaCuspReflectedSourceCorrelation]
    exact div_le_div_of_nonneg_right hrpRaw hd.le
  have hrq : r ≤ q := by
    dsimp [r, q, thetaCuspReflectedSourceCorrelation]
    exact div_le_div_of_nonneg_right hrqRaw hd.le
  have hnormalized :
      Matrix.PosSemidef
        (HilbertMetric.threePointCorrelationMatrix 1 p q r) := by
    apply
      HilbertMetric.threePointCorrelationMatrix_posSemidef_of_arccos_subadditive_closed
      hp0 hp1 hq0 hq1 hr0 hrp hrq
    simpa only [thetaCuspReflectedSourceCorrelationAngle, p, q, r] using hangle
  have hscale (t : ℝ) :
      d * thetaCuspReflectedSourceCorrelation u t =
        thetaCuspReflectedSourceProduct u t := by
    change d * (thetaCuspReflectedSourceProduct u t / d) =
      thetaCuspReflectedSourceProduct u t
    field_simp [hd.ne']
  have hdp : d * p = thetaCuspReflectedSourceProduct u x := hscale x
  have hdq : d * q = thetaCuspReflectedSourceProduct u y := hscale y
  have hdr : d * r = thetaCuspReflectedSourceProduct u (x + y) := hscale (x + y)
  have hmatrix :
      thetaCuspReflectedSourceThreePointMatrix u x y =
        d • HilbertMetric.threePointCorrelationMatrix 1 p q r := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [thetaCuspReflectedSourceThreePointMatrix,
        HilbertMetric.threePointCorrelationMatrix, hdp, hdq, hdr]
    all_goals rfl
  rw [hmatrix]
  exact hnormalized.smul hd.le

/-- Every positive-gap reflected completed-source fibre has a positive-semidefinite ordered
three-point matrix. -/
theorem thetaCuspReflectedSourceThreePointMatrix_posSemidef
    {u x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    Matrix.PosSemidef (thetaCuspReflectedSourceThreePointMatrix u x y) :=
  thetaCuspReflectedSourceThreePointMatrix_posSemidef_of_angle_subadditive
    hx hy
      (thetaCuspReflectedSourceCorrelationAngle_subadditive_global hx hy)

/-- Positive matrix kernel whose integral is the center-mixed three-point matrix. -/
def thetaCuspCenterMixedThreePointSourceKernel
    (a x y r : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  (r * Real.sinh (a * r)) •
    thetaCuspReflectedSourceThreePointMatrix (r / 2) x y

theorem integral_thetaCuspCenterMixedThreePointSourceKernel
    (a x y : ℝ) :
    HTGeometry.integralMatrixKernel (volume.restrict (Ioi 0))
        (thetaCuspCenterMixedThreePointSourceKernel a x y) =
      thetaCuspCenterMixedThreePointMatrix a x y := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [HTGeometry.integralMatrixKernel,
      thetaCuspCenterMixedThreePointSourceKernel,
      thetaCuspReflectedSourceThreePointMatrix,
      HilbertMetric.threePointCorrelationMatrix,
      thetaCuspReflectedSourceProduct,
      thetaCuspCenterMixedThreePointMatrix,
      thetaCuspCenterMixedDensity]

/-- Fibrewise correlation-angle subadditivity passes through Hedenmalm's positive center
mixture. -/
theorem thetaCuspCenterMixedThreePointMatrix_posSemidef_of_sourceAngle_subadditive
    {a x y : ℝ} (ha0 : 0 < a) (ha : a < 1 / 2)
    (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hangle : ∀ u : ℝ,
      thetaCuspReflectedSourceCorrelationAngle u (x + y) ≤
        thetaCuspReflectedSourceCorrelationAngle u x +
          thetaCuspReflectedSourceCorrelationAngle u y) :
    Matrix.PosSemidef (thetaCuspCenterMixedThreePointMatrix a x y) := by
  let mu : Measure ℝ := volume.restrict (Ioi 0)
  let kernel := thetaCuspCenterMixedThreePointSourceKernel a x y
  have hentry : ∀ i j, Integrable (fun r => kernel r i j) mu := by
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [kernel, mu, thetaCuspCenterMixedThreePointSourceKernel,
        thetaCuspReflectedSourceThreePointMatrix,
        HilbertMetric.threePointCorrelationMatrix,
        thetaCuspReflectedSourceProduct] <;>
      first
      | simpa using integrableOn_thetaCuspCenterMixedIntegrand ha0.le ha 0
      | simpa using integrableOn_thetaCuspCenterMixedIntegrand ha0.le ha x
      | simpa using integrableOn_thetaCuspCenterMixedIntegrand ha0.le ha y
      | simpa using integrableOn_thetaCuspCenterMixedIntegrand ha0.le ha (x + y)
  have hkernel : ∀ r, Matrix.PosSemidef (kernel r) := by
    intro r
    have hweight : 0 ≤ r * Real.sinh (a * r) := by
      rcases le_total 0 r with hr | hr
      · exact mul_nonneg hr
          (Real.sinh_nonneg_iff.mpr (mul_nonneg ha0.le hr))
      · exact mul_nonneg_of_nonpos_of_nonpos hr
          (Real.sinh_nonpos_iff.mpr (mul_nonpos_of_nonneg_of_nonpos ha0.le hr))
    exact (thetaCuspReflectedSourceThreePointMatrix_posSemidef_of_angle_subadditive
      hx hy (hangle (r / 2))).smul hweight
  have hintegral :=
    HTGeometry.integralMatrixKernel_posSemidef mu kernel hentry hkernel
  rw [show HTGeometry.integralMatrixKernel mu kernel =
      thetaCuspCenterMixedThreePointMatrix a x y by
    simpa only [mu, kernel] using
      integral_thetaCuspCenterMixedThreePointSourceKernel a x y] at hintegral
  exact hintegral

/-- **Theta-specific center-mixed kernel positivity from source data.**  Every admissible
Hedenmalm center mixture has a positive-semidefinite ordered three-point matrix. -/
theorem thetaCuspCenterMixedThreePointMatrix_posSemidef
    {a x y : ℝ} (ha0 : 0 < a) (ha : a < 1 / 2)
    (hx : 0 ≤ x) (hy : 0 ≤ y) :
    Matrix.PosSemidef (thetaCuspCenterMixedThreePointMatrix a x y) :=
  thetaCuspCenterMixedThreePointMatrix_posSemidef_of_sourceAngle_subadditive
    ha0 ha hx hy fun _ =>
      thetaCuspReflectedSourceCorrelationAngle_subadditive_global hx hy

/-- All admissible nonnegative-gap Hedenmalm center-mixed matrices are positive semidefinite. -/
theorem thetaCuspCenterMixedThreePointMatrices_posSemidef :
    ∀ a x y : ℝ, 0 < a → a < 1 / 2 → 0 ≤ x → 0 ≤ y →
      Matrix.PosSemidef (thetaCuspCenterMixedThreePointMatrix a x y) :=
  fun _ _ _ ha0 ha hx hy =>
    thetaCuspCenterMixedThreePointMatrix_posSemidef ha0 ha hx hy

/-- The center-mixed three-point determinant is nonnegative for every admissible nonnegative-gap
packet. -/
theorem thetaCuspCenterMixedThreePointDeterminant_nonneg
    {a x y : ℝ} (ha0 : 0 < a) (ha : a < 1 / 2)
    (hx : 0 ≤ x) (hy : 0 ≤ y) :
    0 ≤ thetaCuspCenterMixedThreePointDeterminant a x y := by
  have hdet :=
    (thetaCuspCenterMixedThreePointMatrix_posSemidef ha0 ha hx hy).det_nonneg
  have heq :
      (thetaCuspCenterMixedThreePointMatrix a x y).det =
        thetaCuspCenterMixedThreePointDeterminant a x y := by
    simp [thetaCuspCenterMixedThreePointMatrix,
      thetaCuspCenterMixedThreePointDeterminant,
      HilbertMetric.threePointCorrelationMatrix,
      HilbertMetric.threePointCorrelationDeterminant,
      Matrix.det_fin_three]
    ring
  rw [heq] at hdet
  exact hdet

/-- A global source correlation-angle triangle law discharges the named near-center
three-point wall. -/
theorem thetaCuspCenterMixedNearCenterThreePointWall_of_sourceAngle_subadditive
    (hangle : ∀ u x y : ℝ, 0 < x → 0 < y →
      thetaCuspReflectedSourceCorrelationAngle u (x + y) ≤
        thetaCuspReflectedSourceCorrelationAngle u x +
          thetaCuspReflectedSourceCorrelationAngle u y) :
    ThetaCuspCenterMixedNearCenterThreePointWall := by
  apply
    thetaCuspCenterMixedThreePointMatrices_posSemidef_iff_nearCenterWall.mp
  intro a x y ha0 ha hx hy
  exact thetaCuspCenterMixedThreePointMatrix_posSemidef_of_sourceAngle_subadditive
    ha0 ha hx.le hy.le (fun u => hangle u x y hx hy)

/-- **Unconditional near-center wall.**  Source-derived global Riccati positivity discharges
the last theta center-mixed three-point proposition interface. -/
theorem thetaCuspCenterMixedNearCenterThreePointWall :
    ThetaCuspCenterMixedNearCenterThreePointWall :=
  thetaCuspCenterMixedThreePointMatrices_posSemidef_iff_nearCenterWall.mp
    fun a x y ha0 ha hx hy =>
      thetaCuspCenterMixedThreePointMatrices_posSemidef
        a x y ha0 ha hx.le hy.le

/-- Reflected completed-source correlations are even in their center coordinate. -/
theorem thetaCuspReflectedSourceCorrelation_neg_center
    (u t : ℝ) :
    thetaCuspReflectedSourceCorrelation (-u) t =
      thetaCuspReflectedSourceCorrelation u t := by
  have hminus :
      thetaCuspFullSource (-u + t) = thetaCuspFullSource (u - t) := by
    rw [show -u + t = -(u - t) by ring, thetaCuspFullSource_neg]
  have hplus :
      thetaCuspFullSource (-u - t) = thetaCuspFullSource (u + t) := by
    rw [show -u - t = -(u + t) by ring, thetaCuspFullSource_neg]
  have hcenter : thetaCuspFullSource (-u) = thetaCuspFullSource u :=
    thetaCuspFullSource_neg u
  unfold thetaCuspReflectedSourceCorrelation
    thetaCuspReflectedSourceProduct
  rw [hminus, hplus]
  simp only [add_zero, sub_zero]
  rw [hcenter]
  ring

/-- The completed-source correlation angle is even in its center coordinate. -/
theorem thetaCuspReflectedSourceCorrelationAngle_neg_center
    (u t : ℝ) :
    thetaCuspReflectedSourceCorrelationAngle (-u) t =
      thetaCuspReflectedSourceCorrelationAngle u t := by
  unfold thetaCuspReflectedSourceCorrelationAngle
  rw [thetaCuspReflectedSourceCorrelation_neg_center]

/-- The exact cumulant lower bound discharges the source angle triangle law whenever the packet
stays on one modular half-line. -/
theorem thetaCuspReflectedSourceCorrelationAngle_subadditive_of_cumulantCorrection
    {u x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hxyu : x + y ≤ u)
    (hcorrection : ∀ t ∈ Icc 0 (x + y),
      -thetaCuspSingleAtomReflectedRiccatiMargin
          (thetaCuspSingleAtomReflectionScale 1 u)
          (thetaCuspSingleAtomReflectionDefect t)
          (2 * Real.sinh (2 * t)) ≤
        thetaCuspReflectedLikelihoodCumulantCorrection u t) :
    thetaCuspReflectedSourceCorrelationAngle u (x + y) ≤
      thetaCuspReflectedSourceCorrelationAngle u x +
        thetaCuspReflectedSourceCorrelationAngle u y := by
  simpa [thetaCuspReflectedSourceCorrelationAngle,
    thetaCuspReflectedSourceCorrelation,
    thetaCuspReflectedSourceProduct, pow_two] using
      thetaCuspFullSource_reflectedCorrelationAngle_subadditive_of_cumulantCorrection
        hx hy hxyu hcorrection

/-- The exact domination of the negative atom--likelihood cross channel by the two unconditional
positive component margins discharges the same-half-line source angle law. -/
theorem thetaCuspReflectedSourceCorrelationAngle_subadditive_of_crossDomination
    {u x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hxyu : x + y ≤ u)
    (hdomination : ∀ t ∈ Icc 0 (x + y),
      -thetaCuspReflectedAtomLikelihoodRiccatiCross u t ≤
        thetaCuspSingleAtomReflectedRiccatiMargin
            (thetaCuspSingleAtomReflectionScale 1 u)
            (thetaCuspSingleAtomReflectionDefect t)
            (2 * Real.sinh (2 * t)) +
          thetaCuspReflectedLikelihoodCumulantRiccatiMargin u t) :
    thetaCuspReflectedSourceCorrelationAngle u (x + y) ≤
      thetaCuspReflectedSourceCorrelationAngle u x +
        thetaCuspReflectedSourceCorrelationAngle u y := by
  apply
    thetaCuspReflectedSourceCorrelationAngle_subadditive_of_cumulantCorrection
      hx hy hxyu
  intro t ht
  rw [thetaCuspReflectedLikelihoodCumulantCorrection_eq_margin_add_cross]
  have h := hdomination t ht
  linarith

/-- **Unconditional same-half-line source angle law.**  The atom margin strictly absorbs the
negative atom--likelihood interference, so no cumulant or domination interface remains. -/
theorem thetaCuspReflectedSourceCorrelationAngle_subadditive
    {u x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hxyu : x + y ≤ u) :
    thetaCuspReflectedSourceCorrelationAngle u (x + y) ≤
      thetaCuspReflectedSourceCorrelationAngle u x +
        thetaCuspReflectedSourceCorrelationAngle u y := by
  simpa [thetaCuspReflectedSourceCorrelationAngle,
    thetaCuspReflectedSourceCorrelation,
    thetaCuspReflectedSourceProduct, pow_two] using
      thetaCuspFullSource_reflectedCorrelationAngle_subadditive hx hy hxyu

/-- **Legacy seam-localized connector.**  This exact chamber decomposition is retained for API
compatibility; the unconditional global theorem above now discharges both premises. -/
theorem thetaCuspCenterMixedNearCenterThreePointWall_of_cumulantCorrection_and_seamAngle
    (hcorrection : ∀ u x y : ℝ, 0 ≤ x → 0 ≤ y → x + y ≤ u →
      ∀ t ∈ Icc 0 (x + y),
        -thetaCuspSingleAtomReflectedRiccatiMargin
            (thetaCuspSingleAtomReflectionScale 1 u)
            (thetaCuspSingleAtomReflectionDefect t)
            (2 * Real.sinh (2 * t)) ≤
          thetaCuspReflectedLikelihoodCumulantCorrection u t)
    (hseam : ∀ u x y : ℝ, 0 ≤ u → u < x + y → 0 < x → 0 < y →
      thetaCuspReflectedSourceCorrelationAngle u (x + y) ≤
        thetaCuspReflectedSourceCorrelationAngle u x +
          thetaCuspReflectedSourceCorrelationAngle u y) :
    ThetaCuspCenterMixedNearCenterThreePointWall := by
  apply thetaCuspCenterMixedNearCenterThreePointWall_of_sourceAngle_subadditive
  intro u x y hx hy
  let v := |u|
  have hv : 0 ≤ v := abs_nonneg u
  have hangleV :
      thetaCuspReflectedSourceCorrelationAngle v (x + y) ≤
        thetaCuspReflectedSourceCorrelationAngle v x +
          thetaCuspReflectedSourceCorrelationAngle v y := by
    by_cases hxyv : x + y ≤ v
    · exact
        thetaCuspReflectedSourceCorrelationAngle_subadditive_of_cumulantCorrection
          hx.le hy.le hxyv (hcorrection v x y hx.le hy.le hxyv)
    · exact hseam v x y hv (lt_of_not_ge hxyv) hx hy
  rcases le_total 0 u with hu | hu
  · simpa only [v, abs_of_nonneg hu] using hangleV
  · have habs : v = -u := by
      simp only [v, abs_of_nonpos hu]
    rw [habs] at hangleV
    simpa only [thetaCuspReflectedSourceCorrelationAngle_neg_center] using hangleV

/-- **Legacy reduced seam connector.**  This isolates cross domination and seam angle as
independent sufficient inputs; both are now supplied by unconditional source theorems. -/
theorem thetaCuspCenterMixedNearCenterThreePointWall_of_crossDomination_and_seamAngle
    (hdomination : ∀ u x y : ℝ, 0 ≤ x → 0 ≤ y → x + y ≤ u →
      ∀ t ∈ Icc 0 (x + y),
        -thetaCuspReflectedAtomLikelihoodRiccatiCross u t ≤
          thetaCuspSingleAtomReflectedRiccatiMargin
              (thetaCuspSingleAtomReflectionScale 1 u)
              (thetaCuspSingleAtomReflectionDefect t)
              (2 * Real.sinh (2 * t)) +
            thetaCuspReflectedLikelihoodCumulantRiccatiMargin u t)
    (hseam : ∀ u x y : ℝ, 0 ≤ u → u < x + y → 0 < x → 0 < y →
      thetaCuspReflectedSourceCorrelationAngle u (x + y) ≤
        thetaCuspReflectedSourceCorrelationAngle u x +
          thetaCuspReflectedSourceCorrelationAngle u y) :
    ThetaCuspCenterMixedNearCenterThreePointWall := by
  apply thetaCuspCenterMixedNearCenterThreePointWall_of_sourceAngle_subadditive
  intro u x y hx hy
  let v := |u|
  have hv : 0 ≤ v := abs_nonneg u
  have hangleV :
      thetaCuspReflectedSourceCorrelationAngle v (x + y) ≤
        thetaCuspReflectedSourceCorrelationAngle v x +
          thetaCuspReflectedSourceCorrelationAngle v y := by
    by_cases hxyv : x + y ≤ v
    · exact
        thetaCuspReflectedSourceCorrelationAngle_subadditive_of_crossDomination
          hx.le hy.le hxyv (hdomination v x y hx.le hy.le hxyv)
    · exact hseam v x y hv (lt_of_not_ge hxyv) hx hy
  rcases le_total 0 u with hu | hu
  · simpa only [v, abs_of_nonneg hu] using hangleV
  · have habs : v = -u := by
      simp only [v, abs_of_nonpos hu]
    rw [habs] at hangleV
    simpa only [thetaCuspReflectedSourceCorrelationAngle_neg_center] using hangleV

/-- **Legacy seam-only connector.**  Same-half-line and seam-crossing angle laws are now both
unconditional; this theorem remains as a compatibility interface. -/
theorem thetaCuspCenterMixedNearCenterThreePointWall_of_seamAngle
    (hseam : ∀ u x y : ℝ, 0 ≤ u → u < x + y → 0 < x → 0 < y →
      thetaCuspReflectedSourceCorrelationAngle u (x + y) ≤
        thetaCuspReflectedSourceCorrelationAngle u x +
          thetaCuspReflectedSourceCorrelationAngle u y) :
    ThetaCuspCenterMixedNearCenterThreePointWall := by
  apply thetaCuspCenterMixedNearCenterThreePointWall_of_sourceAngle_subadditive
  intro u x y hx hy
  let v := |u|
  have hv : 0 ≤ v := abs_nonneg u
  have hangleV :
      thetaCuspReflectedSourceCorrelationAngle v (x + y) ≤
        thetaCuspReflectedSourceCorrelationAngle v x +
          thetaCuspReflectedSourceCorrelationAngle v y := by
    by_cases hxyv : x + y ≤ v
    · exact thetaCuspReflectedSourceCorrelationAngle_subadditive
        hx.le hy.le hxyv
    · exact hseam v x y hv (lt_of_not_ge hxyv) hx hy
  rcases le_total 0 u with hu | hu
  · simpa only [v, abs_of_nonneg hu] using hangleV
  · have habs : v = -u := by
      simp only [v, abs_of_nonpos hu]
    rw [habs] at hangleV
    simpa only [thetaCuspReflectedSourceCorrelationAngle_neg_center] using hangleV

end

end RHTower
