import GaloisForLFunctions.RHTower.XiGuinandWeilRectangularBottomEdge
import GaloisForLFunctions.RHTower.CCM.CCMRectangularDirectionalDerivative

/-!
# The sharp dyadic prime window as a corrected Xi bottom-edge slope

The normalized rectangular bottom edge splits into its honest von Mangoldt value and its
archimedean value.  After subtracting the archimedean term and restoring the elementary polar
square, its real part is exactly the existing rectangular prime--polar source coefficient.

Consequently the diagonal deformation which keeps the two-edge centre fixed and opens its width
reads the sharp dyadic von Mangoldt shell directly from a literal absolutely convergent
`XiC'/XiC` integral.  This is the value relation needed to move the remaining RH inequality from
the arithmetic source to the Guinand--Weil contour.
-/

open Complex Filter Set
open scoped Topology

noncomputable section

namespace RHTower

/-- Real corrected bottom-edge value: remove the Gamma edge and restore the polar square. -/
def rectangularCorrectedBottomXiValue (L a : ℝ) : ℝ :=
  (normalizedRectangularBottomXiContribution L a -
      normalizedRectangularBottomArchContribution L a).re +
    2 * rectangularEvenPolarFeature L a ^ (2 : ℕ)

/-- The corrected literal Xi bottom edge is exactly the finite rectangular prime--polar source. -/
theorem rectangularCorrectedBottomXiValue_eq_primePolarSource
    {L a : ℝ} (hL : 0 ≤ L) (ha : L ≤ a) :
    rectangularCorrectedBottomXiValue L a =
      rectangularPrimePolarSourceCoefficient L a := by
  rw [rectangularCorrectedBottomXiValue,
    normalizedRectangularBottomXiContribution_eq_prime_add_arch hL ha,
    rectangularPrimePolarSourceCoefficient]
  simp only [add_sub_cancel_right, mul_re, ofReal_re, ofReal_im]
  norm_num

/-- Exact closed-shell expansion of the dyadic corrected-bottom right slope. -/
theorem dyadicPrimePolarSourceDiagonalRightSlope_eq_closedShell (n : ℕ) :
    dyadicPrimePolarSourceDiagonalRightSlope n =
      8 * (Real.exp (Real.log 2 / 4) - Real.exp (-Real.log 2 / 4)) +
        4 * (1 - (Real.sqrt 2)⁻¹) * Real.sqrt n +
        4 * (Real.sqrt 2 - 1) / Real.sqrt n -
        2 * rectangularClosedPrimeShellValue
          (Real.log 2 / 2) (Real.log n) n := by
  rw [dyadicPrimePolarSourceDiagonalRightSlope,
    dyadicAdjacentBlockDiagonalRightSlope]
  ring

/-- The diagonal derivative of the corrected literal bottom edge reads the sharp dyadic shell.
The deformation keeps `a - L/2` fixed, so only the rectangular width opens. -/
theorem hasDerivWithinAt_dyadicCorrectedBottomXiValue_diagonal_logSample
    {n : ℕ} (hn : 4 ≤ n) :
    HasDerivWithinAt
      (fun t : ℝ =>
        rectangularCorrectedBottomXiValue (Real.log 2 / 2 + t)
          ((Real.log n + t) / 2))
      (dyadicPrimePolarSourceDiagonalRightSlope n) (Ici 0) 0 := by
  have hsource :=
    hasDerivWithinAt_dyadicPrimePolarSource_diagonal_logSample hn
  have hnreal : (0 : ℝ) < n := by positivity
  have hloglt : Real.log 2 < Real.log n :=
    Real.strictMonoOn_log (by norm_num) hnreal (by exact_mod_cast (show 2 < n by omega))
  have hsmallNhds : ∀ᶠ t in 𝓝 (0 : ℝ), t < Real.log n - Real.log 2 :=
    Iio_mem_nhds (sub_pos.mpr hloglt)
  have hsmall : ∀ᶠ t in 𝓝[Ici 0] (0 : ℝ),
      t < Real.log n - Real.log 2 :=
    Filter.Eventually.filter_mono nhdsWithin_le_nhds hsmallNhds
  have heq :
      (fun t : ℝ =>
        rectangularCorrectedBottomXiValue (Real.log 2 / 2 + t)
          ((Real.log n + t) / 2)) =ᶠ[𝓝[Ici 0] 0]
      (fun t : ℝ =>
        rectangularPrimePolarSourceCoefficient (Real.log 2 / 2 + t)
          ((Real.log n + t) / 2)) := by
    filter_upwards [hsmall, eventually_mem_nhdsWithin] with t ht htmem
    simp only [mem_Ici] at htmem
    apply rectangularCorrectedBottomXiValue_eq_primePolarSource
    · have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
      linarith
    · linarith
  apply hsource.congr_of_eventuallyEq heq
  apply rectangularCorrectedBottomXiValue_eq_primePolarSource
  · positivity
  · have hlogle : Real.log 2 ≤ Real.log n := hloglt.le
    linarith

/-- A lower bound for the corrected Xi bottom-edge slope directly gives the requested sharp
dyadic von Mangoldt upper bound.  The only endpoint discrepancy is a nonnegative lower-shell
atom, so no error constant is lost. -/
theorem dyadicWeightedPrimeWindow_upper_of_correctedBottomXiSlope_lower
    {n : ℕ} (hn : 4 ≤ n) (C epsilon d : ℝ)
    (hderiv : HasDerivWithinAt
      (fun t : ℝ =>
        rectangularCorrectedBottomXiValue (Real.log 2 / 2 + t)
          ((Real.log n + t) / 2)) d (Ici 0) 0)
    (hslope :
      8 * (Real.exp (Real.log 2 / 4) - Real.exp (-Real.log 2 / 4)) +
          4 * (Real.sqrt 2 - 1) / Real.sqrt n -
          2 * C * (n : ℝ) ^ epsilon ≤ d) :
    dyadicWeightedPrimeWindow n ≤
      2 * (1 - (Real.sqrt 2)⁻¹) * Real.sqrt n +
        C * (n : ℝ) ^ epsilon := by
  have hcanonical :=
    hasDerivWithinAt_dyadicCorrectedBottomXiValue_diagonal_logSample hn
  have hd : d = dyadicPrimePolarSourceDiagonalRightSlope n :=
    (hderiv.derivWithin (uniqueDiffWithinAt_Ici 0)).symm.trans
      (hcanonical.derivWithin (uniqueDiffWithinAt_Ici 0))
  rw [hd] at hslope
  exact dyadicWeightedPrimeWindow_upper_of_primePolarSourceDiagonalRightSlope_lower
    hn C epsilon hslope

end RHTower
