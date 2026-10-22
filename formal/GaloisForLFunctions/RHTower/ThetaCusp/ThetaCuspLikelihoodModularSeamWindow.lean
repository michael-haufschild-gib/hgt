import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspLikelihoodModularSeam
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspLikelihoodRayBoundaryResidue

/-!
# Exact source window for theta likelihood modular scattering

The zero of the first theta atom is the exact boundary of the positive likelihood-coordinate
domain.  Reflecting this boundary gives the maximal positive source interval on which both
modular channels are represented by the same positive spectral measure.

This discharges the repeated negative-coordinate positivity premise in the modular-seam laws.
The source point `x = 1 / 4` lies strictly inside this interval by the elementary exponential
tangent bound and `π > 3`.
-/

open Real MeasureTheory Set

namespace RHTower

noncomputable section

/-- Positive radius of the two-sided likelihood-coordinate source window. -/
def thetaCuspLikelihoodSeamRadius : ℝ :=
  -thetaCuspLikelihoodBoundaryPoint

/-- The explicit boundary point is the exact positivity threshold of the likelihood coordinate. -/
theorem thetaCuspLikelihoodCoordinate_pos_iff_boundaryPoint_lt (x : ℝ) :
    0 < thetaCuspLikelihoodCoordinate x ↔
      thetaCuspLikelihoodBoundaryPoint < x := by
  have hc : 0 < 3 / (2 * Real.pi) := by positivity
  have hs : 0 < Real.sqrt (3 / (2 * Real.pi)) := Real.sqrt_pos.2 hc
  rw [thetaCuspLikelihoodBoundaryPoint, Real.log_lt_iff_lt_exp hs]
  constructor
  · intro h
    apply (Real.sqrt_lt' (Real.exp_pos x)).2
    unfold thetaCuspLikelihoodCoordinate at h
    apply (div_lt_iff₀ (show 0 < 2 * Real.pi by positivity)).2
    nlinarith [Real.pi_pos]
  · intro h
    have hsq : 3 / (2 * Real.pi) < Real.exp x ^ (2 : ℕ) :=
      (Real.sqrt_lt' (Real.exp_pos x)).1 h
    unfold thetaCuspLikelihoodCoordinate
    have hscaled :=
      (div_lt_iff₀ (show 0 < 2 * Real.pi by positivity)).1 hsq
    nlinarith [Real.pi_pos]

/-- The first-atom boundary lies strictly on the negative source half-line. -/
theorem thetaCuspLikelihoodBoundaryPoint_neg :
    thetaCuspLikelihoodBoundaryPoint < 0 := by
  exact (thetaCuspLikelihoodCoordinate_pos_iff_boundaryPoint_lt 0).mp
    (thetaCuspLikelihoodCoordinate_pos le_rfl)

/-- The reflected modular-seam radius is strictly positive. -/
theorem thetaCuspLikelihoodSeamRadius_pos :
    0 < thetaCuspLikelihoodSeamRadius := by
  unfold thetaCuspLikelihoodSeamRadius
  linarith [thetaCuspLikelihoodBoundaryPoint_neg]

/-- Exact source-domain characterization for positivity of the reflected likelihood coordinate. -/
theorem thetaCuspLikelihoodCoordinate_neg_pos_iff_lt_seamRadius (x : ℝ) :
    0 < thetaCuspLikelihoodCoordinate (-x) ↔
      x < thetaCuspLikelihoodSeamRadius := by
  rw [thetaCuspLikelihoodCoordinate_pos_iff_boundaryPoint_lt]
  unfold thetaCuspLikelihoodSeamRadius
  constructor
  · intro h
    linarith
  · intro h
    linarith

/-- Source atom law at the explicit zero-likelihood boundary point. -/
theorem thetaCuspSourceTerm_boundaryPoint_eq_desingularizer_mul_likelihoodRayWeight
    (n : ℕ) :
    thetaCuspSourceTerm thetaCuspLikelihoodBoundaryPoint n =
      thetaCuspLikelihoodBoundaryDesingularizer thetaCuspLikelihoodBoundaryPoint *
        thetaCuspLikelihoodRayWeight n :=
  thetaCuspSourceTerm_eq_desingularizer_mul_likelihoodRayWeight
    thetaCuspLikelihoodCoordinate_boundaryPoint n

/-- Exact completed-source value at the explicit zero-likelihood boundary point. -/
theorem thetaCuspFullSource_boundaryPoint_eq_likelihoodRayBoundaryResidue :
    thetaCuspFullSource thetaCuspLikelihoodBoundaryPoint =
      thetaCuspLikelihoodBoundaryDesingularizer thetaCuspLikelihoodBoundaryPoint *
        thetaCuspLikelihoodRayBoundaryResidue :=
  thetaCuspFullSource_eq_desingularizer_mul_likelihoodRayBoundaryResidue
    thetaCuspLikelihoodCoordinate_boundaryPoint

/-- The completed theta source is strictly positive at its explicit likelihood boundary. -/
theorem thetaCuspFullSource_boundaryPoint_pos :
    0 < thetaCuspFullSource thetaCuspLikelihoodBoundaryPoint :=
  thetaCuspFullSource_pos_of_likelihoodCoordinate_eq_zero
    thetaCuspLikelihoodCoordinate_boundaryPoint

/-- Exact partition scattering throughout the source-certified modular-seam window. -/
theorem thetaCuspLikelihoodPartition_modular_scattering_on_window
    {x : ℝ} (hx : 0 < x) (hxr : x < thetaCuspLikelihoodSeamRadius) :
    thetaCuspLikelihoodPartition (thetaCuspLikelihoodCoordinate x) =
      thetaCuspLikelihoodSeamScattering x *
        thetaCuspLikelihoodPartition (thetaCuspLikelihoodCoordinate (-x)) := by
  exact thetaCuspLikelihoodPartition_modular_scattering
    (thetaCuspLikelihoodCoordinate_pos hx.le)
    ((thetaCuspLikelihoodCoordinate_neg_pos_iff_lt_seamRadius x).2 hxr)

/-- Reciprocal scattering throughout the source-certified modular-seam window. -/
theorem thetaCuspLikelihoodSeamScattering_mul_reflection_on_window
    {x : ℝ} (hx : 0 < x) (hxr : x < thetaCuspLikelihoodSeamRadius) :
    thetaCuspLikelihoodSeamScattering x *
        thetaCuspLikelihoodSeamScattering (-x) = 1 := by
  exact thetaCuspLikelihoodSeamScattering_mul_reflection
    (thetaCuspLikelihoodCoordinate_pos hx.le)
    ((thetaCuspLikelihoodCoordinate_neg_pos_iff_lt_seamRadius x).2 hxr)

/-- First-atom reflection ordering throughout the exact modular-seam window. -/
theorem thetaCuspFirstAtom_reflected_lt_on_window
    {x : ℝ} (hx : 0 < x) (hxr : x < thetaCuspLikelihoodSeamRadius) :
    thetaCuspSourceTerm (-x) 1 < thetaCuspSourceTerm x 1 := by
  exact thetaCuspFirstAtom_reflected_lt_of_likelihoodCoordinate_neg_pos hx
    ((thetaCuspLikelihoodCoordinate_neg_pos_iff_lt_seamRadius x).2 hxr)

/-- The source scattering multiplier is a strict contraction on the exact seam window. -/
theorem thetaCuspLikelihoodSeamScattering_mem_Ioo_on_window
    {x : ℝ} (hx : 0 < x) (hxr : x < thetaCuspLikelihoodSeamRadius) :
    thetaCuspLikelihoodSeamScattering x ∈ Set.Ioo 0 1 := by
  exact thetaCuspLikelihoodSeamScattering_mem_Ioo hx
    ((thetaCuspLikelihoodCoordinate_neg_pos_iff_lt_seamRadius x).2 hxr)

/-- Reflected channel masses agree throughout the exact modular-seam window. -/
theorem integral_thetaCuspLikelihoodSeamChannel_reflection_on_window
    {x : ℝ} (hx : 0 < x) (hxr : x < thetaCuspLikelihoodSeamRadius) :
    (∫ t : ℝ, thetaCuspLikelihoodSeamChannel x t
        ∂thetaCuspLikelihoodSeamMeasure) =
      ∫ t : ℝ, thetaCuspLikelihoodSeamChannel (-x) t
        ∂thetaCuspLikelihoodSeamMeasure := by
  exact integral_thetaCuspLikelihoodSeamChannel_reflection
    (thetaCuspLikelihoodCoordinate_pos hx.le)
    ((thetaCuspLikelihoodCoordinate_neg_pos_iff_lt_seamRadius x).2 hxr)

/-- Reflected channels cross at a positive spectral coordinate on the exact seam window. -/
theorem thetaCuspLikelihoodSeamCrossing_pos_on_window
    {x : ℝ} (hx : 0 < x) (hxr : x < thetaCuspLikelihoodSeamRadius) :
    0 < thetaCuspLikelihoodSeamCrossing x := by
  exact thetaCuspLikelihoodSeamCrossing_pos hx
    ((thetaCuspLikelihoodCoordinate_neg_pos_iff_lt_seamRadius x).2 hxr)

/-- Exact log-partition secant law throughout the source-certified seam window. -/
theorem thetaCuspLikelihoodSeamCrossing_eq_logPartition_secant_on_window
    {x : ℝ} (hx : 0 < x) (hxr : x < thetaCuspLikelihoodSeamRadius) :
    thetaCuspLikelihoodSeamCrossing x =
      (Real.log (thetaCuspLikelihoodPartition
          (thetaCuspLikelihoodCoordinate (-x))) -
        Real.log (thetaCuspLikelihoodPartition
          (thetaCuspLikelihoodCoordinate x))) /
        (thetaCuspLikelihoodCoordinate x -
          thetaCuspLikelihoodCoordinate (-x)) := by
  exact thetaCuspLikelihoodSeamCrossing_eq_logPartition_secant hx
    ((thetaCuspLikelihoodCoordinate_neg_pos_iff_lt_seamRadius x).2 hxr)

/-- Exact channel reflection law throughout the source-certified seam window. -/
theorem thetaCuspLikelihoodSeamChannel_reflection_eq_on_window
    {x : ℝ} (hx : 0 < x) (hxr : x < thetaCuspLikelihoodSeamRadius) (t : ℝ) :
    thetaCuspLikelihoodSeamChannel x t =
      thetaCuspLikelihoodSeamChannel (-x) t *
        Real.exp ((thetaCuspLikelihoodCoordinate x -
          thetaCuspLikelihoodCoordinate (-x)) *
            (thetaCuspLikelihoodSeamCrossing x - t)) := by
  exact thetaCuspLikelihoodSeamChannel_reflection_eq hx
    ((thetaCuspLikelihoodCoordinate_neg_pos_iff_lt_seamRadius x).2 hxr) t

/-- Single-crossing classification throughout the source-certified seam window. -/
theorem thetaCuspLikelihoodSeamChannel_reflection_lt_iff_on_window
    {x : ℝ} (hx : 0 < x) (hxr : x < thetaCuspLikelihoodSeamRadius) (t : ℝ) :
    thetaCuspLikelihoodSeamChannel (-x) t <
        thetaCuspLikelihoodSeamChannel x t ↔
      t < thetaCuspLikelihoodSeamCrossing x := by
  exact thetaCuspLikelihoodSeamChannel_reflection_lt_iff hx
    ((thetaCuspLikelihoodCoordinate_neg_pos_iff_lt_seamRadius x).2 hxr) t

/-- Source proof that the reflected likelihood coordinate remains positive at `x = 1 / 4`. -/
theorem thetaCuspLikelihoodCoordinate_neg_quarter_pos :
    0 < thetaCuspLikelihoodCoordinate (-(1 / 4 : ℝ)) := by
  have hexpLower := Real.add_one_le_exp (-(1 / 2 : ℝ))
  have hexpSquare :
      Real.exp (-(1 / 4 : ℝ)) ^ (2 : ℕ) = Real.exp (-(1 / 2 : ℝ)) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  unfold thetaCuspLikelihoodCoordinate
  rw [hexpSquare]
  nlinarith [Real.pi_gt_three, Real.pi_pos]

/-- The source point `1 / 4` is strictly inside the maximal modular-seam window. -/
theorem quarter_lt_thetaCuspLikelihoodSeamRadius :
    (1 / 4 : ℝ) < thetaCuspLikelihoodSeamRadius :=
  (thetaCuspLikelihoodCoordinate_neg_pos_iff_lt_seamRadius (1 / 4)).1
    thetaCuspLikelihoodCoordinate_neg_quarter_pos

/-- Unconditional strict scattering contraction at the quarter source point. -/
theorem thetaCuspLikelihoodSeamScattering_quarter_mem_Ioo :
    thetaCuspLikelihoodSeamScattering (1 / 4) ∈ Set.Ioo 0 1 :=
  thetaCuspLikelihoodSeamScattering_mem_Ioo_on_window
    (by norm_num) quarter_lt_thetaCuspLikelihoodSeamRadius

/-- Unconditional positive channel crossing at the quarter source point. -/
theorem thetaCuspLikelihoodSeamCrossing_quarter_pos :
    0 < thetaCuspLikelihoodSeamCrossing (1 / 4) :=
  thetaCuspLikelihoodSeamCrossing_pos_on_window
    (by norm_num) quarter_lt_thetaCuspLikelihoodSeamRadius

/-- Unconditional single-crossing law at the quarter source point. -/
theorem thetaCuspLikelihoodSeamChannel_quarter_reflection_lt_iff (t : ℝ) :
    thetaCuspLikelihoodSeamChannel (-(1 / 4 : ℝ)) t <
        thetaCuspLikelihoodSeamChannel (1 / 4) t ↔
      t < thetaCuspLikelihoodSeamCrossing (1 / 4) :=
  thetaCuspLikelihoodSeamChannel_reflection_lt_iff_on_window
    (by norm_num) quarter_lt_thetaCuspLikelihoodSeamRadius t

end

end RHTower
