import GaloisForLFunctions.RHTower.CCMUnitRieszHankelBoundaryPulse

/-!
# Four-unit pole slack cannot pay the unit-Riesz Schur debt

The FU--UR curvature reporter gives an actual fast-minus-slow boundary covariance.  Its scalar
four-unit pulse lies below the incoming pole trace by an exact square.  This file tests whether all
of that unused scalar budget can repair the operator covariance by one additional rank-one channel
in the fast/slow span.

After four-unit normalization, the slow negative coefficient is
`B(u)=4(1-exp(-u/2))`, whereas the entire pole slack is
`S(u)=4(1-exp(-u/2))^(2 : ℕ)`.  Thus `S(u)<B(u)` for every positive aperture.  Any rank-one feature with
slow coordinate normalized to one has form `slow-kappa*fast`; a two-point vector cancelling its
fast coordinate sees quadratic energy `(delta-B(u))*y^(2 : ℕ)`.  Consequently positivity forces
`delta>=B(u)`, independently of `kappa`, and no amplitude paid from `0<=delta<=S(u)` can work.

The closed one-channel theorem has no proof premise: aperture, separation, and budget are encoded as
subtypes.  A stronger final theorem then allows an arbitrary symmetric background on the complete
fast/slow span.  Fast diagonal and mixed coefficients are unrestricted; if its slow diagonal is
funded by pole slack, an explicit fast-null two-point vector still has negative energy.  Hence rank
and fast coupling do not repair the budget deficit.  Nonlocal features outside this reporter span
and additional literal completed-source covariance remain open.
-/

open Set MeasureTheory Filter Topology

noncomputable section

namespace GaloisForLFunctions.RHTower

open _root_.RHTower

/-- Fast output-cutoff coefficient in the corpus four-unit normalization. -/
def unitRieszFourUnitFastBoundaryCoefficient (u : ℝ) : ℝ :=
  (256 / 3) * unitRieszFastBoundaryCoefficient u

/-- Slow output-cutoff coefficient in the corpus four-unit normalization. -/
def unitRieszFourUnitSlowBoundaryCoefficient (u : ℝ) : ℝ :=
  (256 / 3) * unitRieszSlowBoundaryCoefficient u

/-- Fast exponential boundary feature. -/
def unitRieszFastBoundaryFeature (y : ℝ) : ℝ := Real.exp (-y / 2)

/-- Slow exponential boundary feature. -/
def unitRieszSlowBoundaryFeature (y : ℝ) : ℝ := Real.exp (-y / 4)

/-- Actual FU--UR fast-minus-slow covariance after four-unit normalization. -/
def unitRieszFourUnitBoundaryCovarianceCore (u y z : ℝ) : ℝ :=
  unitRieszFourUnitFastBoundaryCoefficient u *
      unitRieszFastBoundaryFeature y * unitRieszFastBoundaryFeature z -
    unitRieszFourUnitSlowBoundaryCoefficient u *
      unitRieszSlowBoundaryFeature y * unitRieszSlowBoundaryFeature z

/-- Entire scalar budget left between incoming pole trace and normalized FU--UR pulse. -/
def unitRieszFourUnitPoleSlack (u : ℝ) : ℝ :=
  4 * (1 - Real.exp (-u / 2)) ^ (2 : ℕ)

/-- One positive rank-one completion in the fast/slow span, normalized to slow coordinate one. -/
def unitRieszOneChannelCompletedBoundaryCore
    (u κ δ y z : ℝ) : ℝ :=
  unitRieszFourUnitBoundaryCovarianceCore u y z +
    δ * (unitRieszSlowBoundaryFeature y - κ * unitRieszFastBoundaryFeature y) *
      (unitRieszSlowBoundaryFeature z - κ * unitRieszFastBoundaryFeature z)

/-- Two-point compression of the normalized one-channel completion. -/
def unitRieszOneChannelCompletedBoundaryMatrix
    (u κ δ L : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![unitRieszOneChannelCompletedBoundaryCore u κ δ 0 0,
      unitRieszOneChannelCompletedBoundaryCore u κ δ 0 L;
    unitRieszOneChannelCompletedBoundaryCore u κ δ L 0,
      unitRieszOneChannelCompletedBoundaryCore u κ δ L L]

/-- Arbitrary symmetric background on the full fast/slow feature span. -/
def unitRieszSpanLocalCompletedBoundaryCore
    (u p q r y z : ℝ) : ℝ :=
  unitRieszFourUnitBoundaryCovarianceCore u y z +
    p * unitRieszFastBoundaryFeature y * unitRieszFastBoundaryFeature z +
    q * (unitRieszFastBoundaryFeature y * unitRieszSlowBoundaryFeature z +
      unitRieszSlowBoundaryFeature y * unitRieszFastBoundaryFeature z) +
    r * unitRieszSlowBoundaryFeature y * unitRieszSlowBoundaryFeature z

/-- Two-point compression of an arbitrary fast/slow-span background completion. -/
def unitRieszSpanLocalCompletedBoundaryMatrix
    (u p q r L : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![unitRieszSpanLocalCompletedBoundaryCore u p q r 0 0,
      unitRieszSpanLocalCompletedBoundaryCore u p q r 0 L;
    unitRieszSpanLocalCompletedBoundaryCore u p q r L 0,
      unitRieszSpanLocalCompletedBoundaryCore u p q r L L]

/-- Two-point coefficient vector that cancels the fast feature exactly. -/
def unitRieszFastNullTwoPointVector (L : ℝ) : Fin 2 → ℝ :=
  ![unitRieszFastBoundaryFeature L, -1]

theorem unitRieszFourUnitFastBoundaryCoefficient_eq (u : ℝ) :
    unitRieszFourUnitFastBoundaryCoefficient u =
      8 * (1 - Real.exp (-u)) := by
  unfold unitRieszFourUnitFastBoundaryCoefficient unitRieszFastBoundaryCoefficient
  ring

theorem unitRieszFourUnitSlowBoundaryCoefficient_eq (u : ℝ) :
    unitRieszFourUnitSlowBoundaryCoefficient u =
      4 * (1 - Real.exp (-u / 2)) := by
  unfold unitRieszFourUnitSlowBoundaryCoefficient unitRieszSlowBoundaryCoefficient
  ring

/-- The new covariance is exactly the parent source covariance, with no changed normalization. -/
theorem unitRieszFourUnitBoundaryCovarianceCore_eq_source
    (u y z : ℝ) :
    unitRieszFourUnitBoundaryCovarianceCore u y z =
      (256 / 3) * unitRieszBoundaryCovarianceCore u y z := by
  have hf : unitRieszFastBoundaryFeature y * unitRieszFastBoundaryFeature z =
      Real.exp (-(y + z) / 2) := by
    rw [unitRieszFastBoundaryFeature, unitRieszFastBoundaryFeature, ← Real.exp_add]
    congr 1
    ring
  have hs : unitRieszSlowBoundaryFeature y * unitRieszSlowBoundaryFeature z =
      Real.exp (-(y + z) / 4) := by
    rw [unitRieszSlowBoundaryFeature, unitRieszSlowBoundaryFeature, ← Real.exp_add]
    congr 1
    ring
  rw [unitRieszFourUnitBoundaryCovarianceCore]
  calc
    unitRieszFourUnitFastBoundaryCoefficient u *
          unitRieszFastBoundaryFeature y * unitRieszFastBoundaryFeature z -
        unitRieszFourUnitSlowBoundaryCoefficient u *
          unitRieszSlowBoundaryFeature y * unitRieszSlowBoundaryFeature z =
        unitRieszFourUnitFastBoundaryCoefficient u *
            (unitRieszFastBoundaryFeature y * unitRieszFastBoundaryFeature z) -
          unitRieszFourUnitSlowBoundaryCoefficient u *
            (unitRieszSlowBoundaryFeature y * unitRieszSlowBoundaryFeature z) := by ring
    _ = unitRieszFourUnitFastBoundaryCoefficient u * Real.exp (-(y + z) / 2) -
          unitRieszFourUnitSlowBoundaryCoefficient u * Real.exp (-(y + z) / 4) := by
      rw [hf, hs]
    _ = (256 / 3) * unitRieszBoundaryCovarianceCore u y z := by
      unfold unitRieszFourUnitFastBoundaryCoefficient
        unitRieszFourUnitSlowBoundaryCoefficient unitRieszBoundaryCovarianceCore
      ring

/-- The budget is the literal pole-trace difference already selected by the parent module. -/
theorem unitRieszFourUnitPoleSlack_eq_trace_difference
    {u : ℝ} (hu : 0 < u) :
    unitRieszFourUnitPoleSlack u =
      boundaryRelativeTrace polePacketProfile u -
        unitRieszFourUnitBoundaryPulse u := by
  rw [poleBoundaryTrace_sub_unitRieszFourUnitBoundaryPulse hu]
  rfl

/-- At every physical aperture, full scalar pole slack is smaller than slow covariance debt. -/
theorem unitRieszFourUnitPoleSlack_lt_slowBoundaryCoefficient
    {u : ℝ} (hu : 0 < u) :
    unitRieszFourUnitPoleSlack u <
      unitRieszFourUnitSlowBoundaryCoefficient u := by
  rw [unitRieszFourUnitSlowBoundaryCoefficient_eq]
  unfold unitRieszFourUnitPoleSlack
  have hrpos : 0 < Real.exp (-u / 2) := Real.exp_pos _
  have hrlt : Real.exp (-u / 2) < 1 :=
    Real.exp_lt_one_iff.mpr (by linarith)
  nlinarith [mul_pos (sub_pos.mpr hrlt) hrpos]

/-- Exact fraction law: pole slack pays only `1-exp(-u/2)` of the slow-channel mass. -/
theorem unitRieszFourUnitPoleSlack_eq_fraction_slowBoundaryCoefficient
    (u : ℝ) :
    unitRieszFourUnitPoleSlack u =
      (1 - Real.exp (-u / 2)) *
        unitRieszFourUnitSlowBoundaryCoefficient u := by
  rw [unitRieszFourUnitSlowBoundaryCoefficient_eq]
  unfold unitRieszFourUnitPoleSlack
  ring

/-- Exact determinant: all fast admixtures enter only through the additional nonpositive tax. -/
theorem unitRieszOneChannelCompletedBoundaryMatrix_det
    (u κ δ L : ℝ) :
    (unitRieszOneChannelCompletedBoundaryMatrix u κ δ L).det =
      (unitRieszFourUnitFastBoundaryCoefficient u *
          (δ - unitRieszFourUnitSlowBoundaryCoefficient u) -
        δ * unitRieszFourUnitSlowBoundaryCoefficient u * κ ^ (2 : ℕ)) *
      (unitRieszSlowBoundaryFeature L - unitRieszFastBoundaryFeature L) ^ (2 : ℕ) := by
  rw [unitRieszOneChannelCompletedBoundaryMatrix, Matrix.det_fin_two_of]
  simp only [unitRieszOneChannelCompletedBoundaryCore,
    unitRieszFourUnitBoundaryCovarianceCore,
    unitRieszFastBoundaryFeature, unitRieszSlowBoundaryFeature,
    neg_zero, zero_div, Real.exp_zero]
  ring

/-- Exact surviving energy after cancelling the fast channel.  Every fast diagonal and mixed
background coefficient disappears; only slow injected mass minus literal slow debt remains. -/
theorem unitRieszFastNullTwoPointVector_energy
    (u p q r L : ℝ) :
    dotProduct (star (unitRieszFastNullTwoPointVector L))
        ((unitRieszSpanLocalCompletedBoundaryMatrix u p q r L).mulVec
          (unitRieszFastNullTwoPointVector L)) =
      (r - unitRieszFourUnitSlowBoundaryCoefficient u) *
        (unitRieszSlowBoundaryFeature L - unitRieszFastBoundaryFeature L) ^ (2 : ℕ) := by
  norm_num [unitRieszFastNullTwoPointVector,
    unitRieszSpanLocalCompletedBoundaryMatrix,
    unitRieszSpanLocalCompletedBoundaryCore,
    unitRieszFourUnitBoundaryCovarianceCore,
    unitRieszFastBoundaryFeature, unitRieszSlowBoundaryFeature,
    dotProduct, Matrix.mulVec, Fin.sum_univ_two]
  ring

/-- Any nonnegative completion amplitude below full slow mass leaves a negative two-point minor. -/
theorem unitRieszOneChannelCompletedBoundaryMatrix_det_neg_of_lt_slow
    {u κ δ L : ℝ} (hu : 0 < u) (hL : 0 < L)
    (hδ : 0 ≤ δ)
    (hδslow : δ < unitRieszFourUnitSlowBoundaryCoefficient u) :
    (unitRieszOneChannelCompletedBoundaryMatrix u κ δ L).det < 0 := by
  rw [unitRieszOneChannelCompletedBoundaryMatrix_det]
  have hA : 0 < unitRieszFourUnitFastBoundaryCoefficient u := by
    unfold unitRieszFourUnitFastBoundaryCoefficient
    exact mul_pos (by norm_num) (unitRieszFastBoundaryCoefficient_pos hu)
  have hB : 0 < unitRieszFourUnitSlowBoundaryCoefficient u := by
    unfold unitRieszFourUnitSlowBoundaryCoefficient
    exact mul_pos (by norm_num) (unitRieszSlowBoundaryCoefficient_pos hu)
  have hfirst :
      unitRieszFourUnitFastBoundaryCoefficient u *
          (δ - unitRieszFourUnitSlowBoundaryCoefficient u) < 0 :=
    mul_neg_of_pos_of_neg hA (sub_neg.mpr hδslow)
  have hsecond :
      0 ≤ δ * unitRieszFourUnitSlowBoundaryCoefficient u * κ ^ (2 : ℕ) :=
    mul_nonneg (mul_nonneg hδ hB.le) (sq_nonneg κ)
  have hcoeff :
      unitRieszFourUnitFastBoundaryCoefficient u *
          (δ - unitRieszFourUnitSlowBoundaryCoefficient u) -
        δ * unitRieszFourUnitSlowBoundaryCoefficient u * κ ^ (2 : ℕ) < 0 := by
    linarith
  have hfeature :
      0 < (unitRieszSlowBoundaryFeature L -
        unitRieszFastBoundaryFeature L) ^ (2 : ℕ) := by
    apply sq_pos_of_pos
    unfold unitRieszSlowBoundaryFeature unitRieszFastBoundaryFeature
    exact sub_pos.mpr (Real.exp_lt_exp.mpr (by linarith))
  exact mul_neg_of_neg_of_pos hcoeff hfeature

/-- Full pole slack never repairs even one separated two-point compression. -/
theorem unitRieszOneChannelCompletedBoundaryMatrix_not_posSemidef_of_le_poleSlack
    {u κ δ L : ℝ} (hu : 0 < u) (hL : 0 < L)
    (hδ : 0 ≤ δ) (hbudget : δ ≤ unitRieszFourUnitPoleSlack u) :
    ¬(unitRieszOneChannelCompletedBoundaryMatrix u κ δ L).PosSemidef := by
  intro hpsd
  have hdet := hpsd.det_nonneg
  have hδslow : δ < unitRieszFourUnitSlowBoundaryCoefficient u :=
    lt_of_le_of_lt hbudget (unitRieszFourUnitPoleSlack_lt_slowBoundaryCoefficient hu)
  have hneg :=
    unitRieszOneChannelCompletedBoundaryMatrix_det_neg_of_lt_slow
      (κ := κ) hu hL hδ hδslow
  exact (not_le_of_gt hneg) hdet

/-- Arbitrary fast diagonal and mixed coupling cannot discount the literal slow-channel debt. -/
theorem unitRieszSpanLocalCompletedBoundaryMatrix_not_posSemidef_of_lt_slow
    {u p q r L : ℝ} (hL : 0 < L)
    (hrslow : r < unitRieszFourUnitSlowBoundaryCoefficient u) :
    ¬(unitRieszSpanLocalCompletedBoundaryMatrix u p q r L).PosSemidef := by
  intro hpsd
  have henergy :=
    (Matrix.posSemidef_iff_dotProduct_mulVec.mp hpsd).2
      (unitRieszFastNullTwoPointVector L)
  rw [unitRieszFastNullTwoPointVector_energy] at henergy
  have hfeature :
      0 < (unitRieszSlowBoundaryFeature L -
        unitRieszFastBoundaryFeature L) ^ (2 : ℕ) := by
    apply sq_pos_of_pos
    unfold unitRieszSlowBoundaryFeature unitRieszFastBoundaryFeature
    exact sub_pos.mpr (Real.exp_lt_exp.mpr (by linarith))
  nlinarith

/-- Typed physical domain for positive aperture or positive sample separation. -/
abbrev UnitRieszPositiveAperture := {u : ℝ // 0 < u}

/-- All nonnegative one-channel amplitudes fundable by the literal pole slack. -/
def UnitRieszPoleSlackBudget (u : UnitRieszPositiveAperture) :=
  {δ : ℝ // 0 ≤ δ ∧ δ ≤ unitRieszFourUnitPoleSlack u}

/-- Arbitrary fast diagonal and coupling, with slow diagonal limited only by literal pole slack. -/
def UnitRieszSpanLocalPoleSlackBackground
    (u : UnitRieszPositiveAperture) :=
  ℝ × ℝ × UnitRieszPoleSlackBudget u

/-- All nonnegative amplitudes that do make one separated compression positive semidefinite. -/
def UnitRieszOneChannelPSDCompletionAmplitude
    (u L : UnitRieszPositiveAperture) (κ : ℝ) :=
  {δ : ℝ // 0 ≤ δ ∧
    (unitRieszOneChannelCompletedBoundaryMatrix u κ δ L).PosSemidef}

/-- Every normalized one-channel positive repair injects at least the full slow-channel mass. -/
theorem unitRieszSlowBoundaryCoefficient_le_psdCompletionAmplitude
    (u L : UnitRieszPositiveAperture) (κ : ℝ)
    (δ : UnitRieszOneChannelPSDCompletionAmplitude u L κ) :
    unitRieszFourUnitSlowBoundaryCoefficient u ≤ δ.1 := by
  by_contra h
  have hlt : δ.1 < unitRieszFourUnitSlowBoundaryCoefficient u :=
    lt_of_not_ge h
  have hneg :=
    unitRieszOneChannelCompletedBoundaryMatrix_det_neg_of_lt_slow
      (κ := κ) u.property L.property δ.property.1 hlt
  have hdet := δ.property.2.det_nonneg
  exact (not_le_of_gt hneg) hdet

/-- Closed source-specific no-go: no proof premise remains outside the typed physical domain. -/
theorem unitRieszPoleSlack_oneChannelCompletion_unconditionally_fails
    (u L : UnitRieszPositiveAperture) (κ : ℝ)
    (δ : UnitRieszPoleSlackBudget u) :
    ¬(unitRieszOneChannelCompletedBoundaryMatrix u κ δ.1 L).PosSemidef :=
  unitRieszOneChannelCompletedBoundaryMatrix_not_posSemidef_of_le_poleSlack
    u.property L.property δ.property.1 δ.property.2

/-- Closed all-rank span-local no-go: no fast diagonal, mixed coupling, or factorization rank can
repair the actual covariance when available slow mass is bounded by the full pole slack. -/
theorem unitRieszPoleSlack_spanLocalCompletion_unconditionally_fails
    (u L : UnitRieszPositiveAperture)
    (background : UnitRieszSpanLocalPoleSlackBackground u) :
    ¬(unitRieszSpanLocalCompletedBoundaryMatrix u
        background.1 background.2.1 background.2.2.1 L).PosSemidef := by
  apply unitRieszSpanLocalCompletedBoundaryMatrix_not_posSemidef_of_lt_slow
    L.property
  exact lt_of_le_of_lt background.2.2.property.2
    (unitRieszFourUnitPoleSlack_lt_slowBoundaryCoefficient u.property)

end GaloisForLFunctions.RHTower

end
