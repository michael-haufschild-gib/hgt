import GaloisForLFunctions.RHTower.XiShiftedArcsineVacuumRenormalizedSourceLaw
import GaloisForLFunctions.RHTower.XiShiftedCanonicalAdmissionAdaptiveArithmeticSourceDegreeConnection

/-!
# Pole-free arcsine-vacuum completed arithmetic source charge

The divergent Christoffel wall is a quotient artifact: it divides a regular completed arithmetic
source by the newborn admitted norm.  Subtracting the full arcsine vacuum *inside that source*,
before the division, gives a pole-free admission-sensitive charge.

At square mass the charge is literally the adaptive mixed rational--Gamma-minus-von-Mangoldt
`P^sharp` source minus the current newborn-norm vacuum.  It vanishes on every coordinate-dilated
arcsine tower and at fixed-degree shifted-Xi recession.  At an occupied strict frontier the
newborn norm is zero while the preceding adaptive source is strictly positive, so the charge
extends through the apparent pole with a finite positive value and a positive continuous germ.

No orientation map, fixed linear reporter, reflection aggregation, or numerical computation is
used.
-/

open Filter Matrix Polynomial Set Topology

namespace RHTower

noncomputable section

namespace XiShiftedCanonicalAdmission

/-- Covariant normalized source charge: literal relative arithmetic source minus the full
current-Christoffel arcsine vacuum.  Formation precedes scale division. -/
def arcsineVacuumRenormalizedRelativeArithmeticSource (w : ℝ) (n : ℕ) : ℝ :=
  relativeArithmeticSource w n -
    arcsineVacuumSourceCounterterm n * admissionChristoffelScaleSq w n

/-- Universal Jacobi-coordinate form of the pole-free source charge. -/
def arcsineVacuumRenormalizedJacobiCharge (s : ℕ → ℝ) (n : ℕ) : ℝ :=
  HTGeometry.adaptiveOrthoJacobiEnergy s n -
    16 * arcsineVacuumSourceCounterterm n * HTGeometry.monicOrthoBeta s (n + 1)

/-- Adjacent-degree innovation of the pole-free source charge. -/
def arcsineVacuumRenormalizedJacobiDegreeInnovation (s : ℕ → ℝ) (n : ℕ) : ℝ :=
  arcsineVacuumRenormalizedJacobiCharge s (n + 1) -
    arcsineVacuumRenormalizedJacobiCharge s n

/-- In a positive current chamber, the covariant source charge is current Jacobi energy minus the
full arcsine price carried by the current newborn edge. -/
theorem arcsineVacuumRenormalizedRelativeArithmeticSource_eq_jacobiCharge
    {w : ℝ} (hw : 1 < w) {n : ℕ} (hn : 0 < n)
    (hH : (HTGeometry.momentHankelMatrix
      (xiShiftedFarRightNormalizedMoment w) (n + 2)).PosDef) :
    arcsineVacuumRenormalizedRelativeArithmeticSource w n =
      arcsineVacuumRenormalizedJacobiCharge
        (xiShiftedFarRightNormalizedMoment w) n := by
  rw [arcsineVacuumRenormalizedRelativeArithmeticSource,
    relativeArithmeticSource_eq_adaptiveOrthoJacobiEnergy hw hn hH,
    admissionChristoffelScaleSq_eq_sixteen_mul_monicOrthoBeta hH]
  unfold arcsineVacuumRenormalizedJacobiCharge
  ring

/-- **Exact adjacent source-innovation law.**  Removing the Christoffel denominator converts
cross-degree transport into one signed Jacobi current.  In particular the newest edge enters with
coefficient `-(15n+20)`; full arcsine centering is not a positive action. -/
theorem arcsineVacuumRenormalizedJacobiDegreeInnovation_eq
    (s : ℕ → ℝ) (n : ℕ) :
    arcsineVacuumRenormalizedJacobiDegreeInnovation s n =
      (HTGeometry.monicOrthoAlpha s (n + 1) -
          HTGeometry.monicOrthoAlpha s n) *
        (∑ j ∈ Finset.range n, HTGeometry.monicOrthoAlpha s j) +
      HTGeometry.monicOrthoAlpha s n * HTGeometry.monicOrthoAlpha s (n + 1) -
      (n : ℝ) * HTGeometry.monicOrthoAlpha s n ^ (2 : ℕ) +
      (n + 2 : ℝ) * HTGeometry.monicOrthoAlpha s (n + 1) ^ (2 : ℕ) +
      (1 - (n : ℝ)) * HTGeometry.monicOrthoBeta s n +
      (16 * (n : ℝ) + 7) * HTGeometry.monicOrthoBeta s (n + 1) -
      (15 * (n : ℝ) + 20) * HTGeometry.monicOrthoBeta s (n + 2) := by
  unfold arcsineVacuumRenormalizedJacobiDegreeInnovation
    arcsineVacuumRenormalizedJacobiCharge
  unfold arcsineVacuumSourceCounterterm
  push_cast
  linear_combination adaptiveOrthoJacobiEnergy_succ_sub_eq s n

/-- Exact finite degree aggregation of source innovations.  No transfer weights remain after the
newborn denominator is removed. -/
theorem arcsineVacuumRenormalizedJacobiCharge_add_eq_sum_innovations
    (s : ℕ → ℝ) (n k : ℕ) :
    arcsineVacuumRenormalizedJacobiCharge s (n + k) =
      arcsineVacuumRenormalizedJacobiCharge s n +
        ∑ j ∈ Finset.range k,
          arcsineVacuumRenormalizedJacobiDegreeInnovation s (n + j) := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Finset.sum_range_succ]
      calc
        arcsineVacuumRenormalizedJacobiCharge s (n + (k + 1)) =
            arcsineVacuumRenormalizedJacobiCharge s (n + k) +
              arcsineVacuumRenormalizedJacobiDegreeInnovation s (n + k) := by
          unfold arcsineVacuumRenormalizedJacobiDegreeInnovation
          rw [Nat.add_succ]
          ring
        _ = (arcsineVacuumRenormalizedJacobiCharge s n +
              ∑ j ∈ Finset.range k,
                arcsineVacuumRenormalizedJacobiDegreeInnovation s (n + j)) +
              arcsineVacuumRenormalizedJacobiDegreeInnovation s (n + k) := by rw [ih]
        _ = arcsineVacuumRenormalizedJacobiCharge s n +
              (∑ j ∈ Finset.range k,
                arcsineVacuumRenormalizedJacobiDegreeInnovation s (n + j) +
              arcsineVacuumRenormalizedJacobiDegreeInnovation s (n + k)) := by ring

/-- Away from the newborn zero, covariant source charge is exactly Christoffel scale times the
signed scale-completed deviation. -/
theorem arcsineVacuumRenormalizedRelativeArithmeticSource_eq_scale_mul_centered
    {w : ℝ} {n : ℕ}
    (hscale : admissionChristoffelScaleSq w n ≠ 0) :
    arcsineVacuumRenormalizedRelativeArithmeticSource w n =
      admissionChristoffelScaleSq w n *
        arcsineCenteredScaleCompletedRelativeArithmeticSource w n := by
  unfold arcsineVacuumRenormalizedRelativeArithmeticSource
    arcsineCenteredScaleCompletedRelativeArithmeticSource
    scaleCompletedRelativeArithmeticSource
  field_simp [hscale]

/-- Fixed-degree shifted-Xi recession has zero covariant charge after full vacuum subtraction. -/
theorem tendsto_arcsineVacuumRenormalizedRelativeArithmeticSource
    {n : ℕ} (hn : n ≠ 0) :
    Tendsto (fun w : ℝ =>
      arcsineVacuumRenormalizedRelativeArithmeticSource w n)
      atTop (nhds 0) := by
  have hsource := tendsto_relativeArithmeticSource hn
  have hscale := tendsto_admissionChristoffelScaleSq hn
  have hvacScale : Tendsto
      (fun w : ℝ => arcsineVacuumSourceCounterterm n *
        admissionChristoffelScaleSq w n)
      atTop (nhds (arcsineVacuumSourceCounterterm n)) := by
    simpa using (tendsto_const_nhds.mul hscale)
  have hsub := hsource.sub hvacScale
  simpa [arcsineVacuumRenormalizedRelativeArithmeticSource,
    arcsineVacuumSourceCounterterm] using hsub

/-- Coordinate-dilated arcsine admissions have identically zero covariant source charge. -/
theorem coordinateDilated_arcsineVacuumRenormalizedRelativeArithmeticSource_eq_zero
    {r : ℝ} (hr : r ≠ 0) {n : ℕ} (hn : n ≠ 0) :
    HTGeometry.momentFunctional
          (XiShiftedArcsineAdmission.coordinateDilatedMoment r)
          (xiShiftedBoundaryAdaptiveShearPolynomial
            (XiShiftedArcsineAdmission.coordinateDilatedAmplitude r n)) /
        HTGeometry.momentFunctional
          (XiShiftedArcsineAdmission.coordinateDilatedMoment r)
          ((XiShiftedArcsineAdmission.coordinateDilatedAmplitude r n) ^ (2 : ℕ)) -
      arcsineVacuumSourceCounterterm n *
        XiShiftedArcsineAdmission.coordinateDilatedAdmissionChristoffelScaleSq r n = 0 := by
  rw [XiShiftedArcsineAdmission.coordinateDilated_adaptiveShear_div_norm hr hn,
    XiShiftedArcsineAdmission.coordinateDilatedAdmissionChristoffelScaleSq_eq hr hn]
  unfold arcsineVacuumSourceCounterterm
  ring

end XiShiftedCanonicalAdmission

/-- Pole-free completed source charge.  Both adaptive source and newborn vacuum are selected by
the current canonical admission before any degree/reflection reporter is applied. -/
def xiShiftedCanonicalAdmissionArcsineVacuumCompletedSourceCharge
    (y : ℝ) (n : ℕ) : ℝ :=
  2 * xiShiftedCanonicalAdmissionAdaptiveShear y n -
    32 * XiShiftedCanonicalAdmission.arcsineVacuumSourceCounterterm n *
      xiShiftedCanonicalAdmissionNorm y (n + 1)

/-- **Literal completed arithmetic-source law.**  At square mass the pole-free charge is the
adaptive mixed rational--Gamma-minus-von-Mangoldt `P^sharp` source minus its current admitted
newborn-norm vacuum. -/
theorem xiShiftedCanonicalAdmissionArcsineVacuumCompletedSourceCharge_eq_literal
    {w : ℝ} (hw : 1 / 2 < w) (n : ℕ) :
    xiShiftedCanonicalAdmissionArcsineVacuumCompletedSourceCharge (w ^ (2 : ℕ)) n =
      xiShiftedAdaptiveMixedCompletedArithmeticSource w
          (HTGeometry.monicMomentAdmissionPolynomial
            (xiShiftedRealMomentSequence w) n) -
        32 * XiShiftedCanonicalAdmission.arcsineVacuumSourceCounterterm n *
          xiShiftedCanonicalAdmissionNorm (w ^ (2 : ℕ)) (n + 1) := by
  have hsource := two_mul_xiShiftedAdaptiveShear_eq_arithmeticSource hw
    (HTGeometry.monicMomentAdmissionPolynomial (xiShiftedRealMomentSequence w) n)
  rw [xiShiftedCanonicalAdmissionArcsineVacuumCompletedSourceCharge]
  rw [← hsource]
  rfl

/-- Inside a positive chamber the former centered wall is merely the pole-free source charge
divided by the current newborn norm. -/
theorem xiShiftedCanonicalAdmissionArcsineVacuumCompletedSourceCharge_eq_wall
    {y : ℝ} {n : ℕ}
    (hN : xiShiftedCanonicalAdmissionNorm y (n + 1) ≠ 0) :
    xiShiftedCanonicalAdmissionArcsineVacuumCompletedSourceCharge y n =
      32 * xiShiftedCanonicalAdmissionNorm y (n + 1) *
        xiShiftedCanonicalAdmissionArcsineCenteredChristoffelSourceWall y n := by
  unfold xiShiftedCanonicalAdmissionArcsineVacuumCompletedSourceCharge
    xiShiftedCanonicalAdmissionArcsineCenteredChristoffelSourceWall
    xiShiftedCanonicalAdmissionChristoffelSourceWall
  field_simp [hN]
  ring

/-- **Strict-frontier pole removal.**  At every occupied strict frontier the newborn vacuum dies
exactly, while the preceding completed adaptive source survives with strict positive charge. -/
theorem xiShiftedCanonicalAdmissionArcsineVacuumCompletedSourceCharge_pos_at_strict_frontier
    {n : ℕ} (hne : (xiShiftedHigherBlockFailureSet n).Nonempty)
    (hstrict : xiShiftedHigherBlockTerminalFrontier n <
      xiShiftedHigherBlockTerminalFrontier (n + 1)) :
    0 < xiShiftedCanonicalAdmissionArcsineVacuumCompletedSourceCharge
      (xiShiftedHigherBlockTerminalFrontier (n + 1)) (n + 1) := by
  have hzero := xiShiftedCanonicalAdmissionNorm_eq_zero_at_strict_frontier hne hstrict
  have hsource :=
    xiShiftedCanonicalAdmissionAdaptiveShear_pos_at_strict_frontier hne hstrict
  rw [xiShiftedCanonicalAdmissionArcsineVacuumCompletedSourceCharge, hzero]
  nlinarith

/-- The pole-free completed source charge is continuous at every occupied strict frontier. -/
theorem continuousAt_xiShiftedCanonicalAdmissionArcsineVacuumCompletedSourceCharge_at_strict_frontier
    {n : ℕ} (hne : (xiShiftedHigherBlockFailureSet n).Nonempty)
    (hstrict : xiShiftedHigherBlockTerminalFrontier n <
      xiShiftedHigherBlockTerminalFrontier (n + 1)) :
    ContinuousAt
      (fun v => xiShiftedCanonicalAdmissionArcsineVacuumCompletedSourceCharge v (n + 1))
      (xiShiftedHigherBlockTerminalFrontier (n + 1)) := by
  let y := xiShiftedHigherBlockTerminalFrontier (n + 1)
  let d := n + 1
  let source : ℝ → ℝ := fun v => xiShiftedCanonicalAdmissionAdaptiveShear v d
  let nextNorm : ℝ → ℝ := fun v => xiShiftedCanonicalAdmissionNorm v (d + 1)
  have hface := xiShiftedHigherBlockTerminalFrontier_strict_step_posSemidef hne hstrict
  dsimp only at hface
  have hy : 0 < y := by
    obtain ⟨v, hv⟩ := hne
    have hvle := le_xiShiftedHigherBlockTerminalFrontier_of_mem hv
    exact lt_of_le_of_lt (hv.1.trans hvle) hstrict
  have hdH : (xiShiftedMomentHankelMatrix y d).PosDef :=
    xiShiftedMomentHankel_posDef_of_le (by omega) hface.1
  have hsource : ContinuousAt source y := by
    have h := continuousAt_xiShiftedCanonicalAdmissionAdaptiveShearMoment
      hy d (ne_of_gt hdH.det_pos)
    simpa only [source, xiShiftedCanonicalAdmissionAdaptiveShear,
      HTGeometry.momentInner_def, xiShiftedBoundaryAdaptiveShearPolynomial] using h
  have hnext : ContinuousAt nextNorm y := by
    have hdet : (xiShiftedMomentHankelMatrix y (d + 1)).det ≠ 0 := by
      simpa only [d] using ne_of_gt hface.1.det_pos
    exact continuousAt_xiShiftedCanonicalAdmissionNorm_of_det hy (d + 1) hdet
  have hscaledSource : ContinuousAt (fun v => 2 * source v) y :=
    continuousAt_const.mul hsource
  have hscaledNext : ContinuousAt
      (fun v => 32 * XiShiftedCanonicalAdmission.arcsineVacuumSourceCounterterm d *
        nextNorm v) y :=
    continuousAt_const.mul hnext
  change ContinuousAt
    ((fun v => 2 * source v) -
      (fun v => 32 * XiShiftedCanonicalAdmission.arcsineVacuumSourceCounterterm d *
        nextNorm v)) y
  exact hscaledSource.sub hscaledNext

/-- The regularized arithmetic producer remains positive on a right germ of every strict
frontier; only the posterior Christoffel division diverges. -/
theorem eventually_pos_xiShiftedCanonicalAdmissionArcsineVacuumCompletedSourceCharge_at_strict_frontier
    {n : ℕ} (hne : (xiShiftedHigherBlockFailureSet n).Nonempty)
    (hstrict : xiShiftedHigherBlockTerminalFrontier n <
      xiShiftedHigherBlockTerminalFrontier (n + 1)) :
    ∀ᶠ v in nhdsWithin (xiShiftedHigherBlockTerminalFrontier (n + 1))
        (Ioi (xiShiftedHigherBlockTerminalFrontier (n + 1))),
      0 < xiShiftedCanonicalAdmissionArcsineVacuumCompletedSourceCharge v (n + 1) := by
  have hcont :=
    continuousAt_xiShiftedCanonicalAdmissionArcsineVacuumCompletedSourceCharge_at_strict_frontier
      hne hstrict
  have hpos :=
    xiShiftedCanonicalAdmissionArcsineVacuumCompletedSourceCharge_pos_at_strict_frontier
      hne hstrict
  exact ((hcont.tendsto.eventually (Ioi_mem_nhds hpos)).filter_mono
    nhdsWithin_le_nhds)

/-- Physical strict-frontier value written entirely as literal completed adaptive mixed source.
The admission-selected vacuum term is zero there, leaving a finite positive arithmetic producer. -/
theorem xiShiftedStrictFrontier_literalArcsineVacuumCompletedSourceCharge_pos
    {n : ℕ} (hne : (xiShiftedHigherBlockFailureSet n).Nonempty)
    (hstrict : xiShiftedHigherBlockTerminalFrontier n <
      xiShiftedHigherBlockTerminalFrontier (n + 1))
    (hphysical : 1 / 4 < xiShiftedHigherBlockTerminalFrontier (n + 1)) :
    let y := xiShiftedHigherBlockTerminalFrontier (n + 1)
    0 < xiShiftedAdaptiveMixedCompletedArithmeticSource (Real.sqrt y)
          (HTGeometry.monicMomentAdmissionPolynomial
            (xiShiftedRealMomentSequence (Real.sqrt y)) (n + 1)) -
        32 * XiShiftedCanonicalAdmission.arcsineVacuumSourceCounterterm (n + 1) *
          xiShiftedCanonicalAdmissionNorm y (n + 2) := by
  dsimp only
  let y := xiShiftedHigherBlockTerminalFrontier (n + 1)
  have hy0 : 0 ≤ y := by
    dsimp only [y]
    linarith
  have hsqrt : 1 / 2 < Real.sqrt y := by
    have hsqrt0 := Real.sqrt_nonneg y
    change 1 / 4 < y at hphysical
    nlinarith [Real.sq_sqrt hy0]
  have hliteral :=
    xiShiftedCanonicalAdmissionArcsineVacuumCompletedSourceCharge_eq_literal
      hsqrt (n + 1)
  have hpos :=
    xiShiftedCanonicalAdmissionArcsineVacuumCompletedSourceCharge_pos_at_strict_frontier
      hne hstrict
  rw [Real.sq_sqrt hy0] at hliteral
  dsimp only [y] at hliteral hpos ⊢
  rw [← hliteral]
  exact hpos

end

end RHTower
