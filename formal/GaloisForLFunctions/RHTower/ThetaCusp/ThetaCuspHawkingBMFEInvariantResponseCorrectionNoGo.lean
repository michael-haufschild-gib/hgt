import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMCrossPairResponseCompensator

/-!
# Functional-equation-invariant response corrections cannot cancel the HB current

The exact reflected Birmingham--Mokhtari current admits arbitrary divisor-dependent scalar
response corrections.  Existing countermodels cancel it by transporting data from the reflected
Xi copy.  This module proves that such reflection nonlocality is necessary.

If a scalar response correction is invariant under functional-equation reflection, its two values
on a reflected pair are the same.  That common scalar factors out of the full corrected current.
The remaining factor is the literal unsquared Einstein--Teukolsky source current, whose zero locus
is already known to be exactly the critical wall.  Therefore

`corrected current = 0  <->  correction = 0 or Re(rho) = 1/2`.

In particular, every everywhere-nonzero FE-invariant response correction cancels exactly on the
critical wall.  This kills the whole copywise invariant scalar-response route, with no analyticity,
boundedness, finite-rank, rationality, or perturbative-order restriction.

The sharp positive survivor is an escape classification: a successful off-wall compensator must
either vanish on that fibre or break FE invariance.  Existing nonzero cross-pair compensators take
the second option by reading the reflected source explicitly.

`[NEW] [HB] [RESPONSE CLASSIFICATION] [REFLECTION LOCALITY NO-GO] [LEAN-PROVED]`
-/

open Complex Real Set

namespace RHTower

noncomputable section

/-- Functional-equation invariance of a scalar response correction on the multiplicity-exact Xi
divisor carrier. -/
def D4BMXiSecondHarmonicResponseCorrectionFEInvariant
    (correction : XiZeroCopy → ℂ) : Prop :=
  ∀ q : XiZeroCopy,
    correction (xiZeroCopyReflectEquiv q) = correction q

/-- An FE-invariant correction factors out of the exact reflected BM current. -/
theorem d4BMXiSecondHarmonicPeierlsResponseCorrectedReflectionCurrent_eq_mul_unsquared_of_feInvariant
    (n : ℕ) (correction : XiZeroCopy → ℂ) (q : XiZeroCopy)
    (hinvariant : correction (xiZeroCopyReflectEquiv q) = correction q) :
    d4BMXiSecondHarmonicPeierlsResponseCorrectedReflectionCurrent
        n correction q =
      correction q *
        d4BMXiSecondHarmonicUnsquaredSourceReflectionCurrent n q := by
  rw [d4BMXiSecondHarmonicPeierlsResponseCorrectedReflectionCurrent,
    d4BMXiSecondHarmonicUnsquaredSourceReflectionCurrent, hinvariant]
  unfold d4BMXiReflectionComplexWeightedRegularComplementaryCurrent
    d4BMXiSecondHarmonicUnitUnsquaredSourceAmplitude
  ring

/-- Sharp pointwise classification: an FE-invariant scalar correction cancels only by vanishing
itself or by lying on the critical wall. -/
theorem d4BMXiSecondHarmonicPeierlsResponseCorrectedReflectionCurrent_eq_zero_iff_of_feInvariant
    (n : ℕ) (correction : XiZeroCopy → ℂ) (q : XiZeroCopy)
    (hinvariant : correction (xiZeroCopyReflectEquiv q) = correction q) :
    d4BMXiSecondHarmonicPeierlsResponseCorrectedReflectionCurrent
        n correction q = 0 ↔
      correction q = 0 ∨ (q.1 : ℂ).re = 1 / 2 := by
  rw [d4BMXiSecondHarmonicPeierlsResponseCorrectedReflectionCurrent_eq_mul_unsquared_of_feInvariant
      n correction q hinvariant,
    mul_eq_zero,
    d4BMXiSecondHarmonicUnsquaredSourceReflectionCurrent_eq_zero_iff]

/-- Off the critical wall, cancellation by an FE-invariant correction forces the response itself
to vanish on that fibre. -/
theorem d4BMXiSecondHarmonicPeierlsResponseCorrectedReflectionCurrent_eq_zero_iff_correction_eq_zero_of_feInvariant_of_offCritical
    (n : ℕ) (correction : XiZeroCopy → ℂ) (q : XiZeroCopy)
    (hinvariant : correction (xiZeroCopyReflectEquiv q) = correction q)
    (hoff : (q.1 : ℂ).re ≠ 1 / 2) :
    d4BMXiSecondHarmonicPeierlsResponseCorrectedReflectionCurrent
        n correction q = 0 ↔ correction q = 0 := by
  rw [d4BMXiSecondHarmonicPeierlsResponseCorrectedReflectionCurrent_eq_zero_iff_of_feInvariant
      n correction q hinvariant,
    or_iff_left hoff]

/-- A nonzero FE-invariant correction preserves the exact critical-wall zero locus of the literal
Einstein--Teukolsky source current. -/
theorem d4BMXiSecondHarmonicPeierlsResponseCorrectedReflectionCurrent_eq_zero_iff_criticalLine_of_feInvariant_of_ne_zero
    (n : ℕ) (correction : XiZeroCopy → ℂ) (q : XiZeroCopy)
    (hinvariant : correction (xiZeroCopyReflectEquiv q) = correction q)
    (hcorrection : correction q ≠ 0) :
    d4BMXiSecondHarmonicPeierlsResponseCorrectedReflectionCurrent
        n correction q = 0 ↔
      (q.1 : ℂ).re = 1 / 2 := by
  rw [d4BMXiSecondHarmonicPeierlsResponseCorrectedReflectionCurrent_eq_zero_iff_of_feInvariant
      n correction q hinvariant,
    or_iff_right hcorrection]

/-- Closed route-class statement: every everywhere-nonzero FE-invariant scalar correction has the
same critical-wall cancellation locus as the literal source. -/
def D4BMXiSecondHarmonicFEInvariantNonzeroResponseCorrectionRouteKilled : Prop :=
  ∀ (n : ℕ) (correction : XiZeroCopy → ℂ),
    D4BMXiSecondHarmonicResponseCorrectionFEInvariant correction →
    (∀ q : XiZeroCopy, correction q ≠ 0) →
    ∀ q : XiZeroCopy,
      d4BMXiSecondHarmonicPeierlsResponseCorrectedReflectionCurrent
          n correction q = 0 ↔
        (q.1 : ℂ).re = 1 / 2

/-- Premise-free Lean certificate killing the full nonzero FE-invariant scalar response route. -/
theorem d4BMXiSecondHarmonicFEInvariantNonzeroResponseCorrectionRouteKilled :
    D4BMXiSecondHarmonicFEInvariantNonzeroResponseCorrectionRouteKilled := by
  intro n correction hinvariant hnonzero q
  exact
    d4BMXiSecondHarmonicPeierlsResponseCorrectedReflectionCurrent_eq_zero_iff_criticalLine_of_feInvariant_of_ne_zero
      n correction q (hinvariant q) (hnonzero q)

/-- Universal cancellation by an everywhere-nonzero FE-invariant response is equivalent to RH. -/
theorem forall_d4BMXiSecondHarmonicPeierlsResponseCorrectedReflectionCurrent_eq_zero_iff_rh_of_feInvariant_of_ne_zero
    (n : ℕ) (correction : XiZeroCopy → ℂ)
    (hinvariant : D4BMXiSecondHarmonicResponseCorrectionFEInvariant correction)
    (hnonzero : ∀ q : XiZeroCopy, correction q ≠ 0) :
    (∀ q : XiZeroCopy,
      d4BMXiSecondHarmonicPeierlsResponseCorrectedReflectionCurrent
        n correction q = 0) ↔ RiemannHypothesis := by
  constructor
  · intro h
    apply (forall_d4BMXiSecondHarmonicUnsquaredSourceReflectionCurrent_eq_zero_iff_rh n).mp
    intro q
    apply (d4BMXiSecondHarmonicUnsquaredSourceReflectionCurrent_eq_zero_iff n q).mpr
    exact
      (d4BMXiSecondHarmonicPeierlsResponseCorrectedReflectionCurrent_eq_zero_iff_criticalLine_of_feInvariant_of_ne_zero
        n correction q (hinvariant q) (hnonzero q)).mp (h q)
  · intro hRH q
    apply
      (d4BMXiSecondHarmonicPeierlsResponseCorrectedReflectionCurrent_eq_zero_iff_criticalLine_of_feInvariant_of_ne_zero
        n correction q (hinvariant q) (hnonzero q)).mpr
    have hsource :=
      (forall_d4BMXiSecondHarmonicUnsquaredSourceReflectionCurrent_eq_zero_iff_rh n).mpr
        hRH q
    exact
      (d4BMXiSecondHarmonicUnsquaredSourceReflectionCurrent_eq_zero_iff n q).mp hsource

/-! ## The known cross-pair escape is necessarily reflection-nonlocal -/

/-- At every off-critical fibre, the existing division-free cross-pair compensator necessarily
breaks FE invariance.  Its unconditional cancellation is therefore not a counterexample to the
route kill above; it realizes the sharp reflection-nonlocal escape. -/
theorem d4BMXiSecondHarmonicCrossPairResponseCorrection_not_feInvariant_of_offCritical
    (n : ℕ) (q : XiZeroCopy) (hoff : (q.1 : ℂ).re ≠ 1 / 2) :
    d4BMXiSecondHarmonicCrossPairResponseCorrection n
        (xiZeroCopyReflectEquiv q) ≠
      d4BMXiSecondHarmonicCrossPairResponseCorrection n q := by
  intro hinvariant
  have hcorrection :
      d4BMXiSecondHarmonicCrossPairResponseCorrection n q ≠ 0 :=
    (d4BMXiSecondHarmonicCrossPairResponseCorrection_eq_zero_iff n q).not.mpr hoff
  have hcancel :=
    forall_d4BMXiSecondHarmonicCrossPairResponseCorrectedReflectionCurrent_eq_zero n q
  have hline :=
    (d4BMXiSecondHarmonicPeierlsResponseCorrectedReflectionCurrent_eq_zero_iff_criticalLine_of_feInvariant_of_ne_zero
      n (d4BMXiSecondHarmonicCrossPairResponseCorrection n) q hinvariant
        hcorrection).mp hcancel
  exact hoff hline

/-- Global FE invariance of the explicit cross-pair compensator is itself equivalent to RH.  Off
RH, its ability to cancel all reflected currents is carried exactly by reflection nonlocality. -/
theorem d4BMXiSecondHarmonicCrossPairResponseCorrection_feInvariant_iff_rh
    (n : ℕ) :
    D4BMXiSecondHarmonicResponseCorrectionFEInvariant
        (d4BMXiSecondHarmonicCrossPairResponseCorrection n) ↔
      RiemannHypothesis := by
  constructor
  · intro hinvariant
    apply
      (forall_d4BMXiSecondHarmonicUnsquaredSourceReflectionCurrent_eq_zero_iff_rh n).mp
    intro q
    apply
      (d4BMXiSecondHarmonicUnsquaredSourceReflectionCurrent_eq_zero_iff n q).mpr
    have hclassification :=
      (d4BMXiSecondHarmonicPeierlsResponseCorrectedReflectionCurrent_eq_zero_iff_of_feInvariant
        n (d4BMXiSecondHarmonicCrossPairResponseCorrection n) q
          (hinvariant q)).mp
        (forall_d4BMXiSecondHarmonicCrossPairResponseCorrectedReflectionCurrent_eq_zero n q)
    rcases hclassification with hcorrection | hline
    · exact
        (d4BMXiSecondHarmonicCrossPairResponseCorrection_eq_zero_iff n q).mp hcorrection
    · exact hline
  · intro hRH q
    have hqline : (q.1 : ℂ).re = 1 / 2 :=
      xi_divisor_support_re_eq_half_of_rh hRH q.1
    have hrefline : ((xiZeroCopyReflectEquiv q).1 : ℂ).re = 1 / 2 :=
      xi_divisor_support_re_eq_half_of_rh hRH (xiZeroCopyReflectEquiv q).1
    rw [(d4BMXiSecondHarmonicCrossPairResponseCorrection_eq_zero_iff n q).mpr hqline,
      (d4BMXiSecondHarmonicCrossPairResponseCorrection_eq_zero_iff n
        (xiZeroCopyReflectEquiv q)).mpr hrefline]

end

end RHTower
