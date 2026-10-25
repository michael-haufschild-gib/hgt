# Complete Lean proofs of the existing Q-I findings

- **ID:** q-i-existing-findings-lean-completion
- **Stage:** 1-in-progress
- **Type:** FORMALIZATION REGISTER
- **Source:** q-i-selective-square-root-band.md
- **Scope:** Every significant finding already argued on paper in this Q-I branch, including its stated corollaries. No new conjecture branch while this register remains incomplete.
- **Proof standard:** Paper arguments and unchecked Lean drafts are UNPROVED. A completed result needs its direct Lean check, transitive axiom audit, umbrella import, and accurate corpus documentation.

## Build discipline

Use only direct `lake --old env lean ...` commands from `formal/`, with one
foreground compiler at a time. No Python scripts for builds, edits, or audits.
No build scripts or wrappers, `lake build`,
umbrella builds, limit increases, placeholders, or added analytic assumptions.
Write an olean only for a written importer or an exactly identified missing
dependency. Preserve existing oleans. Verify new mathlib APIs in scratch;
finish with a direct check of the repository leaf.

## Existing paper obligations

Pending cards below remain in `../2-fully-proven/`; that legacy directory name
does not certify them. Completed cards link to stage 3. Each pending statement
remains UNPROVED until its complete Lean chain passes.
Lean module names below are relative to `GaloisForLFunctions/`; BVI denotes
`BezoutValuationIncidence/`.

| Existing paper card | Required Lean coverage |
| --- | --- |
| `uniform-second-scale-vaughan-gram-at-all-cutoffs.md` | BVI `PronicGramErrorsAroundASmoothRankOneTerm`, `UniformVaughanGramsFollowTheirSmoothRankOneTerm`, `VaughanPacketGramIdentities`, `UniformLogarithmicLawsForVaughanSuperpositions`; common floor-sum corollaries in `UniformLogarithmicCancellationInMobiusFloorSums`; the quantitative Mertens-to-convolution gain below `η/(2+η)` in `UniformVaughanPowerBoundsAreFixedStrips`. All-row logarithmic remainders and the finite Gram comparison are already checked. |
| [vaughan-subcritical-gram-limit-classification.md](../3-formalized/vaughan-subcritical-gram-limit-classification.md) — COMPLETE | All 39 targets in the five arithmetic-amplitude, classification, scalar-topology, matrix-rank, and matrix-topology leaves passed final direct checks and standard-axiom audits. Includes exact attainment and damping independence. |
| [positive-vaughan-cutoff-escape-is-zero-gram-limit.md](../3-formalized/positive-vaughan-cutoff-escape-is-zero-gram-limit.md) — COMPLETE | Exact amplitude and matrix escape equivalences, finite-fiber rigidity, convergence dichotomy, positive-cutoff attainment, and mutually exclusive alternatives. All supporting leaf checks and axiom audits passed. |
| [vaughan-relative-gram-and-harmonic-denominators.md](../3-formalized/vaughan-relative-gram-and-harmonic-denominators.md) — COMPLETE | All ten arithmetic and relative-Gram targets passed final direct checks and standard-axiom audits. Includes calibrated horizons for every positive cutoff schedule and the simultaneous zero/relative-rank-one corollary. |
| [uniform-vaughan-convolution-stretched-exponential-rate.md](../3-formalized/uniform-vaughan-convolution-stretched-exponential-rate.md) — COMPLETE; related existing stage-1 [factorial criterion](vaughan-factorial-order-one-is-a-fixed-strip.md) still pending | All three BVI `UniformStretchedExponentialCancellationInTheVaughanConvolution` targets passed final direct checks and standard-axiom audits. The distinct factorial-order-one criterion still needs HTGeometry `FactorialLogarithmicBoundsArePowerBounds` and BVI `FactorialOrderOneInTheVaughanConvolutionIsAPowerSaving`. |
| `uniform-vaughan-residual-power-rates-are-fixed-strips.md` | BVI `TheExtremeVaughanCutoffReadsItsHarmonicSum`, `PowerCancellationSurvivesTheDampedFloorTransform`, `FixedStripsControlAllVaughanFluctuationReceivers`, `UniformVaughanResidualPowerRatesAreFixedStrips`, `UniformVaughanPowerBoundsAreFixedStrips`; RHTower `MertensPowerBoundsControlMobiusHarmonicSums`. |
| `the-centred-vaughan-pole-has-positive-finite-energy.md` | All seven BVI `TheCentredVaughanPoleHasPositiveFiniteEnergy` targets passed final direct checks and standard-axiom audits, including the eventual faster-power obstruction. The stated endpoint product-horizon nonzero limit still needs its actual Gram chain. |
| `the-endpoint-vaughan-limit-has-rank-two.md` | All twelve BVI `TheVaughanLimitRowsAreIndependentInTwoCells` targets passed final direct checks and standard-axiom audits. `TheActualVaughanLimitGramHasRankTwo` and `TheActualEndpointVaughanGramHasRankTwo` remain pending, including the explicit positive-definite two-by-two prefix/pole Gram corollary; actual summability comes from the moving-limit leaves below. |
| `uniform-half-damping-vaughan-harmonic-gram.md` | BVI `UniformCriticalPronicPairingsFromLogarithmicCancellation`, `UniformLogarithmicPrefixRemaindersInAllVaughanRows`, `UniformHarmonicVaughanGramsAtHalfDamping`, `PositiveFloorMajorantsControlPronicEnergy`, `MovingVaughanRowsConvergeCellByCell`, `UniformHalfDampingVaughanGramsHaveAnActualLimit`, `UniformHarmonicEnergyLawsForVaughanSuperpositions`, `TheHalfDampingVaughanGramLimitsFormARankThreeRay`, `ProductHorizonVaughanGramsAtHalfDampingHaveFiniteLimits`, `EveryNonnegativeEndpointVaughanLimitIsRealized`; HTGeometry `MovingTruncationsPreserveDominatedLimits`, `VanishingPositiveScalesRealizeHarmonicMasses`. |
| `vaughan-admission-phase-transition-at-half-damping.md` | BVI `VaughanAdmissionAtHalfDamping`, `VaughanAdmissionAboveHalfDamping`, `UpperHalfVaughanGramsHaveAnActualLimit`; actual upper-half rank two in the shared infinite-Gram leaf. The paper also asserts critical Wiener convergence of the three floor-coefficient families. This coefficient-norm claim needs its own exact formalization; row-norm convergence alone does not discharge it. |
| [vaughan-zero-cutoffs-remove-the-smooth-obstruction.md](../3-formalized/vaughan-zero-cutoffs-remove-the-smooth-obstruction.md) — COMPLETE | All twenty scalar and coefficient-space targets passed final direct checks and standard-axiom audits. Includes unique coordinate recovery, both exact spans, admitted and quotient dimensions, and unconditional half-damping admission. |
| [vaughan-admitted-rank-filtration-reads-the-zero-abscissa.md](../3-formalized/vaughan-admitted-rank-filtration-reads-the-zero-abscissa.md) — COMPLETE | All twelve targets in BVI `TheVaughanAdmissionRankReadsTheZeroAbscissa` passed the final direct check and standard-axiom audits. Includes cutoff independence, exact zero-width boundary, all three RH criteria, and first/all damping-column summability equivalences. |
| `all-positive-vaughan-tail-power-rates.md` | BVI `VaughanTailPowerGainsAtEveryPositiveDamping`. |
| `vaughan-tail-and-energy-decay-indices.md` | BVI `TheVaughanEmptyLegReadsTheZeroAbscissa`, including full rate-set independence and endpoint distinctions. |
| `vaughan-endpoint-rates-and-zero-multiplicity.md` | BVI `VaughanEndpointScalesHaveUnavoidableOscillation`, `VaughanEndpointRatesForceSimpleBoundaryZeros`. |

## Checked progress

The dependency chain through
`UniformLogarithmicRemaindersInAllVaughanRows.lean` has passed. Its six public
theorems have only `propext`, `Classical.choice`, and `Quot.sound` as transitive
axioms. Scratch, producing, and final direct checks passed; its import and
corpus documentation are present. See
`../3-formalized/uniform-logarithmic-remainders-in-all-vaughan-rows.md`.

The finite Gram comparison also passed its corrected scratch, producing, and
final direct repository checks, with all three public targets using only
standard axioms. It is wired and its scratch was removed; see
`../3-formalized/pronic-gram-errors-around-a-smooth-rank-one-term.md`.
The complete uniform matrix law passed its scratch, producing, and final
direct repository checks. All four targets have only standard transitive
axioms. It is wired as `UniformVaughanGramsFollowTheirSmoothRankOneTerm.lean`;
its scratch was removed. See
`../3-formalized/uniform-vaughan-grams-follow-their-smooth-rank-one-term.md`.
The four finite packet identities passed producing and final direct checks,
with standard transitive axioms only. They are wired as
`VaughanPacketGramIdentities.lean`; the scratch was removed. See
`../3-formalized/vaughan-packet-gram-identities.md`.
The seven homogeneous packet laws also passed corrected producing and final
direct checks, with standard transitive axioms only. They are wired as
`UniformLogarithmicLawsForVaughanSuperpositions.lean`; the scratch was removed.
See `../3-formalized/uniform-logarithmic-laws-for-vaughan-superpositions.md`.
The fourteen arithmetic amplitude results passed producing and final direct
checks, with standard transitive axioms only. They are wired as
`TheCompactArithmeticAmplitudesOfVaughanGrams.lean`; the scratch was removed.
They cover compactness, countable infinitude, finite fibers away from zero,
and the exact positive-cutoff amplitude escape equivalence.
The eight targets in `TheSubcriticalVaughanGramLimitSet.lean` passed corrected
producing and final direct checks, with standard transitive axioms only. They
are wired and their scratch was removed. This includes the explicit independent-
horizon packet-energy-zero corollary. The amplitude-topology leaf's four targets
also passed producing and final direct checks, with standard transitive axioms
only. They give finiteness above each positive level, isolation, the unique zero
accumulation point, and mutual exclusion of the two convergence cases. Its
scratch was removed and the exact escape card moved to stage 3. The four matrix
rank targets also passed corrected producing and final direct checks, with
standard axioms only. `TheRanksOfSubcriticalVaughanLimits.lean` is wired and its
scratch removed: zero amplitude has rank zero; every positive amplitude has rank one.
All nine matrix-topology targets passed their corrected final direct check,
with standard axioms only. `TheTopologyOfSubcriticalVaughanGramLimits.lean`
is wired and its scratch removed. The complete 39-target subcritical card is
now in stage 3, including matrix compactness, countable infinitude, unique zero
accumulation, exact attainment, and normalized damping independence.
The three arithmetic targets in `RHTower/FiniteMobiusHarmonicSumsHaveExplicitLowerBounds.lean`
also passed corrected producing and final direct checks, with standard axioms
only. The module is wired and its scratch removed. Common-denominator clearing
gives `|H_N|≥1/D`, and the factorial specialization gives `|H_N|≥1/N!` for positive N.
All seven targets in `VaughanGramsAtTheirActualHarmonicAmplitude.lean` passed
their corrected final direct check, with standard axioms only. The module is
wired and its scratch removed; the complete ten-target relative-Gram card is
in stage 3.
All seven floor-sum targets passed their final direct check and standard-axiom
audits. `UniformLogarithmicCancellationInMobiusFloorSums.lean` is wired; its
scratch was removed. The rounding, exact omitted-tail identity, common finite
bound, and full uniform logarithmic rate are certified in
`../3-formalized/uniform-logarithmic-cancellation-in-mobius-floor-sums.md`.
All three generic critical-pairing targets passed corrected producing and
final direct checks, with standard axioms only. The module is wired and its
scratch removed; see
`../3-formalized/uniform-critical-pronic-pairings-from-logarithmic-cancellation.md`.
The six actual all-row prefix targets passed producing and final direct checks,
with standard axioms only. The module is wired and its scratch removed; see
`../3-formalized/uniform-logarithmic-prefix-remainders-in-all-vaughan-rows.md`.
This discharges the common logarithmic prefix and linear finite-head inputs
for the endpoint specialization.
All three actual endpoint Gram targets passed corrected producing and final
direct checks with standard axioms only. The module is wired and its scratch
removed; see `../3-formalized/uniform-harmonic-vaughan-grams-at-half-damping.md`.
Its common summable envelope, energy and mixed-pairing bounds, and bounded
harmonic Gram error are certified. Moving-limit and rank claims remain pending.
The three endpoint packet targets passed their corrected final direct check
and standard-axiom audits. The module is wired and its scratch removed; the
endpoint Gram card now covers all six finite Gram and packet targets.
The five positive-floor and pronic-convergence targets also passed corrected
producing and final direct checks with standard axioms only. The module is
wired and its scratch removed; see
`../3-formalized/positive-floor-majorants-and-pronic-convergence.md`.
All nine endpoint-admission targets passed producing and final direct checks
with standard axioms only. `VaughanAdmissionAtHalfDamping.lean` is wired and
its scratch removed. The eleven upper-half admission targets also passed
corrected producing and final direct checks with standard axioms only; that
module is wired and its scratch removed. The complete admission component is
`../3-formalized/vaughan-admission-at-and-above-half-damping.md`.
The separate joint-limit and infinite-rank consequences still require verification.
The five zero-cutoff scalar targets passed corrected producing and final
direct checks with standard axioms only; their module is wired and scratch
removed. All fifteen zero-cutoff coefficient-space targets also passed final
direct checks with standard axioms only. Their module is wired and scratch
removed; the complete twenty-target zero-cutoff card is in stage 3.
All twelve rank-filtration targets passed the corrected final direct check
with standard axioms only. The module is wired and its scratch removed;
the complete rank-filtration card is in stage 3.
All seven centered-pole targets passed corrected producing and final direct
checks with standard axioms only. The module is wired and its scratch removed;
the positive finite energy, arbitrary moving-cutoff limit, and eventual power
cap are certified. The parent card's endpoint product-horizon consequence
remains pending.
All twelve finite two-cell independence targets passed corrected producing
and final direct checks with standard axioms only. The module is wired and
its scratch removed. Both quantitative determinants, linear independence,
the exact row span, and its dimension two are certified at every positive
damping; the infinite Gram consequences remain pending.
Both moving-cell targets passed corrected producing and final direct checks
with standard axioms only. `MovingVaughanRowsConvergeCellByCell.lean` is wired
and its scratch removed. For every positive damping, both centered and
smooth-subtracted rows converge cellwise to the actual two-row frame when
both cutoffs diverge.
All six endpoint moving-limit targets passed corrected producing and final
direct checks with standard axioms only. The module is wired and its scratch
removed. It supplies actual limiting-pairing summability, full pronic convergence,
and the renormalized Gram limit at independent horizons. Rank and limit-ray
corollaries remain pending.
The independent moving-horizon summation theorem passed producing and final
direct checks with standard axioms only. Its HTGeometry module is wired and
its scratch removed; see
`../3-formalized/moving-truncations-preserve-dominated-limits.md`.
All three stretched-exponential targets passed their corrected final direct
check, with standard axioms only. The module is wired and its scratch removed;
the complete card is now in stage 3. This includes the exact stated constant
and the `(3q)!` envelope at one common threshold for all logarithmic orders.
All remaining drafts now have their intended repository leaves. They remain
uncertified until their final direct checks and axiom audits pass. Dependencies and
live compiler handles are recorded in `/tmp/QIVerificationState.txt`; the
complete module queue is `/tmp/QILeanCompletionQueue.md`.

Full Q-I remains open. Formalizing the stated equivalences does not prove a
fixed strip or replace that missing conclusion by a premise.
