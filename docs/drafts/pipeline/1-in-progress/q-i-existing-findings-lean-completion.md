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

All cards below are in `../2-fully-proven/`; that legacy directory name does
not certify them. Each remains UNPROVED until its complete Lean chain passes.
Lean module names below are relative to `GaloisForLFunctions/`; BVI denotes
`BezoutValuationIncidence/`.

| Existing paper card | Required Lean coverage |
| --- | --- |
| `uniform-second-scale-vaughan-gram-at-all-cutoffs.md` | BVI `PronicGramErrorsAroundASmoothRankOneTerm`, `UniformVaughanGramsFollowTheirSmoothRankOneTerm`, `VaughanPacketGramIdentities`, `UniformLogarithmicLawsForVaughanSuperpositions`; common floor-sum corollaries in `UniformLogarithmicCancellationInMobiusFloorSums`; the quantitative Mertens-to-convolution gain below `η/(2+η)` in `UniformVaughanPowerBoundsAreFixedStrips`. All-row logarithmic remainders and the finite Gram comparison are already checked. |
| `vaughan-subcritical-gram-limit-classification.md` | BVI `TheCompactArithmeticAmplitudesOfVaughanGrams`, `TheSubcriticalVaughanGramLimitSet`, `TheOnlyAccumulationOfVaughanAmplitudesIsZero`, `TheRanksOfSubcriticalVaughanLimits`, `TheTopologyOfSubcriticalVaughanGramLimits`. The last leaf supplies exact matrix-family topology, beyond the scalar amplitude statements. |
| `positive-vaughan-cutoff-escape-is-zero-gram-limit.md` | Exact amplitude escape equivalence and matrix convergence dichotomy in the preceding amplitude/classification leaves. |
| `vaughan-relative-gram-and-harmonic-denominators.md` | RHTower `FiniteMobiusHarmonicSumsHaveExplicitLowerBounds`; BVI `VaughanGramsAtTheirActualHarmonicAmplitude`. |
| `uniform-vaughan-convolution-stretched-exponential-rate.md` | BVI `UniformStretchedExponentialCancellationInTheVaughanConvolution`; HTGeometry `FactorialLogarithmicBoundsArePowerBounds`; BVI `FactorialOrderOneInTheVaughanConvolutionIsAPowerSaving`. |
| `uniform-vaughan-residual-power-rates-are-fixed-strips.md` | BVI `TheExtremeVaughanCutoffReadsItsHarmonicSum`, `PowerCancellationSurvivesTheDampedFloorTransform`, `FixedStripsControlAllVaughanFluctuationReceivers`, `UniformVaughanResidualPowerRatesAreFixedStrips`, `UniformVaughanPowerBoundsAreFixedStrips`; RHTower `MertensPowerBoundsControlMobiusHarmonicSums`. |
| `the-centred-vaughan-pole-has-positive-finite-energy.md` | BVI `TheCentredVaughanPoleHasPositiveFiniteEnergy`, including the eventual faster-power obstruction. |
| `the-endpoint-vaughan-limit-has-rank-two.md` | BVI `TheVaughanLimitRowsAreIndependentInTwoCells`, `TheActualVaughanLimitGramHasRankTwo`, `TheActualEndpointVaughanGramHasRankTwo`; actual summability supplied by the moving-limit leaves below. |
| `uniform-half-damping-vaughan-harmonic-gram.md` | BVI `UniformCriticalPronicPairingsFromLogarithmicCancellation`, `UniformLogarithmicPrefixRemaindersInAllVaughanRows`, `UniformHarmonicVaughanGramsAtHalfDamping`, `PositiveFloorMajorantsControlPronicEnergy`, `MovingVaughanRowsConvergeCellByCell`, `UniformHalfDampingVaughanGramsHaveAnActualLimit`, `UniformHarmonicEnergyLawsForVaughanSuperpositions`, `TheHalfDampingVaughanGramLimitsFormARankThreeRay`, `ProductHorizonVaughanGramsAtHalfDampingHaveFiniteLimits`, `EveryNonnegativeEndpointVaughanLimitIsRealized`; HTGeometry `MovingTruncationsPreserveDominatedLimits`, `VanishingPositiveScalesRealizeHarmonicMasses`. |
| `vaughan-admission-phase-transition-at-half-damping.md` | BVI `VaughanAdmissionAtHalfDamping`, `VaughanAdmissionAboveHalfDamping`, `UpperHalfVaughanGramsHaveAnActualLimit`; actual upper-half rank two in the shared infinite-Gram leaf. |
| `vaughan-zero-cutoffs-remove-the-smooth-obstruction.md` | BVI `ZeroVaughanCutoffsRemoveTheSmoothObstruction`, `TheZeroCutoffVaughanCoefficientSpace`. |
| `vaughan-admitted-rank-filtration-reads-the-zero-abscissa.md` | BVI `TheVaughanAdmissionRankReadsTheZeroAbscissa`, using the checked-to-be endpoint and zero-cutoff classifications. |
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
All other remaining leaves named in the table are unchecked drafts. Dependencies and
live compiler handles are recorded in `/tmp/QIVerificationState.txt`; the
complete module queue is `/tmp/QILeanCompletionQueue.md`.

Full Q-I remains open. Formalizing the stated equivalences does not prove a
fixed strip or replace that missing conclusion by a premise.
