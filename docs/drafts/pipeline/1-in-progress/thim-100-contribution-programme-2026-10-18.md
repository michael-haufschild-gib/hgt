# Trans-horizon incidence mechanics: 100-contribution programme

- **ID:** thim-100-contribution-programme-2026-10-18
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** user attachment `41e474e4-e160-40de-8479-f8489a2029d5/pasted-text-1.txt`;
  `formal/GaloisForLFunctions/TransHorizonIncidenceMechanics/README.md` (read-only)
- **Statement:** Develop and verify 100 significant, distinct, native mathematical contributions.

## Contract and counting

Count connected mathematical advances, not declarations, routine corollaries, renamed
classical facts, search results, or conditional restatements of an open target.
Each counted item must identify the field capability it adds, corpus overlap checks,
a dependency-closed proof, an unconditional Lean result, source audit, axiom audit,
and umbrella wiring. Novelty beyond the corpus requires independent evidence;
absence of a search hit is not proof of novelty.

No hgtl7 skill, numerical experiments, new axioms, proof holes, heartbeat increases,
full builds, umbrella builds, commits, or edits to the field README. One foreground
Lean process at a time. Final source audit uses `lake --old env lean`.

## Plan

1. Read current framework and search corpus before each new conjecture.
2. Identify a native mechanism that advances an actual frontier; record precise claim.
3. Prove or refute it on paper. For refutations, extract and prove strongest positive survivor.
4. Formalize exact proved claim, audit source and axioms, wire leaf, regenerate indexes,
   and run formal lint. Distinguish local success from unrelated global failures.
5. Audit significance and novelty, record qualified count, then continue conjecturing.

`update_plan` tool is unavailable in this session; this card tracks the plan.

## Current evidence

- Read entire 165-line field README, repository/formal guidance, formal overview,
  RH constraints, relevant MC/BVI frontier entries, and relevant Serena memories.
- Existing source has universal all-octave Fermi sibling jumps, second differences,
  dyadic wavelet reconstruction, and second-octave squarefree lower bounds.
  These are prior work, not new contributions of this programme.
- Initial hybrid searches completed with source inventory coverage but mostly
  unrelated hits; compiler applicability is not checked by search.
- Current investigation: use valuation saturation and changing-cutoff sieve laws
  to retain signed Fermi/dilation information beyond fixed octave identities.
- Working tree already contains unrelated and concurrent changes, including field
  umbrella and README changes; preserve them.
- Serena symbol access rejects Lean paths as ignored; use source reads and patches.

## Audited contribution ledger

**Qualified count: 1/100.**

| ID | Native contribution | Certificate |
|---|---|---|
| C1 | Sharp logarithmic conditioning of the complete selected Fermi trace, with the same `4/pi^2` leading constant for signed and nonnegative coefficients | [Paper, prior-work audit, and unconditional Lean limits](../3-formalized/thim-sharp-physical-fermi-asymptotic.md) |

C1 includes the supporting observability, instability, ray, and sharp-asymptotic
lemmas. None is separately counted. The final source/olean check, all public
axiom audits, wiring, index regeneration, and generated-file lint passed.
The prior-work audit distinguishes the native physical theorem from classical
Hardy/path ingredients; it makes no unconditional external-priority claim.

Closed C1 extension: [finite-horizon positive-cone gap and odd-trace centering](../3-formalized/thim-finite-horizon-positive-cone-gap.md).
The exact `K_3^+ < K_3` gap, positive-cone maximizer, and centering survivor
are formalized in four supporting leaves. Named source/olean checks, all 48
public axiom audits, imports, index regeneration, and generated-file lint
passed. Classical centering and the two-variable maximum do not justify a
separate contribution. Universal cone equality is retired with its formal
positive survivor; the count stays 1/100.

Closed, uncounted extension: [sharp corrupted valuation-clock recovery](../3-formalized/thim-corrupted-valuation-clock-recovery.md).
Four named leaves and 24 public declarations prove the exact mixed-fault clock
and ambiguity below it. The final significance audit recovered relevant 2020
ultrametric resolving-set classifications. Retain the native formal sharpening
as infrastructure; count increment zero. All named source/olean checks passed;
final imported-axiom audit and generated index/lint are pending.

Next direction is still in prior-work audit. Weighted Fermi/dyadic searches found
existing weighted Hardy and Fermi–Nyman theory. No new theorem or contribution
is claimed from those hits. Arbitrary nonadaptive GCD scheduling also overlaps
known ultrametric metric-basis structure and is not independently counted.

## Earlier checkpoints (superseded)

The first source- and axiom-verified candidate package is
`FermiValuationSamplingAndPronicObservability.lean` (19 public declarations).
Its exact fixed-horizon support classification, sharp reciprocal-cell constants,
and alias obstruction are recorded in
`../3-formalized/thim-fermi-valuation-observability.md`. Qualification as a
significant contribution remains separate from successful compilation.

The second is `FermiSelectedCoefficientTransportAndRecovery.lean` (nine public
declarations), recorded in `../3-formalized/thim-selected-fermi-coefficient-observability.md`.
It recovers the entire coefficient vector from selected Fermi boundaries via
explicit dyadic coefficient transport and proves a uniform 3/2 inverse
coefficient-energy bound after arithmetic inversion of the observations.
`FermiSelectedCoefficientSharpInverse.lean` proves optimality of 3/2 and has
also passed source and axiom audits. All three leaves are wired; formal lint
with generated-file checking passed at that checkpoint. Neither package is counted yet.

The complete-trace package is recorded in
`../3-formalized/thim-full-trace-valuation-depth-stability.md`.
`FermiValuationDepthAndFiniteWindowStability.lean` and
`FermiCompleteTraceValuationStability.lean` now prove unconditional finite and
complete-trace upper bounds with factor `(L+4)*(L+1)`, `L=Nat.log 2 N+1`.
Both passed source and public-axiom audits.
`FermiDyadicRampAndQuadraticTraceLoss.lean` now supplies matching quadratic
lower growth and refutes every horizon-independent inverse constant. All six
leaves are source/axiom-verified and wired; formal lint with generated-file
checking passed at the six-leaf checkpoint. The failed uniform route records its positive
survivor in `../5-failed/thim-horizon-uniform-selected-fermi-coercivity.md`.
Qualified count remains zero: abstract finite-chain Hardy growth is prior work.

`../3-formalized/thim-nonnegative-fermi-trace-conditioning.md` records the stronger
obstruction for nonnegative coefficients. Its seventh leaf,
`FermiNonnegativeDyadicRampTraceObstruction.lean`, passed source and all seven
public-axiom audits and is wired. It reuses the corpus inverse-square interval
bound for the endpoint correction. After the concurrent BiScale umbrella was
completed, fresh index regeneration and global generated lint both passed.
All seven leaves are source/axiom-verified and wired. The extension adds no
separately counted contribution.

## Continued corpus audit, 2026-10-19

The follow-up search protocol recovered prior work missed by the initial broad
deep query. `finiteGridRunLength` returned 26 hits, all inspected; source
references led to BiScale's `finiteGridExtension_stability`,
`finiteGridExtension_sharp`, and `pathSineValue_adjacent`, then the generic
`RHTower.norm_inner_nilpotent_contraction_le_sine`. Source, compiled artifacts,
and a `/tmp` toolchain probe were checked; the three main theorem axiom audits
use only standard Lean axioms. Reuse this machinery rather than reprove a
classical path inequality.

Other checks: `sieve support dyadic` returned 90 hits across five pages, all
inspected; these concern size intervals rather than consecutive 2-adic admission
levels. `valuation bounded gap` returned 13 hits, all inspected. The second
deep search inspected 20 candidate statements, 20 source arguments, two proposed
proof ideas and one ingredient set. The proposed ingredient set concerned
unrelated spectral decay and was rejected. Its 74,258-file source inventory was
complete, but 57,023 compiler entries remained pending, 2,658 stale and 2,654
unavailable. Retrieval completion is not complete proof verification.

The active formalization target is
`../3-formalized/thim-sharp-physical-fermi-asymptotic.md`: its paper proof gives
the actual pronic inverse constant's leading coefficient `4/pi^2`, including
the nonnegative cone. No Lean limit theorem exists yet. Existing sine constants
and generic bounded-gap Poincare mechanisms are prior work; neither is counted
as a contribution. Qualified count remains 0/100.

The eighth leaf, `FermiMixedBoundaryRayStability.lean`, now verifies the
normalized Fermi difference identity, the terminal-centered mixed-boundary sine
inequality, and the exact horizon half-decay/terminal observation relation.
Its source and all six public axioms passed; it is wired and index regeneration
passed. Global generated lint passed. These are ingredients of the new paper theorem,
not a formalized asymptotic or separately counted advances.

The ninth leaf, `FermiPronicRayDecomposition.lean`, verifies the exact
odd-part/dyadic decomposition of both complete physical energies, including
the different weight levels for sieve values and selected jumps. Source,
all three original public axiom audits, index regeneration, and global lint passed.
The sharp asymptotic is still being formalized.

The tenth leaf, `FermiPronicRayWeightAndTailControl.lean`, now contains verified
physical weight comparisons and an explicit complete-ray sine bound including
the exact post-horizon geometric tail. Source, all nine public axiom audits,
and index regeneration passed; the leaf is wired and global generated lint
passed. The sharp asymptotic remains open in Lean.

The eleventh leaf, `FermiPhysicalTraceSineUpperBound.lean`, now proves the
complete physical trace sine upper bound. It reuses the corpus path inequality,
physical ray weights, and exact complete-ray tail control. Source and all four
public axiom audits passed; the leaf is wired and index regeneration passed.
The ninth leaf's added joint-summability theorem also passed source and its
standard-axiom audit. The concurrent `BiScaleUncertainty.SieveAffineTranslationAnchoring`
umbrella import appeared; refreshed index and global generated lint passed.
No unrelated file was changed to silence this gate. Matching nonnegative sharpness and the
asymptotic limit were still unfinished at that checkpoint.

The twelfth leaf, `FermiPhysicalSineAsymptotics.lean`, proves the
unconditional upper half of the sharp asymptotic: for every `ε>0`, uniformly
over all coefficient inputs at sufficiently large dyadic horizons,
`P_(2^r) <= (4/pi^2+ε)*r^2*Q_(2^r)`. Source and the public axiom audit passed;
only standard axioms occur. The leaf is wired and index regeneration passed;
global generated lint failed on the concurrent unwired module
`BiScaleUncertainty.CoprimeOverlapQuarticReadout`, with no error in this leaf.
The matching nonnegative lower family and
full sharp limit remain unfinished. Qualified count stays 0/100.

Focused corpus search recovered `HTGeometry.sum_cos_odd` after a broad deep
packet query missed it. Its source and actual Lean interface were verified;
it gives exact cosine-profile mass `(2*r+1)/4`. Scratch proofs of that mass,
the exact finite difference energy, and nonnegative coefficient differences
passed with standard axioms. The actual finite-horizon coefficient synthesis
and physical trace lower bound are still being formalized.

The thirteenth leaf, `FermiNonnegativeCosinePhysicalTraceLowerBound.lean`,
now verifies the explicit nonnegative dyadic cosine family, positive complete
selected energy, and its finite global physical ratio bound. Source, olean,
and all four public axiom audits passed with only standard axioms; the leaf
is wired and index regeneration passed. At `r=L+1>=2`, `S=(2*r+1)/4`,
`lambda=2-2*cos(pi/(2*r+1))`, it gives `(S-1)*Q<=lambda*S*P`.
The matching asymptotic lower and exact characterization of admissible leading
constants passed the combined scratch check with standard axioms. The former
upper-only module was renamed `FermiPhysicalSineAsymptotics.lean` and expanded
to include these results; its named source/olean check and index regeneration passed. The exact sharp
leading coefficient is `4/pi^2` on both the signed and nonnegative classes.
Both literal dyadic supremum limits passed scratch Lean and standard-axiom audits.
The general-horizon extension is written in scratch, reusing the existing
`sieveSeq_horizon_band_sub`; its prerequisite module needs an olean before checking.
The generated-index lint gate passed after the concurrent orphan module was wired.
The fourteenth leaf, `FermiPhysicalOptimalConstants.lean`, now proves all four
literal supremum limits, including real-logarithm normalization at every horizon.
Its named source/olean check, all six public axiom audits, umbrella wiring,
index regeneration, and global generated-file lint passed. The native package
is qualified once as C1 above. Current count is 1/100.

## Log

- 2026-10-18 — Programme initialized from explicit renewed user goal. Earlier
  completed programmes and concurrent work are prior art and are not counted here.
