# WP04 — OPEN

Main half-integer counting target remains open. The new source-only L1 alternative proves arithmetic rigidity plus RH or failure of every exponentially summable periodic representation with harmonics 2k log q, q≥2. All resonances and the actual measurable trace are retained. No periodic representation is supplied by hW. The independent phase-variation obstruction remains: either λ=Λ on n≥2 and RH holds, or its metric total variation exceeds K*T^α eventually, for every α<1 and K. This improves the previous residual-mass obstruction by charging observed phase changes rather than a real phase lift. No extra premise has been promoted to a producer.

Thirty-eight compiled leaves cover the finite-remainder, global-power, quiet-scale and intrinsic phase-variation obstructions, plus the actual-source frequency contour and factorization bridges:

- `WeilWorkQuantizationKernel.lean`: uniform weighted domination and interval inversion.
- `WeilWorkQuantizationBoundaryPhase.lean`: canonical interval phase on one common full-measure endpoint set.
- `WeilWorkQuantizationEndpointPhase.lean`: endpoint-inclusive limits, with half the atom mass at each endpoint.
- `WeilWorkQuantizationRadialBoundary.lean`: primitive normalized at 2; finite phase limits and exponential radial traces at every height; measurable trace and conjugation symmetry.
- `WeilWorkQuantizationRadialGrowth.lean`: arithmetic normalization, open-strip growth, locally integrable quotient trace, and compact contour convergence.
- `WeilWorkQuantizationSubpolynomial.lean`: every positive power exponent for the actual open-strip quotient and everywhere-defined radial trace, with no continuous critical edge.
- `WeilWorkQuantizationRadialRemainder.lean`: refined actual radial remainder, from finite rectangle differences and arithmetic resonance subtraction.
- `WeilWorkQuantizationPhaseCoupling.lean`: the actual reflected trace forces every represented resonant sum B(m) to equal the nonzero B(1). Clean final direct leaf audit passed; all three declarations use only the three standard axioms (phase-coupling-lean-audit.txt). This is a necessary constraint on a representation, not a source representation theorem.
- `WeilWorkQuantizationLaurentInverse.lean`: the inner Laurent series in inverse coordinates, its analytic negative exponential, nonvanishing on the full exterior, exact multiplicative factorization and decaying Taylor coefficients. Clean final leaf audit; all eight declarations use only the three standard axioms (laurent-inverse-lean-audit.txt). Classical prerequisite, not an independent novelty claim.
- `WeilWorkQuantizationQChain.lean`: polynomial growth of the actual rescaled q-power coefficients; exact and convergent q-chain equation with nonzero geometric right side. Clean final leaf audit; all fourteen declarations use only the three standard axioms (qchain-lean-audit.txt).
- `WeilWorkQuantizationPairing.lean`: two first moments pay the full double-series interchange for polynomial-growth arithmetic coefficients. Every annihilator vanishes at the actual q-decay point; the nonzero analytic exterior inverse cannot do so. Clean final direct leaf audit.
- `WeilWorkQuantizationCircleCoefficient.lean`: termwise circle integration, exact bilateral Laurent coefficients, exterior-series multiplication and all nonpositive coefficient vanishings for a strictly positive analytic factor. Clean final direct leaf audit.
- `WeilWorkQuantizationPositiveFactor.lean`: the actual represented canonical phase excludes the precise strictly positive exterior factorization. This connects the arithmetic obstruction to the analytic annihilator without a Hardy-space premise on the arithmetic sequence. Clean final direct leaf audit; no representation or winding factorization is asserted to follow from hW.
- `WeilWorkQuantizationPeriodicSymbol.lean`: actual analytic Laurent symbol, unit-circle unimodularity and a nonzero annulus, all constructed from the weighted representation.
- `WeilWorkQuantizationAnnulusLog.lean`: integer winding of the actual analytic loop and a winding-normalized logarithm on its annulus.
- `WeilWorkQuantizationWindingFactor.lean`: construction of the analytic factors and arithmetic exclusion of positive winding.
- `WeilWorkQuantizationCumulativeContinuity.lean`: local subunit mass and continuous exponential phase force continuity of the actual cumulative lift; continuous logarithmic differences are constant on connected sets.
- `WeilWorkQuantizationPeriodicRigidity.lean`: bounded actual cumulative phase, represented-source rigidity, and final hW-only `quantization_rigidity_or_no_periodic_phase`. Clean final direct leaf and standard-axiom audits.
- `WeilWorkQuantizationFrequencySum.lean`: countable exponentially summable families retain all source resonances under radial summation. Clean final leaf audit; all three declarations use only the three standard axioms (frequency-sum-lean-audit.txt).
- `WeilWorkQuantizationResonance.lean`: hW alone supplies the exact shifted-resonance limit for the actual measurable trace, exponential coefficient bounds and common-kernel scaling. Clean final leaf audit; all thirteen declarations use only the three standard axioms (source-resonance-lean-audit.txt).
- `WeilWorkQuantizationResonantTerms.lean`: exact shifted coefficient scaling, fixed-frequency nonresonant limits and a summable radial majorant that removes every nonresonant term without a uniform gap. Five declarations passed a clean final leaf audit and use only the three standard axioms (resonant-terms-lean-audit.txt).
- `WeilWorkQuantizationTwistContour.lean`: actual compact radial passage for every linear frequency multiplier, open-strip contour displacement, and a uniform exponential frequency majorant derived from hW.
- `WeilWorkQuantizationRadialPower.lean`: cancellation under an unbounded monotone cumulative phase with sublinear power growth.
- `WeilWorkQuantizationLocalPhase.lean`: bounded cumulative-phase capping with an explicit absolute tail; no global growth bound.
- `WeilWorkQuantizationCumulativePhase.lean`: the canonical finite-interval residual phase, valid almost everywhere and at trace zeros.
- `WeilWorkQuantizationReflectedResidue.lean`: reflected arithmetic residues derived from the actual two Hamburger identities.
- `WeilWorkQuantizationPowerRigidity.lean`: coefficient comparison and final `quantization_rigidity_or_residual_power_obstruction`, whose only substantive input is hW.
- `WeilWorkQuantizationQuietScales.lean`: cancellation along quiet radii and final `quantization_rigidity_or_residual_eventual_power`, with hW as its only substantive input.
- `WeilWorkQuantizationPhaseVariation.lean`: actual circle phase, locally finite metric variation, global Lipschitz profiles and their fundamental theorem.
- `WeilWorkQuantizationVariationLocal.lean`: signed integral localization charged to the actual phase variation, with the original source remainder and absolute tail retained.
- `WeilWorkQuantizationVariationRigidity.lean`: final `quantization_rigidity_or_phaseVariation_eventual_power`, with hW as its only substantive input.
- `WeilWorkQuantizationRadialContour.lean`: uniform signed truncation bound for the canonical trace, including moving lower endpoints; fixed-window radial vanishing.
- `WeilWorkQuantizationRadialMellin.lean`: actual coefficient-theta identity from radial inverse Mellin, reusing the checked source weighted boundary shift.
- `WeilWorkQuantizationRadialTheta.lean`: reflected theta defect and both arithmetic Hamburger/Laplace identities, derived from the actual source.
- `WeilWorkQuantizationRadialLayerCake.lean`: measurable-trace monotone-twist cancellation.
- `WeilWorkQuantizationIntegerFloor.lean`: actual integer atomic submeasure, domination, local integer counts and positive residual measure.
- `WeilWorkQuantizationResidualPhase.lean`: source-derived residual phase and signed cancellation, including boundary zeros.
- `WeilWorkQuantizationFiniteRemainderRigidity.lean`: arithmetic rigidity for finite remainder; final `quantization_rigidity_or_infinite_residual` assumes only hW.

All thirty-eight direct leaf checks passed. K's three leaves passed clean direct audits; all twenty-six declarations use only `propext`, `Classical.choice` and `Quot.sound`. Complete output: phase-variation-lean-audit.txt. The new TwistContour leaf exited 0 with an informational `ring_nf` suggestion; all six declarations use only the three standard axioms (twist-contour-lean-audit.txt). Earlier audits remain recorded in EVIDENCE.md. Paper arguments are in PROOF.md, FINITE-REMAINDER.md, SUBPOLYNOMIAL.md, SUBLINEAR-REMAINDER.md, QUIET-SCALES.md, PHASE-VARIATION.md and RESONANT-PERIODIC.md.

Cycle 15's eighteen public declarations and their dependencies, including three private helpers, passed the scratch axiom audit with only the three standard axioms. Full output and final source-obstruction type: pairing-factor-lean-audit.txt. No full or umbrella build ran. Cycle-15 lint reported six unrelated unreachable modules. Latest cycle-16 lint reports fifteen unrelated unreachable modules and no quantization-module error.

For arbitrary `hW`, `exists_fullMeasure_interval_phase` supplies one full-measure endpoint set with vertical interval integral tending to `π μ((a,b])`. `tendsto_exp_four_mul_interval_phase` identifies the corresponding phase limit with `exp(4πi μ((a,b]))`. It does not prove that this phase equals 1.

Difference from starting corpus: fixed-width smoothed counting and singleton radial extraction were already proved. This investigation connects shrinking-width interval phase to the same measure and retains endpoint atoms to construct radial traces everywhere. A parallel current corpus file now constructs an almost-everywhere trace; this overlap is recorded in EVIDENCE.md. The underlying analytic mechanism is classical. Significant scientific novelty is not claimed for these prerequisites.

Theorem F includes arbitrary finite singular-continuous remainder and accumulating fractional atoms. This exceeds the inspected atomic or closed-edge receivers' directly applicable scope. Scientific novelty relative to literature remains provisional. FINITE-REMAINDER.md contains its complete paper argument and compiled dependency map. Full WP04 still requires control of the infinite-remainder alternative. The floor remainder remains asymmetric: infinitely many atoms just below integers can contribute large mass. Existing signed nearest-integer results must be retained when assessing this limitation. Source conjecture H asks whether the actual Herglotz real part has infimum zero. H2 asks for mass-one integer-null mixtures with arbitrarily small critical archimedean energy. The eleventh audit identified H2 as the existing open prime-blind LP margin problem in STATUS CANNOT-496, not a new conjecture. Both remain unproved; NEXT-CONJECTURE.md records the exact hypotheses and missing implications.

Theorem G is formalized: writing R for λ=Λ on n≥2 together with RH, the exact conclusion is

`R ∨ ∀ α<1, ∀ K∈ℝ, ∃ T≥1, K*T^α < ν.real(Icc (-T) T)`.

Its refined contour estimate and measurable cumulative phase cover arbitrary singular-continuous and accumulating fractional remainder. No source theorem currently supplies a residual-growth bound that excludes the second alternative. The final disjunction is unconditional relative to the specified hW; the helper theorem with a growth hypothesis is not a solution of WP04.

Theorem J is formalized, with the same R and actual ν:

`R ∨ ∀ α<1, ∀ K∈ℝ, ∀ᶠ T→+∞, K*T^α < ν.real(Icc (-T) T)`.

A stronger one-sided cumulative version is also proved. Capping the phase and comparing all fixed rescalings of one quiet filter removes G's global-growth requirement. This is an inspected-corpus advance; scientific novelty remains provisional. Linear or faster residual mass remains possible under this theorem, so WP04 is not solved.

Theorem K is formalized. Put `W(x)=exp(2πi*ν.real(Ioc 0 (2*x)))` and let V(T) be its metric total variation on [0,T]. Then

`R ∨ ∀ α<1, ∀ K∈ℝ, ∀ᶠ T→+∞, K*T^α < V(T)`.

Its only substantive input is hW. Integer phase jumps are invisible; almost-integer jumps have small chord cost. No atomicity, atom enumeration, smooth phase or continuous critical edge is assumed. The exact comparison with diffuse mass plus nearest-integer atom distances is a separate unfinished target, not silently asserted here. This strengthens the inspected corpus's discrete two-sided and smooth-lock receivers; scientific novelty remains provisional. Large phase variation remains an open alternative.

L1 is proved in Lean, with its paper proof in RESONANT-PERIODIC.md. The actual phase cannot have an exponentially summable periodic expansion with frequencies 2k log q, integer q≥2, unless rigidity and RH hold. Exact resonant rows, the normalized annular logarithm, positive-winding exclusion, actual cumulative continuity and bounded-lift rigidity are all paid. No periodic representation is supplied by hW. General L and full WP04 remain open; formal novelty alone does not establish scientific significance.

All finished modules are wired into `RHTower.lean`. The latest completed cycle-16 lint failed on fifteen unrelated unreachable modules; no quantization-module error. No full or umbrella build was run. Existence of a positive input remains WP01's separate problem.


Cycle 16 completes L1, the resonant periodic class in RESONANT-PERIODIC.md. General
almost-periodic conjecture L and unrestricted WP04 remain open. The new source theorem
is not justified by formal novelty alone; external scientific novelty remains provisional.
