# Argon: quasi-RH and critical-line proportion

- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Source:** `docs/reports/review-3110/argon.md`, §§3–4.
- **Goal:** Prove the proposed arithmetic improvements and their zero consequences, or prove precise obstructions with positive survivors. Local corpus only; no numerical experiments.

| Route | Exact unresolved input | Verified qualification |
|---|---|---|
| 3A, projected shift moments | Signed fourth-moment aggregate for actual detector windows, followed by source transport | New literal integer-interval family has power-sized excess even at cube-root cardinality. Exact line-occupancy fourth-moment floor and sharp box-occupancy bounds distinguish the surviving two-coordinate window problem. |
| 3B, cyclotomic near band | Moving-conductor near-band energy at exponent `5/3+ε` or `3/2+ε` | Every positive-power band retains energy abscissa `2Θ` among exponents at least one. Either target strip is equivalent to its near-band bound at any such cutoff. |
| 3.4, JAS consequence | Unconditional quasi-RH plus remaining dressed positivity | Receiver is already formalized; neither premise is discharged by the report. |
| 4.1, centered sieve and pinching | Actual signed cosine prime surplus below its explicit budget | The matching certificate is proved for every `0<λ≤2`, with explicit positive pinching. Unsigned densities arbitrarily close to one can still have logarithmically divergent signed discrepancy. |
| 4.2, seven-center source | Literal finite phase-preserving source majorant | Receiver alone does not prove its source bound. |
| 4.3, two grids / fourth moment | Uniform slack density, or actual Gram fourth-moment upper bound | Non-simultaneous exact locking does not by itself imply a uniform quantitative gap. |

## Route 3A: interval shortcut falsified; balanced windows open

`ArithmeticHarmonicAnalysis/FiniteField/IntegerIntervalResonance.lean` constructs an unbounded prime-field interval family with `B³≤q` and `16 M₄≥t q B²`, where `t≍q^(1/6)`. `LineOccupancyMoment.lean` and `CoordinateBoxLines.lean` give the positive survivors. All three leaves pass focused checks and are wired into `ArithmeticHarmonicAnalysis`; all ten theorem audits contain only `propext`, `Classical.choice`, and `Quot.sound`. The [formalized card](../3-formalized/integer-intervals-retain-subfield-resonance.md) contains the complete mathematical statements and proofs.

The actual cached detector `ProbeGramCommon.jointExtension` retains Eisenstein lattice variables, fixed ray data, ideal characters, and a global extension factor. The interval counterexample does not identify that full source with its obstruction. No improved detector exponent follows yet. The balanced-box fourth moment and composite-conductor transport remain open.

## Route 3B: intrinsic near-band localization

The [power-band theorem](../3-formalized/arbitrarily-thin-power-bands-retain-chebyshev-zero-width.md) is formalized: `Far(N,K)≪ε N^(2Θ+ε)/K`, and every fixed band `K=ceil(N^δ)`, `δ>0`, retains energy abscissa `2Θ` among exponents at least one. All eight theorem audits use standard axioms; both leaves pass and are wired. Either target strip is equivalent to its near-band subpower bound at any positive power cutoff. No actual improved energy estimate, fixed-mode theorem, or logarithmic-band theorem is asserted.

## Route 4.1: phase-resonance obstruction

The [Frullani resonance family](../3-formalized/frullani-sieve-phase-resonance.md) is formalized: smooth densities arbitrarily close to one, with exact mean one and bounded ordinary interval discrepancy, can have centered signed Frullani integral `(t/2)log R+O(1)`. Even reflection preserves the positive-lag obstruction. All eleven public theorems pass standard-axiom audits; the leaf passes and is wired. This falsifies the unsigned-sieve inference; the actual prime-pair route remains open. The positive survivor is the exact logarithmic residue of the phase-weighted density error.

The [cosine-kernel rigidity theorem](../3-formalized/cosine-kernel-additive-rigidity.md) excludes additive zero triples exactly at nondegenerate cosine parameters. The [explicit triple floor](../3-formalized/explicit-weighted-cosine-triple-floor.md) strengthens this to `θ²/[10(π²S²+θ²)]`. The [actual pinching theorem](../3-formalized/trans-threshold-cosine-pinching-credit.md) gives disjoint-pair and finite-zero-Gram rank–trace credit `δλ=1/[200(10+720π²λ²)²]` at every fixed positive bandwidth. Sampling, explicit floor, and pinching leaves pass focused checks; their thirteen public theorem audits use only standard axioms.

The [matching cosine coefficient](../3-formalized/cosine-shape-one-improves-trans-threshold-calibration.md) improves the box rate by at least `43λ/7500` for `λ≥1`, leaving margin `79/1250` above three quarters at `4/3`. All six theorem audits use standard axioms; the leaf passes and is wired. The [matching prime-Gram certificate](../3-formalized/cosine-prime-certificate-with-explicit-pinching.md) is now proved for every `0<λ≤2`, including the endpoint: `(Hcos(λ)+δλ−ε)N−Sλ≤N0simple`. Its three leaves pass final direct checks; all fourteen audits use standard axioms. The actual signed upper bound for Sλ remains open.

The [raw normalization audit](../3-formalized/stabilizer-odd-pair-normalization-audit.md) and [actual-prime comparison](../3-formalized/stabilizer-incomplete-periods-and-prime-comparison.md) are formalized. Full odd rectangles have nonnegative error at most `2Q³` above `2M²`. At `M=Q²`, actual prime-minus-model mean tends to `1−β/2`: the literal scalar 1/4 leaves 7/8; scalar two uniquely centers it. All nineteen audits use standard axioms, and all three leaves pass final direct checks. This [falsifies raw centering](../5-failed/quarter-scaled-stabilizer-raw-centering.md); the signed narrow-aperture estimate remains open.

The [odd conductor bound](../3-formalized/odd-stabilizer-conductor-error-is-bounded.md)
gives `Σμ²σ₂/φ²≤64Q` and `O(Q)∼(1/2)log Q`. The
[exact Poisson row](../3-formalized/exact-poisson-row-for-the-odd-stabilizer.md)
retains a nonnegative primitive spatial correction. It vanishes through the
sharp support horizon `Qb≤πm`; positive rows occur arbitrarily close beyond it,
[refuting universal negative-row cancellation](../5-failed/fixed-cutoff-negative-row-cancellation.md).

The [aperture and fixed-base bounds](../3-formalized/odd-stabilizer-aperture-and-fixed-base-renormalization.md)
give a cubic tail and a Q-independent row envelope. At fixed m, row/log Q→0
and spatial correction/log Q→`Ωhat(0)/(2πm)`; at the moving horizon,
row/log Q→`−Ωhat(0)/2`.

[Decay-preserving Fourier estimates](../3-formalized/decay-preserving-cosine-transport.md)
now transfer the [literal logarithmic row](../3-formalized/literal-logarithmic-stabilizer-transport.md),
including its square-root pair weight. For each fixed smooth profile its signed
dual error is `≤C O(Q)[T⁻¹+(m/(TR))³]`, its row is bounded by `C O(Q)`, and
its logarithmic taper moment by `C O(Q)/T`. All eight audits and both final
direct checks pass. [Actual standard taper transport](../3-formalized/actual-smooth-taper-stabilizer-transport.md)
also gives a uniform Lipschitz constant two and endpoint variation `C O(Q)/T`.
The [literal pair decomposition](../3-formalized/literal-stabilizer-model-row-decomposition.md)
retains both finite cutoffs and bounds global taper variation by
`C floor(X) O(Q)/T`. Global primitive-correction summation, boundary estimates,
cosine-taper compatibility and actual signed prime discrepancy remain open.

The [uniform coprime-harmonic average](../3-formalized/coprime-harmonic-conductor-average.md)
bounds the all-conductor weighted error by `36864(1+log Q)` for arbitrary
positive horizons. Its supporting logarithmic moment is at most 576.
The [logarithmic square mean](../3-formalized/odd-stabilizer-log-square-mean.md)
is formalized with exact coefficient 1/6 and a finite Abel identity.
The [odd-base quadrature estimate](../3-formalized/odd-stabilizer-spatial-quadrature.md)
is also formalized, including exact taper support and conductor aggregation
`K T(1+L+log((Q+1)T))(1+log Q)`. Weighted coprime-harmonic taper summation
and global signed assembly remain open.

## Completion gates

- [ ] Each route's arithmetic conjecture proved or precisely falsified.
- [x] Every dependency-closed new theorem and positive survivor formalized.
- [x] Leaf checks, transitive axiom audits, umbrella imports.
- [x] Exact remaining strip/proportion gaps recorded; no improved consequence claimed.
