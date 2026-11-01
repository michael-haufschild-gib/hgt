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
| 4.1, centered sieve and pinching | Matched cosine prime-side certificate and signed prime-pair discrepancy | Densities arbitrarily close to one can have logarithmically divergent signed discrepancy. Actual disjoint-pair pinching is now positive at every fixed positive bandwidth, including `4/3`. |
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

The [matching cosine coefficient](../3-formalized/cosine-shape-one-improves-trans-threshold-calibration.md) improves the box rate by at least `43λ/7500` for `λ≥1`, leaving margin `79/1250` above three quarters at `4/3`. All six theorem audits use standard axioms; the leaf passes and is wired. The [matching prime-Gram certificate](../0-backlog/cosine-prime-certificate-with-explicit-pinching.md) and signed prime-pair source estimate remain open.

The [raw normalization audit](../3-formalized/stabilizer-odd-pair-normalization-audit.md) gives exact complete-period mean β/2 for the odd-pair packet. The source scalar 1/4 has mean 1/8; scalar 2 uniquely gives mean one. Its seven theorem audits and focused source check pass. This concerns arithmetic weights before the signed coalescent kernel; no actual prime-pair discrepancy bound follows.

## Completion gates

- [ ] Each route's arithmetic conjecture proved or precisely falsified.
- [ ] Every dependency-closed new theorem and positive survivor formalized.
- [ ] Leaf checks, transitive axiom audits, umbrella imports.
- [ ] Requested strip/proportion consequences proved, or exact remaining gaps recorded without claiming those consequences.
