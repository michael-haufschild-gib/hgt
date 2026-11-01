# Argon: quasi-RH and critical-line proportion

- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Source:** `docs/reports/review-3110/argon.md`, §§3–4.
- **Goal:** Prove the proposed arithmetic improvements and their zero consequences, or prove precise obstructions with positive survivors. Local corpus only; no numerical experiments.

| Route | Exact unresolved input | Verified qualification |
|---|---|---|
| 3A, projected shift moments | Signed fourth-moment aggregate for actual detector windows, followed by source transport | New literal integer-interval family has power-sized excess even at cube-root cardinality. Exact line-occupancy fourth-moment floor and sharp box-occupancy bounds distinguish the surviving two-coordinate window problem. |
| 3B, cyclotomic near band | Moving-conductor near-band energy at exponent `5/3+ε` or `3/2+ε` | Far-tail estimate alone does not supply either strip. |
| 3.4, JAS consequence | Unconditional quasi-RH plus remaining dressed positivity | Receiver is already formalized; neither premise is discharged by the report. |
| 4.1, centered sieve and pinching | Signed prime-pair discrepancy and positive pinching credit at bandwidth above one | Numerical factor-two calibration is not an arithmetic estimate. |
| 4.2, seven-center source | Literal finite phase-preserving source majorant | Receiver alone does not prove its source bound. |
| 4.3, two grids / fourth moment | Uniform slack density, or actual Gram fourth-moment upper bound | Non-simultaneous exact locking does not by itself imply a uniform quantitative gap. |

## Route 3A: interval shortcut falsified; balanced windows open

`ArithmeticHarmonicAnalysis/FiniteField/IntegerIntervalResonance.lean` constructs an unbounded prime-field interval family with `B³≤q` and `16 M₄≥t q B²`, where `t≍q^(1/6)`. `LineOccupancyMoment.lean` and `CoordinateBoxLines.lean` give the positive survivors. All three leaves pass focused checks and are wired into `ArithmeticHarmonicAnalysis`; all ten theorem audits contain only `propext`, `Classical.choice`, and `Quot.sound`. The [formalized card](../3-formalized/integer-intervals-retain-subfield-resonance.md) contains the complete mathematical statements and proofs.

The actual cached detector `ProbeGramCommon.jointExtension` retains Eisenstein lattice variables, fixed ray data, ideal characters, and a global extension factor. The interval counterexample does not identify that full source with its obstruction. No improved detector exponent follows yet. The balanced-box fourth moment and composite-conductor transport remain open.

## Next conjecture: route 3B near-band localization

The actual coefficient is `(ψ(j−1)−(j−1))/(j sqrt(j−1))`. Its cyclotomic packet is a Fourier transform of coefficient prefixes, not a bare prime exponential sum. Test whether a fixed collection of low modes already detects the zero-width obstruction; this would distinguish genuine moving-conductor cancellation from mere reduction of mode count. Sources: `ChebyshevCyclotomicCompletion`, `ChebyshevCyclotomicTail`, and `CyclotomicCoercivity.prefixPacket_difference`. No such fixed-mode theorem is asserted yet.

## Completion gates

- [ ] Each route's arithmetic conjecture proved or precisely falsified.
- [ ] Every dependency-closed new theorem and positive survivor formalized.
- [ ] Leaf checks, transitive axiom audits, umbrella imports.
- [ ] Requested strip/proportion consequences proved, or exact remaining gaps recorded without claiming those consequences.
