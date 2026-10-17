# Continuous factorial producer with exact prime-grid values

- **ID:** signed-prime-polar-grid-preserving-smoothing
- **Stage:** 3-formalized
- **Type:** THEOREM PACKAGE
- **Scope:** Signed prime–polar contribution 9 of 100; one package.
- **Paper:** `docs/reports/BiScaleUncertainty/SignedPrimePolarContinuousFactorialProducer.md`
- **Ledger:** `docs/reports/BiScaleUncertainty/SignedPrimePolarTransport-FACTS.md`

## Certified result

For N≥1 set ε=1/(4N), qε(t)=min(1,max(0,(1+ε−t)/ε)), and
Uε,K(x)=exp(x/2) sum_{j=1}^K qε(j exp(x)/K). Define
S_N=(Uε,4N−4Uε,2N+4Uε,N)/sqrt(N) on all real x.

The actual test is continuous and supported in [0,log(4N+1)]. It preserves every
positive-integer grid value of the discontinuous factorial bi-null producer:
S_N(log n)=W_N(log n). Thus its literal von Mangoldt atom sequence is unchanged,
finite and absolutely summable. The polar integrand is globally integrable.

The exact pairing is
ν(S_N)=[2B_N−(1+1/(8N))C_N]/sqrt(N),
where B_N is the existing factorial producer and 0≤C_N≤1 is its harmonic correction.
Consequently
|ν(S_N)|≤[10log(4N+1)+3+1/(8N)]/sqrt(N), and 1≤∫ℝ S_N²≤16.

`continuousFactorialProducer (n : ℕ) : C_c(ℝ,ℝ)` uses N=n+1.
`continuousFactorialProducer_certificate` has only that integer input and bundles
exact grid preservation, the pairing bound and both squared L² bounds.
The origin is zero and the top value is two; the test is formally excluded from
being any real compact continuous source's autocorrelation.

## Proof mechanisms

- Integer-product separation εK≤1 gives exact ramp values at every grid endpoint.
- Piecewise FTC evaluates the continuum ramp; both polar branches remain present.
- The linear logarithmic collar correction cancels in the dilation stencil.
- Finite antitone pairing bounds that stencil in [−2,1], yielding the L² upper bound.
- A full closed top interval retains exp(x/2)/sqrt(N), yielding the lower bound.

No pre-floor discrete counterterm, arithmetic conjecture, or numerical experiment
is used. This resolves the scalar continuity and nonvanishing-size obstruction.
It does not establish arbitrary-correlation packet control or positivity.

## Verification

- [x] Dependency-closed paper proof and predecessor audit.
- [x] Actual C_c test, compact support, and exact grid preservation.
- [x] Literal domain admission, exact pairing and unconditional bound.
- [x] Uniform upper and positive lower squared L² bounds.
- [x] Five final direct leaf checks, all exit 0 with empty diagnostics.
- [x] Fourteen scratch axiom reports: propext, Classical.choice, Quot.sound only.
- [x] Five umbrella imports exactly once; index refresh passes.
- [x] Global lint run; eight unrelated unwired modules, no package-local error.

Leaves: `AntitoneDyadicStencil`, `ClampedExponentialRamp`,
`SignedPrimePolarContinuousFactorialLift`, `SignedPrimePolarContinuousFactorialProducer`,
`SignedPrimePolarContinuousFactorialEnergy`.
Evidence: `/tmp/spp9-*-final.log`, `/tmp/spp9_final_axioms.lean`,
`/tmp/spp9-final-axioms.log`, `/tmp/spp9-index.log`, `/tmp/spp9-lint.log`.
The facts ledger records the exact unrelated lint errors.

Searches `/tmp/spp9-search.json` and `/tmp/spp9-alternating-search.json` are
partial. Candidates and source arguments were inspected; the smooth grid-source
precedents impose autocorrelation zeros and do not supply this construction.
No external novelty claim is inferred from retrieval. The finite stencil, ramp
calculus, arithmetic preservation and norm certificates count together once.

The subsequent actual-source construction is now formalized in
`3-formalized/signed-prime-polar-factorial-source-factorization-2026-10-17.md`.
