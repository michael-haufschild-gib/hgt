# SZ: canonical core energy cannot be controlled by a whole-ray norm

- **ID:** sz-canonical-core-bulk-energy
- **Stage:** 5-failed (whole-ray norm controller); positive survivor formalized
- **Type:** THEOREM [L], unconditional source obstruction
- **Source:** docs/reports/rh-current-frontier-map.md, route SZ
- **Statement:** A canonical core's large negative endpoint forces large physical energy on an interval at that same cutoff; the whole-ray diagonal mean cannot have a polylogarithmic core bound.

## Hard target and conjecture tested

The signed original-cutoff Wronskian remains open. A candidate closure is
to use the exactly admitted finite-core Mellin pairing and bound its diagonal
energy along canonical prime cores by a polylogarithm. The exact insertion
renewal would then have to control the cumulative signed cross term. The
existing moving-head asymptotic instead forces a bulk-energy obstruction.

Let P_N=criticalMovingSquareCore N, H_P=mobiusDivisorContinuousHead P,
and E(P)=integral_1^infinity H_P(x)^2/x^3 dx. Existing source identities
give H_(P_N)(N)=criticalMovingPrimeHead N, and the latter times
log(N)^2/N^(3/2) tends to -h, h=divisorHarmonicBoundary/3>0.
The canonical core covers primes through sqrt(N); it is finite and its
physical integral is already admitted for each N.

## Dependency-closed paper proof

Write U=divisorContinuousUnitHead. Its exact Abel integral has density
primeFreeDivisorDefect(floor t)/(2*sqrt t) for t>1, zero below 1. The
corpus's square-root divisor bound makes this density at most 12 in
absolute value. Hence U is globally 12-Lipschitz. On [0,N], only d<=N
can contribute to H_P. Finite Mobius dilation, |mu|<=1, and
sum_(d<=N)1/sqrt(d)<=2sqrt(N) give

    |H_P(x)-H_P(y)| <= 24sqrt(N)|x-y|,

uniformly in every finite core P. No growing-core source bound is assumed.

At a canonical endpoint put B=-H_(P_N)(N)>0 and L=24sqrt(N).
Since H_P(0)=0, B<=L*N. Therefore delta=B/(2L) lies in (0,N/2].
Throughout [N-delta,N], H_P<=-B/2. For N>=2 this interval lies above 1
up to an irrelevant endpoint. Its contribution to the admitted energy is

    E(P_N) >= delta*B^2/(4N^3) = B^3/(192*N^(7/2)).

The actual negative endpoint asymptotic consequently gives, eventually,

    E(P_N) >= c*N/log(N)^6

for a fixed positive c. Thus the proposed polylogarithmic whole-ray norm
controller fails, even though each finite-core norm exists. This is a
physical interval at the original endpoint, not an inference from a Mellin
jet or a pointwise value on a null set.

## Positive survivor and scope

The survivor is the uniform local regularity and the cubic endpoint-to-bulk
energy law, followed by its literal canonical-core consequence. It quantifies
how the moving signed head must be compensated before taking a growing-core
physical norm. It neither refutes RH nor estimates the remaining complete
source after compensation. The exact survivor and canonical consequence
have passed Lean and standard-axiom audits.

## Lean results and verification

- `MobiusDivisorUniformLocalRegularity`: global unit-source Lipschitz law and
  core-independent local bound, including the zero ray and every integer edge.
- `MobiusDivisorEndpointBulkEnergy`: cubic endpoint-to-bulk law, at the same
  physical cutoff, for the admitted whole-ray diagonal mean.
- `MobiusDivisorCanonicalBulkEnergy`: unconditional existence of c>0 with
  eventual E(P_N)>=cN/log(N)^6; for every real C and natural k, eventually
  E(P_N)>C log(N)^k. All endpoint/source premises are discharged here.

All three leaves pass clean foreground `lake --old env lean <leaf> -o <olean>`
audits and are wired into RHTower; no full or umbrella build. All five public
theorem axiom queries return only propext, Classical.choice, Quot.sound.
No numerical experiments, added axioms, placeholders, or heartbeat changes.

## Remaining hard problem

For full prime exhaustion at a physical cutoff T, only the causal interval
x<=T is needed. The canonical obstruction occurs near the square of its
prime cutoff and therefore does not rule out that original-source budget.
The complete signed two-channel kernel retains both e/d and T/e; replacing
its finite integral by the infinite-ray norm loses the required cancellation.
Complete signed cross-term and Wronskian control remain open. This card closes
only the proposed canonical whole-ray norm controller.

## Corpus audit

Search1182618 is partial with mostly pending/stale compiler metadata; no
matching bulk theorem was returned. Inspected exact sources:
DivisorContinuousHeadRegularity, MobiusDivisorContinuousHeadBlocks,
MobiusDivisorCriticalMovingHeadAsymptotic, MobiusDivisorCriticalMovingCoreObstruction,
MobiusDivisorDilationMean and MobiusDivisorDilationMeanRenewal.
ShellAnchorDebt addresses fresh dense shells above a fixed old core, not this
canonical endpoint sequence. This is a local novelty check only.

## Log

- 2026-10-02 — Paper proof derived while attempting the cumulative finite-core pairing bound. Formalization begins with source regularity, then the bulk law and canonical consequence.
- 2026-10-02 — All five public theorems audited; exact positive survivor formalized. Controller retired, RH unresolved.
