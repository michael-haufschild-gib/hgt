# Uniform adjacent-divisor compensated remainder

- **ID:** BVI-UNIFORM-ADJACENT-COMPENSATED-2026-10-18
- **Stage:** 3-formalized
- **Type:** THEOREM / dependency-closed paper proof and Lean audit
- **Parent:** `bvi-uniform-renormalized-interior-energy-remainder-2026-10-18.md`
- **Full objective:** Problem 4 strict interior contraction remains open.

## Exact statements

For every e,h>0, there exist 0<delta<1 and C>=0 such that, for N>=1,

    |(1/N)*sum_{n=1}^N F_e(n+1)*F_h(n)-Q(e,h)| <= C*N^(-delta).

Consequently another horizon-independent C>=0 satisfies, for every T>=0,

    |sum_{n=1}^{T-1} (F_e(n+1)*F_h(n)-Q(e,h))
         *(1/(n+1)-1/(T+1))| <= C.

Here F and Q are the existing actual divisor field and adjacent density.
No coefficient moment, convergence-rate, or cancellation premise is added.

## Dependency-closed paper proof

Use the audited asymmetric truncation bound

    |Q_N-Q| <= 2 U_h(D)+4 D U_e(A)+AD/N,
    U_e(A) <= K_e*A^(-e/2),  K_e=sum_d |w_(e/2)(d)|/d < infinity.

Choose alpha=e/(8*(1+e)), D=ceil(N^alpha), A=ceil(sqrt(N)), and
delta=min(alpha*h/2,e/8,1/4). Both ceilings lie between their underlying
power and twice that power. Since alpha<=e/8 and alpha<=1/4, the three
terms are bounded by (2 K_h+8 K_e+4)*N^(-delta).

Multiplying by N bounds the centered partial sums by C*N^(1-delta).
Apply the existing `HTGeometry.abel_bound_of_partialSum_le` and
`HTGeometry.summable_increment` at a=1-delta in (0,1). The boundary is
bounded because T^a/(T+1)<=1. The terminal compensation subtracts the
same partial sum divided by T+1, hence contributes another bounded term.
Set the auxiliary sequence to zero at index zero and convert its range
sum to the exact interval 1,...,T-1. This also handles T=0.

## Corpus reuse

Inputs: `AsymmetricAdjacentDivisorTruncation.lean`, the existing adjacent
mean limit, and the existing HTGeometry Abel/increment theorems. Live
predecessor searches retrieved the exact drift and canonical budget,
plus the completed single-field harmonic remainder. The single-field
rate query restricted to PMDivisorMean returned no hits; that result
does not establish absence of a rate elsewhere.

## Verification

- [x] Dependency-closed paper proof.
- [x] Combined scratch check (85594), exit 0, no diagnostics.
- [x] Original-source check and fresh artifacts.
- [x] Public axiom closure and mathlib name probes.
- [x] Umbrella, source index, formal lint, and whitespace audit.
- [x] Archive and remove completed scratch.

Public Lean statements: `exists_pm_adjacent_divisor_mean_power_rate`
and `exists_pm_adjacent_divisor_compensated_bound`, in
`UniformAdjacentDivisorCompensatedRemainder.lean`.

Original-source audit (96521) exited 0 with no diagnostics and emitted
fresh `.olean` and `.ilean` artifacts. Public axiom audit (4141) exited 0:
both theorems use only `propext`, `Classical.choice`, and `Quot.sound`;
thirteen mathlib name probes passed. Source has 282 lines and SHA256
`c001cdad7f7f040f80dfe376245d6e1811082aeecae88155df99df46c64ee0a3`.
One umbrella import, index refresh (34031), exact retrieval of both public
theorems (4620), and owned-file whitespace checks passed.

Formal lint (97795) exited 1 with 381 existing warnings and two unrelated
errors: unreachable `DilationClockSuccessorSeedCoupling` and package-root
`TransHorizonIncidenceMechanics.lean`. No finding names this leaf. This is
not a global lint pass. Six proof/audit files and six search results were
archived, hash-verified, removed, and verified absent. Certificate:
`logs/bvi-uniform-adjacent-compensated-2026-10-18-manifest.json`.
