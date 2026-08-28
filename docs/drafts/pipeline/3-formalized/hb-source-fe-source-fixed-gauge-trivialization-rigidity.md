# HB source-FE source-fixed gauge trivialization rigidity

- **ID:** HC60
- **Stage:** 3-formalized
- **Type:** THEOREM / SOURCE-GAUGE RIGIDITY / HARD FRONTIER
- **Source:** HC59 semilinear coherence; literal polarized source amplitude; rank-one anti-linear
  Hilbert 90
- **Statement:** Literal source-FE cocycle is algebraically gauge-trivial on every Xi orbit, but no
  diagonal gauge preserving literal source coordinates can realify it off critical line. Global
  source-fixed real trivialization exists exactly under RH.

## Corpus-led conjecture

For diagonal basis gauge `b : XiZeroCopy -> C`, set

```text
kappa^b(q) = b(Rq)^(-1) * kappa(q) * conj(b(q)).
```

The explicit amplitude gauge

```text
b_src(q) = if S(q)=0 then 1 else S(q)
```

should be nowhere zero and satisfy `kappa^b_src(q)=1` unconditionally, by exact source transport
`kappa(q) conj(S(q))=S(Rq)`. Thus scalar Hilbert-90 trivialization is no obstruction.

Impose physical source-fixing:

```text
b(q) * S(q) = S(q)  for every q.
```

Off wall `S(q) != 0`, so `b(q)=1`; same at `Rq`. Therefore `kappa^b(q)=kappa(q)`, whose imaginary
part is nonzero off wall. A global nowhere-zero source-fixed gauge with real transformed cocycle
should exist iff RH.

## Predicted consequences

1. Exact diagonal cocycle-gauge formula.
2. Explicit amplitude gauge is nowhere zero and trivializes cocycle to one globally.
3. Source-fixed gauges equal one at every off-wall copy.
4. Source-fixed gauge leaves cocycle unchanged off wall.
5. A source-fixed gauged cocycle can be real only on critical line.
6. Existence of global nowhere-zero source-fixed real trivialization is equivalent to RH.
7. Algebraic Hilbert 90 cannot supply missing producer; source compatibility is exact obstruction.

## Hostile checks

- Use anti-linear basis-change formula with conjugation on input gauge.
- Handle source-extinction wall separately; do not divide by zero.
- Prove amplitude gauge nonzero and global trivialization at every multiplicity copy.
- Require source coordinates fixed, not merely source zero locus.
- Prove global converse with explicit gauge.
- Closed Lean, no new axioms.

## Novelty boundary as of 2026-08-28

Required corpus searches found abstract rank-one anti-linear Hilbert 90, literal source transport,
source-compatibility uniqueness, HC59 semilinear coherence, and cocycle reality iff critical line,
but no explicit global source-amplitude trivialization paired with source-fixed gauge rigidity.
Primary QNM literature searches found normalization-dependent amplitudes/phases and conserved
bilinear source projections (including arXiv:2210.15935), but no zeta-FE source-fixed gauge
classification or RH equivalence. Search is bounded, not exhaustive.

## Gates

- [x] 0 -> 1 in-progress: corpus gap, exact conjecture, hostile proof route, bounded literature audit
- [x] 1 -> 2 fully-proven: dependency-closed paper proof
- [x] 2 -> 3 formalized: closed Lean theorem, target build, axiom/lint audit, umbrella wire
- [ ] 3 -> 4 publication-ready: independent priority audit and standalone exposition

## Log

- 2026-08-28 — Opened after HC59 proved semilinear coherence iff RH and gauge search exposed
  unconditional Hilbert-90 triviality as the remaining normalization loophole.
- 2026-08-28 — Proved an explicit nowhere-zero amplitude gauge trivializes the cocycle
  unconditionally, while every source-fixed gauge is pointwise forced to be the identity off the
  critical line. Consequently a global nowhere-zero source-fixed real cocycle trivialization exists
  iff RH. Formalized in
  `GaloisForLFunctions.RHTower.ThetaCuspHawkingBMSourceFESourceFixedGaugeTrivializationRigidity`.
  Direct Lean check passed; target build passed (`12025/12025`); all nine public theorems audit to
  standard axioms only (`propext`, `Classical.choice`, `Quot.sound`); umbrella import wired. Global
  lint reports only unrelated umbrella-reachability failures and no HC60 violation.
