# Burnol cubic: complete theta-channel classification

- **ID:** TG-BTQT-001
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** TG source loop; `PrimeBurnolThetaModularHolonomy` and `PrimeBurnolThetaCubicTraceCancellation`.
- **Statement:** Every prime-depth block of the literal density-weighted Burnol cubic is
  symmetric and traceless in the two theta coordinates. Its ordinary trace against any
  prime-mixing matrix acting identically on those coordinates is zero.

## Problem and scope

The earlier cutoff theorem covers diagonal prime-depth masks, which commute with the
theta frame. A spectral cutoff of the complete Gram can mix primes and need not commute
with that frame. The candidate was to recover cubic charge using these noncommuting
cutoffs. The theorem below excludes this candidate without deleting any cross-prime entry.
It does not retire TG or exclude theta-sensitive or singular source constructions.

## Exact source and proof

Use any injectively labelled finite literal Burnol packet, with its complete invertible
Gram G and every original clock parameter retained. Set

```
c = G tensor I_2,  p = I tensor diag(1,0),  q = u p u^-1,  r = c^-1 q c,
C = (r-p)^3 - (r-q)^3 - (q-p)^3,  D = c C,
K = I tensor [[0,-1],[1,0]].
```

Here u is the actual prime-dependent sech/tanh theta rotation. No Xi zero or spectral
location premise enters these definitions.

1. Each rotation commutes with the same quarter turn K; c commutes with K too.
2. `K p = (1-p)K`. Transport through u and c gives `K q = (1-q)K` and
   `K r = (1-r)K`.
3. Each of r-p, r-q and q-p anticommutes with K. Their cubes do too. Hence `KD=-DK`.
4. At each pair of prime-depth labels i,j, this matrix equation says exactly
   `D_ij = [[A_ij,B_ij],[B_ij,-A_ij]]`.
5. For every prime-depth matrix W, the diagonal theta sum of `(W tensor I_2)D`
   vanishes separately at every prime-depth label. Thus its ordinary trace is zero.

These are finite algebraic identities. They require no analytic estimate, numerical
experiment, limiting interchange, unproved producer, or extra axiom.

## Positive survivor

The two matrices `A_ij=D_(i,0),(j,0)` and `B_ij=D_(i,0),(j,1)` reconstruct D exactly.
An arbitrary reporter E sees precisely

```
Tr(E D) = sum_i sum_j [
  (E_(i,0),(j,0)-E_(i,1),(j,1)) A_ji
  +(E_(i,0),(j,1)+E_(i,1),(j,0)) B_ji ].
```

The obstruction therefore identifies surviving source information rather than only
announcing trace zero. A continuing construction must use these theta-sensitive channels
or change the common quarter-turn symmetry, with arithmetic provenance and the cofinal
source-to-Xi comparison proved separately. No index integrality is claimed for these readers.

## Novelty and verification

Internal delta from the checked corpus: arbitrary prime-mixing reporters, complete block
classification, and exact reporter-channel pairing; earlier literal theorem used diagonal
masks. No external novelty claim.

Production leaf `formal/GaloisForLFunctions/RHTower/PrimeBurnolThetaQuarterTurn.lean`
is wired to RHTower. Public theorems:

- `RHTower.primeBurnolThetaWeightedCubic_diagonal`
- `RHTower.primeBurnolThetaWeightedCubic_offDiagonal`
- `RHTower.primeBurnolThetaWeightedCubic_block`
- `RHTower.primeBurnolTheta_primeMatrix_trace_eq_zero`
- `RHTower.primeBurnolThetaWeightedCubic_trace_pairing`

Direct check (2026-10-01), exit 0 without warnings:

```
lake --old env lean -o .lake/build/lib/lean/GaloisForLFunctions/RHTower/PrimeBurnolThetaQuarterTurn.olean GaloisForLFunctions/RHTower/PrimeBurnolThetaQuarterTurn.lean
```

Separate scratch import and `#print axioms` audit exited 0. Each theorem depends only on
`propext`, `Classical.choice`, and `Quot.sound`. Public statements have packet data and
parameters, with no unproved analytic premises. No full or umbrella build, numerical
experiment, `native_decide`, or heartbeat increase was used.

Generated indexes refreshed. Repository lint failed on eleven unrelated unwired RHTower
leaves; this leaf was not among the errors. The overall RH goal remains open.
