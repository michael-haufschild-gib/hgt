# Source normal-cone divisor conservation

- **ID:** `source-normal-cone-divisor-conservation-law`
- **Stage:** 5-failed
- **Type:** FAILED UNIVERSAL REINTERPRETATION / POSITIVE SURVIVOR EXTRACTED
- **Scientific status:** `[FALSIFIED]`
- **Closed:** 2026-07-30

## Exact killing result

The original hunch claimed that bounded-exponent Euler sources generated the reciprocal completed
Riemann \(\Xi\) determinant at exceptional scale. They do not. The exact source family is
\[
 A_m(s)=\frac{\zeta(s)}{\zeta(ms)},
\]
and its inverse-depth limit is
\[
 A_m(u/m)\longrightarrow\frac{\zeta(0)}{\zeta(u)}
 =-\frac1{2\zeta(u)}.
\]
This produces reciprocal zeta, not reciprocal \(\Xi\). The missing Gamma and polynomial factors are
not consequences of the bounded-exponent arithmetic filtration. Importing them afterward would
make the claimed source generation decorative.

The generic identities
\[
 F(\varepsilon u)/F(u)\to F(0)/F(u),\qquad
 \operatorname{ord}_\rho(F(0)/F)=-\operatorname{ord}_\rho F
\]
remain correct but are routine complex analysis and receive no novelty credit.

## Representation lesson

Endpoint completion was the wrong primitive. The source has two independent structures:

1. arithmetic exponent depth, which produces the zeta divisor and its reciprocal boundary;
2. archimedean completion, which centers that divisor under \(s\mapsto1-s\) and supplies the unique
   reflection-odd affine coordinate \(s-\tfrac12\).

They must be joined only after their exact roles are separated.

## Strongest positive survivor

`[PAPER-PROVED] [LEAN-PROVED] [NOVELTY UNVERIFIED]`

The complete positive largest-exponent resolution supplies one explicit countable family whose
channels are pairwise disjoint \(0/1\) Dirichlet sources, maximally differential-algebraically
independent over the full zeta differential field, and exactly isodivisorial with zeta. Its finite
carrier prefixes satisfy
\[
 P_{K,N}(s)=\frac{\zeta(s)}{\zeta((K+N)s)}.
\]
The renormalized depth \((K+N)s\), not endpoint completion, is the invariant scale variable. It
gives a scale-transition law:

- fixed \(s\): zeta bulk;
- \(s\to0\) with depth times \(s\to\lambda u\ne0\): scaled reciprocal-zeta divisor;
- depth times \(s\to0\): identity;
- depth times \(s\) escaping through the right half-plane: endpoint constant \(\zeta(0)\).

Thus nonzero finite renormalized depth is exactly the divisor-retaining boundary window. The
completed Xi theory then contributes reflection polarization and quantitative orientation bounds,
without being falsely attributed to the bounded-exponent source.

## New insight

Divisor information is not located at finite source depth or ordinary endpoint scale. It is a
transition invariant visible only when observation scale and source depth are renormalized
together. Differential complexity and divisor complexity decouple: countably many transverse,
maximally differential-free positive channels can carry one common longitudinal divisor and fuse
to its opposite-polarity boundary.

## Survivor status

- Paper-proof and exact theorem card:
  `docs/drafts/pipeline/3-formalized/positive-hypertranscendental-divisor-scale-transition-law.md`
- Formal carrier:
  `formal/GaloisForLFunctions/RHTower/XiSourceNormalConeDivisorConservation.lean`
- Main declaration:
  `RHTower.positiveHTBulkBoundaryDuality_law`
