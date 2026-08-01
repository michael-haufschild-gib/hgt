# Route E sublinear factor-replacement flow

- **ID:** route-e-sublinear-factor-replacement-flow
- **Stage:** 5-failed
- **Type:** FALSIFIED
- **Source:** `../1-in-progress/route-e-squarefree-exponential-gibbs-parity.md` ·
  `OPEN-SOURCE-001`
- **Statement:** Every uniformly sublinear displacement pruning of Route E's
  `{one prime ↔ two primes, one prime above z ↔ four primes at most z}` graph has
  linear isolated Gibbs capacity on a positive-density power-smooth squarefree sector.

## Goal

The proposed producer sought an unsigned proof of the literal zero/one-large-prime Möbius
boundary estimate.  It split Gibbs capacity among binomially lifted factor-replacement
incidences and required aggregate unused capacity
`O_epsilon(N^(1/2+epsilon))`, with `N=1/x`, on edges of displacement
`z^(1+o(1))=N^(1/2+o(1))` at critical aperture.

This card retires only that sublinear-window producer.  Route E and its literal
`OPEN-SOURCE-001` remain open.

## Gates

- [x] 0 → 1  in-progress: literal graph, physical window, source implication, and capacity
  objective were specified.
- [x] 1 → 2  fully-proven: exact finite gap law is proved here; positive-density consequence uses
  standard unconditional squarefree-friable asymptotics.
- [x] 2 → 3  formalized: exact finite gap and isolation implications are unconditional Lean
  theorems in `MobiusBoundaryOppositeSignTransport.lean`; direct source check passes.
- [ ] 3 → 4  publication-ready: package finite obstruction with cited friable-density input.

## Exact killing theorem

Let every prime divisor of `n` be at most `y`, with `y<z`.  If `m` is adjacent to `n` in the
undirected Route E replacement graph, then

```text
                         |m-n| >= n/y^4.                  (F1)
```

Proof.  There are four orientations.

1. If `n=aq`, `m=ars`, then a prime cannot equal a product of two primes.  Hence
   `|m-n|=a|q-rs|>=a`, while `q<=y`, so `n<=ay<=ay^4`.
2. If `n=ars`, `m=aq`, the same non-equality gives `|m-n|>=a`, while
   `n<=ay^2<=ay^4`.
3. If `n=ap`, `p>z`, then `p|n` contradicts `p<=y<z`; this orientation is impossible.
4. If `n=aq1q2q3q4`, `m=ap`, then each `qi<=y`.  A prime cannot equal a product of four
   primes, so `|m-n|>=a` and `n<=ay^4`.

These cases exhaust the relation and prove `(F1)`.

Now fix `theta<1`, choose

```text
0<alpha<min(1/2,(1-theta)/4),  y=N^alpha.
```

The unconditional Dickman asymptotic and Ivić--Tenenbaum squarefree-smooth density give
`Omega_alpha(N)` squarefree `y`-smooth integers in `[N/2,N]`.  For each such `n`, `(F1)` gives

```text
|m-n| >= (1/2)N^(1-4alpha) > N^theta.
```

Thus every one is isolated after displacement-`N^theta` pruning.  Critical aperture satisfies
`z^2` of order `N log N`, so all these vertices lie inside the exact boundary truncation.
Their weights `exp(-n/N)` are bounded below by `exp(-1)`, giving `Omega_alpha(N)` isolated
capacity.  This exceeds `N^(1/2+epsilon)` for any fixed `epsilon<1/2`.

The density input is recorded with range and source in the active Route E card; see
[Gorodetsky, §1.4](https://link.springer.com/article/10.1007/s00209-024-03601-w) for the
quoted Ivić--Tenenbaum asymptotic.

## Hostile second pass: can the friable sector be removed?

No.  For fixed noninteger `u>1`, `Y=X^(1/u)`, de la Bretèche--Tenenbaum's complex
friable-average theorem specialized to `f=mu` gives

```text
sum_(n<=X, P+(n)<=Y) mu(n)
= X/(log Y)^2 {phi_(-1)(u)+O_u(1/log Y)}.                (F2)
```

The delay solution satisfies `v phi_(-1)'(v)=phi_(-1)(v-1)` and equals one on `(0,1]`;
therefore it is positive.  The friable sector has deterministic signed bias
`asymp_u X/log^2 X`, so assigning it an independent strict-half bound is false.  Source:
[de la Bretèche--Tenenbaum, Corollary 1.3](https://tenenb.perso.math.cnrs.fr/PPP/Friable-complex.pdf).

Scalar largest-prime renewal also cannot bootstrap this bias away.  In an `X^alpha` weighted
sup norm its positive operator norm is

```text
sum_(X^(1/u)<p<=X) p^(-alpha),
```

which tends to `log u` at `alpha=1` but grows like
`X^(1-alpha)/((1-alpha)log X)` for every `alpha<1`.  Linear-norm PNT contraction does not
extend to any fixed power-saving norm.

## No-go closure

- **Exact killing theorem/mechanism:** `(F1)` plus positive-density squarefree friable numbers
  forces linear isolated capacity in every uniformly sublinear window.
- **Strongest positive survivor:** the exact macroscopic-gap law `(F1)`, with sharp exponent four
  forced by the largest permitted replacement token; and the positive friable signed profile
  `(F2)`.
- **New insight:** power-smooth bulk is neither geometrically local nor signed-negligible.  Any
  viable Route E transport must carry deterministic friable bias across macroscopic smooth/rough
  seams.  Critical aperture approaches integer delay seam `u=2`; its beyond-all-orders
  zero/one-sector remainder, not short-interval incidence, is the literal open source.
- **Status:** `(F1)` paper- and Lean-proved.  Lean theorems:
  `le_pow_four_mul_dist_of_boundaryFactorReplacementAdjacent_of_primeFactors_le` and
  `not_boundaryFactorReplacementWindowAdjacent_of_primeFactors_le_of_pow_mul_lt` in
  `formal/GaloisForLFunctions/RHTower/MobiusBoundaryOppositeSignTransport.lean`.
  `(F2)` is a published external theorem specialized transparently to Möbius.  Route E remains
  open.

## Log

- 2026-08-01 — extracted after hostile audit falsified
  `WEIGHTED-FIBER-INCIDENCE-REGULARITY` and its
  `LOCAL-FRACTIONAL-BOUNDARY-FLOW` consequence.
