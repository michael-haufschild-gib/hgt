# Uniform Boolean Gram lift has insufficient Xi quadratic mass

- **ID:** `prime-gamma-uniform-boolean-gram-quadratic-no-go`
- **Stage:** 3-formalized
- **Type:** THEOREM / SP-E METRIC NO-GO
- **Scientific status:** `[PROVED HERE] [CORPUS-NEW] [NOVELTY UNVERIFIED] [NOT RH]`
- **Parent:**
  `prime-gamma-signed-eulerian-curvature-plucker-lift.md`
- **Source inputs:**
  - `../../2-fully-proven/not_new_scientific_knowledge/12-prime-theta-fock-incidence/prime-sieve-boolean-first-trace-connection-curvature.md`;
  - `../not_new_scientific_knowledge/prime-sieve-boolean-first-trace-curvature-ideal-law.md`;
  - `formal/GaloisForLFunctions/HTGeometry/PrimeSieveDensityTelescope.lean`;
  - `formal/GaloisForLFunctions/RHTower/XiCTaylorThetaTailMomentLogConvex.lean`.

## Candidate under attack

Enumerate primes increasingly, so `p_0=2`, and put

```text
P_n={p_0,...,p_(n-1)},
a_n=product_(j<n)(1-1/p_j),
w_n=a_n/p_n.
```

The exact first-trace theorem identifies `w_n D_(P_(n+1))` as the magnitude of the corrected
Boolean edge.  Embed all finite Boolean diagonals into the common probability space of two
independent sign configurations and use its uniform `L^2` metric.  Then

```text
<D_P,D_Q>=2^(-|P union Q|).
```

Let `v_n=w_n D_(P_(n+1))`, let `G_N=(<v_i,v_j>)_(0<=i,j<=N)`, and form the stable Gram polynomial

```text
B_N(u)=det(I+u G_N).
```

This is the most direct cofinal realization of the preceding Pluecker survivor: it uses literal
source edges, no Xi data, and the canonical uniform Boolean metric.

## Theorem `[PROVED HERE]`

For every finite `N`, writing

```text
T_N=trace(G_N),
Q_N=trace(G_N^2),
r_N=[u^2]B_N(u)/[u]B_N(u)^2,
```

one has

```text
T_N <= 7/48,
Q_N >= 1/64,
r_N=(T_N^2-Q_N)/(2T_N^2) <= 13/98.                       (1)
```

For the normalized square-coordinate Xi source

```text
A(u)=sum a_k u^k,
a_k=M_k/((2k)! M_0),
M_k=thetaCuspRawEvenMoment(k),
```

moment log-convexity gives

```text
a_2/a_1^2=M_0 M_2/(6 M_1^2) >= 1/6.                     (2)
```

Since

```text
13/98 < 1/6,                                               (3)
```

no scalar rescaling of `B_N` can converge coefficientwise, hence no locally uniform rescaling can
converge to `A`.

## Proof

The sieve losses telescope:

```text
sum_(n>=0) w_n=1,
w_0=1/2.
```

For `n>=1`, `a_n<=1/2` because the factor from `p_0=2` is already present, and `p_n>=3`.
Consequently

```text
0<=w_n<=1/6,
sum_(n>=1)w_n=1/2.                                        (4)
```

The diagonal of the Boolean Gram is

```text
(G_N)_(nn)=||v_n||_2^2=w_n^2 2^(-(n+1)).                  (5)
```

The first term is `w_0^2/2=1/8`.  For the tail, use `2^(-(n+1))<=1/4`,
`w_n^2<=(1/6)w_n`, and `(4)`:

```text
sum_(n>=1)(G_N)_(nn)
 <=(1/4)(1/6)sum_(n>=1)w_n
 <=1/48.
```

Thus `1/8<=T_N<=7/48`.  Since `G_N` is positive semidefinite,

```text
Q_N=sum_(i,j)|(G_N)_(ij)|^2 >= (G_N)_(00)^2=1/64.
```

Newton's trace identity gives the degree-two Gram coefficient:

```text
[u^2]B_N=(T_N^2-Q_N)/2.
```

Therefore

```text
Q_N/T_N^2 >= (1/64)/(7/48)^2=36/49,
r_N <= (1-36/49)/2=13/98,
```

which proves `(1)`.  Equation `(2)` is Cauchy--Schwarz for the positive completed theta measure:
`M_1^2<=M_0 M_2`.  The ratio `r_N` is unchanged by `u -> c_N u`, so `(1)`--`(3)` exclude every
scalar activity normalization.

## Verdict and positive survivor

`[FALSIFIED]` Literal first-trace edges plus the uniform Boolean metric do not have enough
second exterior mass to approximate Xi.  Pluecker lifting repaired stability but not the source
metric.

`[POSITIVE SURVIVOR]` The missing Gamma completion is metric, not another scalar edge weight.  It
must reweight or rotate Boolean curvature columns before the Gram determinant so that squared
two-minors contribute at least the theta moment floor `1/6`.  Equivalently, completion must reduce

```text
trace(G_N^2)/trace(G_N)^2
```

from the uniform Boolean lower bound `36/49` to at most `2/3` already at degree two.  This is an
exact, scale-free finite gate for any proposed Gamma/theta metric.

The natural next carrier is not the nested diagonal edge family itself but the completed
two-face curvature sections `(1-D_p)D_q` and `D_p(1-D_q)`, paired in the nonuniform Gamma/co-Poisson
metric supplied by the all-prime Euler--Gamma/Mobius transgression.

## Hostile audit

1. Gram stability alone is insufficient; `(1)` kills the most canonical Gram choice.
2. The result does not exclude nonuniform source metrics, nonnested curvature columns, or graded
   matrix pencils.
3. Reweighting with `a_1,a_2` would be circular.  Metric must come from Gamma/theta connection
   before coefficient comparison.
4. Uniform Boolean `L^2` is canonical only for the raw sign cube.  Functional-equation completion
   is not measure-preserving in that metric, so failure is informative rather than terminal.
5. No numerical approximation is used; separation is the exact rational gap `(3)`.

## Gates

- [x] literal nested first-trace edge Gram family defined
- [x] uniform Boolean trace ceiling proved
- [x] uniform Boolean inverse-participation floor proved
- [x] normalized quadratic coefficient ceiling `13/98` proved
- [x] theta-source quadratic floor `1/6` proved
- [x] all scalar normalizations excluded
- [x] Lean formalization
- [ ] construct source-native Gamma/co-Poisson metric on curvature sections
- [ ] pass degree-two gate in that metric
- [ ] all-degree coefficient comparison and local-uniform limit
- [ ] RH

## Lean certificate

Module:
`formal/GaloisForLFunctions/RHTower/PrimeGammaUniformBooleanGramQuadraticNoGo.lean`

Headline declarations:

```text
GaloisForLFunctions.HTGeometry.uniformBooleanTailTrace_le_one_div_fortyEight
GaloisForLFunctions.HTGeometry.gramNormalizedQuadraticRatio_le_thirteen_div_ninetyEight
GaloisForLFunctions.HTGeometry.one_div_sixtyFour_le_gramEntrySqSum_of_zero_zero
GaloisForLFunctions.HTGeometry.sieveFirstTraceWeight_le_one_div_six
GaloisForLFunctions.HTGeometry.sum_sieveFirstTraceWeight_tail_le_half
GaloisForLFunctions.HTGeometry.sieveUniformBooleanTailTrace_le_one_div_fortyEight
GaloisForLFunctions.HTGeometry.sieveUniformBooleanTrace_mem_Icc
RHTower.one_div_six_le_thetaSquareCoordinateQuadraticRatio
RHTower.uniformBooleanGramRatio_ne_thetaSquareCoordinateQuadraticRatio
```

Verification on 15 August 2026:

- direct module check passed;
- target-only build passed: `8968/8968` jobs;
- module wired into `RHTower.lean`; umbrella build intentionally not run;
- axiom audit: only `propext`, `Classical.choice`, and `Quot.sound`.
