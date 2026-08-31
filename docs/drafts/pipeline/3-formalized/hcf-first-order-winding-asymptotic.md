# HCF first-order winding asymptotic

- **ID:** HCF-WIND-4PI
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Source:** internal HCF/Plemelj corpus
- **Statement:** The canonical first-order pole--Gamma winding satisfies
  `criticalFeatureCanonicalFirstOrderPoleGammaWinding(n) / N(n) -> 4*pi`.

## Goal

Remove archimedean winding as an unknown in the source-only HCF covariance. Combined with the
exact first-order Plemelj reduction, the desired covariance ceiling `4/25` is equivalent to a
source-boundary lower budget `4*pi - 4/25`, up to `o(N)`. No Xi divisor is selected in the winding
or boundary statistic.

## Gates

- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [x] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [x] 2 → 3  formalized: Lean theorem `tendsto_criticalFeatureCanonicalFirstOrderPoleGammaWinding_div_zeroCount`, `lake build` green, axiom audit PASS
- [ ] 3 → 4  publication-ready: standalone paper (theorem + proof + Lean certificate + Door-2)

## Approach

`[PROVED HERE]` Put `L(t) = Re (archFactor'/archFactor)(3/2+it)` and
`A(T)=2 integral_0^T L(t) dt`. The closed logarithmic-derivative formula gives

`A(T) = 2 gammaVerticalPhase(3/4,T/2) + O(T)`.

Indeed the two rational pole terms are uniformly bounded on `Re(s)=3/2`, while the constant
`-log(pi)/2` integrates to `O(T)`. The corpus theorem `tendsto_gammaVerticalPhase_ratio` yields
`gammaVerticalPhase(3/4,u) ~ u log u`; hence `A(T) ~ T log T`.

The real part `L` is even by Schwarz conjugation (equivalently, termwise from the closed formula).
The canonical unit cells tile `[-n-2,n+1]`, so the exact lattice winding is

`A(n+2) + A(n+1) ~ 2 n log n`.

Riemann--von Mangoldt in the corpus gives `N(n) ~ n log n/(2*pi)`. Dividing proves the stated
limit `4*pi`.

Consequent exact target: because the endpoint increment is `o(N)` and phase covariance equals
winding minus source-boundary average, a `4/25` covariance ceiling is equivalent to asymptotic
source-boundary lower bound `(4*pi - 4/25) N`; `21/100` corresponds to `4*pi - 21/100`.

Formalization also proves the conservation law

`(phaseCovariance(n) + sourceBoundary(n)) / N(n) -> 4*pi`

and the exact asymptotic equivalence at every ceiling constant. The phase boundary is bounded above
by `2*pi` times multiplicity of its finite real-`XiC` packet. Thus remaining lower floor cannot come
from Gamma winding or phase averaging alone: it must create almost maximal real-boundary mass from
prime/source structure.

## Log

- 2026-08-31 — `[CONJECTURE]` generated from exact source-only first-order reduction.
- 2026-08-31 — `[PROVED HERE]` via closed archFactor jet, Gamma vertical phase asymptotic,
  canonical cell tiling, and Riemann--von Mangoldt.
- 2026-08-31 — `[FORMALISED]` in
  `HedenmalmCriticalFeatureFirstOrderWindingAsymptotic.lean`; targeted build and axiom audit pass.
