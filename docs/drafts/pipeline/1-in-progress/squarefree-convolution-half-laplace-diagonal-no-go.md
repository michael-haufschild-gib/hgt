# Squarefree convolution-half Laplace diagonal no-go

- **ID:** squarefree-convolution-half-laplace-diagonal-no-go
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** `squarefree-convolution-half-laplace-source-criterion.md`
- **Status:** `[ATTACKING] [NOT RH]`

## Goal

Prove unconditionally

`¬ PoleClearedFirstTraceLaplaceLocallyBounded`.

This would retire frozen bridge L-HEAT1 without assuming RH and isolate what any successor
infinite-order smoothing must change.

## Gates

- [x] 0 → 1 in-progress: well-posed, source-pure, explicit attack
- [ ] 1 → 2 fully-proven: complete paper proof, no open dependency
- [ ] 2 → 3 formalized: Lean theorem, targeted build green, public axiom audit
- [ ] 3 → 4 publication-ready: standalone paper and Lean certificate

## Frozen conjecture L-HEAT-NOGO

At `boundaryExteriorPoint = 6/11`, local boundedness of the pole-cleared diagonal family forces
the samples

`squarefreeHalfLaplaceSum N boundaryExteriorPoint`

to decay geometrically because `poleFactorSqrtApprox N boundaryExteriorPoint` grows at least as
`5^(N-24)`. These samples occur at heat times `t_N = 1/(N+1)`.

## Attack

Let

`F(t) = coeffLaplaceProfile (fun n => LSeries.term squarefreeConvolutionHalf (6/11) n) t`.

1. Prove local boundedness forces `F(t_N) = O(5^-N)`.
2. Compare adjacent heat times using
   `|exp(-n x)-exp(-n y)| ≤ exp(-n min(x,y)) n |x-y|`.
   The coefficient estimate `|a_n n^(-6/11)| ≤ n^(-6/11)` and the corpus real-power
   exponential-moment bound should give `F(t) = O(t^(1/2))` as `t→0+`.
3. Exponential decay at infinity and the positive-power zero bound make the Mellin transform of
   `F` analytic for `Re(z)>-1/2`.
4. After translating by `6/11` and multiplying by reciprocal Gamma, obtain an analytic
   continuation of `LSeries squarefreeConvolutionHalf` through `s=1`.
5. Square in a nonempty Euler overlap and use analytic uniqueness on the connected half-plane.
   At `s=1`, the left side contains the factor `s-1`, while `zetaResidueUnit 1 = 1`, contradiction.

## Hostile checks

- Geometric smallness only holds on the diagonal mesh; interpolation must be proved, not assumed.
- A bounded-coefficient estimate loses the needed positive power. The proof must retain the
  `n^(-6/11)` Dirichlet weight.
- Mellin identity initially holds only when `Re(z)>1`; translated overlap is still nonempty and
  suffices for analytic uniqueness.
- Reciprocal Gamma must be used as an entire factor so its pole at zero creates no domain hole.

## Falsifier

Failure of the adjacent-time interpolation estimate or inability to obtain any positive power at
zero retires this proof mechanism, not the original local-boundedness question.

## No-go closure

- **Exact killing theorem/mechanism:** pending.
- **Strongest positive survivor:** pending.
- **New insight:** pending.
- **Status:** paper and Lean attack open.

## Log

- 2026-09-04 — opened after corpus search found no Selberg--Delange asymptotic but did find the
  needed real-power exponential-moment and generic bounded-coefficient Laplace--Mellin machinery.
