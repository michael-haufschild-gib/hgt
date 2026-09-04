# Squarefree convolution-half Laplace diagonal no-go

- **ID:** squarefree-convolution-half-laplace-diagonal-no-go
- **Stage:** 5-failed
- **Type:** FALSIFIED
- **Source:** `squarefree-convolution-half-laplace-source-criterion.md`
- **Status:** `[LEAN-PROVED NO-GO] [AXIOM-AUDITED] [NOT RH]`

## Goal

Prove unconditionally

`¬ PoleClearedFirstTraceLaplaceLocallyBounded`.

This would retire frozen bridge L-HEAT1 without assuming RH and isolate what any successor
infinite-order smoothing must change.

## Gates

- [x] 0 → 1 in-progress: well-posed, source-pure, explicit attack
- [x] 1 → 2 fully-proven: complete paper proof, no open dependency
- [x] 2 → 3 formalized: Lean theorem, targeted build green
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
   Bounded coefficients suffice: reciprocal mesh gap `O(N^-2)` cancels the exponential first
   moment `O(N^2)`, so `F` is bounded near zero.
3. Exponential decay at infinity and zero-end boundedness make Mellin transform of `F` analytic
   for `Re(z)>0`.
4. After translating by `6/11` and multiplying by reciprocal Gamma, obtain an analytic
   continuation of `LSeries squarefreeConvolutionHalf` through `s=1`.
5. Square in a nonempty Euler overlap and use analytic uniqueness on the connected half-plane.
   At `s=1`, the left side contains the factor `s-1`, while `zetaResidueUnit 1 = 1`, contradiction.

## Hostile checks

- Geometric smallness only holds on the diagonal mesh; interpolation must be proved, not assumed.
- No positive-power decay is needed: boundedness already translates to `Re(s)>6/11`, a connected
  half-plane containing `s=1`.
- Mellin identity initially holds only when `Re(z)>1`; translated overlap is still nonempty and
  suffices for analytic uniqueness.
- Reciprocal Gamma must be used as an entire factor so its pole at zero creates no domain hole.

## No-go closure

- **Exact killing theorem/mechanism:**
  `not_poleClearedFirstTraceLaplaceLocallyBounded`; geometric diagonal suppression plus uniform
  reciprocal-mesh interpolation yields forbidden Mellin continuation across zeta pole.
- **Strongest positive survivor:** reciprocal heat mesh transport is uniformly bounded for every
  bounded boundary coefficient stream. Viable successors must break heat/pole clock coupling or
  change source through literal singular/nonlinear renormalization.
- **New insight:** Selberg--Delange growth is unnecessary. Even boundedness, not decay, at heat
  origin crosses `s=1` after `6/11` Mellin translation.
- **Status:** dependency-closed paper proof and Lean theorem in
  `SquarefreeConvolutionHalfLaplaceDiagonalNoGo.lean`; direct check and targeted build
  `13034/13034` pass; umbrella wired; public theorem axiom audit contains only `propext`,
  `Classical.choice`, `Quot.sound`.

## Log

- 2026-09-04 — opened after corpus search found no Selberg--Delange asymptotic but did find the
  needed real-power exponential-moment and generic bounded-coefficient Laplace--Mellin machinery.
- 2026-09-04 — conjecture proved: exact local-bound hypothesis is false. Positive survivor and
  replacement-class constraint recorded; moved to `5-failed`.
