# Squarefree convolution-half Laplace criterion

- **ID:** squarefree-convolution-half-laplace-criterion
- **Stage:** 3-formalized
- **Type:** BRIDGE THEOREM (paper + Lean)
- **Source:** `squarefree-convolution-half-laplace-source-criterion.md`
- **Status:** `[PROVED HERE] [LEAN-PROVED] [NOT RH]`

## Statement

For the canonical convolution half `a*a=mu^2`, retain every coefficient and damp index `n` by
`exp(-n/(N+1))`. Every resulting Dirichlet sum is entire and converges pointwise to the canonical
Euler half on `Re(s)>1`. Local boundedness of its pole/Carleman-normalized family on
`Re(s)>1/2` implies `RHLadder 1`.

## Proof

At fixed damping time, `|a_n|<=n` and a local lower bound on `Re(s)` reduce every summand to
`n^M exp(-n/(N+1))`; this is summable for every natural `M`, giving entire holomorphy by the
complex M-test. As `N->infinity`, damping weights tend pointwise to one and stay in `[0,1]`.
Absolute convergence of the original half series on `Re(s)>1` therefore gives pointwise
undamping by dominated convergence.

The synchronized Cayley pole factor has its existing Euler-chamber limit, and the Carleman half
determinant is fixed and nonzero. Vitali then extends any locally bounded normalized family across
`rightHalf`; squaring and analytic uniqueness identify its limit with the pole-cleared first trace,
which is exactly the first parity rung.

## Lean formalization

Module:
`formal/GaloisForLFunctions/RHTower/SquarefreeConvolutionHalfLaplaceCriterion.lean`.

Main theorems:

- `analyticOnNhd_squarefreeHalfLaplaceSum`
- `tendsto_squarefreeHalfLaplaceSum`
- `tendsto_poleClearedFirstTraceLaplaceApprox`
- `rhLadder_one_of_poleClearedFirstTraceLaplaceLocallyBounded`

Verification on 2026-09-04: direct check pass; targeted build `12847/12847`; axiom audits only
`propext`, `Classical.choice`, `Quot.sound`; umbrella import wired.

## Open arithmetic input

No local boundedness is proved. Expected Selberg--Delange behavior predicts boundary growth and
may close this family negatively, but that asymptotic is absent from current Lean corpus. Raw and
Cesaro no-gos do not by themselves imply exponential-weighted divergence.
