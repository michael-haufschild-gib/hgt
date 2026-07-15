# All-order zeta-parity law for the Gamma factorial microscope

- **ID:** `gamma-factorial-all-order-zeta-parity`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Scientific status:** `[PROVEN IN LEAN] [CANDIDATE NEW SCIENTIFIC KNOWLEDGE]`
- **Statement:** After subtracting the reciprocal principal jet and dividing by its exact
  factorial scale, every odd polygamma order has the nonzero residue
  `2m!ζ(m+1)`, while every positive even order has zero residue.

## Goal

Determine the first bounded coefficient of the exact all-order pole-jet law and prove that the
parity split is uniform in the jet order.  This identifies which coordinates are already detected
by the zeta layer and which pass to the finer finite Euler-product tail.

## Theorem

Let `sₙ=(-1)^(n+1)/n!`, let `m≥1`, and fix `x≠0`.  Lean proves

\[
 \frac{s_n^{m+1}\psi^{(m)}(-n+s_nx)
       -(-1)^{m+1}m!/x^{m+1}}{s_n^{m+1}}
 \longrightarrow
 \bigl(1+(-1)^{m+1}\bigr)m!\zeta(m+1).
\]

Consequently, for every `r∈ℕ`, order `m=2r+1` has residue

\[
 2(2r+1)!\zeta(2r+2)\ne0,
\]

whereas every positive even order `m=2r+2` has residue zero.

## Meaning

The exact Gamma pole germ is not governed by one harmonic asymptotic.  Its bounded subordinate
layer is triangular by parity: odd polygamma orders are detected by even zeta values, while even
orders cancel between the local polygamma value at `1` and the limiting generalized harmonic sum.
The cancellation is structural and transfers control to the finite-tail scale, rather than
annihilating those coordinates.

## Lean certificate

Module: `formal/GaloisForLFunctions/HTGeometry/GammaFactorialAllOrderZetaLayer.lean`.

Headline declarations:

- `tendsto_shiftedHarmonicPowerSum_factorial`
- `tendsto_gammaFactorialScaledPolygamma_correction`
- `tendsto_gammaFactorialScaledPolygamma_odd_correction`
- `gammaFactorialScaledPolygamma_odd_correction_limit_ne_zero`
- `tendsto_gammaFactorialScaledPolygamma_even_correction`

Direct compilation and the individual Lake target pass.  Axiom audits use only `propext`,
`Classical.choice`, and `Quot.sound`.  Formal lint passes.  No full build and no numerical
computation were used.

## Gates

- [x] 0 → 1 in-progress: exact bounded layer isolated from the all-order source identity
- [x] 1 → 2 fully-proven: shifted harmonic convergence and parity reduction proved uniformly
- [x] 2 → 3 formalized: general Lean theorems, targeted build, axiom audit, and lint pass
- [ ] 3 → 4 publication-ready: combine with the finite-tail layer and complete priority audit

## Approach

Control the shift in each generalized harmonic summand uniformly by a summable comparison after
the factorial microscope sends `sₙx` to zero.  Evaluate the unshifted sum by the Riemann zeta
limit, evaluate the local polygamma value at one, and add the two exact coefficients.  Their signs
reinforce in odd order and cancel in even order.

## Log

- 2026-07-15 — proved and formalized uniformly for every positive polygamma order.
