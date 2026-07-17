# Dumitrescu--Wolf universality disproof loses the vertical zero phase

- **ID:** dumitrescu-wolf-universality-disproof-phase-wrap
- **Stage:** 5-failed
- **Type:** FALSIFIED
- **Source:** C. Dumitrescu and M. Wolf, *The Disproof of the Riemann Hypothesis*, arXiv:2102.08313v3
- **Statement:** The proposed contradiction depends on false limits for two tangent/Riccati sequences; their phases wrap infinitely often, so the vertical zero contribution is not an integer multiple of `pi` plus `o(1)`.

## Proposed route

Assume RH and integrate `zeta'/zeta` around a rectangle inside the critical
strip.  Universality prescribes the top horizontal contribution.  The
functional equation treats the two vertical edges.  The preprint then tries
to telescope the vertical zero sum and quantize it as `Q pi+o(1)`, producing
an alleged contradiction with the integer-valued argument principle.

## Exact obstruction `[PROVED HERE]`

The two auxiliary recurrences in Lemma 2 are tangent-addition recurrences.
Their increments have magnitude asymptotic to

```text
(beta-alpha)/gamma_k.
```

The sum of reciprocal zero ordinates diverges.  Consequently each accumulated
phase diverges while its increments tend to zero.  It crosses every multiple
of `pi` with vanishing overshoot, so the tangent has a subsequence tending to
zero and repeatedly wraps through its poles.  It cannot converge to
`+infinity` or `-infinity` as claimed.

The full proof is in
`../2-fully-proven/needs-audit/dumitrescu-wolf-tangent-phase-wrap-obstruction.md`.
The Appendix's Perron-theorem argument does not fix this: a limsup statement
for `|z(n)|^(1/n)` does not imply the displayed ratio limit, and the purported
finite-limit equation retains coefficients depending on `n` whose off-diagonal
ratio tends to zero.

The paper also chooses a denominator-tail tolerance `1/T^2`.  After restoring
the paired numerator `2(s-1/2)` and integrating over length `2T`, this controls
the discarded integral only by `O(1)`, rather than the required `o(1)`.

## Positive residue

The `T-gamma_k` and `T+gamma_k` channels cannot be assigned separate endpoint
phases.  Their leading divergent tails cancel only after pairing, leaving an
exact moving zero boundary layer concentrated near `gamma_k=T`.  Horizontal
universality does not determine that layer.  Any future contour disproof must
control this paired phase uniformly in the same heights selected by
universality.

## Anti-theatre verdict

This route supplies no unconditional off-critical zero and no negative exact
Weil-form sample.  Formalizing the phase-wrap lemma would certify a failed
preprint rather than advance the RH-false source, so no Lean build is
authorized for this dead route.

## Re-entry condition

Reopen only with a uniform theorem for the paired vertical zero boundary layer
at the universality-selected heights.  Separate limits for the two divergent
tangent phases are not a valid re-entry condition.

