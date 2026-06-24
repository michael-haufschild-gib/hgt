# Axis Positivity Does Not Imply Hankel Positivity

- **ID:** axis-positivity-does-not-imply-hankel-positivity
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper) / source-transfer guardrail
- **Source:** `seam-log-coefficient-positivity-insufficient.md`,
  `archimedean-generator-axis-mode.md`,
  `combination-mode-reducibility-baker-bridge.md`,
  `source-selector-repair-obligation-ledger.md`
- **Statement:** Coordinatewise positivity of axis-mode data cannot imply the
  Hankel square-test positivity needed by the reciprocal seam route. The
  missing Euler-product transfer must control nonlinear combination-mode
  inequalities, not only signs of individual prime or moment coefficients.

## Setup

Call a condition axis-positive if it only asserts nonnegativity of individual
coordinates, such as

`a_k >= 0 for every k`

or nonnegativity of individual source coefficients before they enter a Hankel or
Schur expression.

The first nontrivial Hankel square test for a sequence `(a_k)` is

```text
[ a_0  a_1 ]
[ a_1  a_2 ] >= 0,
```

equivalently

`a_0 >= 0`, `a_2 >= 0`, and `a_0 a_2 - a_1^2 >= 0`.

The determinant is a combination-mode condition: it multiplies two axis
coordinates and compares the product with a square of a third.

## Theorem

Axis positivity does not imply the first Hankel square test.

In particular, there are strictly positive coordinates `a_0,a_1,a_2` such that

`a_0>0`, `a_1>0`, `a_2>0`,

but

`det [[a_0,a_1],[a_1,a_2]] < 0`.

## Proof

Take

`a_0=1`, `a_1=3`, `a_2=1`.

All three coordinates are positive, but

`det [[1,3],[3,1]] = 1 - 9 = -8 < 0`.

Thus the quadratic form is negative on `(1,-1)`:

`a_0 - 2a_1 + a_2 = -4`.

Therefore coordinatewise positivity cannot imply Hankel positive
semidefiniteness, even at the first nontrivial square test.

## Consequence for the Euler-Product Transfer

The open NR-2 prime-side transfer cannot be stated as

`Lambda(n) >= 0  => repaired index sign`

unless the proof supplies the missing combination-mode mechanism.

The Euler product gives source orientation and coefficient signs on axis-mode
data. The repaired semilocal index is a Hankel/Schur condition. Between them is
the actual theorem:

`axis-mode Euler data + completed archimedean boundary => combination-mode Hankel/Schur positivity`.

Without that transfer, coefficient positivity is only a necessary shadow. It
does not control cross-moment minors, kernel exhaustion, omitted channels, or
the full Schur/index sign.

## Theatre Test

For any proposed Euler-product proof of the repair sign:

1. Identify the axis-positive input, such as `Lambda(n)>=0` or positive local
   factors.
2. Identify the combination-mode output, such as a Hankel minor, Schur matrix,
   or negative-index count.
3. Show the explicit transfer from the first to the second.
4. If the argument only lists coordinatewise signs, it has not reached the
   repair theorem.

## Novelty And Significance Gate

The proof is elementary and intentionally small. Its significance is route
control: it prevents the live Euler-product transfer from being weakened to a
coefficient-sign statement. The real theorem must explain why the completed
source object sends axis-mode prime positivity into nonlinear semilocal
combination-mode positivity.

## Gates

- [x] 0 -> 1 in-progress: weak axis-positive version of the Euler transfer
  isolated.
- [x] 1 -> 2 fully-proven: positive-coordinate counterexample written.
- [ ] 2 -> 3 formalized: finite determinant calculation.

## Log

- 2026-06-24 -- Codex: created to sharpen NR-2/NR-2-prime-transfer. The card
  blocks replacing the semilocal Schur/index theorem by coefficient positivity.

## 2026-06-24 positive source weights need pointwise kernels

`positive-source-weights-require-pointwise-hankel-kernels.md` gives the exact linear-transfer criterion behind this guardrail. If positive Euler/source weights alone are supposed to imply a Hankel or Schur sign for every positive weighting, then each point source must already contribute a positive semidefinite Hankel kernel.

Thus a failed pointwise kernel test means the proof must use extra source structure beyond coefficient positivity: exact weights, multiplicativity, archimedean cancellation, or the completed explicit formula as more than a positive-weight sum.

## 2026-06-24 Atom displacement is an indefinite combination mode

`hankel-atom-displacement-tangent-indefinite.md` supplies the tangent-level version of this warning. Moving a Hankel atom gives the form `2m q(r)q'(r)`, not a coordinatewise-positive square. It is already indefinite on affine test polynomials.

So in the Jensen/root-motion chart, positive prime amplitudes do not enter the Hankel square test as positive coordinates. They weight indefinite combination-mode tangents, which forces the Euler transfer to be a genuine completed-source or index theorem.
