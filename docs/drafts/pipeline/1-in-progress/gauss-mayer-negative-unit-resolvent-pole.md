# Negative-unit resolvent pole behind determinant cancellation

- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Parent:** [negative-unit real nonvanishing](gauss-mayer-negative-unit-real-nonvanishing.md).

## Target

For real `w>0`, prove that `I+R(w)+tP` is invertible for every complex `t`.
Let `G(w)=(I+R(w))⁻¹`, `u_w(z)=1−(1+z)^(-w)`, and
`F(w)f=f(0)u_w`. Prove the exact inverse formula

`(I+R(w)+tP)⁻¹=(I−tF(w))G(w)`.

Near the complex source parameter `w=1`, establish holomorphy of `G,F`
and the genuine nonzero rank-one residue

`(w−1)(I+L(w))⁻¹ → −F(1)G(1) ≠ 0`.

Thus the negative-unit determinant would be holomorphic and nonzero while
the actual inverse retains a simple operator pole. Also determine the
source order of `D(w,−1)D(w,1)` from the two signed factors before any
Selberg/scattering comparison.

## Source mechanism

The checked response gives `(I+R)u=1` and `u(0)=0`. Hence `F²=0`,
`(I+R)F=P`, and `I+R+tP=(I+R)(I+tF)`. The unipotent factor has inverse
`I−tF`. Negative-unit determinant nonvanishing is still an open parent
input. Once proved, the actual source Fredholm invertibility theorem and
this factorization give invertibility of `I+R`, without assuming it.

Openness of the unit group and analytic Banach-algebra inversion would
make `G` holomorphic near one. On `Re w>0`, the response is the negative
of the first entire branch remainder applied to `1`, providing source
holomorphy of `F`. Substituting `t=ζ(w)` isolates the proposed residue.
Testing `F(1)G(1)` on `(I+R(1))1` returns `u_1≠0`.

## Existing inputs and open obligations

The corpus has the response identity, exact rank-one determinant update,
and the actual source determinant/invertibility equivalence. It did not
surface this source inverse formula or its Laurent residue. Mathlib's
`analyticAt_inverse` supplies analytic inversion at a proved unit;
`meromorphicOrderAt_mul_of_ne_zero` preserves order under an analytic unit.

Discharge parent nonvanishing first, then actual operator factorization,
unit construction, analytic dependence, nonzero residue, and signed-product
order. No complex half-plane invertibility or scattering identification
may be assumed.
