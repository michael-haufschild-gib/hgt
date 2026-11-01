# Successor telescoping cancels the negative-unit Mayer determinant pole

- **Stage:** 1-in-progress
- **Type:** Conjecture
- **Parent:** [exact determinant pole](../3-formalized/gauss-mayer-rank-one-determinant-pole.md).

## Target

For every `Re w>0` and complex `t`, prove

`det(I+R(w)+tP)=det(I+R(w))`.

Then `B(w,−1)=0` throughout this half-plane and the actual source determinant
satisfies `D(w,−1)=A(w,−1)`, including its assigned value at `w=1`.
Consequently it is holomorphic throughout the half-plane. This settles one
specific nonzero cancellation required by the even-word determinant product.

## Paper mechanism

The actual disc-algebra response `f_w(z)=1−(1+z)^(−w)` vanishes at zero.
For `a=n+z`, both `a` and `a+1` have positive real part, so
`Im(log(a+1)−log a)∈(−π,π)`. Exponential/logarithm inversion therefore gives
`log(1+a⁻¹)=log(a+1)−log a`, proving the principal-power identity on the
whole complex disc. The genuine branch terms are exactly

`(n+z)^(−w) f_w((n+z)^(−1)) = (n+z)^(−w)−(n+z+1)^(−w)`.

The existing source bound makes the telescoping tail tend to zero for
`Re w>0`. Normal convergence identifies the sum with the actual remainder,
yielding `(I+R(w))f_w=1`.

Cauchy analysis transports evaluation at zero to the bounded Hilbert
functional `q(v)=Σ_j(−1)^j(6/5)^(−j)v_j`. With `u=Qf_w`, `x=Q1`, and
`A` the Hilbert remainder, one has `u+Au=x`, `q(u)=0`, `q(x)=1`.
The existing `det2Op_rankOne_update` thus gives the factor `exp(−t)`.
The genuine diagonal correction contributes `exp(t)` and cancels it.
No inverse of `I+A` is assumed.

## Audit and scope

The strengthened all-parameter statement follows from the same successor
identity as the initial rational response at `w=1`. Principal powers and
the vanishing tail are now included in its paper proof; Lean verification
is in progress. Targeted corpus searches supplied no checked exact source
cancellation theorem. No literature-priority claim is made.

The value at `w=1` and its possible vanishing order remain undetermined.
The parameter `λ=1`, primitive modular coding, Selberg/scattering comparison,
and off-critical resonance exclusion remain open.
