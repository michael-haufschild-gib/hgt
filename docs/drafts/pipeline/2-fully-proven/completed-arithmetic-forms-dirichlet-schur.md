# Exact Dirichlet inverse and Schur cost of the arithmetic bridge

- **ID:** completed-arithmetic-forms-dirichlet-schur
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)

## Statement

For `Q ≥ 1`, let `B_Q(i,j)=Q min(i,j)-ij` on `1≤i,j<Q`, and set

`E_Q(a)=Σ_i,j a_i a_j B_Q(i,j)`.

Extend a potential `b` by `b_0=b_Q=0`. Its Dirichlet difference and energy are

`(L b)_i=2b_i-b_(i-1)-b_(i+1)`,

`D_Q(b)=Σ_(0≤i<Q) (b_(i+1)-b_i)²`.

The inverse of the interior arithmetic bridge is `L/Q`. In particular, with `d=L b/Q`,

`E_Q(a)-2Σ_i a_i b_i+D_Q(b)/Q = E_Q(a-d) ≥ 0`.

Thus the exact Schur cost of the linear coupling `Σ_i a_i b_i` is `D_Q(b)/Q`:
the maximum of `2Σ_i a_i b_i-E_Q(a)` is `D_Q(b)/Q`, attained at `a=d`.

The arithmetic identification is literal:
`B_Q(i,j)=Σ_(m|Q,m≠1) G_m(i,j)`.

## Proof

The function `i ↦ min(i,j)` has second difference one at `i=j` and zero elsewhere.
The linear product term has zero second difference. Hence

`2B_Q(i,j)-B_Q(i-1,j)-B_Q(i+1,j)=Q·1_(i=j)`.

Both boundary values of the kernel vanish. Therefore its potential `u=B_Q a` obeys
`Lu=Qa` and `u_0=u_Q=0`.

Uniqueness follows from the recurrence: a function with zero second difference on the interior
has `u_i=u_0+i(u_1-u_0)`. Its two zero endpoint values force it to vanish. Consequently
`B_Q(Lb/Q)=b` on the entire interval.

Finite summation by parts gives `Σ_i b_i(Lb)_i=D_Q(b)`. Symmetry of `B_Q` then gives
`E_Q(d)=D_Q(b)/Q` and `Σ_i,j a_i d_j B_Q(i,j)=Σ_i a_i b_i`.
Expanding the quadratic form at `a-d` proves the identity. The nonnegativity is the
unconditional completed-conductor Gram theorem. Equality is attained at `a=d`.

## Source consequence

A comparison against the complete divisor-conductor Gram pays a mixed linear term in the
Dirichlet variation of its coupling vector, including the two boundary differences. Absolute
row size is absent from this exact cost. Identifying and estimating the actual complete-Weil
coupling vector remains a separate arithmetic theorem.

## Dependencies

- `sum_nontrivial_divisors_primitivePrefixGram`.
- `discreteBridge_quadratic_nonneg`.
- Finite summation and elementary second-difference algebra.

Lean formalization is required before these conclusions count as established results.
