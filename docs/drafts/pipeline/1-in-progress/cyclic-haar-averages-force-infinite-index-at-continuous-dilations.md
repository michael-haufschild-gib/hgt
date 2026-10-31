# Cyclic Haar averages force infinite index at continuous dilations

- **ID:** HAAR-CYCLIC-AVERAGE-INFINITE-INDEX
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Parent:** [Finite-index Mautner rigidity](finite-index-mautner-rigidity-for-the-haar-successor.md)
- **Statement:** A Hermitian rational affine kernel with integer Haar successor and a dilation reading continuous at one has infinite negative index.

## Reduction and positive subspaces

The [normalized polynomial correction](../2-fully-proven/finite-index-periodic-affine-kernels-have-a-zero-axis-polynomial-correction.md) reduces a putative finite-index example to a bi-integer-invariant kernel with unchanged axis readings. In its column representation, every rational translation acts locally periodically. The [dilation-replication argument](bi-integer-invariant-haar-kernels-split-into-positive-and-slope-parts.md#positivity-of-the-moving-subspaces) makes each `range(T_b−1)` nonnegative.

Local periodicity gives the canonical projection `P_b` onto `Fix(T_b)` along `range(T_b−1)`, equal on each vector to its finite orbit average. It is self-adjoint for the column pairing `B` and commutes with every translation.

## Finite cyclic Hecke bound

Write `v_a=v_(D_a)` and assume `a,c∈bℤ`. Put `u_a=(1−P_b)v_a`, `u_c=(1−P_b)v_c`, and `d=den(c/a)`. The first `d` translates `T_(jc)v_a` are orthonormal by the Haar reading. Their projected fixed parts all equal `P_bv_a`. Consequently

`B(Σ_(j<d) T_(jc)u_a, Σ_(j<d) T_(jc)u_a) = d−d² B(P_bv_a,P_bv_a) ≤ d`.

Every summand has the same pairing with `u_c`, since `T_cu_c=u_c`. Also `0≤B(u_c,u_c)≤1`. Cauchy–Schwarz on the nonnegative moving subspace gives

`|B(u_a,u_c)|²≤1/d≤|c/a−1|` for `a≠c`.

The last inequality follows from the nonzero integer `num(c/a)−den(c/a)`. This estimate needs no affine-invariant limiting form or positive-plus-slope decomposition.

## Negative Gram limit

For a fixed finite index set take `a_(N,i)=1+i/(N+1)` and `b_N=1/(N+1)²`. Then `a_(N,i)/b_N=(N+1)(N+1+i)` is a positive integer. Haar averaging gives

`B(P_(b_N)v_(a_(N,i)),P_(b_N)v_(a_(N,i))) = 1/((N+1)(N+1+i)) → 0`.

For distinct `i,j`, the moving pairing tends to zero by the cyclic bound. Continuity of the original dilation reading gives `B(v_(a_(N,i)),v_(a_(N,j)))→1`. Orthogonality of fixed and moving parts therefore makes the projected Gram matrices converge to `J−I`. Their negative index is bounded by the column-space index, while `J−I` on `n+1` coordinates has `n` negative directions. Stability of negative inertia contradicts every finite bound.

## Positive slopes and adelic carriers

The positive-slope subgroup has two cosets. Extending its kernel by zero gives a Hermitian kernel on the full rational affine group and multiplies negative index by two, by the verified `negIndex_extendFromSubgroup` law. Translation readings and positive dilation readings are unchanged. Thus the proposed obstruction also covers positive-slope affine kernels. An adelic carrier with these rational-axis readings restricts to that subgroup; pullback cannot increase negative index.

## Verification boundary

Required Lean results: normalized polynomial correction; local periodicity; nonnegative moving subspaces; canonical cyclic projections; cyclic Hecke bound; projected Gram limit and inertia comparison; positive-slope extension and the actual adelic restriction. The positive structural conclusions are the nonnegative moving subspaces and their finite cyclic bound. The stronger positive-plus-slope decomposition remains a separate conjecture.
