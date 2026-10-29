# Finite reciprocal criteria transfer packet bounds to a constrained form

- **ID:** ACP-FINITE-SECULAR-CRITERION
- **Stage:** 3-formalized
- **Type:** THEOREM (paper and Lean)
- **Parent:** arithmetic-counting-small-prime-secular-gap.md
- **Statement:** An exact finite reciprocal criterion, its negative witness and tail estimate, and an eventual packet-limit principle reduce the actual parity gap to a scalar limit.

## Closed finite criterion

For a finite set S, positive weights w_i, b>0 and c nonzero, the form
`-b x_0^2+sum_S w_i x_i^2` is nonnegative under the constraint
`c x_0+sum_S a_i x_i=0` exactly when

`b sum_S a_i^2/w_i <= c^2`.

Write R=`sum_S a_i^2/w_i` and E=`sum_S w_i x_i^2`.
Weighted Cauchy--Schwarz gives `c^2 x_0^2 <= R E`, hence
`b c^2 x_0^2 <= b R E <= c^2 E`. Cancel the positive factor c^2.
Conversely set `x_i=a_i/w_i` and `x_0=-R/c`. This satisfies the
constraint and has form `R-b R^2/c^2`. If R=0 the criterion is immediate;
if R>0, its nonnegativity is equivalent to the criterion. Strict failure
therefore produces a negative constrained vector.

If S is contained in U and `w_i>=eta>0` outside S, split the reciprocal
sum into S and U minus S. Each omitted term is at most `a_i^2/eta`, so

`sum_U a_i^2/w_i <= sum_S a_i^2/w_i + (sum_U a_i^2-sum_S a_i^2)/eta`.

## Exact Hermitian form

Let A be real Hermitian, with orthonormal eigenbasis e_i and eigenvalues
lambda_i. Fix an energy t between the single distinguished value
`L-lambda_0` and every other `L-lambda_i`, with `<v,e_0>` nonzero.
Expand x in this basis, set `d_i=L-lambda_i-t` and `a_i=<v,e_i>`.
Parseval and the spectral theorem identify

`L ||x||^2-<Ax,x>-t ||x||^2 = sum_i d_i x_i^2`,
`<v,x>=sum_i a_i x_i`.

Applying the finite criterion with b=-d_0 gives the exact iff

`(t-(L-lambda_0)) sum_(i!=0) a_i^2/(L-lambda_i-t) <= a_0^2`.

Both directions use all vectors: finite synthesis realizes every coordinate
vector, while Parseval supplies the coordinates of every original vector.
No variational approximation or omitted spectral direction enters this iff.

## Eventual packet limits

Suppose each finite packet k supplies eventual bounds
`lower_k(N)<=A(N)<=upper_k(N)`, and both bounds have horizon limits
`l_k,u_k`. If `l_k->a` and `u_k->a`, then A(N)->a.
For any b<a, choose k with b<l_k and then a horizon with b<lower_k(N).
Intersect that event with the packet inequality to obtain b<A(N).
For b>a use u_k<b and the upper inequality. These ordered neighborhood
conditions are exactly convergence to a. No uniform horizon in k is assumed.

## Scope and existing-source audit

The weighted Cauchy--Schwarz input is
`Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul`. The spectral decomposition
is `HTGeometry.shiftedHermitianEnergy_eq_sum`. The corpus already has an
infinite secular Rayleigh-floor theorem and a private exhaustion argument
in `ConjugateDiagonalGeometry/CommonSourceMetric.lean`. The present finite
iff, tail estimate and eventual version supply the concrete transfer
infrastructure. They are classical linear algebra and ordered limits;
no novelty claim is made for their abstract mathematical principles.

The actual prime-matrix hypotheses must still be discharged on the parent
card. This card does not assume a gap or prove the final arithmetic gap.

## Formalization

The installed leaf is `FiniteReciprocalMassControlsTheHyperplane.lean`.
Its six public endpoints are `diagonal_hyperplane_nonneg_iff`,
`reciprocal_mass_le_packet_add_tail`, `exists_negative_diagonal_on_hyperplane`,
`one_negative_diagonal_nonneg_iff`, `hermitian_hyperplane_bound_iff`, and
`tendsto_of_eventual_packet_bounds`. Scratch check 7621 and canonical
check 76613 exited zero; the canonical check had no diagnostics.
All six transitive axiom audits use only `propext`, `Classical.choice`,
`Quot.sound`. The adjacent audit preserves exact commands, source hash
and actual output. The umbrella and foundational README are wired;
owned scratch and logs are cleaned.

- [x] Dependency-closed finite algebra and ordered-limit proof.
- [x] All six Lean proofs and transitive axiom audit.
- [x] Canonical source audit, wiring and durable evidence.
