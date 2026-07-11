# Semilocal number-form equivalence

- **ID:** semilocal-number-form-equivalence
- **Stage:** 2-fully-proven
- **Type:** THEOREM / DOMAIN BRIDGE (paper)
- **Scientific status:** BRIDGE / NOT NEW SCIENTIFIC KNOWLEDGE
- **Source:** normalized archimedean and finite semilocal cyclic measures

## Statement

Let `P` be a finite prime set. Identify the archimedean and semilocal cyclic spectral spaces by the
cyclic transition `J_P`, which is the identity on functions. Their probability measures satisfy

`c_P dmu_infinity <= dnu_P <= C_P dmu_infinity`             (1)

for explicit constants `0<c_P<=C_P<infinity`.

Let `N_infinity,N_P` be the two number operators associated to the common polynomial filtration

`E_n={polynomials of degree <=n}`.

Then their closed quadratic-form domains coincide under `J_P`:

`Dom(N_infinity^(1/2))=Dom(N_P^(1/2))`,                    (2)

and their number forms are quantitatively equivalent:

`c_P <f,N_infinity f>_infinity
 <= <f,N_Pf>_P
 <= C_P <f,N_infinity f>_infinity`.                         (3)

After harmless adjustment of the constants for the two Hilbert norms, the energy spaces

`Dom(D) intersect Dom(N_infinity^(1/2))`

and

`Dom(D) intersect Dom(N_P^(1/2))`

are the same topological vector space. Therefore the archimedean and genuine cyclic semilocal formal
prolate forms have a canonical common energy domain under `eta_P`, despite the algebraic-core
disjointness of the different `theta_P`-transported control.

## Proof

The Euler density bounds give (1). For any of the two Hilbert norms, let `Pi_n` be the orthogonal
projection onto `E_n`. If

`f=sum_(j>=0)c_j p_j`

in the corresponding orthonormal Jacobi basis, then

`dist(f,E_n)^2=||(1-Pi_n)f||^2=sum_(j>n)|c_j|^2`.

Summing in `n` and exchanging the nonnegative sums gives

`sum_(n>=0)dist(f,E_n)^2
 =sum_(j>=1)j|c_j|^2
 =<f,Nf>`.                                                  (4)

The expression may be infinite; finiteness is exactly membership in the number-form domain.

For every polynomial `q in E_n`, equation (1) gives

`c_P||f-q||_infinity^2<=||f-q||_P^2<=C_P||f-q||_infinity^2`.

Taking the infimum over `q in E_n` yields

`c_P dist_infinity(f,E_n)^2
 <=dist_P(f,E_n)^2
 <=C_P dist_infinity(f,E_n)^2`.

Summing and using (4) proves (2)--(3).

The scaling operator `D` is multiplication by the same variable under the cyclic spectral identity,
and the two `L^2` norms are equivalent by (1). Hence its form domain is the same set with equivalent
graph norms. Intersecting with (2) proves the energy-space statement.

## Canonical bounded energy representative

For `lambda>0`, define the positive closed energy form

`a_(lambda,P)(f)=||Df||_P^2+lambda^2<N_P^(1/2)f,N_P^(1/2)f>_P+||f||_P^2`

and the formal prolate form

`q_(lambda,P)(f)=-||Df||_P^2+lambda^2<N_P^(1/2)f,N_P^(1/2)f>_P`.

On the common energy space,

`|q_(lambda,P)(f)|<=a_(lambda,P)(f)`.

Thus Riesz representation gives a canonical bounded self-adjoint contraction `C_(lambda,P)` on the
energy completion satisfying

`q_(lambda,P)(f,g)=a_(lambda,P)(f,C_(lambda,P)g)`.           (5)

This bounded representative exists without selecting a self-adjoint extension of the indefinite
formal prolate operator.

## Route consequence

- `[PROVED]` The direct cyclic comparison through `eta_P` has a canonical common number-form and
  energy domain.
- `[PROVED]` The `theta_P` core-disjointness theorem and this result are compatible: they concern two
  different source transports. `theta_P` preserves Sonin spaces; `eta_P` preserves cyclic polynomial
  filtrations.
- `[PROVED]` The indefinite prolate constraint has the canonical bounded energy representative (5).
- `[LIMIT]` A bounded representative on the energy completion is not a self-adjoint prolate operator
  on the original `L^2` space. Recovering one requires a gap/domain/boundary theorem for the form.
- `[OPEN CORE]` Determine whether `C_(lambda,P)` has a source-selected zero-gap structure compatible
  with the exact Sonin sector, or whether the absence of a gap obstructs every closed `L^2`
  realization.

## Novelty audit

The distance-to-filtration identity and equivalence-of-forms argument are standard Hilbert-space
approximation theory. Their application repairs the exact domain bookkeeping for Route B but is a
BRIDGE, not new scientific knowledge.
