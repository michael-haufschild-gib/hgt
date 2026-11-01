# The spectral pole coefficient should also govern raw determinant growth

- **Stage:** 0-backlog
- **Type:** Conjecture
- **Parent:** [raw negative-unit limit](../3-formalized/gauss-mayer-raw-negative-unit-determinants.md).

## Target

For `0<Re w<1`, let `E_N(w,λ)=det(I−λL_N(w))`. Conjecture:

`N^(w−1) E_N(w,λ) → B(w,λ)/(1−w)` for every complex `λ`,

where `B` is the actual coefficient in `D(w,λ)=A(w,λ)+ζ(w)B(w,λ)`.
Thus the same rank-one coefficient should control both the source pole and
raw branch-cutoff growth. Outside its closed discrete countable spectral
zero set, the proposed norm asymptotic is

`|E_N(w,λ)|/N^(1−Re w) → |B(w,λ)|/|1−w| > 0`.

At `λ=−1`, the coefficient vanishes and the stronger unnormalized convergence
is already certified. A vanishing leading coefficient alone would not prove
convergence at other exceptional parameters.

## Mechanism to audit

The genuine decomposition is `L_N=R_N+a_NP`. One-row determinant multilinearity
should give `E_N=A_N+a_NB_N`, where `A_N` and `B_N` use fixed perturbations
`R_N` and `R_N+P`. The certified uniform geometric remainder bounds and
entrywise convergence should give `A_N→A` and `B_N→B`. Applying actual
cutoff normalization to the constant input at zero gives
`N^(w−1)a_N→(1−w)^(−1)`, while `N^(w−1)→0`.

The corpus search returned the exact affine source determinant, raw matrix
decomposition, and negative-unit cancellation, but no checked general
raw-determinant asymptotic. Formalization and complete paper audit remain
pending. No literature-priority or resonance-exclusion claim is made.

## Stronger finite-part conjecture

Let `P f=f(0)·1`, `a_N=Σ_{n≤N} n^(−w)`, and
`K_N=(I−P)L_N(I−P)`. Conjecture on `Re w>0`:

`E_N(w,λ)−a_N B(w,λ) → A(w,λ)`.

For `w≠1`, this would give
`E_N−N^(1−w)B/(1−w) → D`. In the critical strip, raw determinants would
then converge exactly at the zeros of `B`, with limit `D=A` there.

The proposed new input is double centering. Writing `a(z)=(n+z)^(−w)`
and `u(z)=1/(n+z)`, the centered branch is exactly

`a(z)[f(u(z))−f(u(0))]+[a(z)−a(0)][f(u(0))−f(0)]`.

The checked inverse-branch and Cauchy bounds suggest decay
`O(n^(−Re w−2))`, including a linear-in-degree monomial bound.
The rank-one coefficient should equal `−λ det(I−λK_N)` by a finite
triangular change of basis and expansion along the constant coordinate.
A uniform geometric determinant perturbation bound would then give
`B_N−B=O(N^(−Re w−1))`; since `|a_N|≤N`, its product with `a_N` vanishes.

This stronger statement remains conjectural until the compression identity,
branch estimate, and determinant bound are proved and kernel-checked.
Initial corpus searches returned existing geometric determinant limits and
one-row affine dependence, but no checked theorem discharging these inputs.
