# Exact finite part of raw Mayer determinants

- **Stage:** 1-in-progress
- **Type:** Conjecture
- **Parent:** [raw negative-unit limit](../3-formalized/gauss-mayer-raw-negative-unit-determinants.md).

## Target

Let `L_N(w)` be the genuine first-`N` branch operator,
`a_N=Σ_{n≤N} n^(−w)`, and `E_N(w,λ)=det(I−λL_N(w))`.
For the actual decomposition `D=A+ζB`, conjecture on `Re w>0`:

`E_N(w,λ)−a_N B(w,λ) → A(w,λ)`.

For `w≠1`, this implies
`E_N−N^(1−w)B/(1−w) → D`. On `0<Re w<1`, raw determinants
would converge exactly at the zeros of `B`, with limit `D=A` there.
Otherwise their norms grow as
`N^(1−Re w)|B(w,λ)|/|1−w|`.
The known closed discrete countable zero set contains `λ=0,−1`.

## Compression mechanism

Write `P f=f(0)·1`, `R_N=L_N−a_NP`, and
`K_N=(I−P)R_N(I−P)=(I−P)L_N(I−P)`.
Finite determinant row multilinearity gives `E_N=A_N+a_NB_N`.
A triangular change of basis should identify
`B_N=−λ det(I−λK_N)` and `B=−λ det(I−λK)`, where
`K=(I−P)R(I−P)`. This requires no inverse or source nonvanishing.

For one branch, put `a(z)=(n+z)^(−w)`, `u(z)=1/(n+z)`.
Its double-centered action is exactly

`a(z)[f(u(z))−f(u(0))]+[a(z)−a(0)][f(u(0))−f(0)]`.

On the actual disc, `|u(z)−u(0)|≤5/n²` and `|u(0)|=1/n`.
The checked branch-weight bounds therefore give a monomial bound
`j[5M(w)+(5/2)|w|M(w+1)]n^(−Re w−2)`.
The existing Cauchy rescaling converts this to a geometric matrix bound.

A uniform determinant perturbation inequality would bound `|B_N−B|`
by `C Σ_{n>N}n^(−Re w−2)`. Since `|a_N|≤N`, its product with
`|a_N|` is at most `C Σ_{n>N}n^(−Re w−1)→0`.
Uniform geometric continuity already gives `A_N→A`.

## Open proof obligations

- Exact finite-section compression identity and passage to Fredholm limits.
- Actual double-centered branch and geometric tail bounds.
- Dimension-independent determinant perturbation bound.
- Finite-part limit and exact convergence classification.

Corpus searches returned affine source determinants, uniform geometric
remainder estimates, rank-one determinant identities, and multilinear
perturbation estimates. No checked result yet discharges the three new
inputs above. Scratch formalization has begun; no certificate is claimed.
No literature-priority or resonance-exclusion claim is made.
