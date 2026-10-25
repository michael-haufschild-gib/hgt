# Uniform harmonic Gram law at half damping

- **ID:** uniform-half-damping-vaughan-harmonic-gram
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Source:** uniform-second-scale-vaughan-gram-at-all-cutoffs.md
- **Statement:** At half damping, the centered Vaughan Gram differs from its explicit harmonic rank-one term by a bounded matrix uniformly over all cutoffs and horizons. Its renormalized moving-cutoff limit is an actual finite Gram of two source rows.
- **Novelty status:** Endpoint refinement of the uniform convolution argument; initial corpus search found the fixed-cutoff admission law and smooth-power estimates, not this uniform bounded-error statement. No external novelty claim.

## Exact endpoint statement

Fix `ε=1/2`. Let `e_i(n;U,V)` be the five centered pieces,
`H_U=Σ_(d≤U)μ(d)/d`, `K_(U,V)=subHalfZetaCoeff(1/2)H_UH_V`,
`s=(0,0,-1,1,0)`, and `J(T)=Σ_(1≤n≤T)1/(n+1)`.
There is a finite constant `C`, independent of `U,V,T,i,j`, such that

`|G^c_ij(T;U,V)-K_(U,V)^2 s_i s_j J(T)|≤C`.

In particular, every entry outside the two-by-two convolution block is uniformly
bounded. The convolution block has one explicit harmonic divergence. Removing its
smooth coefficient gives uniform bounded energy, even when the cutoffs move.

## Uniform pointwise remainder

The dependency-closed paper argument in the source card proves arbitrary logarithmic
mean-error bounds for the undamped small-small coefficient
`a_(U,V)=μ_≤U⋆μ_≤V⋆1`, with mean `H_UH_V`. Its bound
`|a_(U,V)(d)-H_UH_V|≤C₀ τ(d)^2` is uniform in both cutoffs.

At half damping the generalized finite hyperbola estimate remains valid:

`|A_r(n)|≤C₁ D^(1/2)(1+log D)^4+26 L_D n D^(-1/2)`,

where `L_D` is a common bound for `|Σ_(d≤x)r(d)|/x` for all `x≥D`.
For any prescribed `A>0`, take `D=floor(n/(log n)^b)` with
`b/2>A+4`, and use a partial-sum logarithmic rate of order greater than `A+b/2`.
The resulting bound is `O_A(sqrt(n)/(log n)^A)` uniformly in `U,V`.

The same argument applies uniformly to the truncated Möbius patterns. Indeed,
their partial sums are `M(min(U,x))`. If `min(U,x)≤sqrt(x)`, their absolute value
is at most `sqrt(x)`. Otherwise the checked arbitrary logarithmic Mertens estimate,
with `log(min(U,x))≥(log x)/2`, gives a common arbitrary logarithmic rate.
The untruncated actual Möbius pattern has that rate as well.

For the unit pattern, the read source theorem `abs_subHalfRemainder_le` gives
remainder `O(n^(1/4))` at `ε=1/2`. It is not a pointwise constant bound; the
quarter-power error is still smaller than `sqrt(n)/(log n)^A` for every fixed `A`.
The harmonic factors are uniformly bounded. The pole correction is bounded by `1/2`.
The exact sum of the five centered pieces is the interior prefix.

Consequently there are remainders `r_i(n;U,V)` with

`e_i(n;U,V)=K_(U,V)s_i sqrt(n)+r_i(n;U,V)`

and, for every fixed `A`, a common eventual estimate

`|r_i(n;U,V)|≤C_A sqrt(n)/(log n)^A`.

A finite initial interval has one uniform bound: the summable Vaughan divisor
majorant bounds all centered pieces by a fixed multiple of `n`, and `K_(U,V)` is
bounded. These statements include zero cutoffs.

## Summing the Gram error

Use the remainder estimate with `A=2`. Uniformly in `U,V,i`, both sums

`Σ_(n≥1) sqrt(n)|r_i(n;U,V)|/[n(n+1)]`,
`Σ_(n≥1) |r_i(n;U,V)|^2/[n(n+1)]`

are bounded. Their tails are dominated respectively by constant multiples of
`1/(n(log n)^2)` and `1/(n(log n)^4)`; the finite initial ranges are already paid.
Expanding the product of the two centered pieces proves the stated bounded error.
This is stronger than a norm-triangle `O(sqrt(log T))` error because the mixed
smooth/remainder pairing is absolutely summable.

For any real coefficient vector `w`, writing `Q_w=K_(U,V)(w_3-w_2)`, the same bound gives

`|‖Σ_i w_i e_i‖_T^2-Q_w^2 J(T)|≤C(Σ_i|w_i|)^2`.

Thus packets with `Q_w=0` have one uniform bound over all cutoffs and horizons.
At positive cutoffs, harmonic nonvanishing identifies that condition with `w_2=w_3`.
For the uncentered packet one must also remove its linear mean.

## The moving renormalized Gram

Let `A(n)` be the actual centered power-damped Möbius divisor prefix at half damping,
and let `P(n)` be the centered pole piece, namely minus the active correction.
Both rows have finite pronic energy. Set

`R=(A,A,-A,0,P)`.

For each fixed `n`, as both cutoffs tend to infinity, the small pieces tend to `A`,
the small-small piece tends to `-A` by the actual convolution identity, and the
both-large piece tends to zero. Their means converge to the full reciprocal mean.
Also `H_UH_V→0`, so each `r_i(n;U,V)→R_i(n)`.

The common summable squared envelope above gives convergence of the remainders in
pronic L². This also holds for partial pairings at any horizon `T→∞`: the common
summable envelope pays the omitted tail uniformly. Their pairings therefore tend to

`G∞_ij=Σ_(n≥1)R_i(n)R_j(n)/[n(n+1)]`.

The two smooth/remainder pairings are uniformly bounded in absolute value, while
`K_(U,V)→0`. Hence, with `T,U,V→∞` independently,

`G^c_ij(T;U,V)-K_(U,V)^2 s_i s_j J(T) → G∞_ij`.

The limiting matrix is positive semidefinite and has rank exactly two. All five rows
lie in the span of `A` and `P`; their two-cell determinant proves independence, with
`det Gram(A,P)≥1/62208`, as shown in `the-endpoint-vaughan-limit-has-rank-two.md`.
The positive first pole cell also gives `G∞_44≥1/64`; see
`the-centred-vaughan-pole-has-positive-finite-energy.md`. Both refinements have
dependency-closed paper proofs and await Lean verification.
A finite limit of the scalar harmonic mass `K_(U,V)^2 J(T)→ℓ` gives
actual Gram limit `G∞+ℓssᵀ`; an unbounded harmonic mass forces the corresponding
convolution diagonal to diverge. The cutoff/horizon interaction is thus carried by
one explicit nonnegative scalar at the endpoint.

The finite limiting matrices consequently form the ray `G∞+ℓssᵀ`, `ℓ≥0`.
Their rank is two for `ℓ=0` and three for `ℓ>0`: the independent coefficient
directions `(1,1,-1,0,0)` and `(0,0,0,0,1)` supporting `G∞` have zero fourth
coordinate, whereas `s` does not. Conversely, convergence of the full Gram forces
convergence of the harmonic mass, because its `(3,3)` entry is that mass plus a
remainder tending to zero.

Every value `ℓ≥0` is attainable with both cutoffs divergent. For `ℓ=0`, take
`U=V=N,T=N²`. For `ℓ>0`, put `k_N=K_(N,N)^2>0` and take
`T_N=ceil(exp(ℓ/k_N))`. Harmonic nonvanishing makes this well-defined; `k_N→0`
makes `T_N→∞`. Since `J(T)-log T` stays bounded and rounding changes the logarithm
by a quantity tending to zero, `k_N J(T_N)→ℓ`. Thus the ray is the exact set of
finite joint-limit matrices, not merely an upper description. These rank and
realization corollaries also await Lean formalization.

## Product horizons

At `T=UV`, let `W=max(U,V)`. For positive cutoffs, `T≤W²`, so
`J(T)≤1+2log W`. The harmonic factors are bounded, and the factor at `W` has every
logarithmic saving. Consequently `K_(U,V)^2 J(UV)→0` whenever `UV→∞`, uniformly in
the factorization. Finite products and zero products are harmless. The centered
product-horizon trace therefore has one uniform finite bound at half damping.
If both cutoffs diverge, the actual centered product-horizon Gram tends to `G∞`.
The limit is nonzero: its pole diagonal is at least `1/64`.

## Audit and status

Read source dependencies include `abs_subHalfRemainder_le`, the checked mean-zero
prefix hyperbola estimate at `ε≤1/2`, the actual half-damping receiver budget,
arbitrary logarithmic Mertens and harmonic bounds, the exact five-piece identity,
and the uniform finite floor majorant. The endpoint argument introduces no new
analytic premise. The uniform double-convolution logarithmic theorem, generic
damped logarithmic transfer, and actual convolution fluctuation are now checked
in Lean. This card's bounded-error law and moving-limit corollaries remain
unformalized. Existing half-admission and product-horizon drafts do not yet establish
these stronger claims. Full Q-I remains open.

## Relation to subcritical limit classification

The dependency-closed paper
`vaughan-subcritical-gram-limit-classification.md` identifies the normalized
subcritical limit set as a countably infinite compact family, discrete away from
zero. Positive nonzero limits there require an eventually fixed harmonic amplitude
and bounded cutoffs. At half damping, the additional factor `J(T)` amplifies
vanishing amplitudes into every finite nonnegative harmonic mass, producing the
continuous ray above even with both cutoffs divergent. The distinction concerns
the exact limiting matrices; it supplies no fixed-strip power estimate.
