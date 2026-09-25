# Alternating signature of the unique Gamma gap correction

- **ID:** `stc-hyperbolic-gap-krein-signature`
- **Stage:** 2-fully-proven (paper)
- **Type:** exact finite-packet inertia theorem and carrier reinterpretation
- **Routes:** STC, Gamma-six/Sonin source lift, RHist
- **Status:** `[PROVED ON PAPER] [GENERAL INERTIA LEAN PENDING] [NOT AN RH PROOF]`

## Kernel forced by all-prime flatness

The [flat-completion theorem](stc-hyperbolic-gap-flat-completion.md) proves that, at every nonzero real grade `g`, the only continuous gap-only correction equal to one at coincidence that makes the literal normalized Gamma prime pair a one-prime coboundary is

```text
K_g(x,y)=S(g(x-y)/2),
S(t)=sinh(t)/t,  S(0)=1.
```

This uniqueness holds even when flatness is imposed only on actual ordered prime pairs. For distinct real nodes `x₁<⋯<x_N`—in particular distinct prime logarithms—let `K_N=(K_g(x_i,x_j))`.

## Theorem: exact inertia on every packet

For every `g≠0` and `N≥1`, `K_N` is nonsingular and

```text
sign(det K_N)=(-1)^[N(N-1)/2],
inertia(K_N)=(ceil(N/2) positive, floor(N/2) negative).   (1)
```

The inertia is independent of the node spacing and of the nonzero grade magnitude. In particular every two-prime packet has one negative direction; negative and positive indices both grow without bound as prime packets grow. No invertible congruence on these finite packets can make this correction positive semidefinite. The finite-packet conclusion does not assert that the infinite unweighted prime matrix defines a bounded operator.

## Proof

Put `a=|g|>0`. The exact integral representation is

```text
K_g(x,y)=(1/a) ∫_[-a/2,a/2] exp(u x) exp(-u y) du.       (2)
```

Let `μ` be normalized Lebesgue measure on that interval. The real Andréief identity gives

```text
det K_N = (1/N!) ∫ det[exp(u_j x_i)]_(i,j)
                     det[exp(-u_j x_i)]_(i,j)
                     dμ(u₁)⋯dμ(u_N).                    (3)
```

For strictly increasing `u₁<⋯<u_N` and `x₁<⋯<x_N`, the first determinant is strictly positive. Here is a dependency-closed sign argument. A nonzero sum of `N` real exponentials with distinct exponents has at most `N-1` real zeros: divide by its lowest exponential, differentiate, and apply Rolle plus induction. Therefore its evaluation determinant at distinct ordered nodes never vanishes; this is already formalized as `det_realExponentialVandermonde_ne_zero` in the corpus. For fixed ordered `x`, the region of strictly ordered exponent vectors `u` is convex, so continuity and nonvanishing make the determinant sign constant there. At the particular exponents `u_j=j-1`, the matrix is `[(exp x_i)^(j-1)]`, the ordinary Vandermonde matrix, with strictly positive determinant `∏_(i<j)(exp x_j-exp x_i)`. Hence the sign is positive for every ordered `u`. The second determinant in (3) reverses the exponent order, so its sign is `(-1)^[N(N-1)/2]` times a strictly positive number. The product has that fixed nonzero sign whenever the `u_j` are distinct. Coincidence hyperplanes have zero `μ^N` measure, proving the strict determinant sign in (1).

Apply the same argument to each leading `k×k` principal submatrix. Its determinant `Δ_k` has sign `(-1)^[k(k-1)/2]` and is nonzero. The symmetric `LDLᵀ` factorization exists without pivoting; its `k`th diagonal pivot is `Δ_k/Δ_(k-1)` and has sign `(-1)^(k-1)`. Sylvester inertia then gives exactly the alternating count in (1).

The proof uses only positivity of the integration measure and the strict exponential-Vandermonde sign. Therefore the same determinant sign and inertia hold for **any** finite positive symmetric measure `μ` on a compact real interval whose support contains at least `N` points, with `K(x,y)=∫exp(u(x-y))dμ(u)`. Symmetry makes `K` real symmetric; at least `N` support points give positive product-measure mass to tuples of distinct `u_j`. The uniform measure in (2) is the source-selected specialization. By contrast, replacing real `u` by imaginary frequencies gives a Fourier Gram kernel with a positive quadratic form. The source correction lies on the real-exponent, indefinite side of this Fourier/Laplace change of geometry.

## Route consequence

Entrywise positivity of `S` conceals an **infinite-index indefinite geometry**. The exact source flattening is a forward/reflected exponential pairing (2), not a Hilbert-positive Gram kernel. Even a finite-negative-index Pontryagin carrier cannot retain all packet forms; any faithful all-prime completion needs a genuinely indefinite space or a non-congruent singular quotient that removes negative directions by an independently derived law. The [two-prime Lean theorem](../../../../formal/GaloisForLFunctions/HTGeometry/HyperbolicGapFlatCompletion.lean) proves the first negative and positive directions; (1) proves their growth on paper.

In particular, this kernel cannot itself serve as a finite-negative-square generalized-Nevanlinna reader whose index counts off-critical zeros: its negative index already grows like half the packet size at every nonzero grade, without any Xi divisor input. A divisor-sensitive reader would need a source-derived subtraction, quotient or coupling that changes this background signature while retaining the canonical prime phase.

The same inertia law rules out a **uniformly finite-channel repair**. If a symmetric correction `B_N` has rank at most `r₀`, the negative subspace of `K_N` has dimension `floor(N/2)` and its intersection with `ker B_N` has dimension at least `floor(N/2)-r₀`. On that intersection the quadratic form of `K_N+B_N` equals the strictly negative form of `K_N`. Hence `K_N+B_N` still has at least `floor(N/2)-r₀` negative directions. A fixed number of extra one-prime channels cannot make all cofinal packets positive; a source law that removes the background signature must have growing rank or use a genuinely singular quotient. This does not exclude infinite-rank compact or nonlocal corrections.

This identifies a source-selected carrier type but does not supply the RH-producing rule: one must still connect its signed forward/reflected pairing to the canonical phase-twisted Sonin exterior and prove a divisor-specific positive or sub-root Calkin law. Merely defining a Krein completion, or discarding negative directions, would not exclude off-line zeros.

The [exterior spectral reader theorem](stc-flat-gap-exterior-spectral-reader.md) identifies a second, independent obstruction: the canonical prime charge is not even a closable functional of the reflection-positive Hilbert completion associated with this kernel. Its spectral evaluation lies outside the source-selected band.

## Audit

- The normalized source pair and uniqueness of its gap correction are in the linked flat-completion card; the exponential cocycle uniqueness step is formalized in `HyperbolicGapFlatCompletion.lean`.
- The corpus already formalizes real exponential-Vandermonde **nonvanishing** in `NavierStokesRealExponentialVandermonde.lean` and the real Andréief identity in `Zeta5AndreiefTransfer.lean`. Their combination with a strict sign proof and `LDLᵀ` inertia is new paper work here; general Lean formalization remains open.
- Deep corpus search for the exact gap-sinc inertia theorem was partial. No external priority claim is made.
