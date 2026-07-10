# Finite Sonin Euler corners have an l2 Calkin lower bound

- **ID:** sonin-finite-calkin-l2-lower-bound
- **Stage:** 2-fully-proven
- **Type:** THEOREM / OBSTRUCTION
- **Date:** 2026-07-10
- **Status banner:** `[NOVELTY UNVERIFIED]` The compact-distance theorem, Euler specialization, and
  all-prime obstruction are proved. Scientific priority still requires a Wiener--Hopf, Toeplitz,
  crossed-product, and Sonin/prolate literature audit.
- **Parents:**
  `sonin-euler-metric-corner-noncompact.md`;
  `sonin-two-scale-quadratic-corner-noncompact.md`
- **Lean target:** `formal/GaloisForLFunctions/RHTower/SoninEulerFiniteL2Lower.lean`

## Theorem `[PROVED HERE]`

Let `a>0`, let `r_1,...,r_m>1` be distinct real scales, and let

`L_r=(1-Q_a)(U_r+U_r^(-1))Q_a`

on the actual even Sonin carrier. For every coefficient vector `c in C^m` and every compact
operator `K`,

`(sum_i |c_i|^2)^(1/2) <= ||sum_i c_i L_(r_i)-K||`.       (1)

For the positive Euler corners `C_r=-r^(-1/2)L_r`, this becomes

`(sum_i |c_i|^2/r_i)^(1/2) <= ||sum_i c_i C_(r_i)-K||`.  (2)

In particular, for finite prime sets `F`,

`dist(sum_(p in F) C_p, Compact) >= (sum_(p in F) 1/p)^(1/2)`. (3)

Thus the unsmoothed all-prime positive Euler boundary sum cannot remain bounded modulo compact
operators; along `p<=X` its essential norm has at least square-root prime-harmonic growth.

More generally, if coefficients `c_p` have all finite sections uniformly bounded modulo compacts
by `B`, then

`sum_p |c_p|^2/p <= B^2`;                                      (4)

in particular `(c_p)` must belong to the weighted space `l2(1/p)`.

## Proof

The empty family is immediate, so assume `m>=1`.

### 1. One shell separates every scale

Let

`r_min=min_i r_i>1`.

If `m>=2`, let

`sigma=min_(i!=j) max(r_i/r_j,r_j/r_i)>1`;

for `m=1`, set `sigma=2`. Choose

`a/r_min<c<a`

and then choose `t` with

`1<t<min(a/c,sigma)`.

Put `d=tc`. Then

`a/r_i<c<d<a`                                             (4)

for every `i`, and

`d/c<max(r_i/r_j,r_j/r_i)`                               (5)

for every `i!=j`. If `r_i<r_j`, (5) gives `r_i d<r_j c`; hence the exterior shells
`r_iJ`, where `J={c<|x|<d}`, are pairwise disjoint.

### 2. Simultaneous exterior preimages survive the Sonin constraint

Let `v_n` be an orthonormal sequence of even functions supported in `J`, and set

`g_(i,n)=U_(1/r_i)v_n`, `f_(i,n)=Q_a g_(i,n)`.

By (4), every `g_(i,n)` is supported outside `[-a,a]`, in a bounded shell independent of `n`.
The finite time--band block on that shell is compact. The Sonin projection-correction estimate
therefore gives

`||f_(i,n)-g_(i,n)||->0`                                 (6)

for every `i`.

For a fixed coefficient vector `w`, put

`g_(w,n)=sum_i w_i g_(i,n)`, `f_(w,n)=sum_i w_i f_(i,n)`.

The pairwise disjoint support shells make the vectors `g_(i,n)` orthonormal as `i` varies. Hence

`||g_(w,n)||=||w||_2`.

Finite summation and (6) give

`||f_(w,n)-g_(w,n)||->0`, `||f_(w,n)||->||w||_2`.        (7)

Each `g_(i,n)` is an orthonormal sequence in `n`, hence weakly null; (6) and finite summation imply
that `f_(w,n)` is weakly null.

### 3. The scale matrix converges to the identity

Because `v_n` is supported inside `[-a,a]`, one has `Q_av_n=0`. Since `f_(i,n)` lies in
`range(Q_a)`, orthogonality of the projection gives

`<L_(r_j)f_(i,n),v_n>=<D_(r_j)f_(i,n),v_n>`,             (8)

where `D_r=U_r+U_r^(-1)`.

By (6), the right side differs by `o(1)` from `<D_(r_j)g_(i,n),v_n>`. The dilation group law gives

`D_(r_j)g_(i,n)
 =U_(r_j/r_i)v_n+U_(1/(r_i r_j))v_n`.                    (9)

If `i=j`, the first summand in (9) is `v_n`; the second is supported beyond `a`, hence is
orthogonal to `v_n`. If `i!=j`, (5) makes the shell supporting the first summand disjoint from `J`
in either scale order. The second summand is again exterior because `a<r_i c<r_i r_j c`.
Consequently

`<L_(r_j)f_(i,n),v_n> -> delta_(ij)`.                    (10)

### 4. The compact-distance lower bound

Let

`T_c=sum_j c_jL_(r_j)`.

Choose a vector `w` with `||w||_2=1` which norm-attains the coefficient functional determined by
`c`; equivalently, after the harmless conjugation dictated by the inner-product convention,

`|sum_i c_iw_i|=||c||_2`.

Equations (7) and (10) imply

`||f_(w,n)||->1`,

`|<T_cf_(w,n),v_n>|->||c||_2`.                          (11)

For every compact `K`, weak nullity and boundedness give `||Kf_(w,n)||->0`. Since `||v_n||=1`,

`|<(T_c-K)f_(w,n),v_n>| <= ||T_c-K|| ||f_(w,n)||`.

Passing to the limit in this inequality and using (11) proves (1).

### 5. Euler and prime consequences

For `C_r=-r^(-1/2)L_r`, apply (1) to the dilation coefficients

`-c_i/r_i^(1/2)`.

This gives (2). Taking `c_i=1` on a finite prime set gives (3). Since the sum of reciprocal primes
diverges, the Calkin norms of the canonical finite all-prime sums are unbounded. More quantitatively,
the classical prime-harmonic asymptotic gives a lower growth of order `sqrt(log log X)` along
`p<=X`.

For arbitrary prime coefficients, suppose every injective finite prime family admits a compact
perturbation after which the corresponding corner sum has norm at most `B`. Apply (2) to that
compact perturbation. Every finite weighted energy sum is at most `B^2`; the nonnegative-series
criterion then gives (4).

## Attack and exact scope

- `[PROVED]` The narrow-shell construction handles the empty, singleton, and arbitrary finite
  injective families.
- `[PROVED]` The off-diagonal inward branch misses the common shell in both scale orders; the
  outward branch is exterior for every ordered pair.
- `[PROVED]` No uniform bound on a post-dilation Sonin correction is needed: pairing against the
  forbidden shell removes `1-Q_a` exactly.
- `[PROVED IN PARENTS]` Each exterior preimage is asymptotically fixed by the actual two-constraint
  Sonin projection.
- `[PROVED IN PARENTS]` Compact operators annihilate bounded weakly-null sequences in norm.
- `[PARENT-THEORY WARNING]` The abstract l2 lower bound resembles the regular-representation bound
  for a finite group-algebra element. Scientific content, if any, must lie in proving that the fixed
  Sonin constraint realizes this regular behavior and in the all-prime obstruction, not in the
  Hilbert-space inequality itself.
- `[OPEN CORE]` The theorem gives a lower bound, not the exact Calkin norm of a general finite
  combination. It does not exclude a renormalized or phase-compensated global prime construction
  whose finite sections are not the canonical positive Euler sums.

## Novelty and significance gate

- **Novelty:** `[NOVELTY UNVERIFIED]` The prior project theorem proves only coefficient isolation and
  Calkin linear independence. No scientific priority claim is made until the exact quantitative
  theorem and its Wiener--Hopf/Toeplitz parent-theory status are audited.
- **Significance:** Equation (3) excludes not only compactness but boundedness modulo compacts of
  the canonical unsmoothed all-prime additive Euler seam. Any surviving prime aggregation must
  renormalize, smooth, or introduce a genuinely global cancellation before reaching the boundary.

## Lean realization

`formal/GaloisForLFunctions/RHTower/SoninEulerFiniteL2Lower.lean` formalizes the theorem in a dual
but equivalent shell geometry: one common exterior shell is corrected once by `Q_a`, and its inward
images at all scales are pairwise orthonormal. The module constructs the finite separating shell,
proves simultaneous corner convergence, derives the compact-distance bound including the empty
family, proves the exact positive Euler weighting, and transports it to the literal concrete
Hardy--Titchmarsh source operators.

The final endpoints are
`finiteCoefficientL2Norm_le_norm_finiteEvenDilationCorners_sub_compact_all`,
`finiteEulerCoefficientL2Norm_le_norm_finiteEvenPositiveEulerCorners_sub_compact`,
`finiteEulerCoefficientL2Norm_le_norm_finiteArchimedeanPrimeEulerCorners_sub_compact`, and
`finitePrimeReciprocalL2Norm_le_norm_archimedeanEulerCorners_sub_compact`. The endpoint
`summable_primeEulerCoefficientEnergy_of_uniform_sub_compact_bound` formalizes the weighted
`l2(1/p)` necessity. The endpoint
`exists_finitePrime_archimedeanEulerCorner_sub_compact_norm_gt` combines the finite-prime theorem
with mathlib's divergence of the reciprocal-prime sum to produce canonical source corner sums
whose distance from every compact operator exceeds any prescribed bound. The weaker endpoint
`exists_finitePrime_archimedeanEulerCorner_norm_gt` follows by taking the compact operator to be
zero.

The sharper rate is encoded in `formal/GaloisForLFunctions/RHTower/PrimeHarmonicLogLower.lean`:
the Mertens-type bound `log log (X+1) - 1 <= sum_(p<=X) 1/p` is proved unconditionally from the
finite Euler product over `Nat.primesBelow (X+1)`, and the endpoints
`sqrt_log_log_sub_one_le_norm_sum_primesBelow_eulerCorners_sub_compact` and
`sqrt_log_log_sub_one_le_essentialNorm_sum_primesBelow_eulerCorners` give the exact
square-root double-logarithmic growth of the canonical ordered all-prime exhaustion
`sum_(p in primesBelow (X+1)) C_p` against every compact perturbation.

## Gates

- [x] 0 -> 1: exact quantitative claim and simultaneous-shell mechanism isolated
- [x] 1 -> 2: complete proof, boundary cases, and parent-theory attack
- [x] 2 -> 3: compact-distance, Euler, source, finite-prime, and weighted coefficient forms formalized
- [ ] 3 -> 4: independent literature and significance audit
