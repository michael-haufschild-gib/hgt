# DA Taylor Log-Ratio Algebraicity and Resonance Law

- **ID:** `da-taylor-log-ratio-algebraicity-resonance-law`
- **Stage:** 2-fully-proven / needs scientific-novelty audit
- **Type:** THEOREM (paper) / GENERAL DA LAW / COEFFICIENT-MAGNITUDE CONSTRAINT
- **Scientific status:** `[PROVED HERE] [NOVELTY UNVERIFIED] [SIGNIFICANT]`
- **Statement:** If an eventually full-support DA power series has a finite negative-logarithmic coefficient ratio limit greater than one, that limit is algebraic and its logarithmic magnitudes satisfy an infinite subsequence of logarithmically accurate integer shift resonances.

## Goal

Identify what a finite algebraic differential constraint forces when Taylor magnitudes decay on an asymptotically geometric logarithmic scale. The result is a necessary law for DA functions, not merely a sufficient HT example.

The constraint is arithmetic even though the coefficients and their phases are arbitrary complex numbers: Mahler normalization makes the ADE integral, and repeated Archimedean cancellation forces an integer relation in the limiting logarithmic ratio.

## Theorem `[PROVED HERE] [NOVELTY UNVERIFIED]`

Let

`f(z)=sum_(n>=0) a_nz^n`

be DA over `C(z)`. Assume that `a_n!=0` eventually, put

`b_n=-log|a_n|`,

and suppose that eventually `b_n>0` and

`b_(n+1)/b_n -> lambda` with `1<lambda<infinity`.                            `(LR)`

Then:

1. `lambda` is algebraic over `Q`.
2. There are a nonzero integer Laurent polynomial

   `Q(T)=sum_r d_rT^r in Z[T,T^(-1)]`,

   with

   `Q(1)=Q(lambda)=0`,                                                       `(R1)`

   a constant `C>0`, and an infinite sequence `q_k->infinity` such that

   `|sum_r d_r b_(q_k+r)| <= C log q_k`.                                    `(R2)`

The Laurent polynomial and the sequence may depend on the integer-normalized ADE satisfied by `f`.

## Corollary: transcendental log-ratio forces HT `[PROVED HERE]`

Let `lambda>1` be transcendental. Every entire or formal power series with eventually nonzero coefficients, eventually positive `b_n=-log|a_n|`, and

`b_(n+1)/b_n -> lambda`

is HT over `C(z)`, independently of all coefficient phases.

This strictly strengthens the exact geometric profile `b_n=A lambda^n`: arbitrary subleading fluctuations are allowed as long as the successive ratio converges to the same transcendental limit.

## Corollary: DA extended log-ratio spectrum `[PROVED HERE]`

Let `f` be an eventually full-support DA entire series with eventually positive `b_n=-log|a_n|`. If the extended limit

`lim b_(n+1)/b_n in [1,infinity]`

exists, then it belongs to

`{1} union (RealAlgebraicNumbers intersect (1,infinity))`.                  `(S)`

Indeed, a finite limit greater than one is algebraic by the theorem. The limit `infinity` is impossible by the log-superlacunary phase-uniform HT theorem. Thus the only nonalgebraic boundary value left by a convergent ratio is `1`.

## Proof

A finite Taylor prefix is irrelevant to DA status and to `(LR)`, so work on a full nonzero tail.

Assume `f` is DA. Mahler's integer-normalization theorem gives a nonzero

`P in Z[z,Y_0,...,Y_m]`

such that

`P(z,f,f',...,f^(m))=0`.                                                     `(1)`

Let `D>=1` be the largest total `Y`-degree of `P`. For the generic series

`F(z)=sum_(n>=0)X_nz^n`,

expand and group equal coefficient monomials:

`[z^N]P(z,F,F',...,F^(m))=sum_(nu in A_N)c_(N,nu)X^nu`.                     `(2)`

Every displayed `c_(N,nu)` is a nonzero integer. For fixed `P`, both the number of atoms and the absolute values of their coefficients are bounded by a fixed power of `N+2`.

After substituting `X_n=a_n`, define

`V_N(nu)=sum_n nu_n b_n=-log|a^nu|`.                                        `(3)`

The integer zero-sum identity has the following Archimedean bend property: its two smallest distinct grouped-atom valuations differ by at most

`C_P log(N+2)`.                                                             `(4)`

If the minimum is tied, the gap is zero. If it is unique, (4) follows from the triangle inequality: the integer weight of the largest-magnitude atom has modulus at least one, while the polynomially many remaining weighted atoms can cancel it only within a polynomial magnitude factor.

### 1. Ratio convergence confines the two smallest atoms

Choose constants

`1<mu<lambda<Lambda`.

Condition `(LR)` gives, for all sufficiently large `n`,

`mu <= b_(n+1)/b_n <= Lambda`.                                              `(5)`

In particular `b_n/log n->infinity`, and for every fixed integer `r`,

`b_(n+r)/b_n -> lambda^r`.                                                  `(6)`

The balanced-survival theorem for generic ADE coefficients supplies constants `B` and `N_0` such that, for every `N>=N_0`, (2) has a nonzero degree-`D` atom all of whose source indices lie in

`[N/D-B,N/D+B]`.                                                            `(7)`

Write `q=floor(N/D)`. The witness (7) has valuation at most `D b_(q+B+1)` after increasing `B` harmlessly.

When `D>=2`, every atom of degree `d<D` has a source index at least

`N/(D-1)-O_P(1)`,

which lies a positive linear distance above `q`. By the lower ratio bound in (5), its valuation exceeds the balanced witness by an exponential factor. When `D=1`, degree-zero terms occur at only finitely many coefficient indices.

Choose a fixed `B'>B` so large that

`mu^(B'-B-2)>2D`.

Every degree-`D` atom with largest source index above `q+B'` then has valuation more than twice the witness upper bound for all large `N`. The source-sum constraint bounds all remaining indices below once the largest is bounded. Hence there is a constant `K=K_P` such that:

- every global valuation minimizer has degree `D` and all indices in `[q-K,q+K]`;
- every lower-degree or outside-window atom is separated from the global minimum by `omega(log N)`.

Because (4) requires a second atom within `O(log N)`, the second-smallest atom must also have degree `D` and lie in the same bounded window.

### 2. Pigeonholing produces one persistent integer resonance

For every sufficiently large `N`, choose two distinct bounded degree-`D` atoms realizing the bend (4). Write their multiplicity difference relative to `q` as

`d_(N,r)=nu_(q+r)-mu_(q+r)`, `|r|<=K`.

Each `d_(N,r)` is an integer of absolute value at most `D`, not all are zero, and

`sum_r d_(N,r)=0`                                                          `(8)`

because both atoms have total degree `D`.

Only finitely many such integer vectors exist. Therefore one nonzero vector `(d_r)` occurs for infinitely many coefficient indices `N_k`. Passing to that subsequence and putting `q_k=floor(N_k/D)`, equation (4) becomes

`|sum_r d_r b_(q_k+r)| <= C log q_k`                                       `(9)`

after changing the constant. This is `(R2)`, and (8) gives `Q(1)=0`.

Divide (9) by `b_(q_k)`. The right side tends to zero because `b_n/log n->infinity`. By (6), the left side tends in absolute value to

`|sum_r d_r lambda^r|=|Q(lambda)|`.

Thus `Q(lambda)=0`. Since `Q` is a nonzero integer Laurent polynomial, multiplying by a power of `T` gives a nonzero integer polynomial vanishing at `lambda`. Therefore `lambda` is algebraic. This proves `(R1)` and the theorem. `square`

The HT corollary is the contrapositive: a DA series with a ratio limit greater than one cannot have a transcendental limit. No phase condition entered the proof. `square`

## What the law says

1. **DA quantizes asymptotically geometric logarithmic decay.** A ratio limit greater than one cannot be an arbitrary real number; it must be algebraic.
2. **Algebraicity is only the first obstruction.** DA also forces a zero-mass Laurent relation whose shift defect is no larger than logarithmic size infinitely often.
3. **The law is phase-uniform.** It constrains the moduli of every DA realization, even with arbitrary complex phases and coefficient fields.
4. **The logarithmic scale is structural.** It is exactly the loss allowed by polynomially many integer-weighted ADE convolution atoms.
5. **No converse is claimed.** Algebraic `lambda` and a resonance such as (R2) do not imply DA.

## Boundary cases

- The theorem does not cover `lambda=1`; this contains theta, Valiron, and polynomial or stretched-exponential logarithmic profiles and is the central remaining regime.
- A pure algebraic geometric profile `b_n=A lambda^n` has many exact shift resonances and passes this necessary test, but may still be HT.
- Log-superlacunary profiles have ratio tending to infinity and are covered by the separate largest-index dominance theorem.
- Zero coefficients require a support-sensitive refinement and are left to support-gap theory.

## Exact RH-route scope

The transcendental-ratio corollary makes HT status constant across every phase fiber with the prescribed magnitude profile. Hence no RH implementation whose selector factors only through that HT bit, the limiting logarithmic ratio, or the associated magnitude/Newton data can recover phase-sensitive zero localization on the fiber.

This does not exclude complete Connes, Hilbert--Polya, de Branges, Nyman--Beurling, Weil, Li, or de Bruijn--Newman routes. It excludes only implementations that discard their route-specific spectral, norm, positivity, Euler-product, heat-flow, or divisor information and attempt to replace it by this coefficient-magnitude invariant.

## Parent and novelty status

- Mahler 1971 supplies integer normalization.
- Lipshitz--Rubel gap theory constrains support rather than full-support Archimedean magnitudes.
- Valiron--Wiman growth theory uses maximum terms and finite-jet asymptotics; no algebraicity law for a Taylor negative-log ratio limit was located there.
- Arithmetic coefficient theorems assume algebraic Taylor coefficients and prove denominator or non-Archimedean bounds; the present theorem allows arbitrary complex coefficients and deduces algebraicity of a real asymptotic ratio.
- Tropical differential algebra studies supports and local non-Archimedean orders, not the Archimedean valuation `-log|a_n|`.
- Exact searches for the statement, its ratio-limit formulation, and its integer-shift-resonance mechanism located no parent theorem. Scientific novelty remains provisional pending complete inspection of the Lipshitz--Rubel papers and specialist review.

## Lean status

No Lean formalization is claimed. Complete formalization requires Mahler normalization, generic coefficient extraction and balanced survival, the Archimedean bend estimate, ratio-limit asymptotics, and the finite pigeonhole argument. The theorem cannot enter stage 3 until all of it is formalized unconditionally.

## Gates

- [x] Exact necessary DA law stated.
- [x] Complete unconditional paper proof.
- [x] Transcendental-ratio phase-uniform HT corollary.
- [x] Significance gate: algebraicity and logarithmic resonance are forced from arbitrary-complex DA coefficient magnitudes.
- [ ] Complete parent-literature and rediscovery gates.
- [ ] Whole theorem formalized unconditionally in Lean.

## Log

- 2026-07-11 — Proved that a finite negative-log coefficient ratio limit greater than one is algebraic for every eventually full-support DA series, with a logarithmically accurate integer shift resonance along an infinite subsequence.
