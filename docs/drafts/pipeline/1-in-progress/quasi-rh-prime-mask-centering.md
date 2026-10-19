# Prime-mask calibration and a cube-root Gram block

- **ID:** quasi-rh-prime-mask-centering
- **Stage:** 1-in-progress
- **Type:** CONJECTURE, with a closed finite arithmetic optimization
- **Source:** [Fixed-strip task](quasi-rh-fixed-strip-improvement.md)
- **Statement:** Realize a mean-preserving prime-mask average inside the exceptional detector source, and estimate its nonexceptional blocks before absolute summation.

## Mechanism and first tests

The cached upstream `Mellin/SixthPowerAverage.lean:161` identifies the sixth-power row as a weighted coprimality sum. `MeanSquare/ThetaDensity.lean:542` separates its totient-density main term and literal remainder. This motivates changing the detector's coefficients, rather than assuming cancellation from the Möbius inversion already encoding coprimality.

Deleting all exceptional Poisson frequencies is not yet an orthogonal projection on the physical detector. No factorization or principal-signal preservation has been established. Merely subtracting the scalar mean is also insufficient: a prime coprimality mask has variance `(p−1)/p²`, which remains positive after centering.

## Closed paper result: optimal calibrated prime packet

For a nonempty finite set S of primes, put

`A = Σ_{p∈S}(p−1)`, `m(c)=Σ c_p(1−1/p)`,
`V(c)=Σ_{p,q∈S} c_p c_q [ρ(pq)−ρ(p)ρ(q)]`, where `ρ(n)=φ(n)/n`.

CRT gives `V(c)=Σ c_p²(p−1)/p²`. Completing the square gives the exact identity

`V(c) = m(c)²/A + Σ_{p∈S} (p−1)(c_p/p−m(c)/A)²`.

Indeed, expansion yields `V(c)−2m(c)²/A+m(c)²A/A²` on the right of the residual sum. Every weight `p−1` is positive. Thus at mean one, the unique minimizing coefficients are `c_p=p/A`, and the variance is exactly `1/A`. This also gives a stability identity, not just an upper bound.

The literal mask `F_S(n)=Σ p·1[p∤n]/A` has mean one and centered variance `1/A` on a complete CRT period. `QuasiRHCalibratedPrimeMasks.lean` proves the optimization, uniqueness, stability identity, coefficient mass, and corresponding right-radial Dirichlet-series square-density conclusion using the native covariance receiver.

The coefficient mass is `Σ c_p = 1+|S|/A`. For primes at least R>1, `A≥|S|(R−1)`, so the variance is at most `1/(|S|(R−1))` and the coefficient mass at most `1+1/(R−1)`. These finite inequalities require no prime-counting hypothesis.

## Closed paper result: uniform finite-prefix square bound

Write `K=|S|`, `W(n)=Σ_{p∈S} p·1[p∣n]`, and `B=K/A`. Then `F_S(n)−1=(K−W(n))/A`. Exact counting of multiples gives

`Σ_{1≤n≤N} W(n) = Σ_p p⌊N/p⌋ ≥ NK−Σ_p p = NK−A−K`,

`Σ_{1≤n≤N} W(n)² = Σ_{p,q} pq⌊N/lcm(p,q)⌋ ≤ N(A+K²)`.

For the second inequality, distinct primes contribute `pq/lcm(p,q)=1`, while each diagonal contributes `p`; hence the double sum is `K²+Σ(p−1)`. Expanding `(K−W)²`, using the lower bound on the linear term with its negative coefficient, and dividing by `A²` yields

`Σ_{1≤n≤N} (F_S(n)−1)² ≤ N/A + 2B(1+B) ≤ N/A + 4`.

The last step uses `A≥K`, since every prime is at least two. The estimate holds for every natural N and every nonempty finite prime set, uniformly when the prime set moves with N. It requires no complete CRT period. This closes the rational-mask finite-prefix estimate on paper; it does not yet identify the detector's weighted Eisenstein remainder with this mask.

## Detector conjecture: arithmetic realization

Choose auxiliary prime ideals in one dyadic range, with the fixed calibration removed and coefficients proportional to their norms. Conjecture: the resulting linear combination of detector rows admits an exact principal-plus-centered decomposition whose exceptional **remainder** is governed by the prime-mask variance, while its principal residue stays nonzero. The construction must be made at the source level; multiplying an arbitrary existing row by a nearly constant mask does not reduce that row's variance.

This is open. The prime-mask calculation concerns rational primes. Transport to Eisenstein prime ideals, the detector's weighted physical window, the actual character weights, and the principal Mellin residue are separate proof obligations. New auxiliary primes also consume conductor/slot budget. No saving is counted until these costs are included.

## Nonexceptional conjecture: keep the bilinear block intact

Normalize a `canonicalLatticeBlock` by its existing fixed-modulus, common-ideal and Schwartz factors. If q is the norm of its arithmetic modulus and N its residual lattice scale, seek

`|block| ≪ε N² min(1,q^(1/3+ε)/N)`

together with the existing rapid decay in the radial frequency variable. The conjecture is for the literal structured character block, not every bounded periodic zero-mean function. The first tests are prime conductor, distinct local characters, and common-support degeneracies.

Propagating this particular bound through the frequency and ideal sums changes their threshold from `CD≈Y/P` to `CD≈Y/P^(1/3)`. The ideal sum at exponent one costs logarithms, absorbable in ε; the resulting nonexceptional term is `P^(4/3+ε)/Y`. Combined with an exceptional remainder of subpower size, the five-sixths budget is met at `(x,y,L)=(1/6,2/3,1/6)`.

The existing `HyperKloostermanFactoredModuliBilinear.norm_sq_factored_moduli_le` supplies a reusable proof pattern: retain one arithmetic sum inside Cauchy–Schwarz, split diagonal/off-diagonal pairs, complete the latter modulo the product modulus, and estimate complete correlations. It applies to `Kl₃` over rational moduli `p s²`; it is **not** already a bound for this sextic Eisenstein block. `large_sieve_gamma0_cubic` is a spectral sieve with a cubic height weight, not a cubic-character large sieve.

## Three-quarters requirement

Even both conjectures above do not overcome the retained reflected allowance. With a unit-sized exceptional term and `P^(4/3)/Y`, the nominal budget without reflected loss reaches three quarters at `(x,y,L)=(1/12,1/3,7/12)`. The present reflected allowance there is `1/2` in energy, adding `1/4` after the square root. A three-quarters construction must remove that cost on the actual reflected source or supply a different source normalization. The conjectural prime-mask centering must therefore be tested on the zero-retained-length reflected face, not only on the low Gram term.

## Gates and exact next steps

- [x] Derive the calibrated finite-prime optimizer and its stability identity on paper.
- [x] Formalize the exact optimization and literal radial square-density conclusion.
- [x] Prove the rational-mask finite-prefix estimate on paper, uniformly in the moving prime set.
- [ ] Formalize that finite-prefix estimate.
- [ ] Identify an admissible physical detector with these calibrated coefficients and a nonzero principal residue.
- [ ] Transfer the finite-prefix estimate to the detector's weighted Eisenstein remainder.
- [ ] Expand the actual nonexceptional block's complete off-diagonal correlation; check whether the factored-modulus proof pattern applies.
- [ ] Pay every conductor, slot, and reflected-source cost before claiming either improved strip.

The arithmetic realization and cube-root block estimate are conjectures. The finite optimization is elementary supporting mathematics; external novelty is unclaimed.
