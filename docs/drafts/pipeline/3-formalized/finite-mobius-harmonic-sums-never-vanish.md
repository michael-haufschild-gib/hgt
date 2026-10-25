# Finite Möbius harmonic sums never vanish

- **ID:** finite-mobius-harmonic-sums-never-vanish
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** vaughan-finite-cutoff-receiver-normal-form.md
- **Statement:** Every positive finite Möbius harmonic sum is nonzero; every prime in the terminal half-interval occurs exactly once in its reduced denominator.
- **Novelty status:** Elementary denominator argument; no external novelty claim. Two corpus searches found harmonic decay and floor identities, but not this finite nonvanishing statement.

## Exact statement

Let `H_N=Σ_(1≤n≤N) μ(n)/n ∈ ℚ`. For `N≥1`, `H_N≠0`.
More precisely, if `p` is prime and `N/2<p≤N`, then `v_p(H_N)=-1`.
Consequently each such prime divides the reduced denominator of `H_N`, and its square
does not divide that denominator. The product of all these distinct terminal primes
divides the denominator.

## Dependency-closed proof

For `N=1`, the unique term is `1`. For `N≥2`, the existing
`exists_mem_sievePrimeTail` in `GlobalRenormalizedDefectSignAtLargeHorizons.lean`
supplies a prime `p` with `N/2<p≤N`, by Bertrand's theorem applied to `floor(N/2)`.

Fix any such `p`. The only multiple of `p` among `1,…,N` is `p` itself. Put `D=N!`.
The integer `D` therefore has `p`-adic valuation exactly one. Multiplying the rational
sum by `D` gives the integer

`S=Σ_(1≤n≤N) μ(n)(D/n)`.

For `n≠p`, the integer `n` is prime to `p`, hence `p | D/n`. For `n=p`, the quotient
`D/p` is not divisible by `p`, and `μ(p)=-1`. Thus

`S ≡ -D/p ≠ 0 (mod p)`.

Hence `S≠0`, `p∤S`, and `v_p(S/D)=-1`. Reducing the fraction cancels no factor `p`.
Repeating for every terminal prime and using their pairwise coprimality gives the
denominator product law. The argument also gives a reusable variant for arbitrary
integer coefficients `a(n)` when the coefficient `a(p)` is not divisible by `p`.

## Vaughan consequence

For positive fixed cutoffs `U,V`, the harmonic factors in the smooth-power term obey
`H_U H_V≠0`. Since `subHalfZetaCoeff ε<0` for `0<ε<1`, the scalar condition

`subHalfZetaCoeff ε * H_U * H_V * (w_3-w_2)=0`

is equivalent to `w_3=w_2`. Thus, in the proposed fixed-cutoff receiver normal form,
removing the smooth-power direction forces equal coefficients on the small-small and
both-large pieces. This is a finite-cutoff rigidity law. It supplies no uniform lower
bound of polynomial size for `H_N`, and no fixed power saving at moving cutoffs.

## Lean status

The exact declarations include `moebiusHarmonicPartialRat_ne_zero`,
`padicNorm_moebiusHarmonicPartialRat`, `padicValRat_moebiusHarmonicPartialRat`,
`padicValNat_den_moebiusHarmonicPartialRat`,
`terminal_prime_dvd_den_moebiusHarmonicPartialRat`,
`prod_terminal_primes_dvd_den_moebiusHarmonicPartialRat`, and `sum_moebius_div_ne_zero`.

The complete proof is in `formal/GaloisForLFunctions/RHTower/FiniteMobiusHarmonicSumsNeverVanish.lean`.
It uses the equivalent
p-adic norm argument: the terminal-prime summand has norm `p`, all other summands have
norm at most one, and the nonarchimedean inequality fixes the full norm at `p`.
The draft includes nonvanishing, valuation minus one, exact denominator exponent,
the product-divisibility law, and the real-valued nonvanishing corollary.
The corrected scratch check passed all eight public theorem audits, using only
`propext`, `Classical.choice`, and `Quot.sound`. The checked source is copied into the
repository leaf and wired into the RHTower umbrella. Its olean is required by the
residual Vaughan classification; its producing check passed. The final direct no-olean
check passed. No umbrella was compiled.
The full Q-I problem remains open.

## Log

- 2026-10-25 — Extracted finite nonvanishing from the smooth-power coefficient condition.
