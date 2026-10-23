# Twin primes: a signed sum at the cubic roughness threshold

- **ID:** twin-prime-signed-cubic-roughness
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** `twin-prime-unconditional-programme-2026-10-23.md`
- **Statement:** There exist `c>0` and `N₀` such that for every integer
  `N≥N₀`, the prime-weighted Möbius sum defined below is at most
  `-c N/log N`.

## Exact candidate

For `N≥2`, let `z_N` be the least natural number whose cube is at least
`2N+2`. Put

`R(N) = Σ_{N<p≤2N, p prime, P⁻(p+2)>z_N} (log p) μ(p+2)`.

The candidate is `R(N) ≤ -c N/log N` for all sufficiently large `N`.
This asserts a negative mean on an explicitly sifted arithmetic sequence;
it is stronger than infinitude and can fail even if twin primes are infinite.
No instance, numerical evidence, or new proof of this estimate is claimed.

## Why this would suffice: exact finite algebra

Every integer `m≤2N+2` with all prime factors greater than `z_N` has at most
two prime factors counted with multiplicity. Otherwise three such factors
would give `m>z_N³≥2N+2`. Thus `m>1` is a prime, a prime square, or a product
of two distinct primes. Their Möbius values are respectively `-1,0,+1`.

Also `z_N≤N` for `N≥2`: `N³≥2N+2` follows from
`N³≥4N≥2N+2`. Consequently every twin pair with `N<p≤2N` survives the cutoff.
It follows exactly that

`R(N) = S₂(N) - T(N)`,

where `T(N)=Σ_{N<p≤2N, p and p+2 prime} log p` and `S₂(N)` is the same
weighted sum over distinct-semiprime shifts with both factors greater than
`z_N`. Since `S₂(N)≥0`, the conjectured negative bound forces
`T(N)≥c N/log N`, and hence infinitely many twin primes.

This local classification is elementary. It is a diagnostic reduction,
not the missing analytic theorem, and is not an assumption to add to Lean.

## Attack and audit

**Verdict: BRIDGE.** The statement isolates a sufficient parity-sensitive
estimate. No novelty beyond the classical asymptotic-sieve programme has
been established. The finite classification alone does not pass the
scientific-novelty gate.

### Internal evidence

Queries: `Mobius function on shifted primes arithmetic progressions level
distribution`; `signed Mobius rough shifted prime semiprime cubic least
prime factor`.

- `RHTower.Sieve.roughPairSieve` and `siftedSum_roughPairSieve` encode
  two-dimensional rough-pair sieving. Inspected definitions and equality;
  neither provides a signed lower bound at this cutoff.
- `BezoutValuationIncidence.eventually_abs_sum_class_moebius_log_le`
  is cancellation of Möbius over all integers in one fixed prime-modulus
  residue class. Inspected statement and proof mechanism. It does not
  restrict to shifted primes or supply uniformity in growing moduli.
- `TwinPrime.twinMass_eq_signed_residual_difference` preserves the exact
  sign deficit but does not estimate it.

### External evidence

- [Lü–Wang–Wu, 2026, Theorem 1 and §5.3](https://arxiv.org/html/2610.20242v1):
  claims unrestricted shifted-prime cancellation. The final averaging
  argument fixes all auxiliary intervals before the large-scale limit.
  Its nonempty small-prime marks vanish on the sifted set used here.
- [Guo, 2026, author statement of Theorem 1.1](https://raw.githubusercontent.com/aster2024/openai-math-followups/main/rough-pairs-fixed-distance/README.md):
  claims Liouville sign equidistribution for pairs with sieve cutoff at
  most `exp((log X)^(1/3750))`. The factor-count conclusion grows with `X`;
  the author explicitly excludes a statement for primes or fixed factor
  count. Statement and dependency list checked; full proof not audited.
  This subpolynomial cutoff does not reach the cubic cutoff above.
- [Tao's asymptotic-sieve discussion](https://terrytao.wordpress.com/tag/parity-problem/):
  identifies rough Möbius correlations as parity-sensitive quantities
  and explains the loss of small-prime multiplicativity. Its conditional
  discussion supplies neither the present bound nor an unconditional input.

### Attempts that do not close the estimate

1. Unrestricted cancellation is at the wrong restriction and error scale.
   Subtracting the nonsifted contribution requires estimating that
   contribution with its arithmetic signs; it cannot be discarded.
2. The existing nonempty-divisor marks vanish on this entire sifted set.
   Averaging more such marks leaves the restriction zero.
3. Inclusion-exclusion gives the exact expansion

   `R(N)=Σ_{d|Q(z_N)} μ(d) Σ_{N<p≤2N, p prime, d|p+2} log p μ(p+2)`,

   where `Q(z)` is the product of primes at most `z`. The identity follows
   by expanding `Π_{q|Q(z)}(1-1_{q|p+2})`. Fixed-modulus estimates do not
   control the full sum: moduli grow, and absolute summation loses the
   sign whose bias is the target.
4. Calling `S₂(N)` an easier term does not prove its size. In factor
   coordinates it requires the simultaneous primality of `q`, `r`, and
   `qr-2`, together with the moving cutoff and interval endpoints.

**[OPEN CORE]** Prove a one-sided signed estimate for the displayed
divisor/progression expansion strong enough to make `R(N)` negative by
order `N/log N`. No available bound has been shown to do this.

## Next research action

The direct rough-dilation transfer is
[closed at its stated scope](../5-failed/twin-prime-direct-rough-dilation-transfer.md).
Its positive survivor, the exact cubic dilation classification, is
[formalized](../3-formalized/twin-prime-cubic-dilation-classification.md).
This leaves the signed estimate open.

The next analytic attack is
[centered distribution at the root residue](twin-prime-centered-root-distribution.md).
It retains the mixed modulus constraint instead of trying to move the
rough cutoff through an incompatible label supply.

## Log

- 2026-10-23 — Exact candidate, finite reduction, literature scope, and
  failed transfer attempts recorded. Analytic estimate and twin-prime
  infinitude remain open. No conditional Lean theorem added.
- 2026-10-23 — Inspected the rough graph's label supply, physical scale,
  masked moment, and dilation identity. Polynomial cutoff cannot be
  substituted into those parameters. Prime-product and twin-dilation
  classifications passed Lean and axiom audits. Shifted-prime determinant
  restriction and the centered distribution target remain analytic gaps.
