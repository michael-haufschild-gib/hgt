# One damped all-prime Calkin Gram detects Xi orientation

- **ID:** `xi-prime-seam-summable-calkin-aggregate`
- **Stage:** 1-in-progress
- **Type:** CANDIDATE, `[TOP-DOWN]`, `[VALUE RELATION]`
- **Parents:** `sonin-prime-seam-exterior-factorization.md`;
  `summable-euler-calkin-injectivity.md`
- **Statement:** A canonical absolutely summable damping packages every prime-pair Xi seam
  coboundary into one norm-convergent Sonin Gram operator; compactness of that operator is
  equivalent to critical-line orientation on the fibre.

## Goal

Replace the family of pairwise compactness hypotheses in `XiPrimeSeamCalkinGram.lean` by one
concrete operator per Xi divisor fibre.  The reduction must be source-pure: it may use only the
literal prime Euler corners, canonical seam values, rapid nonzero damping, and Calkin compactness.
It must not assume the common seam charge vanishes.  Cofinal prime decay must force that vanishing
after injectivity has produced coherence.

The intended chain is

```text
compactness of one damped all-prime Gram on every Xi fibre
  -> every damped matrix coefficient vanishes
  -> all prime seam charges are coherent
  -> their common charge vanishes by cofinal decay
  -> Re(rho)=1/2 on every Xi fibre
  -> RH.
```

## Gates

- [x] 0 → 1 in-progress: well-posed, source-pure, finite injectivity and summability attack fixed
- [ ] 1 → 2 fully-proven: complete proof that rectangular partial sums recover every coefficient
- [ ] 2 → 3 formalized: Lean theorem, narrow build green, axiom audit clean, umbrellas wired
- [ ] 3 → 4 publication-ready: not sought; this is a proof-chain interface

## Approach

Enumerate the primes by `Nat.nth Nat.Prime`.  For a strip point `rho`, let

```text
a_i(rho) = orbitwiseNatPrimeSeamCharge (nth Prime i) rho,
d_i(rho) = 2^(-(i+1)) / (1 + |a_i(rho)|),
A_ij(rho) = d_i(rho)d_j(rho)(a_i(rho)-a_j(rho)).
```

Every `d_i` is positive, and

```text
|A_ij| <= 2 * 2^(-(i+1)) * 2^(-(j+1)),
```

so the double operator series converges absolutely in norm.  Prove an infinite extension of the
existing finite prime quadratic Calkin injectivity: if an absolutely summable matrix coefficient
family gives a compact norm-summed Gram operator, every coefficient is zero.  The proof takes
rectangular finite sections, applies the existing quantitative finite matrix-entry lower bound
against the compact full sum, and lets the rectangle exhaust `Nat × Nat`.

Since the damping never vanishes, compactness gives `a_i=a_j` for all indices.  The nth-prime
enumeration is onto the primes, so this is exactly `OrbitwisePrimeSeamChargesCoherent rho`.  The
already formalized coherence-collapse theorem kills the common charge and pins `Re rho=1/2`.

## Verification risks

- The infinite theorem is restricted to absolutely summable coefficients.  It does not claim
  injectivity for the raw divergent Euler ordering or conditionally regularized completed products.
- The damping is deliberately nonzero and fibre-dependent.  It preserves the zero set of every
  pair coefficient but does not pretend to be the undamped completed Euler curvature.
- Compactness of the aggregate remains the source-side target.  The contribution is that it is one
  concrete norm-convergent target, not an uncountable or pairwise family of interfaces.

## Log

- 2026-07-13 — created in progress after the repaired summable one-prime injectivity exposed the
  missing two-prime infinite-matrix extension.
