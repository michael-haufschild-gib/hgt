# Prime-power dilation tail differential matroid

- **ID:** `prime-power-dilation-tail-differential-matroid`
- **Stage:** 1-in-progress
- **Type:** CONJECTURE / `[CONJECTURE]` / `[NOVELTY UNVERIFIED]`
- **Parent:** `finite-alphabet-prime-dirichlet-complete-relation-law.md`
- **Statement:** For a finite-range prime coefficient family, every finite collection of dilated
  translates `P_b(r s + a)` has exact differential rank equal to the source tail rank times the
  number of dilation--shift blocks; no cross-dilation relation occurs.

## Goal

Classify the complete finite prime-power layer geometry rather than stopping at the first-prime
layer.  If the statement survives proof and priority audit, the all-positive source gives a new
positive constraint on the zeta reconstruction: each finite collection of dilation layers is
differentially free in the derivative--translation category, while `log zeta` couples the entire
countable tower through an infinitary weighted sum.

## Gates

- [x] 0 -> 1 in-progress: exact finite statement, converse, determinant coefficient, and analytic
  boundary isolated
- [ ] 1 -> 2 fully-proven: block determinant and dynamic finite-prime coefficient proof complete
- [ ] 2 -> 3 formalized: power-supported derivation law, nonzero convolution determinant,
  finite-prime Jacobian transfer, analytic dilation carrier, and countable finite-character
  corollary verified
- [ ] 3 -> 4 publication-ready: definitive literature audit and inclusion in a new stronger paper

## Conjecture

`[CONJECTURE]` Let `R` be a finite nonempty set of positive integers.  For every `r in R`, let
`A_r` be a finite nonempty set of shifts with pairwise distinct real parts.  Let
`b_j : Primes -> C` have finite joint range and tail span dimension `rho`.  Then

```text
dtrdeg E_fin < P_bj(r s + a) : j, r in R, a in A_r >
  = rho * sum_r card(A_r).
```

The complete relation ideal is the direct sum, over `(r,a)`, of the source-tail linear relation
ideal.  In particular a tail-independent source family makes every finite dilation--translate
palette differentially algebraically independent.

## Approach

1. The `k`th derivative of `P_b(r s+a)` is supported at `p^r` with prime coefficient
   `b(p) p^(-a) (-r log p)^k`.
2. For the prime derivation at `q`, a power-supported column satisfies
   `partial_q f = r b(q) e_(q^(r-1))`.
3. Choose disjoint full-rank prime packets separately in each dilation block, avoiding the finite
   prime activity of a putative coefficient relation.
4. In the convolution Jacobian determinant inspect the coefficient at
   `N0 = product q_(r,l)^(r-1)`.  Unique factorization forces contributing permutations to
   preserve every dilation block, so the coefficient factors as a nonzero scalar times the
   product of the packet determinants.
5. Use a determinant-nonzero Jacobian criterion in the fraction field, then the existing dynamic
   common-kernel lift to pass over the entire finite-prime coefficient field.
6. Transfer the power-supported arithmetic functions to absolutely convergent Dirichlet series
   and take finite character for the countable dilation tower.

## Verified core

The full-rank valuation-layer theorem is complete and formalized in
`prime-power-valuation-layer-block-separation.md`.  It proves, for arbitrary finite nonuniform
layer alphabets `A_r`, that layerwise tail independence gives algebraic independence of the full
`sum_r card(A_r)` family over the intrinsic finite-prime coefficient field.  It also proves the
exact distinguished determinant coefficient, the power-supported prime-derivation law, globally
prime-disjoint cofinite packet selection, and the dynamic common-kernel transfer.  The analytic
bridge is now also complete: a power-supported carrier is exactly the corresponding integral
argument dilation of its prime Dirichlet series, the all-order chain factor is `(r+1)^k`, and every
finite nonuniform Boolean orientation--shift--jet tower is algebraically independent as actual
upper-end analytic germs.

What remains on this card is strictly the rank-deficient strengthening: identify the complete
relation ideal and exact rank when the source tail rank is smaller than the displayed alphabet.

## Failure tests

- The row-prime packets must be globally disjoint; otherwise unique factorization does not isolate
  the intended determinant coefficient.
- The `r=1` block contributes exponent zero.  Block preservation still follows after all
  `r>1` assignments are forced, but this boundary must be proved explicitly.
- Distinct real parts are needed within each fixed dilation block.  No claim is made for equal-real
  oscillatory shifts.
- The theorem concerns differential-algebraic relations under derivatives and translations.  It
  does not assert closure under dilation or countable summation.

## Log

- 2026-07-15 -- the full-rank arithmetic and analytic theorems are formalized; only the
  rank-deficient complete relation classification remains open on this card.
