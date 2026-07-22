# Positive progression projector rigidity law

- **ID:** `PROGRESSION-POS-RIGID-001`
- **Stage:** 2-fully-proven / needs-audit
- **Type:** THEOREM (paper), Lean connector pending
- **Status:** `[PROVED HERE] [UNIVERSAL CLASSIFICATION] [CANDIDATE NEW APPLICATION] [NOVELTY UNVERIFIED] [NOT RH]`
- **Source:** failed attempted extension of `PARITY-RAW-001` from modulus `2` to arbitrary modulus
- **Statement:** Divisibility projection of a Hermitian additive convolution is nonnegative for every complex coefficient sequence exactly for moduli `1` and `2`.

## Goal

Determine whether the parity-positive Hermitian projector can be extended to additive totals
divisible by an arbitrary modulus. This is the natural route to progression-localized Möbius and
Liouville sign recurrence. The answer is an exact rigidity law: parity is the only nontrivial
universally positive divisibility projector.

## Theorem

Let `q >= 1`. For a finite complex sequence `a = (a_n)_{n>=1}`, put

```text
A(z) = sum_{n>=1} a_n z^n,
H_a(N) = sum_{m+n=N} a_m conjugate(a_n),
P_{q,a}(r) = sum_{q | N} H_a(N) r^N       (r > 0).
```

Then the following are equivalent:

1. `P_{q,a}(r) >= 0` for every finite complex sequence `a` and every real `r > 0`;
2. `q = 1` or `q = 2`.

For `q = 1`,

```text
P_{1,a}(r) = |A(r)|^2.
```

For `q = 2`,

```text
P_{2,a}(r) = (|A(r)|^2 + |A(-r)|^2) / 2.
```

For every `q >= 3`, the two-point polynomial

```text
A_q(z) = z - z^(q-1)
```

is an exact negative witness:

```text
P_{q,a_q}(r) = -2 r^q < 0.
```

## Proof

For `q = 1`, the full Hermitian Cauchy product is `A(r) conjugate(A(r))`.

For `q = 2`, the order-two character projector gives

```text
P_{2,a}(r)
  = (A(r) conjugate(A(r)) + A(-r) conjugate(A(-r))) / 2,
```

which is nonnegative.

Now assume `q >= 3` and choose `a_1 = 1`, `a_{q-1} = -1`, with all other coefficients zero.
The only possible output degrees of the Hermitian Cauchy product are

```text
2, q, 2q-2.
```

Because `q >= 3`, neither `2` nor `2q-2` is divisible by `q`. The coefficient at degree `q` is

```text
a_1 conjugate(a_{q-1}) + a_{q-1} conjugate(a_1) = -2.
```

Therefore the complete divisibility projection is exactly `-2 r^q`, proving failure for every
`q >= 3`. This proves the equivalence.

## Why the naive cyclotomic argument fails

Let `zeta_q` be a primitive `q`-th root of unity. The ordinary root-of-unity filter does extract
coefficients with output degree divisible by `q`, but its summands are

```text
A(zeta_q^j r) * conjugate_coeff_series(zeta_q^j r),
```

not `|A(zeta_q^j r)|^2`. Complex conjugation changes `zeta_q^j` into `zeta_q^(-j)`. These coincide
for every character value only at order `2`. Averaging actual squared norms instead selects pairs
whose two indices are congruent modulo `q`; it does not select additive totals divisible by `q`.

## No-go closure

- **Exact killing mechanism:** Hermitian conjugation reverses the cyclotomic phase. Additive-total
  projection is a Gram average only when every phase used is self-conjugate, yielding the
  nontrivial case `q=2`.
- **Strongest positive survivor:** complete classification above, with an exact two-monomial
  counterexample for every `q>=3`.
- **New insight:** even-index Möbius/Liouville recurrence is structurally maximal among universal
  divisibility-progression consequences. Any finer progression theorem must use arithmetic input
  beyond Hermitian positivity.
- **Status:** dependency-closed paper proof; corpus and targeted primary-literature searches found
  no prior application to Möbius/Liouville additive sign recurrence; specialist priority audit
  remains required.

## Corpus and literature collision audit

- Repository search found the order-two projector and unrelated root-of-unity machinery, but no
  classification of positive divisibility projectors.
- Mangerel's final 2024 theorem proves strict nonmaximality of the Liouville binary convolution
  for every `N>=11`; it does not supply this projector classification or positive recurrence.
- Cantarini--Gambini--Zaccagnini (2026) study weighted convolution formulae; targeted exact-term
  searches found no matching rigidity theorem.
- Root-of-unity filtering itself is standard. Candidate novelty is the universal-positivity
  classification and its role as the sharp boundary of the Möbius/Liouville recurrence law, not
  the filtering identity.

## Gates

- [x] well-posed source-pure theorem
- [x] exact dependency-closed paper proof
- [x] strongest positive survivor extracted from failed route
- [x] repository collision audit
- [x] targeted primary-literature search
- [ ] specialist / MathSciNet / zbMATH priority audit
- [ ] exact Lean witness and positive endpoint connector
- [ ] publication-ready integration
- [ ] recognized major open problem solved
- [ ] RH

## Log

- 2026-07-22 — conjectured arbitrary-modulus positive projection from the parity law.
- 2026-07-22 — falsified it by phase-conjugation audit; extracted and proved exact `q=1,2`
  classification with witness `z-z^(q-1)` for every `q>=3`.
