# The complete affine squarefree-projection error

- **ID:** twin-prime-affine-squarefree-transfer
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) / BRIDGE
- **Source:** [growing affine cancellation](../2-fully-proven/twin-prime-polylogarithmic-affine-cancellation.md).
- **Statement:** The actual two-Möbius correlation differs from its finite square-divisor Liouville expansion by an explicit uniform error, with no cancellation premise.

## Exact objects and theorem

A reduced primitive affine row is `F(t)=at+b`, with positive integer
`a`, `0<=b<a`, and `gcd(a,b)=1`. These conditions define its arithmetic
domain; none asserts cancellation. For two such rows `F,G`, natural
`T` and positive integer cutoffs `R,S`, define

```text
C_mu(T) = sum_(1<=t<=T) mu(F(t)) mu(G(t)),
C_lambda(T;R,S) = sum_(1<=d<=R,1<=e<=S) mu(d)mu(e)
                   sum_(1<=t<=T,d^2|F(t),e^2|G(t))
                     lambda(F(t))lambda(G(t)).
```

The unconditional finite estimate is

```text
|C_mu(T)-C_lambda(T;R,S)|
 <= T/R + floor(sqrt(F(T)))
      + R [T/S + floor(sqrt(G(T)))].                 (1)
```

In particular, taking `S=R^2` gives

```text
|C_mu(T)-C_lambda(T;R,R^2)|
 <= 2T/R + floor(sqrt(F(T))) + R floor(sqrt(G(T))).   (2)
```

The right side contains no unproved analytic input. The retained
Liouville sum is an explicit finite expression, not an assumed bound.
Its later cancellation must itself be proved in Lean before the
paper correlation theorem can be claimed as formalized.

## Complete paper proof

For positive `n`, unique factorization gives

`mu(n)=lambda(n) sum_(d^2|n) mu(d)`.

Indeed the square-divisor sum is the product of `1-1` over primes
whose square divides `n`, hence is the squarefree indicator. On
squarefree integers Liouville and Möbius agree. Let

`A_R(n)=lambda(n) sum_(1<=d<=R,d^2|n) mu(d)`.

Consequently `|A_R(n)|<=R` and

`|mu(n)-A_R(n)|<=#{d: R<d<=floor(sqrt(n)), d^2|n}`.   (3)

For a primitive affine row, a divisor `d^2` either shares a prime
with the slope and divides no row value, or is coprime to the slope
and selects a single residue class of `t mod d^2`. In the interval
`1<=t<=T`, this class has at most `T/d^2+1` points. An elementary
proof sends each selected `t` to `floor(t/d^2)`: equality of that
quotient and the common residue forces equality of `t`, and the
quotients lie between zero and `floor(T/d^2)`.

Since `F(t)<=F(T)`, summing (3), interchanging finite sums and
using that count gives

`sum_(t<=T) |mu(F(t))-A_R(F(t))|
 <= T sum_(R<d<=floor(sqrt(F(T)))) 1/d^2
      + floor(sqrt(F(T)))
 <= T/R + floor(sqrt(F(T)))`.                       (4)

For the last inequality, `d>=R+1>=2` gives
`1/d^2<=1/(d-1)-1/d`; the sum telescopes to at most `1/R`.
Empty ranges satisfy the same bound.

Use the exact decomposition

```text
mu(F)mu(G)-A_R(F)A_S(G)
 = [mu(F)-A_R(F)]mu(G) + A_R(F)[mu(G)-A_S(G)].
```

Triangle inequality, `|mu(G)|<=1`, `|A_R(F)|<=R`, and (4)
for each row prove (1). Expanding the two finite sums identifies
their product with `C_lambda(T;R,S)`. Substitution `S=R^2`
and positivity of `R` prove (2). This includes `T=0`.

## Dependency and scientific status

This is the elementary squarefree-projection step used in the
source's quantitative transfer. Verdict **BRIDGE**; no new
number-theoretic cancellation or scientific novelty is claimed.
The exact finite bound is now formalized. Continue with the
short Fourier, finite-law and graph inputs listed on the parent
card, together with the determinant-sensitive refinement. No analytic hypothesis may be added
to this theorem or its eventual application.

## Gates

- [x] Exact unconditional finite statement and closed paper proof.
- [x] Reuse audited corpus/mathlib arithmetic identities.
- [x] Lean finite squarefree identity, progression count and tail bound.
- [x] Lean two-row error estimate and asymmetric-cutoff specialization.
- [x] Foreground leaf audit, transitive axiom audit and umbrella wiring.

## Log

- 2026-10-23 — Began formalizing the pending paper result after
  the user's explicit instruction to discharge every input in Lean.
  The parent analytic estimate and twin-prime infinitude remain open
  as Lean proofs.

## Lean certificate

Module: `formal/GaloisForLFunctions/twin-prime/AffineSquarefreeTransfer.lean`.
Namespace: `TwinPrime.AffineSquarefree`.

- `moebius_sub_approx`: exact signed square-divisor tail.
- `Row.card_dvd_le`: primitive affine residue count.
- `sum_abs_moebius_sub_approx_le`: full one-row error.
- `sum_approx_mul_eq`: identification with the explicit Liouville sum.
- `abs_correlation_sub_le`: inequality (1).
- `abs_correlation_sub_square_cutoff_le`: inequality (2).

Foreground audit:
`lake --old env lean GaloisForLFunctions/twin-prime/AffineSquarefreeTransfer.lean`
exited 0 without warnings. All six transitive axiom audits returned
only `propext`, `Classical.choice`, and `Quot.sound`. Audit directives
were removed. The module is imported by `twin-prime/Main.lean`;
no umbrella build was run.

- 2026-10-24 — Completed the finite transfer and its dependency
  audit. The larger cancellation statement and twin-prime
  infinitude remain unproved in Lean.
