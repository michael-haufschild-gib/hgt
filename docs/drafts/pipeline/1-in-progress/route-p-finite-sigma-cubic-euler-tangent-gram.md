# Route P finite-sigma cubic Euler tangent Gram

- **ID:** `route-p-finite-sigma-cubic-euler-tangent-gram`
- **Label:** P-G170
- **Stage:** 1-in-progress
- **Type:** OWN CONJECTURE / SOURCE-TANGENT IDENTIFICATION
- **RH status:** open
- **Computation used:** no
- **Lean target:**
  `formal/GaloisForLFunctions/RHTower/RoutePFiniteSigmaCubicEulerTangentGram.lean`

## Conjecture

Let `t=R(sigma-1)` and let `h_sigma,a` be P-G169's literal full-Euler column at projective node
`u_R(a)=R*a-1/2`. Coordinatewise it is the normalized critical carrier

```text
h_sigma,a(n) = n^(-1/2-t*a) / sqrt(zeta(sigma)).
```

Therefore the depth derivative of P-G168's half-weighted packet is the actual Euler-source vector

```text
T_sigma,a = sqrt(R) * t * log(n) * (h_sigma,2a(n)-h_sigma,a(n)).
```

Construct this vector in `EulerPositiveL2`, prove it is the coordinatewise derivative of the
half-weighted packet, and compute its exact Gram. For one unpolarized pair the Gram term is

```text
R*t^2 * zeta(1+t(a+b))/zeta(sigma) * M_2(1+t(a+b)),
```

where `M_2` is the full-Euler normalized second log moment. Prove its critical limit is
`2/(a+b)^3`. The four polarized terms must then converge to
`cubicLogMomentHellingerHorizontalKernel(a,b)`.

## Why this is new

P-G168 proves the cubic kernel is a mixed derivative of the limiting abstract Hardy overlap.
P-G169 proves that overlap is the limit of actual full-Euler columns. Neither constructs the
finite-`sigma` derivative vector or proves that differentiation survives as an exact source Gram.
P-G170 does: cubic log-moment weighting is forced by the source tangent before divisor
specialization.

## Hostile checks

1. Log-weighted columns must be square summable for every `sigma,R,a>0`; no formal derivative of an
   unproved `L2` path may be used.
2. The `1/2` packet coefficient and doubled-node chain rule must cancel exactly, leaving
   `log(n)(h_2a-h_a)`.
3. The Gram limit must combine both pole laws: first-order zeta-overlap residue and second-order
   normalized log-moment residue. Importing the limiting kernel by definition earns no credit.
4. Actual Hilbert inner product must equal the four finite-`sigma` arithmetic terms before any
   limit is taken.
5. This closes horizontal source formation, not ordinate localization or Euler--Gamma trace budget.

## Conjecture loop

- **C1:** differentiate only the limiting Hardy kernel. **Insufficient:** P-G168 already does this;
  it supplies no finite-`sigma` arithmetic source.
- **C2:** use finite differences of source columns without a source tangent. **Insufficient:** the
  cubic log moment is invisible until the exact depth derivative inserts `log n`.
- **C3:** build the log-weighted derivative column directly in `EulerPositiveL2`, compute its Gram,
  then take the residue-controlled critical limit. **Selected.**

## Closed result

Lean constructs the log-weighted projective column in `EulerPositiveL2`, proves the literal
projective column's coordinate derivative, and proves the doubled-node chain rule turns the
half-weighted packet derivative into

```text
sqrt(R) * R*(sigma-1) * log(n) * (h_sigma,2a(n)-h_sigma,a(n)).
```

The Hilbert vector has exactly this coordinate weight. Its inner product is exactly the four-term
finite-`sigma` arithmetic Gram assembled from normalized zeta overlaps and normalized second Euler
log moments. Each unpolarized term converges to `2/(a+b)^3`; their polarization converges to
`cubicLogMomentHellingerHorizontalKernel(a,b)`.

This closes the missing source-tangent interchange: P-G168's cubic mixed jet is not merely a
derivative of a post-limit kernel. It is the critical limit of a genuine pre-limit Euler Hilbert
Gram whose `log n` insertion is forced by differentiation. Remaining obstruction is vertical
ordinate localization plus completed Euler--Gamma trace control.

Scratch compilation produced
`/tmp/routep-snapshot/GaloisForLFunctions/RHTower/RoutePFiniteSigmaCubicEulerTangentGram.olean`.
All capstones depend only on `propext`, `Classical.choice`, and `Quot.sound`; targeted forbidden
scan is clean. Umbrella import was verified present; umbrella was not compiled by this work.

## Gates

- [x] corpus collision and dead-route audit
- [x] Lean log-weighted projective source column
- [x] Lean coordinate derivative of half-weighted source packet
- [x] Lean exact finite-`sigma` tangent Gram
- [x] Lean critical limit to cubic horizontal kernel
- [x] scratch compile, forbidden-token scan, and axiom audit
- [x] umbrella import wired without umbrella build
- [ ] dyadic ordinate localization and Euler--Gamma trace budget
