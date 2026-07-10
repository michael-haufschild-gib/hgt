# A finite Euler head has zero verified-height amplification

- **ID:** finite-euler-height-no-amplification
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) / route guardrail / `[BRIDGE]`
- **Source:** `FiniteEulerInert.lean`; `CarrierChargeSoftness.lean`
- **Statement:** For every `0 <= H < U` and every finite bundle of genuine
  local Euler factors, the finite-Euler-decorated functional-equation class
  contains a member with no upper-strip zero through height `H` and an
  off-critical-line zero at a height strictly between `H` and `U`.

## Goal

Separate the exact infinite Euler product from every finite source
approximation in verified-height arguments.  A theorem that turns a zero-free
certificate through `H` into any strict continuation above `H` cannot follow
from functional-equation symmetry plus finitely many exact Euler factors.

## Theorem

Let `P` be a finite set of integers greater than one, and let `0 <= H < U`.
There is a member `f` of `FiniteEulerClass P` such that

1. `f(z) != 0` whenever `0 < Re z < 1` and `0 < Im z <= H`;
2. there is a `rho` with `0 < Im rho`, `H < Im rho < U`, `0 < Re rho < 1`,
   `Re rho != 1/2`, and `f(rho)=0`.

Choose

```text
c   = (H+U)/2,
rho = 1/4 + i c,
f   = feBundle(P) * orbitQuartic(rho).
```

The finite Euler bundle is nonvanishing throughout the open critical strip.
The orbit quartic has exactly the four zeros

```text
rho, 1-rho, conjugate(rho), 1-conjugate(rho).
```

Its two upper-half-plane zeros have height `c>H`, while its two conjugates
have negative height.  Hence the lower upper-strip window is zero-free and the
prescribed higher window contains an off-line zero.

## Lean certificate

- Theorem: `RHTower.finiteEulerClass_no_height_amplification`
- File: `formal/GaloisForLFunctions/RHTower/FiniteEulerInert.lean`
- Inputs: `feBundle_ne_zero_on_strip`, `fESchwarz_orbitQuartic`, and the
  explicit factorization of `orbitQuartic`.
- No new axiom or analytic placeholder.

## Research consequence

This is not a theorem about the Riemann zeta-function: the witness does not
retain zeta's exact infinite Euler product.  It is a sharp falsifier for three
candidate amplifiers:

- functional-equation symmetry alone;
- a fixed finite set of exact local Euler factors;
- qualitative openness of a verified zero-free height window.

Any positive verified-height amplifier must use either the exact infinite
Euler product or new quantitative boundary data at the verified endpoint.

## Gates

- [x] 0 -> 1 in-progress: height-local claim and explicit witness stated.
- [x] 1 -> 2 fully-proven: factorization proof complete.
- [x] 2 -> 3 formalized: Lean theorem checks axiom-clean.
- [ ] 3 -> 4 publication-ready: not a standalone publication claim; retain as
  a formal route guardrail.

## Log

- 2026-07-10 -- formalized while attacking verified-height amplification.
