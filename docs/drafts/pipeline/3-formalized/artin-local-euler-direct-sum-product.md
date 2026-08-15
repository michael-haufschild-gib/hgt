# Artin local Euler polynomial: direct-sum product law

- **ID:** `artin-local-euler-direct-sum-product`
- **Stage:** 3-formalized
- **Type:** THEOREM (classical local infrastructure)
- **Status:** `[LITERATURE] [PAPER-PROVED] [LEAN-PROVED] [BRIDGE] [NOT NEW]`
- **Statement:** `P_I(rhoV × rhoW, phi) = P_I(rhoV, phi) * P_I(rhoW, phi)`.

## Goal

Formalize the first additivity law of the genuine local Artin source, using actual representations,
actual invariant submodules, and actual characteristic polynomials.  This is the local algebra
behind the multiplicativity of Euler factors for direct sums; it does not posit a global
`ArtinLFunction` or any analytic property.

## Exact formal result

`formal/GaloisForLFunctions/RHTower/ArtinLocalEulerProduct.lean` defines the explicit linear
equivalence

```text
invariantsProdLinearEquiv : (V × W)^I ≃ₗ V^I × W^I
```

and proves that it conjugates the induced Frobenius action on the product invariant subspace to
the product of the two induced actions
(`invariantsProdLinearEquiv_conj_toInvariants`).  For every field `k`, group `D`, normal subgroup
`I`, finite-dimensional actual representations `rhoV`, `rhoW`, and `phi : D`, it then proves

```text
localEulerPolynomial_prod:
  P_I(rhoV.prod rhoW, phi) = P_I(rhoV, phi) * P_I(rhoW, phi).
```

No proposition interface carries this equality and no new axiom is introduced.

## Paper proof

The invariant space of a product representation is canonically `V^I × W^I`.  Under this explicit
linear equivalence, Frobenius on invariants is the product endomorphism.  The characteristic
polynomial of a product endomorphism is the product of characteristic polynomials, and reversal
over a field preserves that product.  This has no arithmetic or analytic premise.

## Verification

- `lake env lean GaloisForLFunctions/RHTower/ArtinLocalEulerProduct.lean` passed.
- `lake build GaloisForLFunctions.RHTower.ArtinLocalEulerProduct` passed; this is the targeted
  module build, not an umbrella or full build.
- `/tmp/ArtinLocalEulerProductAxioms.lean` reports `[propext, Quot.sound]` for
  `invariantsProdLinearEquiv_conj_toInvariants` and
  `[propext, Classical.choice, Quot.sound]` for `localEulerPolynomial_prod`.
- The leaf is imported by `formal/GaloisForLFunctions/RHTower.lean`; the umbrella was deliberately
  not built.

## Anti-theatre boundary

This proves only local source compatibility.  It neither descends from `Q` to a base prime nor
constructs an infinite Euler product, proves convergence/continuation, or controls a continued
divisor.  It cannot cross the C2 source-to-divisor obstruction.

## Log

- 2026-08-15 — opened after the fixed-prime Euler polynomial layer was formalized.  An explicit
  invariants-product equivalence and characteristic-polynomial proof source-checked in scratch.
- 2026-08-15 — formalized, target-built, axiom-audited, and wired without an umbrella build.
