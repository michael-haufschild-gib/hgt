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

`formal/GaloisForLFunctions/RHTower/Artin/ArtinLocalEulerProduct.lean` defines the explicit linear
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

The generic theorem is now connected to the actual arithmetic and finite-place objects rather than
left as an abstract local-algebra result.  The same module proves

```text
frobeniusInertiaEulerPolynomial_prod:
  P_Q(rhoV.prod rhoW) = P_Q(rhoV) * P_Q(rhoW),
```

and `formal/GaloisForLFunctions/RHTower/Artin/ArtinNumberFieldLocalEulerProduct.lean` proves

```text
numberFieldFinitePlaceLocalEulerPolynomial_prod:
  P_v(rhoV.prod rhoW) = P_v(rhoV) * P_v(rhoW)
```

for the choice-free carrier `v : HeightOneSpectrum (𝓞 K)`.  The latter unfolds the internally
chosen prime above `v`, installs only its proved number-field instances, and invokes the actual
upstairs theorem; it introduces no selected-prime assumption in its public statement.

## Paper proof

The invariant space of a product representation is canonically `V^I × W^I`.  Under this explicit
linear equivalence, Frobenius on invariants is the product endomorphism.  The characteristic
polynomial of a product endomorphism is the product of characteristic polynomials, and reversal
over a field preserves that product.  This has no arithmetic or analytic premise.

## Verification

- `lake env lean GaloisForLFunctions/RHTower/Artin/ArtinLocalEulerProduct.lean` passed.
- `lake build GaloisForLFunctions.RHTower.Artin.ArtinLocalEulerProduct` passed; this is the targeted
  module build, not an umbrella or full build.
- `/tmp/ArtinLocalEulerProductAxioms.lean` reports `[propext, Quot.sound]` for
  `invariantsProdLinearEquiv_conj_toInvariants` and
  `[propext, Classical.choice, Quot.sound]` for `localEulerPolynomial_prod` and the new actual
  `frobeniusInertiaEulerPolynomial_prod` adapter.
- `lake env lean GaloisForLFunctions/RHTower/Artin/ArtinNumberFieldLocalEulerProduct.lean` and its
  targeted `lake build GaloisForLFunctions.RHTower.Artin.ArtinNumberFieldLocalEulerProduct` passed.
  `/tmp/ArtinNumberFieldLocalEulerProductAxioms.lean` reports only
  `[propext, Classical.choice, Quot.sound]`.
- Both leaves are imported by `formal/GaloisForLFunctions/RHTower.lean`; the umbrella was
  deliberately not built.

## Anti-theatre boundary

This proves only local source compatibility, now including the actual finite base-prime carrier.
It neither constructs an infinite Euler product, proves convergence/continuation, nor controls a
continued divisor.  It cannot cross the C2 source-to-divisor obstruction.

## Log

- 2026-08-15 — opened after the fixed-prime Euler polynomial layer was formalized.  An explicit
  invariants-product equivalence and characteristic-polynomial proof source-checked in scratch.
- 2026-08-15 — formalized, target-built, axiom-audited, and wired without an umbrella build.
- 2026-08-15 — extended to the actual Frobenius--inertia polynomial and then to the choice-free
  number-field finite-place polynomial.  Both new leaf checks/builds and standard-foundation axiom
  audits passed; no global product or analytic claim was added.
