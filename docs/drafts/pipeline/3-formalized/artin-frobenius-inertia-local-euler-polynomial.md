# Artin Frobenius--inertia local Euler polynomial

- **ID:** `artin-frobenius-inertia-local-euler-polynomial`
- **Stage:** 3-formalized
- **Type:** THEOREM (classical local infrastructure)
- **Status:** `[LITERATURE] [PAPER-PROVED] [LEAN-PROVED] [BRIDGE] [NOT NEW]`

## Exact target

For actual Mathlib arithmetic data, use a prime ideal `Q`, decomposition group
`MulAction.stabilizer G Q`, inertia subgroup `Q.inertia (MulAction.stabilizer G Q)`, and chosen
arithmetic Frobenius `arithFrobAt R G Q`; do not introduce a synthetic `LocalData` structure.
For a finite-dimensional complex representation `rho` of the ambient Galois group, define

```text
P_Q(rho,T) = det(1 - T rho(Frob_Q) | V^(I_Q)).
```

The dependency-closed generic layer is the same construction for an actual group `D`, actual
normal subgroup `I`, actual representation `rho`, and actual `phi : D`, realized as the reversed
characteristic polynomial on `V^I`.  The arithmetic adapter connects this to Mathlib's inertia,
stabilizer, and arithmetic Frobenius.

## Formal result

`formal/GaloisForLFunctions/RHTower/ArtinLocalEulerFactor.lean` proves:

1. `localEulerPolynomial rho I phi` is the reversed characteristic polynomial of the genuine
   induced action on `V^I` and equals `det (1 - T rho(phi) | V^I)` in a chosen basis
   (`localEulerPolynomial_eq_det`).
2. Its value at zero is one (`localEulerPolynomial_eval_zero`).
3. The induced endomorphism and polynomial are unchanged if two lifts differ by inertia
   (`toInvariants_frobenius_eq_of_mul_inv_mem` and
   `localEulerPolynomial_eq_of_mul_inv_mem`).
4. The actual arithmetic Frobenius adapter is lift-independent for every
   `IsArithFrobAt R sigma Q` (`frobeniusInertiaAction_eq_of_isArithFrobAt` and
   `frobeniusInertiaEulerPolynomial_eq_of_isArithFrobAt`).
5. The actual local polynomial has value one at zero
   (`frobeniusInertiaEulerPolynomial_eval_zero`).

No statement is carried by a `Prop` interface and no new axiom is introduced.  Generic arguments
quantify over real mathematical inputs; Mathlib supplies normality of the actual inertia subgroup
and the theorem that arithmetic Frobenius lifts differ by inertia.

## Paper proof

Normality of `I` makes `V^I` stable under `D`.  Every `i : I` acts trivially on that subspace, so
two lifts whose quotient difference lies in `I` induce the same endomorphism.  For a basis of
`V^I`, reversal of the ordinary characteristic polynomial is `det(1 - T A)`, and its value at
zero is the determinant of the identity.  Mathlib proves inertia normal in the actual
decomposition group and proves two arithmetic Frobenius elements differ by inertia.

## Literature alignment

For a finite Galois extension and finite prime, this is the standard local Artin polynomial.  The
global local factor is `P_Q(rho, N(Q)^(-s))^(-1)`.  Sources: Artin (1930); Cogdell's Artin
L-function survey; Horawa's L-function notes; Gun--Hazra--Sahu (2025), DOI
10.1007/s00605-025-02060-7.

## Verification

- `lake env lean GaloisForLFunctions/RHTower/ArtinLocalEulerFactor.lean` passed.
- `lake build GaloisForLFunctions.RHTower.ArtinLocalEulerFactor` passed; this is the targeted
  module build, not an umbrella or full build.
- `/tmp/ArtinLocalEulerAxioms.lean` reports only
  `[propext, Classical.choice, Quot.sound]` for
  `localEulerPolynomial_eq_of_mul_inv_mem`, `frobeniusInertiaAction_eq_of_isArithFrobAt`, and
  `frobeniusInertiaEulerPolynomial_eq_of_isArithFrobAt`.
- The leaf is imported by `formal/GaloisForLFunctions/RHTower.lean`; the umbrella was deliberately
  not built.

## Anti-theatre boundary

This is necessary source infrastructure, not evidence for Artin holomorphy.  It supplies the
genuine Frobenius determinants deliberately absent from the C2 countermodel, but it gives no
non-circular law connecting their Euler product to a continued divisor.  It also does not yet
identify primes above a base number-field prime, their norms, changing-prime conjugacy,
Euler-product convergence, conductor/archimedean factors, Brauer continuation, or effectivity.
The open core remains the source-to-divisor/effectivity law.

## Log

- 2026-08-15 — opened after audit confirmed the character-theory frontier lacks every genuine
  Frobenius/inertia local-factor object, while Mathlib already contains the needed arithmetic
  primitives.
- 2026-08-15 — formalized the generic and actual-arithmetic local Euler polynomial layer;
  source check, targeted olean build, and standard-foundation axiom audit pass.  Wired the leaf
  into `RHTower.lean` without an umbrella build.
