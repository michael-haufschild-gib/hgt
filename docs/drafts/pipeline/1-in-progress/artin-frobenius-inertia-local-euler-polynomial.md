# Artin Frobenius--inertia local Euler polynomial

- **ID:** `artin-frobenius-inertia-local-euler-polynomial`
- **Stage:** 1-in-progress
- **Type:** THEOREM (classical local infrastructure)
- **Status:** `[LITERATURE] [PAPER-PROVED] [BRIDGE] [NOT NEW]`

## Exact target

For an actual finite Galois local datum, do not introduce a synthetic `LocalData` structure.  Use
Mathlib's actual prime ideal `Q`, decomposition group `MulAction.stabilizer G Q`, inertia subgroup
`Q.inertia (MulAction.stabilizer G Q)`, and chosen arithmetic Frobenius
`arithFrobAt R G Q`.  For a finite-dimensional complex representation `rho` of the ambient Galois
group, define

```text
P_Q(rho,T) = det(1 - T rho(Frob_Q) | V^(I_Q)).
```

The first dependency-closed formal layer is the same construction for an actual group `D`, actual
normal subgroup `I`, actual representation `rho`, and actual element `phi : D`, realized as the
reversed characteristic polynomial of `phi` on `V^I`.  Then connect it to the Mathlib arithmetic
objects above.

## First theorem bundle

1. `V^I` is the concrete invariant submodule and carries the actual restricted `D`-action.
2. The reversed characteristic polynomial is exactly `det(1 - T rho(phi) | V^I)` in a chosen
   basis and has value `1` at `T = 0`.
3. Replacing `phi` by another lift differing by inertia leaves the endomorphism and polynomial
   unchanged.
4. The arithmetic adapter uses `Ideal.inertia`, `MulAction.stabilizer`, and `arithFrobAt`; no
   arbitrary local-factor proposition, postulated Frobenius, or choice-dependent interface.

## Paper proof

Normality of `I` makes `V^I` stable under `D`.  Every element of `I` acts trivially on that
subspace, so two Frobenius lifts with quotient difference in `I` induce the same endomorphism.
For a basis of `V^I`, reversal of the ordinary characteristic polynomial is
`det(1 - T A)`, and its value at zero is the determinant of the identity.  Mathlib proves
inertia normal in the actual decomposition group and proves two arithmetic Frobenius elements
differ by inertia.

## Literature alignment

For a finite Galois extension and a finite prime, this is the standard local Artin polynomial.
The global local factor is `P_Q(rho, N(Q)^(-s))^(-1)`.  Sources: Artin (1930); Cogdell's Artin
L-function survey; Horawa's L-function notes; Gun--Hazra--Sahu (2025), DOI
10.1007/s00605-025-02060-7.

## Anti-theatre boundary

This is necessary source infrastructure, not evidence for Artin holomorphy.  It supplies the
genuine Frobenius determinants deliberately absent from the C2 countermodel, but it gives no
non-circular law connecting their Euler product to a continued divisor.  The open core remains
the source-to-divisor/effectivity law.

## Lean constraints

- Use actual Mathlib objects, not a `Prop` interface or new axiom.
- Generic algebraic theorems quantify over their real mathematical inputs; the arithmetic adapter
  discharges normality and Frobenius-existence from Mathlib.
- No `sorry`, `admit`, `axiom`, `opaque`, or `unsafe`; source-check first, then one targeted olean
  build and no umbrella build.

## Log

- 2026-08-15 — opened after audit confirmed the character-theory frontier lacks every genuine
  Frobenius/inertia local-factor object, while Mathlib already contains the needed arithmetic
  primitives.
