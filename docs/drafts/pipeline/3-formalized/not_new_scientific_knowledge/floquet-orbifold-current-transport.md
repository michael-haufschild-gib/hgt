# Floquet orbifold-current transport

- **ID:** `floquet-orbifold-current-transport`
- **Stage:** 3-formalized
- **Type:** LEAN BRIDGE
- **Scientific status:** `[FORMALIZED] [BRIDGE] [NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Module:** `formal/GaloisForLFunctions/HTGeometry/FloquetOrbifoldTail.lean`

## Certified statement

For

```text
R_1(z)=z^2+1,
R_2(z)=(z-1)^2,
J_0(y)=y'/y,
J_1(y)=y'/(y-1),
```

Lean proves

```text
R_2(R_1(y))=y^4,
R_1(R_2(y))=(y-1)^4+1,
J_1(R_1(y))=2 J_0(y),
J_0(R_2(y))=2 J_1(y),
J_0(R_2(R_1(y)))=4 J_0(y),
J_1(R_1(R_2(y)))=4 J_1(y).
```

The declarations are:

```text
floquetR₂_comp_R₁
floquetR₁_comp_R₂
phaseOneCurrent_floquetR₁
phaseZeroCurrent_floquetR₂
phaseZeroCurrent_twoStep
phaseOneCurrent_rotatedTwoStep
```

## Scope

These exact identities are the algebraic core of the paper theorem
`floquet-orbifold-tail-emergence`.  The classification that the two individual maps have trivial
tails while the period maps have the displayed complete tails remains paper-level, so this bridge
does not promote the whole theorem to stage 3.

## Verification

- The targeted leaf build passes.
- Axiom reports contain only `propext`, `Classical.choice`, and `Quot.sound`.
- No placeholders or unsafe declarations occur.

## RH impact

No direct consequence.  The formal result only demonstrates that a protected current can belong
to an ordered rational protocol rather than an autonomous step.
