# The clipped critical-Mellin center pairs linearly with every half-density radial envelope

- **ID:** `ccm-coupled-finite-aperture-center-pairing`
- **Stage:** 3-formalized
- **Type:** THEOREM / CONNES-SOURCE BRIDGE
- **Scientific status:** `[LEAN-PROVED] [BRIDGE] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH PROOF]`
- **Formal source:**
  `formal/GaloisForLFunctions/RHTower/CCMCriticalMellinFiniteApertureCenterPairing.lean`

## Theorem

Let

```text
J(h)=exp(h)-1+h-Psi(exp(h))
```

and let `R : R -> C` be continuous with

```text
norm(R(h)) <= B exp(-h/2),    h>=0,    B>=0.
```

For `H>=0`, define the genuinely integrable clipped center pairing

```text
C_H(R)
 = integral_0^H exp(-h/2) J(h) R(h) dh
   + J(H) integral_H^infinity exp(-h/2) R(h) dh.
```

Then

```text
norm(C_H(R)) <= B (log 4+7)(H+1).
```

The tail integral is proved integrable from the stated half-density envelope; no convention for a
nonintegrable Bochner integral is used.

## Route consequence

The actual Poisson-center cross channel therefore costs only a linear finite-aperture factor once
the radial source has its square-root BV envelope. This removes a quantitative prime-number-theorem
remainder from the continuous-polar source problem. It does not supply the radial PSWF envelope,
the one-sided Poisson--Muntz identity, or the fixed-mode variation bound.

## Verification

The leaf module was checked directly in the pinned project toolchain. The axiom audit for the main
pairing theorem and its two improper-integral prerequisites contains only `propext`,
`Classical.choice`, and `Quot.sound`; there are no project axioms or placeholders.
