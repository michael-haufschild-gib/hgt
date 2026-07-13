# Xi Hurwitz functional-equation anchor divisor-orbit locus

- **ID:** `xi-hurwitz-fe-anchor-divisor-orbit-locus`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) / POSITIVE VALUE-RELATION LAW
- **Scientific status:** `[PROVED] [BRIDGE] [NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Lean:** `formal/GaloisForLFunctions/RHTower/XiHurwitzFEAnchorCircuitCollision.lean`

## Statement

Fix an actual Xi zero `rho` in the open critical strip.  For every open-strip anchor `tau`, the
three analytically continued Hurwitz functions in the shift variable with frozen exponents

```text
rho, 1-rho, tau
```

are differentially dependent over `C(a)` exactly when

```text
tau = rho or tau = 1-rho.
```

Thus the differential-dependence anchor locus is precisely the two-point functional-equation
orbit of the Xi divisor point.  Every open-strip point outside the Xi divisor gives an independent
triple.  In particular the canonical anchor `tau=1/2` gives an unconditionally independent triple
at every actual Xi zero.

## Proof

The intrinsic continued-Hurwitz differential matroid first gives the exact three-node law

```text
triple dependence
  iff q(rho)=q(1-rho) or q(rho)=q(tau) or q(1-rho)=q(tau).
```

The first collision is incompatible with Xi zerohood: open-strip rigidity identifies the
functional-equation pair at a real point where Xi is positive.  In the other two branches,
character equality identifies the exponents modulo `Z`; because both lie in the open strip, the
integer ambiguity vanishes and `tau` equals `rho` or `1-rho`.  Conversely either equality repeats
one member of the triple and hence gives a circuit.

## Consequence

The Arakelov-algebraicity field in the earlier fixed half-anchor RH certificate is superfluous.
The circuit condition alone excludes every hypothetical right-half Xi zero and therefore implies
RH.  This is a hypothesis discharge, not an unconditional RH proof: no source theorem producing
the hypothetical circuit is asserted.

## Principal declarations

- `continuedHurwitzFEAnchorTripleDependent_iff_monoScalar_collision`
- `xiZero_continuedHurwitzFEAnchorTripleDependent_iff_anchor_eq_orbit`
- `xiZero_continuedHurwitzFEAnchorTriple_independent_of_anchor_ne_zero`
- `xi_ne_zero_of_openCriticalStrip_of_monoScalar_eq_half`
- `xiZero_continuedHurwitzHalfFEAnchorTriple_independent`
- `XiRightHurwitzHalfFEAnchorCircuit`
- `riemannHypothesis_of_xiRightHurwitzHalfFEAnchorCircuit`

## Gates

- [x] exact character-collision classification formalized
- [x] character collision converted to the two-point anchor locus
- [x] regular-anchor triple freeness formalized
- [x] algebraicity-free RH consumer formalized
- [ ] source-side mechanism forcing a circuit at hypothetical right-half zeros
