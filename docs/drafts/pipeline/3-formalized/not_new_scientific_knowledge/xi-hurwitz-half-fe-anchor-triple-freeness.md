# Xi Hurwitz half-anchor functional-equation triple freeness

- **ID:** `xi-hurwitz-half-fe-anchor-triple-freeness`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) / POSITIVE VALUE-RELATION LAW
- **Scientific status:** `[PROVED] [BRIDGE] [NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Lean:** `formal/GaloisForLFunctions/RHTower/XiHurwitzFEAnchorCircuitCollision.lean`

## Statement

For every actual Xi zero `rho` in the open critical strip, the three analytically continued
Hurwitz functions in the shift variable with frozen exponents

```text
rho, 1-rho, 1/2
```

are differentially independent over `C(a)`.

Equivalently, Lean proves

```text
xi rho = 0
  -> not (ContinuedHurwitzFEAnchorTripleDependent rho (1/2)).
```

## Proof

The intrinsic continued-Hurwitz differential matroid resolves any dependence into one of the
three monodromy-character collisions

```text
q(rho)=q(1-rho),  q(rho)=q(1/2),  q(1-rho)=q(1/2).
```

Character equality identifies the two exponents modulo `Z`.  Open-strip rigidity turns each
collision into a real point of `(0,1)`: the first identifies the functional-equation pair, while
the other two identify one member with the half exponent.  Xi is strictly positive on that real
interval, contradicting zerohood.

## Consequence

The Arakelov-algebraicity field in the earlier fixed half-anchor RH certificate is superfluous.
The circuit condition alone excludes every hypothetical right-half Xi zero and therefore implies
RH.  This is a hypothesis discharge, not an unconditional RH proof: no source theorem producing
the hypothetical circuit is asserted.

## Principal declarations

- `xi_ne_zero_of_openCriticalStrip_of_monoScalar_eq_half`
- `xiZero_continuedHurwitzHalfFEAnchorTriple_independent`
- `XiRightHurwitzHalfFEAnchorCircuit`
- `riemannHypothesis_of_xiRightHurwitzHalfFEAnchorCircuit`

## Gates

- [x] three collision branches isolated
- [x] half-anchor branches excluded without algebraicity
- [x] unconditional Xi-zero triple freeness formalized
- [x] algebraicity-free RH consumer formalized
- [ ] source-side mechanism forcing a circuit at hypothetical right-half zeros
