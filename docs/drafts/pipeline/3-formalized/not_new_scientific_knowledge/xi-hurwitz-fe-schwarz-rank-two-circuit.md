# Xi Hurwitz FE--Schwarz rank-two circuit

- **ID:** `xi-hurwitz-fe-schwarz-rank-two-circuit`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) / VALUE-REFLECTION RH CHAIN
- **Scientific status:** `[PROVED] [BRIDGE] [NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Lean:** `formal/GaloisForLFunctions/RHTower/XiHurwitzFEAnchorCircuitCollision.lean`
  and `formal/GaloisForLFunctions/RHTower/XiHurwitzFESchwarzPairValueRelation.lean`

## Statement

For every complex exponent `rho` in the open critical strip, let `H_s` denote the analytically
continued Hurwitz function in the shift variable with frozen exponent `s`.  Then

```text
H_(1-rho) and H_(conj rho) are differentially dependent over C(a)
  iff Re(rho)=1/2.
```

No Xi-zero assumption is used in this pointwise law.  Restricting it to the Xi divisor gives the
global equivalence

```text
every Xi divisor point has the FE--Schwarz Hurwitz pair circuit
  iff RH.
```

## Proof

The intrinsic two-function continued-Hurwitz differential matroid gives

```text
pair dependence iff q(1-rho)=q(conj rho),
q(s)=exp(-2*pi*i*s).
```

Both exponents lie in the open strip.  Equality of their characters says that their difference is
an integer, and open-strip rigidity removes the integer ambiguity.  Thus

```text
1-rho=conj rho iff Re(rho)=1/2.
```

Conversely the critical-line equation identifies the two exponents, so the pair repeats one
continued-Hurwitz function and is differentially dependent.

## Top-down reduction

This strictly reduces two previous interfaces:

1. the three-function circuit `H_rho,H_(1-rho),H_(conj rho)` is unnecessary;
2. proportionality of every positive-order anchor jet is unnecessary.

The remaining chain is

```text
source-defined differential relation between H_(1-rho) and H_(conj rho)
  -> equality of their monodromy characters
  -> equality of the FE and Schwarz reflected exponents
  -> critical-line location
  -> RH.
```

The global circuit predicate is still RH-equivalent.  A valid producer must therefore arise from
the arithmetic source before inspecting the horizontal zero coordinate; merely asserting the
relation on the Xi divisor is not an unconditional proof.

The source interface is now completely identified rather than left independent.  Lean proves

```text
FE--Schwarz pair dependence at rho
  iff the common first-prime seam charge C_2(rho) vanishes,
```

and, over the complete Xi divisor,

```text
XiHurwitzFESchwarzPairCircuit
  iff XiFirstPrimeSeamChargesVanish
  iff xiHurwitzOrientationEnergy = 0.
```

Thus the pair circuit does not open a second source route.  It is an HGT coordinate for the same
orientation defect already reconstructed by regular Cauchy prime--Gamma source packets.  The only
surviving input on this splice is nonnegativity of the Weil form on their algebraic source core.

## Principal declarations

- `continuedHurwitzFESchwarzPairDifferentiallyDependent_iff_re_eq_half`
- `XiHurwitzFESchwarzPairCircuit`
- `xiHurwitzFESchwarzPairCircuit_iff_riemannHypothesis`
- `riemannHypothesis_of_xiHurwitzFESchwarzPairCircuit`
- `continuedHurwitzFESchwarzPairDependent_iff_firstPrimeSeamCharge_eq_zero`
- `continuedHurwitzFESchwarzPairDependent_iff_anchorPrimeTwoSeam_tendsto_zero`
- `xiHurwitzFESchwarzPairCircuit_iff_firstPrimeSeamChargesVanish`
- `xiHurwitzFESchwarzPairCircuit_iff_orientationEnergy_zero`

## Gates

- [x] exact rank-two differential-dependence law formalized
- [x] Xi-zero hypothesis removed from the pointwise law
- [x] global equivalence to RH formalized
- [x] exact equality with the common first-prime seam formalized
- [x] exact equality with zero scalar orientation energy formalized
- [x] direct module compilation succeeds
- [ ] source-core nonnegativity for the concrete regular-Cauchy prime--Gamma span
