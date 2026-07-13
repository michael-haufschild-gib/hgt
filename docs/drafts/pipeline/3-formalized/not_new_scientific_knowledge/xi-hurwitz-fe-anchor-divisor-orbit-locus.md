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

## Consequences

The Arakelov-algebraicity field in the earlier fixed half-anchor RH certificate is superfluous, but
the stronger conclusion is a positive retirement: the fixed-half circuit is impossible at every
actual Xi zero.  A theorem producing that circuit over all hypothetical right-half zeros would not
be an intermediate source law; its assertion is already equivalent to there being no such zeros.

The nontrivial reflection splice uses `tau=conj(rho)`.  At an actual Xi zero the exact orbit law and
real-strip positivity give

```text
dependence of {H_rho, H_(1-rho), H_(conj rho)}
  iff conj(rho)=1-rho
  iff Re(rho)=1/2.
```

The companion rank-two theorem is stronger: for every open-strip `rho`, without assuming it is an
Xi zero,

```text
dependence of {H_(1-rho), H_(conj rho)} iff Re(rho)=1/2.
```

Thus the earlier all-order projective anchor-jet interface reduces to one two-function differential
relation.  Its global Xi-divisor law is equivalent to RH, not an unconditional proof.  The relation
is now proved equivalent to vanishing of the common first-prime seam charge and to zero scalar
orientation energy, so there is no independent Hurwitz producer left to seek; the remaining
research content is regular-Cauchy source-core nonnegativity.

## Principal declarations

- `continuedHurwitzFEAnchorTripleDependent_iff_monoScalar_collision`
- `continuedHurwitzFESchwarzPairDifferentiallyDependent_iff_re_eq_half`
- `xiHurwitzFESchwarzPairCircuit_iff_riemannHypothesis`
- `xiZero_continuedHurwitzFEAnchorTripleDependent_iff_anchor_eq_orbit`
- `xiZero_continuedHurwitzFESchwarzTripleDependent_iff_re_eq_half`
- `xiZero_continuedHurwitzFEAnchorTriple_independent_of_anchor_ne_zero`
- `XiHurwitzFESchwarzTripleCircuit`
- `xiHurwitzFESchwarzTripleCircuit_iff_riemannHypothesis`
- `xi_ne_zero_of_openCriticalStrip_of_monoScalar_eq_half`
- `xiZero_continuedHurwitzHalfFEAnchorTriple_independent`
- `XiRightHurwitzHalfFEAnchorCircuit`
- `riemannHypothesis_of_xiRightHurwitzHalfFEAnchorCircuit`

## Gates

- [x] exact character-collision classification formalized
- [x] character collision converted to the two-point anchor locus
- [x] regular-anchor triple freeness formalized
- [x] algebraicity-free RH consumer formalized
- [x] fixed-half circuit route retired positively
- [x] finite FE--Schwarz circuit criterion formalized
- [x] FE--Schwarz criterion reduced to a rank-two relation independent of Xi zerohood pointwise
- [x] rank-two relation identified exactly with the common seam/orientation-energy zero locus
- [ ] regular-Cauchy source-core nonnegativity
