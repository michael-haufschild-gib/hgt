# Xi Hurwitz functional-equation anchor circuit collision

- **ID:** `xi-hurwitz-fe-anchor-circuit-collision`
- **Stage:** 3-formalized
- **Type:** THEOREM / HGT VALUE-RELATION RH CHAIN
- **Scientific status:** `[PROVED] [BRIDGE] [NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Lean:** `formal/GaloisForLFunctions/RHTower/XiHurwitzFEAnchorCircuitCollision.lean`

## Statement

For an Xi-divisor point `rho`, write

```text
H_s(a) = continued Hurwitz function with exponent s,
q(s)   = exp(-2*pi*i*s),
w(rho) = 1 - 1/rho.
```

Suppose every hypothetical right-half Xi-divisor point has a nonintegral anchor `tau` with
algebraic character `q(tau)`, an algebraic Arakelov coordinate `w(rho)`, and an algebraic
differential relation over `C(a)` among

```text
H_rho, H_(1-rho), H_tau.
```

Then RH holds.

For a general moving anchor, these inputs imply RH.  The canonical half anchor is substantially
stronger. Lean proves

```text
q(1/2) = -1,
```

and open-strip rigidity then excludes all three collision branches without using `w(rho)`.
Consequently it is enough to assume differential dependence of the single moving family

```text
H_rho, H_(1-rho), H_(1/2)
```

for every hypothetical right-half divisor point. No anchor selection, Arakelov algebraicity, or
separate character-algebraicity premise remains.

## Three-branch circuit resolution

The intrinsic continued-Hurwitz differential matroid says that differential independence is
exactly injectivity of the monodromy characters.  Dependence of the three-function family therefore
forces one of

```text
q(rho)     = q(1-rho),
q(rho)     = q(tau),
q(1-rho)   = q(tau).
```

Each branch excludes the hypothetical zero.

### Functional-equation branch

Both `rho` and `1-rho` lie in the open critical strip. Character equality makes their difference
an integer, and strip injectivity forces

```text
rho = 1-rho.
```

This point is real and lies strictly between zero and one, where Xi is positive.

### Half-anchor branches

For `tau=1/2`, either collision with the anchor identifies the corresponding exponent with
`1/2` modulo `Z`.  Open-strip rigidity removes the integer ambiguity, leaving the real point
`1/2`, where Xi is strictly positive.  These branches therefore require no algebraicity theorem.

The complete chain is

```text
moving differential circuit {H_rho,H_(1-rho),H_(1/2)}
  -> one of three monodromy collisions
  -> open-strip equality with the FE partner or the half anchor
  -> positive real Xi value
  -> no right-half Xi zero
  -> RH.
```

## Why this is not the existing finite-anchor theorem

The finite-anchor capture theorem requires every anchor in the augmented family to have algebraic
monodromy character. Here `1-rho` is a moving anchor and its character is not assumed algebraic.
The proof instead resolves the full three-node circuit and treats its three collision branches
separately. The new theorem is therefore not an instance of finite algebraic-anchor capture.

The premise contains no negative-real character condition, zero-location sign, real-rootedness,
Weil positivity, or RH-equivalent limiting measure.  The exact anchor-locus audit below shows,
however, that the fixed-half source circuit cannot be a weaker intermediate theorem: it is false at
every actual Xi zero.  Its global right-half formulation is therefore already equivalent to the
absence of right-half zeros.

## Exact anchor-locus audit

The circuit has now been classified for every open-strip anchor.  At an actual Xi zero `rho`,

```text
ContinuedHurwitzFEAnchorTripleDependent rho tau
  iff tau = rho or tau = 1-rho.
```

Therefore a circuit with the fixed regular half anchor is not a hidden weak consequence of the
Hurwitz matroid: it is impossible at every actual Xi zero.  Conversely, using an anchor already
equal to `rho` or `1-rho` merely repeats the divisor and supplies no orientation information.

The useful reflection specialization is instead the moving Schwarz anchor `tau=conj(rho)`.  Lean
first proves the stronger rank-two law, without an Xi-zero hypothesis,

```text
dependence of {H_(1-rho), H_(conj rho)}
  iff Re(rho)=1/2.
```

Consequently it also proves at every actual Xi zero

```text
dependence of {H_rho, H_(1-rho), H_(conj rho)}
  iff Re(rho)=1/2.
```

Indeed the exact anchor locus gives `conj(rho)=rho` or `conj(rho)=1-rho`.  The first equality would
make `rho` a real open-strip zero and is excluded by positivity; the second is precisely the
critical-line equation.  Thus one finite differential circuit joins holomorphic functional-
equation reflection to Schwarz reflection.  Globally this circuit law is equivalent to RH, so the
remaining source problem is to produce such a relation without first reading the horizontal zero
coordinate.  The pair relation has now been identified exactly with the already formalized common
first-prime seam charge and scalar orientation energy.  It therefore does not define an independent
source-producer problem: its surviving source obligation is precisely regular-Cauchy source-core
nonnegativity.

## Principal declarations

- `continuedHurwitzFEAnchorTripleExponent`
- `ContinuedHurwitzFEAnchorTripleDependent`
- `monoScalar_collision_of_continuedHurwitzFEAnchorTripleDependent`
- `continuedHurwitzFEAnchorTripleDependent_iff_monoScalar_collision`
- `monoScalar_one_sub_eq_inv`
- `xi_ne_zero_of_openCriticalStrip_of_monoScalar_eq_oneSub`
- `xiZero_continuedHurwitzFEAnchorTripleDependent_iff_anchor_eq_orbit`
- `continuedHurwitzFESchwarzPairDifferentiallyDependent_iff_re_eq_half`
- `XiHurwitzFESchwarzPairCircuit`
- `xiHurwitzFESchwarzPairCircuit_iff_riemannHypothesis`
- `xiZero_continuedHurwitzFESchwarzTripleDependent_iff_re_eq_half`
- `xiZero_continuedHurwitzFEAnchorTriple_independent_of_anchor_ne_zero`
- `XiHurwitzFESchwarzTripleCircuit`
- `xiHurwitzFESchwarzTripleCircuit_iff_riemannHypothesis`
- `riemannHypothesis_of_xiHurwitzFESchwarzTripleCircuit`
- `XiRightArakelovAlgebraicHurwitzFEAnchorCircuit`
- `riemannHypothesis_of_xiRightArakelovAlgebraicHurwitzFEAnchorCircuit`
- `monoScalar_half_eq_neg_one`
- `xi_ne_zero_of_openCriticalStrip_of_monoScalar_eq_half`
- `xiZero_continuedHurwitzHalfFEAnchorTriple_independent`
- `XiRightHurwitzHalfFEAnchorCircuit`
- `riemannHypothesis_of_xiRightHurwitzHalfFEAnchorCircuit`
- `XiRightArakelovAlgebraicHurwitzHalfFEAnchorCircuit`
- `riemannHypothesis_of_xiRightArakelovAlgebraicHurwitzHalfFEAnchorCircuit`

## Open core

`[OPEN CORE]` Prove nonnegativity of the Weil form on the concrete algebraic regular-Cauchy
prime--Gamma source span.  The already formalized source closure then forces zero orientation
energy, equivalently the two-function relation between `H_(1-rho)` and `H_(conj rho)`.  Do not
target the fixed half anchor: its circuit is positively ruled out at every actual Xi zero and its
global right-half formulation merely restates RH.

## Gates

- [x] moving three-exponent Hurwitz family typed
- [x] differential circuit resolved into three exact character collisions
- [x] functional-equation character inversion proved
- [x] FE-pair collision excluded in the open strip
- [x] both anchor branches reduced to the Arakelov--Hurwitz theorem
- [x] anchor choice eliminated using the canonical algebraic character `q(1/2)=-1`
- [x] Arakelov algebraicity eliminated from the fixed half-anchor circuit
- [x] unconditional differential freeness of the actual Xi FE/half-anchor triple proved
- [x] fixed-half source route retired positively by the exact anchor-locus law
- [x] finite FE--Schwarz circuit characterized pointwise and globally
- [x] FE--Schwarz interface reduced further to a rank-two circuit with no pointwise Xi hypothesis
- [x] rank-two circuit identified with common first-prime charge and scalar orientation energy
- [x] RH capstone formalized without new axioms
- [ ] regular-Cauchy source-core nonnegativity
