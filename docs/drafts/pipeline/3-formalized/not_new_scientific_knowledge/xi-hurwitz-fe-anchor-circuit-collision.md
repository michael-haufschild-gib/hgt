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

Suppose every hypothetical right-half Xi-divisor point has:

1. algebraic Arakelov coordinate `w(rho)`;
2. a nonintegral anchor `tau` with algebraic character `q(tau)`; and
3. an algebraic differential relation over `C(a)` among

```text
H_rho, H_(1-rho), H_tau.
```

Then RH holds.

The anchor can be fixed canonically. Lean proves

```text
q(1/2) = -1,
```

so it is enough to assume algebraicity of `w(rho)` and differential dependence of the single
moving family

```text
H_rho, H_(1-rho), H_(1/2)
```

for every hypothetical right-half divisor point. No anchor selection or separate
character-algebraicity premise remains.

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

### First anchor branch

`q(rho)=q(tau)` transfers algebraicity from the anchor to `q(rho)`. Algebraicity of both `w(rho)`
and `q(rho)` contradicts a nonreal Xi zero by the formalized Gelfond--Schneider collision; a real
Xi zero in the open strip is also impossible.

### Reflected anchor branch

Lean proves

```text
q(1-rho) = q(rho)^(-1).
```

Thus algebraicity of `q(1-rho)=q(tau)` transfers through inversion to `q(rho)`, and the same
Arakelov--Hurwitz collision applies.

The complete chain is

```text
algebraic Arakelov coordinate
  + moving differential circuit {H_rho,H_(1-rho),H_(1/2)}
  -> one of three monodromy collisions
  -> FE strip collision or Gelfond--Schneider collision
  -> no right-half Xi zero
  -> RH.
```

## Why this is not the existing finite-anchor theorem

The finite-anchor capture theorem requires every anchor in the augmented family to have algebraic
monodromy character. Here `1-rho` is a moving anchor and its character is not assumed algebraic.
The proof instead resolves the full three-node circuit and treats its three collision branches
separately. The new theorem is therefore not an instance of finite algebraic-anchor capture.

The premise contains no negative-real character condition, zero-location sign, real-rootedness,
Weil positivity, or RH-equivalent limiting measure. It is nevertheless only a formal bridge: the
source differential circuit and algebraic Arakelov realization are not proved.

## Principal declarations

- `continuedHurwitzFEAnchorTripleExponent`
- `ContinuedHurwitzFEAnchorTripleDependent`
- `monoScalar_collision_of_continuedHurwitzFEAnchorTripleDependent`
- `monoScalar_one_sub_eq_inv`
- `xi_ne_zero_of_openCriticalStrip_of_monoScalar_eq_oneSub`
- `XiRightArakelovAlgebraicHurwitzFEAnchorCircuit`
- `riemannHypothesis_of_xiRightArakelovAlgebraicHurwitzFEAnchorCircuit`
- `monoScalar_half_eq_neg_one`
- `XiRightArakelovAlgebraicHurwitzHalfFEAnchorCircuit`
- `riemannHypothesis_of_xiRightArakelovAlgebraicHurwitzHalfFEAnchorCircuit`

## Open core

`[OPEN CORE]` Produce, from one completed arithmetic source and before inspecting zero location, a
moving differential circuit coupling the two holomorphic functional-equation exponents to the
fixed half-exponent Hurwitz function. Independently realize the corresponding Arakelov coordinate
algebraically. A relation which merely equates two monodromy characters does not discharge this
task; the required input is an actual differential identity or bounded-rank source module.

## Gates

- [x] moving three-exponent Hurwitz family typed
- [x] differential circuit resolved into three exact character collisions
- [x] functional-equation character inversion proved
- [x] FE-pair collision excluded in the open strip
- [x] both anchor branches reduced to the Arakelov--Hurwitz theorem
- [x] anchor choice eliminated using the canonical algebraic character `q(1/2)=-1`
- [x] RH capstone formalized without new axioms
- [ ] source differential circuit
- [ ] algebraic Arakelov realization
