# Projective Hurwitz anchor-jet reflection implies RH

- **ID:** xi-hurwitz-projective-anchor-jet-rh
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Source:** top-down cross-corpus synthesis from Hurwitz anchor transversality, analytic moment determinacy, upper-end differential independence, and Xi reflection
- **Statement:** If the complete positive-order canonical Hurwitz anchor jets at exponents `1-rho` and `conj rho` are proportional by one scalar for every Xi divisor point `rho`, then RH holds.

## Formal status

`[PROVED IN LEAN, CONDITIONAL]` For every open-strip Xi zero `rho`, Lean proves

```text
exists c, forall r >= 1,
  d_a^r H_(1-rho)(1) = c * conj(d_a^r H_rho(1))
    -> Re rho = 1/2.
```

The global all-divisor hypothesis therefore implies `RiemannHypothesis`.

## Exact chain

Write

```text
H_s(a) = continuedHzeta(s,a),
J_r(s) = d_a^r H_s(1).
```

The formal chain is

```text
projective positive-order anchor jets
  -> equality of the complete Taylor jets of H_(1-rho) and c H_(conj rho)
  -> local equality at a=1
  -> equality throughout the connected upper half-plane
  -> equality in the upper-end meromorphic differential field
  -> differential dependence of the reflected Hurwitz pair
  -> equality of their monodromy characters
  -> 1-rho = conj rho inside the open critical strip
  -> Re rho = 1/2.
```

The zero-order Taylor coefficients match because Xi reflection makes both Hurwitz anchor values
zero.  The positive-order Schwarz law

```text
J_r(conj s) = conj(J_r(s)),  r >= 1,
```

is unconditional for `Re s > 0`: the exact anchor formula reduces it to conjugation of the
ascending Pochhammer coefficient and of `zeta(s+r)` in its absolutely convergent half-plane.

Anchor transversality also proves that the projective scalar is nonzero.  Equivalently, the open
target can be stated without an auxiliary scalar as equality of all normalized jets

```text
J_r(1-rho) / J_1(1-rho)
  = conj(J_r(rho)) / conj(J_1(rho)),  r >= 1.
```

## Named open core

`[OPEN CORE]` Produce the normalized reflected anchor-germ identity from an independently defined
prime--Gamma or monodromy source relation, rather than from `Re rho = 1/2`, a zero-location
assumption, or a divisor-built interpolation.

A useful source theorem would identify the normalized local shift germs

```text
H_(1-rho)(a) / J_1(1-rho)
and
conj-exponent H_rho(a) / conj(J_1(rho))
```

near `a=1`, or prove equality of their complete normalized coefficient systems.  Only local value
data are required; the passage to global shift dependence and then to the character collision is
now discharged.

## Non-redressing audit

- `[POSITIVE BRIDGE]` The theorem closes a previously missing change of variable: local anchor
  coefficient data now yield a genuine relation in the Hurwitz shift variable.
- A single scalar may vary with the divisor point; exact reflected equality is not assumed.
- No Arakelov algebraicity, auxiliary anchor, zero simplicity, positivity cone, limiting measure,
  or rectangular asymptotic is used.
- The all-order requirement is load-bearing at the present level of generality:
  `FiniteJetGradedRealityNoGo.lean` constructs reflected analytic completed-flux germs agreeing
  through any prescribed finite depth and first disagreeing later.  A finite-coefficient producer
  would therefore need additional Hurwitz/zeta rigidity, not analytic determinacy alone.
- The actual-zeta Euler-unit tangent completeness theorem rules out a continuous regular-flux
  invariant as the producer: finite FE--Schwarz Euler-unit modifications are dense at fixed
  divisor.  A viable producer must positively couple the divisor marking to the source relation.
- `[NOT AN RH PROOF]` The global projective reflection law is itself forced by RH with scalar `1`.
  Without an independent source producer it is an exact criterion, not a breakthrough.
- `[NOVELTY UNVERIFIED]` No new-scientific-knowledge claim is made for this conditional bridge.

## Gates

- [x] 0 -> 1 in-progress: exact value relation and non-circular producer obligation isolated
- [ ] 1 -> 2 fully-proven: construct the projective relation from an independent source theorem
- [ ] 2 -> 3 formalized: formalize that unconditional producer and close RH
- [ ] 3 -> 4 publication-ready: standalone proof and literature audit

## Lean surface

```text
ascPochhammer_eval_conj
continuedHzeta_anchorJet_conj
eventuallyEq_at_one_eqOn_UHP
XiHurwitzAnchorJetProjectiveReflectionCompatible
xiHurwitzAnchorJet_projectiveScalar_ne_zero
xi_re_eq_half_of_anchorJetProjectiveReflectionCompatible
XiHurwitzAnchorJetProjectiveReflectionLaw
riemannHypothesis_of_xiHurwitzAnchorJetProjectiveReflectionLaw
```

Module:

```text
GaloisForLFunctions.RHTower.XiHurwitzAnchorJetProjectiveReflection
```

## Verification

- [x] exact file typecheck
- [x] no new axiom, `sorry`, `admit`, `opaque`, or `unsafe` declaration
- [ ] formal lint after live-tree stabilization
- [ ] generated index refresh after live-tree stabilization

## Log

- 2026-07-13 -- top-down sweep found that the existing anchor transversality and analytic-jet
  determinacy theorems compose with upper-end Hurwitz differential independence.  Formalized the
  projective local-value-to-global-character collision and the conditional RH capstone.
