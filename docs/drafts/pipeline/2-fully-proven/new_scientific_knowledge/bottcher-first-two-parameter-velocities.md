# The first two Böttcher parameter velocities are algebraically independent

- **ID:** bottcher-first-two-parameter-velocities
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Date:** 2026-07-10
- **Status banner:** `[CANDIDATE NEW SCIENTIFIC KNOWLEDGE]` The proof is complete. A targeted
  primary-literature audit found the parent Mahler hypertranscendence theorem, but not the
  two-velocity statement or its jet-forcing mechanism. The novelty label remains provisional until
  expert review. No proof of RH is claimed.
- **Source:** further development of
  `../../3-formalized/new_scientific_knowledge/u0-topic-capstone.md` and its first-velocity object
  `u0`.
- **Statement:** Let `phi_c` be the normalized Böttcher coordinate of `f_c(z)=z^2+c` near infinity,
  so that `phi_c(f_c(z))=phi_c(z)^2` and `phi_c(z)/z -> 1`. The meromorphic germs at infinity

  `V_1(z) = partial_c phi_c(z)|_{c=0}` and
  `V_2(z) = partial_c^2 phi_c(z)|_{c=0}`

  are algebraically independent over `C(z)`.

## Goal

The formalized `u0` program isolates the first parameter velocity at the monomial fibre and proves
its independence from many nonexceptional Böttcher coordinates. The next field-level question is
intrinsic rather than comparative:

> Does the deformation of the Böttcher constraint already acquire a second algebraically new
> direction at order two?

The theorem answers yes. No algebraic curve over `C(z)` contains the velocity and acceleration of
the normalized conjugacy at `c=0`.

This is constraint-first. Both functions are obtained by differentiating the same conjugacy
constraint; no carrier, flow, finite-coefficient extrapolation, or numerical certificate enters the
argument.

## Theorem `[PROVED HERE]`

Let `phi_c` be the normalized Böttcher coordinate for `z^2+c`, jointly holomorphic in `(c,1/z)` for
`c` near zero and `z` near infinity. Define the parameter jets

`V_1(z) = partial_c phi_c(z)|_{c=0}`,

`V_2(z) = partial_c^2 phi_c(z)|_{c=0}`.

Then

`trdeg_{C(z)} C(z)(V_1,V_2) = 2`.

Equivalently, for every nonzero polynomial `P in C(z)[X,Y]`,

`P(V_1(z),V_2(z)) != 0`

as a meromorphic germ at infinity.

## Brick 1 `[SEARCH, reproved]`: the fixed constraint in the reciprocal coordinate

Put `t=1/z` and

`F(c,t) = t phi_c(1/t)`.

The usual product construction of the Böttcher coordinate converges normally for `(c,t)` in a
small bidisk. Thus `F` is jointly holomorphic there and `F(0,t)=1`. After shrinking the bidisk, take
the uniquely normalized logarithm

`L(c,t)=log F(c,t)`, with `L(0,t)=0`.

The reciprocal form of `f_c` is

`R_c(t)=1/f_c(1/t)=t^2/(1+c t^2)`.

Since

`F(c,R_c(t)) (1+c t^2) = F(c,t)^2`,

the entire deformation is fixed by the constraint

`L(c,R_c(t)) = 2L(c,t) - log(1+c t^2)`.                 (1)

Define its first two logarithmic parameter jets

`A(t)=partial_c L(0,t)`,

`B(t)=partial_c^2 L(0,t)`.

These are convergent power-series germs at `t=0`.

## Brick 2 `[PROVED]`: the first jet is a hypertranscendental Mahler function

Differentiating (1) once at `c=0` gives

`A(t^2)=2A(t)-t^2`.                                      (2)

The analytic solution with zero constant term is unique, and iteration of (2) gives

`A(t)=sum_{j>=0} 2^(-(j+1)) t^(2^(j+1))`.                (3)

In particular, `A` is not rational. One elementary proof uses only the gaps in (3): coefficients
of a rational power series satisfy an eventual constant-coefficient recurrence, whereas (3) has
arbitrarily long zero blocks followed by another nonzero coefficient.

Di Vizio--Fernandes--Mishna's order-one iterative-equation theorem now applies to

`A(t^2)=2A(t)-t^2`.

For completeness, its exceptional homogeneous equation has no nonzero algebraic solution. If an
algebraic germ `Y` satisfied

`Y(t^2)=2Y(t)`,

Newton--Puiseux gives `Y=t^v(u_0+...)`, where `v in Q` and `u_0 != 0`. Comparing valuations gives
`2v=v`, so `v=0`; comparing leading coefficients then gives `u_0=2u_0`, a contradiction. Since `A`
is not rational, the published dichotomy yields

`A is differentially transcendental over C(t)`.          (4)

Thus no nonzero polynomial over `C(t)` vanishes on any finite derivative jet of `A`.

## Brick 3 `[PROVED HERE]`: the second parameter constraint exposes the spatial derivative

At `c=0`,

`R_0(t)=t^2`, and `partial_c R_c(t)|_0=-t^4`.

Because `L(0,t)` is identically zero, the ordinary first and second `t`-derivatives of `L(0,t)`
vanish. Differentiating (1) twice in `c` therefore gives

`B(t^2)-2t^4 A'(t^2)=2B(t)+t^4`.                         (5)

Differentiating (2) in `t` gives

`A'(t^2)=A'(t)/t-1`.

Substitution into (5) produces the triangular second-velocity constraint

`B(t^2)=2B(t)+2t^3 A'(t)-t^4`.                           (6)

The crucial feature is not merely that `B` satisfies another Mahler equation. Equation (6) makes
the first spatial derivative of the preceding parameter jet recoverable from `B` and its dyadic
transform:

`t A'(t) = (B(t^2)-2B(t)+t^4)/(2t^2)`.                   (7)

## Brick 4 `[PROVED HERE]`: algebraicity of the acceleration would collapse hypertranscendence

Work in the Laurent-series field `E=C((t))`, and let

`K=C(t,A)`.

The injective endomorphism `sigma:E -> E`, `sigma(g)(t)=g(t^2)`, preserves `K` because (2) gives

`sigma(t)=t^2`, and `sigma(A)=2A-t^2`.

Suppose, for contradiction, that `B` is algebraic over `K`. Applying `sigma` to a nonzero polynomial
relation for `B` shows that `sigma(B)=B(t^2)` is algebraic over `sigma(K)`, hence over `K`. The
elements algebraic over `K` form a field, so (7) implies that `tA'(t)`, and therefore `A'(t)`, is
algebraic over `K=C(t,A)`.

Clearing denominators in a polynomial relation for `A'` over `C(t,A)` gives a nonzero algebraic
differential equation

`Q(t,A,A')=0`

over `C(t)`. This contradicts (4). Hence

`B is transcendental over C(t,A)`.                        (8)

Since (4) in particular makes `A` transcendental over `C(t)`, (8) proves

`trdeg_{C(t)} C(t)(A,B)=2`.                               (9)

## Brick 5 `[PROVED HERE]`: return to the actual Böttcher jets

Since `F=exp L` and `L(0,t)=0`,

`partial_c F(0,t)=A(t)`,

`partial_c^2 F(0,t)=B(t)+A(t)^2`.

As `phi_c(1/t)=F(c,t)/t`, this gives

`V_1(1/t)=A(t)/t`,

`V_2(1/t)=(B(t)+A(t)^2)/t`.                              (10)

The change `t=1/z`, the nonzero scaling by `t`, and the triangular replacement
`B -> B+A^2` are birational over the base field. Therefore (9) and (10) imply

`trdeg_{C(z)} C(z)(V_1,V_2)=2`.

This proves the theorem.

## What is imported and what is new

- `[SEARCH]` Joint holomorphic dependence of the normalized Böttcher coordinate near infinity is
  standard and also follows directly from its normally convergent product.
- `[SEARCH]` The order-one Mahler dichotomy used to prove (4) is imported from Lucia Di Vizio,
  Gwladys Fernandes, and Marni Mishna, *Inhomogeneous order 1 iterative functional equations with
  applications to combinatorics*, arXiv:2309.07680, especially Theorem D / Corollary 4.12.
- `[PROVED HERE]` The exact second-jet equation (6), the recovery formula (7), and the resulting
  algebraic independence of the first two parameter velocities are the new mechanism.
- `[SEARCH]` Becker--Bergweiler and later work concern hypertranscendence or algebraic geometry of a
  fixed Böttcher coordinate. They do not state the parameter-jet theorem proved here.

## Literature boundary and novelty audit

The audit searched exact and adjacent combinations of

- `Böttcher coordinate` + `second parameter derivative`;
- `Böttcher coordinate` + `parameter velocities` + `algebraic independence`;
- `infinitesimal Böttcher coordinate` + `quadratic family`;
- `Böttcher coordinate` + `variation formula` + `parameter derivative`.

The closest primary sources located were:

1. Di Vizio--Fernandes--Mishna, arXiv:2309.07680: the parent iterative-equation
   hypertranscendence theorem used for `A`;
2. Dreyfus--Hardouin--Roques, arXiv:1507.03361: general Mahler hypertranscendence, not parameter
   jets of Böttcher coordinates;
3. Saleh, arXiv:2606.24553: bialgebraic sets for fixed Böttcher coordinates, not derivatives in the
   polynomial parameter;
4. Ren, arXiv:2604.02014: coefficient and arithmetic structure of Böttcher coordinates, not
   algebraic independence of parameter jets.

No exact statement or the recovery mechanism (7) was located. This is evidence for novelty, not a
claim of exhaustive bibliographic certainty. Independent expert review remains required before the
status banner can be upgraded from candidate.

## Significance gate

The theorem is stronger than project-local novelty for three reasons.

1. It identifies a new intrinsic transcendence phenomenon in a classical holomorphic dynamical
   family: tangent and acceleration of the normalized conjugacy are already algebraically
   independent.
2. It reveals a reusable constraint mechanism. The next parameter jet contains, through dyadic
   pullback, a derivative of the previous jet; algebraicity of the new jet would create a forbidden
   finite differential handle on the old one.
3. It opens a precise higher-jet problem. The obstruction to extending the proof to all parameter
   orders is no longer vague: one must control the triangular Faà di Bruno terms and the failure of
   `C(t,A,B,...)` to be visibly stable under dyadic pullback without adjoining earlier spatial jets.

This does not prove RH and does not supply a zero-localization theorem. It advances the new HGT
branch by producing a concrete algebraically independent deformation tower at its first nontrivial
two levels.

## Lean certificate and exact remaining value

The formal tree now contains the full algebraic-independence mechanism for the Taylor-series values
`A` and `B`. In particular,

```text
formal/GaloisForLFunctions/U0/SecondVelocityJet.lean
  dyadicSubst_secondJet
  mahlerSigma_secondJet

formal/GaloisForLFunctions/U0/VelocityPairIndependence.lean
  eulerDeriv_velocity_eq
  secondJet_transcendental_over_velocity
  velocity_pair_algebraicIndependent
```

constructs both formal jets, proves the triangular Mahler constraint and recovery formula, and
proves that no nonzero two-variable polynomial over `C(t)` vanishes at their images in the graded
Mahler carrier. The targeted Lean build passes. The axiom report for both final declarations is
exactly `propext`, `Classical.choice`, and `Quot.sound`.

The positive additional value needed for stage 3 is now sharply smaller: identify these formal
series with the first two parameter derivatives of the jointly holomorphic normalized Böttcher
family. Once that analytic Taylor-identification map is present, the carrier theorem transfers the
already formalized independence statement to the actual germs `V_1,V_2`.

## Gates

- [x] 0 -> 1 in-progress: exact object, fixed constraint, attack mechanism, and literature boundary
- [x] 1 -> 2 fully-proven: complete paper proof above; no open mathematical dependency
- [ ] 2 -> 3 formalized: the formal-series independence theorem is complete; add the analytic
  parameter-jet identification for the actual normalized Böttcher family
- [ ] 3 -> 4 publication-ready: independent novelty review and standalone exposition

## Open core

`[CONJECTURE]` If

`V_m(z)=partial_c^m phi_c(z)|_{c=0}` for `m>=1`,

then every finite family `V_1,...,V_m` is algebraically independent over `C(z)`.

The present theorem is the first case not implied by the hypertranscendence of a single velocity.
At order three and above, differentiating (1) continues to expose spatial derivatives of lower
parameter jets, but the required pullback-stable base field contains mixed parameter/spatial jets.
The positive value needed for the all-orders theorem is a pullback-stable field generated by the
mixed parameter/spatial jets. The all-orders statement is not claimed here.

## Log

- 2026-07-10 — derived the reciprocal logarithmic constraint, proved the triangular second-jet
  equation, and closed algebraic independence by Mahler hypertranscendence of the first jet.
- 2026-07-10 — completed a targeted primary-literature audit; exact novelty remains provisional
  pending expert review.
- 2026-07-11 — audited current Lean truth: the complete formal-series pair theorem and recovery
  mechanism are now formalized; only the analytic identification with the actual parameter jets
  remains before stage 3.
