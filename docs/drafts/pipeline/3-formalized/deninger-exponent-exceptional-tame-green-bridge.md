# Deninger exponent-exceptional tame Green bridge

- **ID:** `deninger-exponent-exceptional-tame-green-bridge`
- **Stage:** 3-formalized
- **Type:** THEOREM / SOURCE CONSTRUCTION / SINGULAR TRANSPORT
- **Scientific status:** `[PROVED HERE] [FORMALIZED] [NEW CORPUS-SPECIFIC CONJUNCTION]`
- **Route:** L
- **Statement:** The literal exponent deformation `zeta(s)/zeta(zs)` has, at every
  multiplicity-exact Xi divisor point, an exceptional fibre whose reflected pole displacement is
  the completed-Xi Green fracture.  The constant-leg Milnor tame boundary on its two marked pole
  sections is `(-m,m)` at grade `6^m`, and the Deninger horizontal character reads it as the
  actual degree-`6^m` Gamma/Burnol/BV radial coefficient.  Both the Green displacement and the
  physical tame readout land coefficient-faithfully in completed Calderon--Witt incidence.

## Goal

Construct the source object and singular principal-symbol comparison which Route L had previously
described only as a place-marked Rost--Schmid requirement.  The theorem must precede any
critical-line specialization, retain reflected pole sections as ordered branches, use the actual
Xi multiplicity, recover the already fixed physical Gamma-six coefficient rather than a fitted
zero-equivalent scalar, and map it into the existing completed incidence carrier.

This card does **not** assert fixed-reader cyclicity.  It removes construction and local
principal-symbol ambiguity from the remaining RH-bearing theorem.

## Exact theorem

Define

```text
E(z,s) = zeta(s) / zeta(zs).
```

For an Xi divisor support point `rho`, let `d(rho)` be the analytic order of zeta at `rho`; this is
the completed-Xi divisor multiplicity.  In the two-variable blow-up chart

```text
z = 1+t,
s = rho+t w,
```

one has the exact identities

```text
s-rho  = t w,
zs-rho = t(w+rho+t w).                                  (EET.1)
```

For every regular projective direction `w != 0,-rho`,

```text
lim_(t->0, t!=0) E(1+t,rho+t w)
  = (w/(w+rho))^d(rho).                                 (EET.2)
```

The raw exceptional profile has a zero of positive order at `w=0`, a marked pole section at
`w=-rho`, and unit value in its reciprocal chart at the physical endpoint `w=infinity`.

Let

```text
rho# = 1-conj(rho),
p(rho)  = -rho,
p(rho#) = -rho#.
```

Then

```text
p(rho#)-p(rho)
  = rho-rho#
  = 2 Re(rho)-1
  = xiNearbyPoleDualityAdjunctionFracture(rho).          (EET.3)
```

Retain the two possibly coincident sections as marked branches and put

```text
f_rho(w) = (w+rho)/(w+rho#).
```

Its marked divisor orders are `+1` on the source branch and `-1` on the reflected branch.  For
the constant-leg Milnor symbol `{f_rho,6^m}`, the constant-leg tame formula

```text
partial_v {f,c} = c^(-v(f))
```

therefore gives

```text
source tame exponent    = -m,
reflected tame exponent =  m.                           (EET.4)
```

The product of the two local tame units is one.  This is multiplicative reciprocity only.

Let

```text
g_6(s) = exp((2 Re(s)-1) log 6)
chi_s(k) = g_6(s)^k.
```

The oriented marked-tame reader is

```text
T_m(s) = chi_s(m)-chi_s(-m)
       = g_6(s)^m-g_6(s)^(-m)
       = deningerTensorSquareRadialMateCurvature(6^m,s). (EET.5)
```

At `m=1`, the actual ordered `(2,3)` Gamma/Calderon--Witt boundary coefficient is

```text
positive Gamma calibration * T_1(rho).                  (EET.6)
```

Finally, finite-support completed-Xi vectors carrying either side of `(EET.3)` or `(EET.5)` map
through the existing completed Xi-to-Calderon--Witt isometry.  Decoding at `rho` gives respectively

```text
Green fracture * fixed nonzero incidence witness,
degree-6^m mate curvature * fixed nonzero incidence witness.              (EET.7)
```

Thus the construction loses neither coefficient nor divisor copy.

## Proof

### 1. Actual multiplicity factorization

Every Xi divisor support point lies in `0 < Re(rho) < 1`, hence is not the zeta pole.  Zeta is
analytic there and is not identically zero in any neighbourhood.  Finiteness of its analytic
order and the analytic-order factorization theorem give a germ `u` such that

```text
zeta(s) = (s-rho)^d u(s),
u(rho) != 0.
```

The completed-Xi/zeta order comparison identifies this `d` with the actual Xi support
multiplicity.

### 2. Exponent blow-up

Substitution gives `(EET.1)` by ring algebra.  On a punctured neighbourhood of `t=0`, local
factorization at both source and target yields

```text
E(1+t,rho+t w)
 = ((t w)/(t(w+rho+t w)))^d
     u(rho+t w)/u(rho+t(w+rho+t w))
 = (w/(w+rho+t w))^d
     u(rho+t w)/u(rho+t(w+rho+t w)).
```

The regular-direction conditions make the cancellation legitimate.  Continuity and
`u(rho)!=0` send the cofactor ratio to one, proving `(EET.2)`.  The zero, pole-denominator, and
infinity-chart assertions are direct evaluations; positivity of `d` is the Xi divisor
multiplicity theorem.

### 3. Reflected pole transport

Critical-line reflection is `rho#=1-conj(rho)`.  Subtracting the two marked pole sections gives

```text
-rho#-(-rho)=rho+conj(rho)-1=2 Re(rho)-1.
```

The existing completed-Xi nearby-pole theorem identifies the last scalar with the Green
fracture, proving `(EET.3)`.

### 4. Tame boundary and reciprocity

At the numerator branch, `v(f_rho)=1`; at the denominator branch, `v(f_rho)=-1`.  Since the
constant leg has valuation zero, the tame formula reduces to `c^(-v(f))`.  With `c=6^m`, this is
exactly `(EET.4)`.  Adding the two exponents gives zero, so the product of local tame units is one.
No additive oriented difference vanishes by this argument.

### 5. Physical readout

The Deninger gain is multiplicative in ordinary integer degree.  Induction gives

```text
deningerHalfDensityMateGain(6^m,s)=g_6(s)^m.
```

Reading the reflected slot minus the source slot therefore yields `(EET.5)`.  The existing exact
Gamma/Deninger comparison gives `(EET.6)`.  Applying the already constructed completed
Xi-to-incidence isometry to a one-coordinate Xi vector proves `(EET.7)`.

## Conjecture/failure loop

### C1 — exponent depth itself generates completed Xi

**Failed previously.**  The source-normal-cone conservation law proves exponent arithmetic and
archimedean completion are independent.  This card never claims otherwise: Xi supplies the
actual divisor centre, reflection, and completion; exponent deformation supplies the singular
normal chart.

### C2 — use only the shell-first or divisor-first limit

**Failed.**  The two limits disagree and do not define a continuous corner.  Blow-up retains the
projective direction and produces the nonconstant exceptional profile `(EET.2)`.

### C3 — identify the exceptional pole but discard its reflection label

**Failed.**  Codiagonalization erases the horizontal displacement.  Retaining two marked sections
before scalarization produces `(EET.3)`.

### C4 — tame reciprocity annihilates the Gamma coefficient

**Failed sharply.**  Reciprocity proves product one, while the physical reader is the additive
oriented difference `chi_s(m)-chi_s(-m)`.  It is nonzero off the critical line.

### C5 — the marked tame packet merely has the same zero set as Gamma

**Failed as too weak.**  Multiplicativity of the actual Deninger gain proves exact equality with
the degree-`6^m` mate curvature, and the existing positive calibration identifies the literal
Gamma coefficient.

### C6 — local coefficient comparison is already strict Route-L descent

**Failed.**  The one-coordinate incidence landing does not prove that the full corrected shell
operator, including its trace-class remainder, is transported by a strict chain map.  Nor does it
prove fixed-reader cyclicity.  These are the surviving hard theorems.

## Frontier gain

Before this theorem, Route L's open square asked simultaneously for:

1. a concrete pre-specialization singular source object;
2. its reflected pole transport;
3. a principal-symbol realization of `[6^m]-[6^(-m)]`;
4. comparison with the actual Gamma/Burnol/BV coefficient;
5. a coefficient-faithful completed incidence landing;
6. strict trace-ideal transport and fixed-reader cyclicity.

Items 1--5 are now closed, with unconditional Lean proofs.  Remaining open core is item 6:

```text
lift the exceptional marked-tame principal-symbol comparison from one local divisor coefficient
to the complete shell-amplified corrected source modulo trace class; prove the lift preserves both
critical-edge slots and makes the already fixed physical reader cyclic on its chain boundary.
```

This is narrower than the former generic “construct a Rost--Schmid/Meyer comparison” frontier.

## Hostile audit

- No RH statement, critical-line hypothesis, Stokes annihilation, or new axiom occurs.
- Regular directions are the honest domain of the rational exceptional profile; they are encoded
  as a subtype, not inferred from RH.
- Xi multiplicity is used exactly; no simple-zero assumption occurs.
- Source and reflected sections remain marked even when their supports coincide.
- Tame reciprocity is recorded separately from the additive physical reader.
- The completed incidence map is the pre-existing isometry; no target quotient is defined by the
  desired kernel.
- The result does not claim the full shell weak-trace class is in the strict chain-map domain.
- The result does not claim fixed-reader cyclicity; that assertion remains RH-bearing.

## Novelty audit

- `[CORPUS]` Analytic local factorization of zeta, additive activation blow-up, Xi reflection and
  multiplicity, Deninger mate curvature, Gamma calibration, and completed incidence isometry.
- `[PROVED HERE]` Exact multiplicative-exponent chart `(EET.1)--(EET.2)` at actual Xi
  multiplicity; reflected exceptional-pole/Green identity `(EET.3)`; marked constant-leg tame
  packet `(EET.4)`; exact all-grade physical comparison `(EET.5)`; and their completed incidence
  landings `(EET.7)` as one dependency-closed chain.
- `[NOVELTY UNVERIFIED]` No broad literature-priority claim is made.  The closest located parent
  theme is Kaad--Nest's operator-theoretic realization of the Tate tame symbol
  (`arXiv:1408.3851`); no source located in the targeted search contained this exponent blow-up,
  reflected Xi pole displacement, Gamma-six tame readout, and Calderon--Witt landing conjunction.

## Lean surface

Module:
`formal/GaloisForLFunctions/RHTower/DeningerExponentExceptionalTameGreenBridge.lean`

Main declarations:

- `deningerExponentCollisionTarget_sub`
- `deningerExponentExceptionalOrder_eq_xiSupportMultiplicity`
- `exists_riemannZeta_xiConormalFactorization`
- `tendsto_deningerExponentDeformationActivation_exceptionalProfile`
- `deningerExponentExceptionalRawProfile_zero`
- `deningerExponentExceptionalInfinityChart_zero`
- `deningerExponentExceptionalPole_displacement_eq_greenFracture`
- `deningerGammaSixExceptionalTameExponent_source`
- `deningerGammaSixExceptionalTameExponent_reflected`
- `deningerGammaSixExceptionalTameUnit_product`
- `deningerHalfDensityMateGain_six_pow`
- `deningerGammaSixExceptionalTameReader_eq_mateCurvature`
- `deningerCalderonWittBaseGammaBoundaryDefectCoefficient_eq_exceptionalTameReader`
- `deningerExponentExceptionalGreenIncidence_sourceValue`
- `deningerGammaSixExceptionalTameIncidence_sourceValue`

## Gates

- [x] 0 -> 1: hard source frontier isolated; failed-route audit completed
- [x] 1 -> 2: dependency-closed paper proof and hostile audit
- [x] 2 -> 3: unconditional Lean module; no `sorry`, `admit`, `axiom`, `opaque`, or `unsafe`
- [x] direct `lake env lean` check
- [x] wired into `GaloisForLFunctions.RHTower`
- [x] axiom audit: only `propext`, `Classical.choice`, `Quot.sound`
- [x] targeted `lake build GaloisForLFunctions.RHTower.DeningerExponentExceptionalTameGreenBridge`
- [ ] repository lint audit
- [ ] 3 -> 4: standalone external exposition and external novelty review

## Log

- 2026-08-11 — Derived the multiplicative exponent collision and exceptional profile; rejected
  shell-first/divisor-first scalar limits.
- 2026-08-11 — Identified reflected exceptional pole displacement with completed-Xi Green
  fracture and the two marked tame branches with exponents `(-m,m)`.
- 2026-08-11 — Proved exact Gamma-six/all-grade Deninger readout and completed Calderon--Witt
  incidence landings.
- 2026-08-11 — Formalized the full dependency-closed chain in Lean; direct check, targeted build,
  and axiom audit passed.
