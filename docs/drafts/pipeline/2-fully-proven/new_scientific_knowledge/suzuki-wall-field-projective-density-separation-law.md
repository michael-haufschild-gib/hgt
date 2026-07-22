# Suzuki wall-field projective density separation law

- **ID:** `suzuki-wall-field-projective-density-separation-law`
- **Stage:** 2 — fully proved on paper
- **Type:** REPRESENTATION CORRECTION / PROJECTIVE DENSITY WELD / FAILED LINEAR-PRODUCER SURVIVOR
- **Scientific status:** `[PAPER-PROVED] [SOURCE-SPECIFIC]`
  `[CANDIDATE NEW SCIENTIFIC KNOWLEDGE] [NOVELTY UNVERIFIED] [NOT RH]`
- **Parents:** `suzuki-critical-wall-field-square-root-weld.md`,
  `suzuki-projective-affine-secant-tensor-lift.md`
- **RH used:** no
- **Computation used:** no
- **Primary sources:** M. Suzuki, arXiv:2606.09096v1; Shamovich--Vinnikov,
  arXiv:1410.2826; Sakhnovich, arXiv:2104.12694

## Killing mechanism and representation lesson

The one-mode resolvent-dressed wall law is exact but cannot be canonical Suzuki producer by itself.
Suzuki characteristic response is projective: multiplying one source state by common nonzero
scalar cancels from normalized quotient.  Corpus already killed finite-Morse one-mode domination
for this reason.

Stronger survivor changes carrier.  Common source scaling is invisible only after division.
Division-free marked affine-secant tensor and characteristic denominator are both homogeneous
degree two.  Their common density retains wall-field square—and wall-field square is exactly
far-hinge numerator.

## Theorem A: common quadratic density `[PAPER-PROVED]`

Over a commutative ring define

```text
T_(alpha,beta)(x,X,y,Y,c)
 =(X+c)Y-(alpha+beta)xY+alpha*beta*x*y,
D_(alpha,beta)(y,Y)=(Y-beta*y)(Y-alpha*y).
```

For every scalar `omega`,

```text
T(omega*x,omega*X,omega*y,omega*Y,omega*c)=omega^2*T(x,X,y,Y,c), (1)
D(omega*y,omega*Y)=omega^2*D(y,Y).                              (2)
```

If coordinates are produced by complex-linear observations of one scaled source vector, including
homogeneous coordinate `c=K(e)`, linearity puts exactly same `omega` in all five slots, so
`(1)--(2)` apply without extra hypothesis.

### Proof

Substitute scaled coordinates.  Every monomial in `T` contains exactly two source-linear factors;
both factors of `D` are source-linear.  Factor `omega^2`.  For linear observations use
`B(omega*v)=omega B(v)`, `D(omega*v)=omega D(v)`, and `K(omega*e)=omega K(e)` first.

## Theorem B: wall field is exact projective density `[PAPER-PROVED]`

For `n=p^(e+1)`, parent square-root weld gives

```text
omega_e(t)^2
 =Lambda(n)/sqrt(n)*exp(i*t*log n)
 =:H_e(t).                                                     (3)
```

Hence

```text
T(omega_e*x,omega_e*X,omega_e*y,omega_e*Y,omega_e*c)=H_e(t)*T, (4)
D(omega_e*y,omega_e*Y)=H_e(t)*D.                               (5)
```

`H_e(t)` is exactly numerator of Xi-real far delayed-hinge atom before factor `-i/t^2`.  Universal
far-prime channel is therefore common homogeneous density of actual marked projective carrier,
not separate positive prime atom.

### Proof

Insert `omega=omega_e(t)` into `(1)--(2)` and substitute `(3)`.

## Theorem C: quotient blindness is exact and harmless before division `[PAPER-PROVED]`

For real `t`, wall field never vanishes.  Indeed `b_e^2=Lambda(n)/sqrt(n)>0`, so `b_e>0`, and its
complex exponential phase is nonzero.  Therefore whenever `D!=0`,

```text
T(omega_e*x,...,omega_e*c)/D(omega_e*y,omega_e*Y)=T/D.          (6)
```

Thus normalized quotient forgets arithmetic density exactly, while division-free determinant
line retains it exactly.  Projective cancellation does not kill far weld; it dictates where weld
must live.

## Division-free source cross law

Existing affine-secant identity plus `(4)` yields

```text
beta*omega_e(X-beta*x+c)*omega_e(Y-alpha*y)
-alpha*omega_e(X-alpha*x+c)*omega_e(Y-beta*y)
 =(beta-alpha)*H_e(t)*T_(alpha,beta)(x,X,y,Y,c).        (7)
```

This is exact common-gauge source numerator before characteristic division.

## Hostile audit

1. **Projective scaling no-go absorbed.**  Quotient is invariant as required; claim concerns its
   determinant-line density.
2. **Homogeneous coordinate scales.**  `c=K(e)` is linear in same source vector.  Independent fixed
   constants would break theorem and are excluded from source interpretation.
3. **No norm square.**  Density is complex bilinear `omega_e^2`, preserving full delay phase.
4. **No positivity.**  `H_e(t)` is complex away from zero height; `(4)--(7)` assert factorization,
   not positive Gram.
5. **Divisor retained.**  Quotient statement requires unscaled denominator nonzero.  Division-free
   laws need no such hypothesis.
6. **Endpoint regularity irrelevant.**  No pointwise deficiency trace or unbounded boundary
   evaluation is used.
7. **External collision.**  Projective homogeneity and Livšic determinantal representations are
   classical `[BRIDGE]`; audited sources do not identify Suzuki prime-power Gamma wall field with
   common affine-secant determinant density.

Verdict: `SURVIVES PRELIMINARY ATTACK`.

## Scientific consequence and open core

Failed linear view placed `omega_e` in normalized response.  Correct architecture is

```text
unscaled marked tensor/denominator geometry
   x common arithmetic density H_e(t)=omega_e(t)^2
   -> division-free Suzuki source cross numerator
   -> characteristic division only after cancellation/positivity.          (8)
```

### `SUZUKI-MARKED-TENSOR-DENSITY-WARD` `[CONJECTURE]`

Identify actual marked Robin, polar--Gamma, and holonomy completion inside unscaled tensor in
`(4)` and prove complete division-free rectangular Ward density uniformly lower bounded before
quotient.  Far-prime numerator is already supplied by common density `H_e`; it must not be added as
independent Gram channel.

First `[OPEN CORE]` is exact unscaled marked-tensor compensation identity, not spectral-measure
endpoint equality and not normalized quotient positivity.

## Novelty audit

- Degree-two scaling is elementary projective algebra `[BRIDGE]`.
- Wall-field square/far-hinge identity is parent source theorem.
- Corpus contained these separately and explicitly warned projective scaling kills linear
  producer, but did not identify far hinge as common determinant-line density surviving exactly
  before division.
- Candidate novelty is source-specific representation correction and factorization `(4)--(8)`;
  independent priority review remains required.

## Formalization gates

- [x] internal and external audit
- [x] exact paper proof and hostile review
- [ ] unconditional Lean formalization
- [ ] actual unscaled marked-tensor compensation identity
- [ ] rectangular Ward lower bound and RH
