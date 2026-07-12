# Polygamma reflection value law

- **ID:** `polygamma-reflection-value-law`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Scientific status:** `[SEARCH] [FORMALIZATION] [NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Statement:** Every reflected polygamma pair away from the integers is exactly the corresponding
  derivative of the cotangent carrier.  In particular,
  `psi'(z)+psi'(1-z)=pi^2/sin(pi z)^2`, `psi'(1/2)=pi^2/2`, and
  `psi'(1)=pi^2/6`.

## Exact relations

For every `n : N` and `z` outside `Z`, the formalized sign convention is

```text
psi^(n)(z) - (-1)^n psi^(n)(1-z)
  = -pi D^n[cot(pi z)].                                    (1)
```

At `n=1`, differentiating the cotangent gives

```text
psi'(z)+psi'(1-z)=pi^2/sin(pi z)^2.                        (2)
```

The fixed point of reflection then gives the exact value

```text
psi'(1/2)=pi^2/2.                                          (3)
```

Combining the centre value with duplication gives

```text
psi'(1)=pi^2/6.                                            (4)
```

## Proof

The banked digamma reflection identity holds on the nonintegral locus.  Continuity of
`sin(pi z)` makes this locus a neighbourhood of every admissible point.  Equality on that
neighbourhood may therefore be differentiated `n` times.  The affine involution contributes the
factor `(-1)^n` through `iteratedDeriv_comp_const_sub`; constant multiplication extracts `-pi`.
For `n=1`, the quotient rule and `sin^2+cos^2=1` identify the derivative of `cot(pi z)` with
`-pi/sin(pi z)^2`.  Substitution of `z=1/2` proves `(3)`.  The duplication relation
`psi'(1/2)=3 psi'(1)` then proves `(4)`.

## Parent classification

`[SEARCH]` This is the classical polygamma reflection formula, recorded as NIST DLMF 5.15.6:

- https://dlmf.nist.gov/5.15.E6
- the underlying digamma reflection is DLMF 5.5.4: https://dlmf.nist.gov/5.5.E4

The relation is mathematically nontrivial and was absent from both the local tree and the pinned
mathlib checkout, but its formalization is not new scientific knowledge.

## Lean certificate

File: `formal/GaloisForLFunctions/RHTower/PolygammaReflection.lean`.

- `polygamma_reflection`: all-order reflected value law `(1)`;
- `trigamma_reflection`: exact cosecant-square law `(2)`;
- `trigamma_one_half`: exact central value `(3)`;
- `trigamma_one`: exact unit value `(4)`.

The module is imported by `GaloisForLFunctions.RHTower`.

## RHTower and parent integration audit

The relation was checked against every current `deriv Complex.digamma` and reflected-digamma
consumer in `formal/GaloisForLFunctions/RHTower` and `formal/GaloisForLFunctions`.

1. `ReflectionCocycleArchimedean.lean` needs strict comparison of trigamma values at unequal
   positive real arguments.  Its monotonicity theorem supplies that native order information;
   the reflection sum does not replace it.
2. `WindingCurvature.lean` needs a one-line vertical norm bound at real part `1/4`.  Reflection
   transports the value to the companion `3/4` line plus an exact cosecant term, but does not
   improve the existing one-sided estimate.
3. `ReflectedDigammaAnomaly.lean` studies a digamma sum whose horizontal derivative is a trigamma
   difference.  Formula `(2)` controls the complementary reflected sum, so the existing strict
   selector proof remains the stronger native statement for that object.
4. `GammaDifferentialFE.lean` supplies the off-pole smoothness and iterated-derivative algebra used
   by `(1)`.  The new theorem adds the missing reflected value API without introducing a new
   hypothesis or duplicating its recurrence and residue theorems.

Thus the current tree gains a reusable exact relation and central special value.  Existing consumers
retain their native estimates because replacing them would discard order or one-sided information;
no hypothesis-discharge or gap-closure claim is made for this relation.

## Gates

- [x] exact paper relation identified in the parent literature
- [x] local and mathlib declaration search confirms the all-order relation was absent
- [x] all-order reflected value law formalized
- [x] trigamma and central-value specializations formalized
- [x] exact unit trigamma value formalized through duplication
- [x] RHTower and parent consumer audit completed
- [x] targeted module build passes
- [x] generated indexes, axiom audit, and formal lint gate pass

The umbrella build reaches and accepts `PolygammaReflection`; its independent existing failure is
`SummableEulerCalkinInjectivity.lean`, whose rewrite, type, and heartbeat errors do not depend on
this module.  The four public reflection and special-value theorems use only `propext`,
`Classical.choice`, and
`Quot.sound`.
