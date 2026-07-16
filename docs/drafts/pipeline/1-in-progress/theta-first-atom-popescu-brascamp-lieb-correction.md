# Theta first atom: Popescu corrected Brascamp--Lieb certificate

- **ID:** `theta-first-atom-popescu-brascamp-lieb-correction`
- **Stage:** 1-in-progress
- **Type:** `[PHYSICS-TRANSFER] [SOURCE-SPECIFIC] [RH-DOWNSTREAM]`
- **Parent:** `theta-first-atom-variable-curvature-brascamp-lieb.md`
- **Primary source:** I. Popescu, *A refinement of the Brascamp--Lieb--Poincare inequality in one
  dimension*, arXiv:1311.4118.

## Live mechanism

For a probability density `exp(-V)` on the line, write `h=V''`.  Popescu's first correction to
Brascamp--Lieb is

```text
Var(f)
 <= integral (f')^2 / h
    - integral (D(h^(-1) f'))^2 / (1 + A(h^(-1))),        (PBL)
```

provided `h>0` and `1+A(h^(-1))>0`, where

```text
A(E) = (2 E'' + 2 V' E' - (E')^2/E + 4 E V'') / 4.
```

The correction is a nonnegative Witten-resolvent value.  It vanishes only when
`D(h^(-1)f')=0`, the equality family already identified in the source.

For the first theta atom and `f(x)=x^2`, `(PBL)` strictly strengthens the variable-curvature
target:

```text
a_0 a_2-a_1^2
 <= 4 a_0 J - a_0 C,

J = integral x^2 / V'' dnu,
C = integral (D(2x/V''))^2 / (1+A(1/V'')) dnu.          (TC)
```

Consequently the corrected certificate

```text
64 c^2 a_0 J - 16 c^2 a_0 C
  <= (45-16 c^2) a_1^2,                                 (PCert)
```

with `c=3005/2997`, implies the relaxed first-atom gate

```text
16 c^2 a_0 a_2 <= 45 a_1^2.
```

This is strictly weaker than the uncorrected `Jcert`: the source itself supplies `C>=0`.

## Algebraic positivity condition

Popescu proves that `1+A(1/V'')>0` is equivalent to

```text
N_V = 3(V''')^2 + 8(V'')^3
      - 2 V'''' V'' - 2 V''' V'' V' > 0.                (N)
```

For the theta Born--Witten density, put

```text
q = pi*n^2*exp(2x)-3/2,
r = 2q+3.
```

The exact logarithmic derivatives are

```text
V'    = 2q-3/2-3/q,
V''   = r*(2+3/q^2),
V'''  = r*(4-6/q^2-18/q^3),
V'''' = r*(8+12/q^2+108/q^3+162/q^4).
```

Direct algebra gives

```text
q^6 N_V = r^2 * P(q),

P(q) = 96q^7+232q^6+624q^5+768q^4-36q^3
       +630q^2+162q+324.
```

On the theta half-line `q>3/2`; hence

```text
768q^4-36q^3 = q^3(768q-36)>0,
```

and every remaining term in `P` is positive.  Thus `(N)` holds strictly for every positive theta
atom.  This is an unconditional source fact, not an additional hypothesis.

## Why this advances the corpus

The failed uniform-curvature route retained only `V''>=19`.  The variable-curvature route retained
`1/V''` but still discarded the positive resolvent remainder in `(PBL)`.  The corrected route keeps
both source values.  It therefore weakens the only open first-atom certificate without changing
the existing Hankel consumer.

The general algebraic correction interface belongs in `HTGeometry`; the theta derivative chain
and strict positivity proof belong in `RHTower`.

## Formalized surface

- `formal/GaloisForLFunctions/HTGeometry/OneDimBrascampLiebCorrection.lean` proves the exact
  inverse-curvature jet reduction, positivity equivalences for both correction weights, the
  nonnegativity and strict-improvement relations, and the corrected quadratic-certificate
  transfer theorem.
- `formal/GaloisForLFunctions/RHTower/PrimeArchThetaBornWittenPopescuCorrection.lean` proves the
  third- and fourth-derivative profiles, the cleared polynomial identity, strict positivity of
  `N_V`, and strict positivity of both Popescu correction weights for every positive theta atom.
- The new module is imported through the existing two-channel virial/Rayleigh route, so the
  correction values are available to its current RH consumer without changing that consumer.

## Open analytic core

1. Formalize the half-line version of `(PBL)`, including the endpoint current and exhaustion.
2. Instantiate `f=x^2` and define the correction value `C`.
3. Prove `(PCert)` from the exact theta profiles, Ward relations, or the supersymmetric resolvent.
4. Feed the resulting relaxed first-atom gate to the existing degree-one theta Hankel consumer.

The independent upper radial-ratio hypothesis remains open.

## Gates

- [x] primary correction theorem identified
- [x] exact theta positivity condition derived on paper
- [x] generic correction algebra formalized in HTGeometry
- [x] theta derivative profiles and positivity condition formalized in RHTower
- [ ] half-line corrected Brascamp--Lieb theorem formalized
- [ ] corrected theta certificate proved
- [ ] relaxed first-atom gate discharged
