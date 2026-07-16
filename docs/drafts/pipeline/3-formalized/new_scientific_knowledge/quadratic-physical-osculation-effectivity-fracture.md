# Quadratic physical osculation and source effectivity form independent obstruction axes

- **ID:** `quadratic-physical-osculation-effectivity-fracture`
- **Stage:** 3-formalized
- **Type:** PHYSICAL-CHARACTER CONTACT LAW / UNIFIED-OBJECT DISCRIMINATOR
- **Scientific status:** `[PROVED] [LEAN-FORMALIZED] [CANDIDATE NEW HT STRUCTURE]`
  `[NOVELTY UNVERIFIED] [NOT AN RH RESULT]`
- **Lean:**
  - `formal/GaloisForLFunctions/HTGeometry/QuadraticPhysicalCharacterOsculation.lean`
  - `formal/GaloisForLFunctions/HTGeometry/PhysicalOsculationEffectivityFracture.lean`
  - `formal/GaloisForLFunctions/HTGeometry/PeriodIncidenceUniformEffectivity.lean`
- **Unified parent:**
  `../../1-in-progress/hypertranscendental-source-fracture-hypercube.md`

## Quadratic osculation phase law `[PROVED]`

For source weights `a,b,c,d in C`, put

```text
F_(a,b;c,d)(lambda)
  =(exp(a lambda)-1)(exp(b lambda)-1)
   -(exp(c lambda)-1)(exp(d lambda)-1).                    (1)
```

Lean proves the complete jet formula

```text
F^(n)(0)
  =(a+b)^n-a^n-b^n-(c+d)^n+c^n+d^n.                       (2)
```

In particular,

```text
F(0)=F'(0)=0,
F''(0)=2(ab-cd).                                          (3)
```

Therefore

```text
ab != cd  -> ord_0 F=2.                                   (4)
```

If `ab=cd`, then

```text
F'''(0)=3ab(a+b-c-d).                                     (5)
```

Consequently

```text
ab=cd, ab!=0, a+b!=c+d  -> ord_0 F=3.                     (6)
```

Equations `(4)` and `(6)` are an exact two-phase law.  Equality of tangent products cancels the
source-height-two jet.  The next symmetric datum, the pair sum, measures the curvature mismatch
and forces tangency excess one.

## Hankel-conic realization `[PROVED]`

Take the rank-three source vector

```text
tau_alpha=(1,alpha,alpha^2)                                (7)
```

and the Hankel relation

```text
P(x_0,x_1,x_2)=x_1^2-x_0 x_2.                             (8)
```

The tangent vector `(7)` lies on `(8)`, while its physical exponential arc has pullback

```text
P(exp(lambda)-1, exp(alpha lambda)-1, exp(alpha^2 lambda)-1).
```

Lean proves

```text
d^j/dlambda^j|_0 =0,                 j=0,1,2,
d^3/dlambda^3|_0 =-3 alpha^2(alpha-1)^2.                  (9)
```

Hence for `alpha!=0,1` the contact order is exactly three.  The algebraic source height is two, so
the physical tangency excess is exactly one.

If `(1,alpha,alpha^2)` is linearly independent over `Q`, then the same conclusion holds while the
integral period group has rank three inside the real plane `C`.

## Osculation/effectivity fracture `[PROVED]`

On the same rank-three source, consider also the quadratic binomial with pairs

```text
(1,alpha) and (alpha^2,1).                                (10)
```

Rational independence forces `alpha!=0,1`, hence `alpha!=alpha^2`.  By `(4)`, its physical contact
order is exactly two.  By `(6)`--`(9)`, the Hankel constraint on the same source has contact order
three.  The uniform-effectivity phase law independently gives

```text
period-incidence has a continuous left inverse
  <-> the embedded integral period group is discrete.     (11)
```

The rank-three source in `(7)` is nondiscrete, so it has no continuous global incidence inverse.
Lean packages the exact witness

```text
one source;
contact order 2 for one quadratic constraint;
contact order 3 for another quadratic constraint;
no continuous global period-incidence inverse.            (12)
```

Thus global effectivity does not determine physical osculation.  The nonclosed-range obstruction
and the tangency-excess obstruction can coexist, but neither is a function of the other.

## Anti-theatre verdict

```text
[NO-GO]
All recurring obstruction chains are shadows of one scalar defect, one interval, or one
unfiltered derived object.
```

The theorem `(12)` falsifies that compression already in the smallest rank-three chart.  Holding
the complete embedded period source fixed leaves the global effectivity phase fixed while the
physical contact order changes.

```text
[POSITIVE]
The minimal conservative unified object is at least bifiltered:

  global source-effectivity phase  x  local physical-osculation filtration.       (13)
```

This is not a demand to add two unrelated decorations.  Both axes are forced by the same source
character map: effectivity asks whether its complete integral family has a bounded lift;
osculation asks how its analytic arc meets the source constraint ideal.  Equation `(12)` proves
that a conservative realization must retain their interaction without identifying them.

Osculation is still not conservative for orientation.  The separately formalized reversal law
shows that balanced even-rank sources can have identical complete physical defect germs after full
orientation reversal.  Thus the bifiltration `(13)` lives over a source orientation/anomaly lift;
it cannot replace that lift.  See `physical-defect-orientation-anomaly.md`.

## Bold next conjecture

> **[CONJECTURE -- NORMALIZED SOURCE OSCULATION/EFFECTIVITY REES PRINCIPLE.]**  Every
> source-effectively normalized constrained hypertranscendental system carries a
> presentation-invariant bifiltered incidence
> object `R_F^(p,q)`.  The `p` filtration is the physical arc-contact filtration of the source
> constraint ideal.  The `q` filtration is the critical bornological effectivity filtration of the
> embedded integral source.  Continuation, spectral completeness, positivity, monodromy, and
> boundary-condition obstructions are conservative realization defects of different bidegrees.
> A source producer resolves an obstruction only when its reporter family kills the normalized
> joint-fixed gauge and produces the distinguished polarized section in the required bidegree, not
> by proving a criterion on one marginal filtration.

The normalization qualifier is essential.  The Gamma periodic-gauge collision proves that a bare
source constraint plus any fixed finite pointing does not canonically determine its HT germ.

The conjecture is falsified if a natural HT family has two constraints with different physical
contact order but every jointly conservative realization identifies their obstruction classes, or
if the effectivity filtration can be reconstructed functorially from contact order alone.

For a future zeta realization, the critical zeros would be the self-dual degeneracy support of the
distinguished section of this bifiltered object.  This is a research hypothesis, not an RH result.

## Where to look next

1. **All-degree binomial law.**  For multisets `A,B` of equal cardinality, classify the contact
   order of
   `prod_(a in A)(exp(a lambda)-1)-prod_(b in B)(exp(b lambda)-1)` by the first unmatched symmetric
   moment.  The quadratic theorem predicts a Stirling/Bell-polynomial jet tower.
2. **Presentation invariance.**  Define the physical arc valuation on a source constraint ideal,
   not on a chosen generator, and build its Rees object.
3. **Interaction morphism.**  Construct a presentation-invariant map from the osculation Rees
   filtration to the powered period-incidence filtration on a normalized stratum.  Its failure to
   be strict is the first candidate interaction class linking local degeneracy to global
   nonattainment.
4. **Natural positive-tangency HT source.**  The conic source is an exact source-geometric model,
   and the universal realization machinery can engineer it.  Find it in a natural Barnes,
   multiple-sine, theta/Fay, or other special-function source before claiming universality.
5. **Second independent family.**  Compare two natural HT families with the same contact order but
   different effectivity germ, and two with the same effectivity phase but different contact
   order.  This is the minimal conservativity test for `(13)`.

## External novelty boundary

Orders of contact along arcs, contact loci, arc valuations, toric arc spaces, rational normal
curves, and Hankel determinantal ideals are parent mathematics.  The derivative formulas
`(2)`--`(6)` are elementary once the correct physical pullback is written down and are not by
themselves claimed as Fields-scale novelty.

Primary adjacent sources include Ein--Lazarsfeld--Mustaţă on contact loci
(`https://arxiv.org/abs/math/0303268`), Ishii on toric arc spaces
(`https://arxiv.org/abs/math/0312324`), and Conca--Mostafazadehfard--Singh--Varbaro on Hankel
determinantal rings and rational normal curves (`https://arxiv.org/abs/1709.05685`).

The candidate-new content is the exact HT source fracture `(12)` and the forced bifiltered
architecture `(13)`: arithmetic/topological effectivity and complex-analytic osculation are two
independent conservative axes of one source-character object.  Targeted searches found the parent
axes but no theorem coupling them in hypertranscendental source geometry.  This is negative search
evidence, not priority certification.  Fields-scale significance requires the interaction
morphism in item 3 and a natural HT realization in item 4.

## Lean certificate

Lean proves unconditionally:

- the complete derivative tower `(2)`;
- the exact contact-order phase law `(4)` and `(6)`;
- the conic cubic coefficient and exact order three;
- the rank-three rational-independence corollary;
- a transverse order-two constraint on the same source;
- the combined osculation/effectivity fracture witness `(12)`;
- uniform continuous source effectivity iff period discreteness.

The two exact-module builds and both direct touched-file checks pass.  No full build was run.

## Gates

- [x] positive tangency excess constructed exactly
- [x] no-go paired with a stronger positive structure
- [x] quadratic phase law proved for a family, not one numerical example
- [x] same-source effectivity/contact independence proved
- [x] Lean formalization unconditional
- [x] adjacent arc-space and Hankel parent theories separated
- [x] RH kept as a downstream pressure test
- [ ] all-degree symmetric-moment contact theorem proved
- [ ] ideal-level Rees filtration constructed
- [ ] normalized presentation-invariant interaction morphism constructed
- [ ] natural HT special-function realization found
- [ ] exact external priority audit completed
