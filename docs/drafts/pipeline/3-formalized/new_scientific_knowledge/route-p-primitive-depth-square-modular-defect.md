# Route P primitive depth-square modular defect and cubic compensation

- **ID:** `route-p-primitive-depth-square-modular-defect`
- **Label:** P-G178
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) / SOURCE-SIDE CONTRACTION LAW
- **RH used:** no
- **Computation used:** no
- **Parents:** P-G173, P-G174, P-G176, P-G177

## Conjecture loop

P-G173's positive collision kernel uses both Hardy nodes `a` and `2a`.  The reflected joint-depth
audit initially suggested that the doubled copy might be only another flat diagonal gauge.  On a
primitive cell `(p,e)`, however, the arithmetic map

```text
D(p,e)=(p,2e+1)
```

squares the valuation `n=p^(e+1)` and therefore doubles its logarithmic clock exactly.  This led
to the first conjecture: realize the doubled Hardy copy by arithmetic squaring while retaining the
original resolved-von-Mangoldt amplitude.

Direct attack exposed a defect.  Since `Lambda(n^2)=Lambda(n)`, the amplitude at `n^2` is smaller
than the amplitude at `n` by `sqrt n`; coefficient preservation therefore needs modular gain

```text
g(p,e)=sqrt(p^(e+1)).
```

This gain is unbounded even on the fixed prime-two depth tower, so arithmetic squaring is not a
bounded reindexing in counting norm.  Retiring the construction here would miss the strongest
positive survivor.  Re-evaluating it in P-G174's native cubic measure gives the exact identity

```text
w(D(p,e)) g(p,e)^2 = w(p,e)/8.                         (P-G178.1)
```

Thus cubic damping does not merely make the source trace summable: it exactly compensates the
unbounded coefficient-preserving modular defect.  The failed counting-norm conjecture pivots to an
exact weighted contraction.

## Paper proof

Write `n=p^(e+1)` and

```text
w(p,e)=115/[864 (e+1)^3 p^(e+1) (log p)^2].
```

Then

```text
D(p,e)=(p,2e+1),
valuation(D(p,e))=p^(2e+2)=n^2,
log valuation(D(p,e))=2 log n.
```

The reflected holonomy depends on differences of these log clocks, so applying `D` to both
endpoints sends aperture `a` to `2a`.  The same identity holds for normalized reflected incidence.

The resolved-von-Mangoldt amplitude is `q_n=sqrt(Lambda(n)/n)`.  Using
`Lambda(n^2)=Lambda(n)` gives

```text
sqrt(n) q_(n^2)=q_n.                                    (P-G178.2)
```

Along `(2,e)`, `sqrt(2^(e+1))` tends to infinity, proving that this coefficient-preserving gain is
not bounded in counting norm.

For the cubic measure,

```text
w(D(p,e))
 =115/[864 (2e+2)^3 p^(2e+2) (log p)^2]
 =w(p,e)/(8n).
```

Multiplication by `g(p,e)^2=n` proves `(P-G178.1)`.  Therefore, for every finite primitive packet
`S` and real coefficient family `f`,

```text
sum_(pe in S) w(D pe) |g(pe) f(pe)|^2
  =(1/8) sum_(pe in S) w(pe)|f(pe)|^2.                  (P-G178.3)
```

The same identity holds on the native natural-number prime--Gamma weight after valuation pullback.
Finally, P-G173's tagged doubled node is exactly the node obtained from `D`, with the collision
ordinate retained.  Every statement is source-side and independent of Xi zeros.  `QED`

## New knowledge and anti-theatre audit

The significant new fact is the cancellation of two defects that looked incompatible in
isolation:

1. arithmetic clock dilation is exact but requires unbounded half-density gain;
2. cubic inverse-log damping loses exactly `2^3=8` under the same dilation;
3. after combining them in the native Route-P measure, the map is an exact strict contraction.

This explains structurally why P-G173 needs a doubled node and why P-G174's third logarithmic
moment is the compatible trace density.  The cubic exponent is not an arbitrary summability
device in this construction; it is the dilation degree producing the fixed `1/8` energy factor.

This is not RH and does not imply P-G176's terminal target-capacity law.  It constructs a literal
coefficient-faithful arithmetic incidence only between primitive source scales.  Remaining hard
theorem is a completed Gamma--Euler/Xi landing that carries this weighted contraction through the
P-G177 determinant-line or another genuinely two-variable pre-divisor mechanism, before zero
specialization.  Claiming target contraction from `(P-G178.3)` alone would be theatre.

## No-go closure

- **Exact killing mechanism:** coefficient preservation under `n -> n^2` needs unbounded gain
  `sqrt n`, so no bounded counting-norm relabeling can realize P-G173's doubled source copy.
- **Strongest positive survivor:** the identical map is an exact `1/8` squared-energy contraction
  in P-G174's cubic source measure.
- **New insight:** source clock and source half-density are not separately functorial under
  squaring; their modular mismatch is exactly neutralized by cubic log-moment density.
- **Status:** paper proof dependency-closed and formalized unconditionally in Lean.

## Lean certificate

Module:

```text
formal/GaloisForLFunctions/RHTower/
  RoutePPrimitiveDepthSquareModularDefect.lean
```

Main theorems:

- `xiGammaEulerValuationNat_routePPrimitiveDepthSquare`;
- `xiGammaEulerPrimitiveReflectedNormalizedIncidence_depthSquare`;
- `routePPrimitiveDepthSquareModularGain_mul_amplitude`;
- `not_bddAbove_range_routePPrimitiveDepthSquareModularGain`;
- `routePPrimitiveDepthSquare_cubicWeight_modularGain_sq`;
- `routePPrimeGammaCubicWeight_depthSquare_modularGain_sq`;
- `routePPrimitiveDepthSquare_cubicWeightedEnergy`;
- `routePCollisionDoubledNode_inr_eq_depthSquare`.

`lake env lean /tmp/pg178.lean` passed.  Only the missing leaf `.olean` was built with
`lake build GaloisForLFunctions.RHTower.RoutePPrimitiveDepthSquareModularDefect`; umbrella was not
built.  Capstone axiom audit reports only `propext`, `Classical.choice`, and `Quot.sound`.
Forbidden-token scan is clean.  Umbrella import is wired.

## Next gate

Construct a source-pure two-variable or determinant-line landing for which P-G178's weighted
depth-square map is the causal-to-polar block and prove that its conormal cubic form is P-G173's
collision Gram.  The landing must be defined from Gamma--Euler data and analytic continuation,
not from Xi divisor copies or P-G176 capacity.
