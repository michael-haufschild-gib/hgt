# Positive quadratic source cones are convex and generating

- **ID:** qii-positive-quadratic-source-cone-geometry
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** ../1-in-progress/q-ii-source-effectivity-and-linear-degree.md
- **Statement:** A nonnegative symmetric quadratic reserve gives an additive convex source cone closed under nonnegative scaling. Every finite fibre-invariant threshold nonpositive at zero generates the whole cycle space.

## Paper proof [PROVED HERE]

Write a(x),b(x) for the two polar degrees. The source cone consists of
a,b≥0 and Q(x,x)≤2a(x)b(x). For two effective inputs x,y, positive-form
Cauchy–Schwarz gives Q(x,y)²≤Q(x,x)Q(y,y). The elementary inequality

    4 a(x)b(x)a(y)b(y) ≤ (a(x)b(y)+b(x)a(y))²

then gives Q(x,y)≤a(x)b(y)+b(x)a(y). Expanding the quadratic form proves
addition closure. Quadratic homogeneity proves nonnegative scalar closure;
zero membership and convexity follow.

For generation, no quadratic hypothesis is needed. Let Phi be finite and
fibre-invariant, with Phi(0)≤0. Given x, choose

    M=|a(x)|+|b(x)|+|Phi(x)|+1,
    z=M H+M V.

The fibre quadrant makes z effective. Both polar degrees of x+z are
nonnegative and their product dominates Phi(x), while fibre invariance
gives Phi(x+z)=Phi(x). Thus x+z is effective and x=(x+z)−z.

These statements concern the geometry of the selected effective set.
They do not provide RR or Bézout for the original intersection pairing.

## Lean certificate

Module `formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/PositiveQuadraticSourceCones.lean`:

- `PolarSurface.sourceCone_quadratic_add_closed`
- `PolarSurface.zero_mem_sourceCone_quadratic`
- `PolarSurface.smul_mem_sourceCone_quadratic`
- `PolarSurface.sourceCone_quadratic_convex`
- `PolarSurface.sourceCone_generating`

Actual-file `lake --old env lean` check passed. All five transitive axiom
audits returned only `propext`, `Classical.choice`, and `Quot.sound`.
Temporary prints removed; umbrella and README wired. Existing generic
positive-form Cauchy–Schwarz was reused. External novelty unverified.
