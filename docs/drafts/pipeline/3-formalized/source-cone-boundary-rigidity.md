# Source-cone boundary rigidity

- **ID:** source-cone-boundary-rigidity
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Parent:** [Q-II research](../1-in-progress/q-ii-source-effectivity-and-linear-degree.md)
- **Statement:** RR and Bézout on a fibre-invariant source cone require exact representation of the nonnegative intersection defect.

## Exact classification

Write `δ(x,y)=polar(x,y)-pair(x,y)`. For a nonnegative, even, fibre-invariant reserve `Φ`,
the source cone is `EΦ={x:deg_H(x)≥0,deg_V(x)≥0,Φ(x)≤2deg_H(x)deg_V(x)}`.

1. `Bezout(EΦ) ↔ ∀x y, δ(x,y)²≤Φ(x)Φ(y)`.
2. `RR(EΦ) ∧ Bezout(EΦ) ↔ ∀x, Φ(x)=δ(x,x)`.
3. The same exact-representation criterion holds for the strict source cone.
4. For the graded cone, which tests only nonnegative ample degree, Bézout itself forces
   `Φ≥0`. Consequently graded RR and Bézout are exactly `0≤Φ=δ`, even without `Φ(0)=0`.

These are unconditional classifications. Their structural hypotheses describe the source
architecture; no analytic positivity premise is assumed in their conclusions.

## Paper proof

[PROVED HERE] Translate each source to prescribed fibre degrees without changing `Φ` or `δ`.
Degrees `(Φ(x),1/2)` lie on the determinantal boundary and have square `Φ(x)-δ(x,x)`.
Bézout therefore forces `δ≤Φ`; the existing RR classification forces `Φ≤δ`. If the
inequality is strict, move the polar capacity halfway between the two values to obtain
a negative-square class strictly inside the strict cone. Exact nonnegative representation
gives Hodge index and identifies the cone with the closed positive cone.

For the mixed criterion, balanced lifts with degrees `sqrt(Φ(x)/2)` and
`sqrt(Φ(y)/2)`, applied to both signs of the second source, give
`δ(x,y)²≤Φ(x)Φ(y)`. Conversely that bound and hyperbolic AM–GM pay the mixed defect.

For signed reserves, if `Φ(x)<0`, choose degrees `(p,-p)` with `p²=-Φ(x)/2`.
This gives a graded-effective class of ample degree zero. The pure-fibre class of degrees
`(c,1)`, where `c=2+max(Φ(0),0)`, is also graded-effective. Their intersection is
`p(1-c)<0`. Thus graded Bézout forces nonnegativity, reducing to the preceding classification.

## Applications

Every nonnegative linear combination of the two fibre degrees is nonnegative on every
source cone, independently of Bézout. The zero-reserve cone satisfies Bézout exactly when
the diagonal defect vanishes identically. For an L² reserve, simultaneous RR and Bézout
require the exact identity `W(f,f)=c∫f²`, rather than any coercive lower bound.

At every positive aperture, the existing low-frequency-blind source space has a cone with
reserve half its proved coercivity constant. It satisfies RR and ampleness, and still
contains a strict negative-square class. This separates degree positivity and RR supply
from the self-inclusive Bézout axiom on the original, uncompensated surface.

## Lean certificate

Modules in `formal/GaloisForLFunctions/ArithmeticCastelnuovoSeveri/`:

- `SourceConeBoundaryRigidity.lean`:
  `PolarSurface.sourceCone_bezout_iff_defect_sq_le`,
  `PolarSurface.sourceCone_riemannRoch_and_bezout_iff`,
  `PolarSurface.strictSourceCone_riemannRoch_and_bezout_iff`,
  `PolarSurface.sourceCone_zero_bezout_iff`.
- `GradedSourceConeBoundaryRigidity.lean`:
  `PolarSurface.gradedSourceCone_bezout_iff`,
  `PolarSurface.gradedSourceCone_riemannRoch_and_bezout_iff`.
- `SourceConeBoundaryApplications.lean`:
  `lowBlind_halfCoercivity_riemannRoch_ample_and_negative_square`.

Individual `lake --old env lean` compilations succeeded. Transitive `#print axioms`
checks on the listed classification and application endpoints report only `propext`,
`Classical.choice`, and `Quot.sound`. No custom analytic axiom or placeholder occurs.

## Scope

This classifies the source-cone architecture and corrects the reversed RR/Bézout inequality
in the earlier overview. It does not prove an independent all-aperture source-payment law,
construct payment-sheaf duality, or infer Bézout for an arbitrary chosen RR cone from the
existence of some RR/Bézout cone.
