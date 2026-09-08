# Local geometric interpolation at the Selberg quarter value

- **ID:** SELBERG-LOCAL-GEOMETRIC-INTERPOLATION
- **Stage:** 3-formalized
- **Parent:** [Constructive conjecturing loop](../1-in-progress/selberg-quarter-conjecturing-loop.md)
- **Scope:** Explicit local hyperbolic fields. This is not the all-congruence Selberg theorem.

## Exact statement

For every real `a` and every upper-half-plane point `z=x+iy`, put

`G_a(z)=exp((log y)/2 - (a/2)*log(x^2+y^2))`.

With the positive hyperbolic Laplacian `Delta=-y^2*(partial_x^2+partial_y^2)`,

`Delta G_a = (1/4 + a*(1-a)*y^2/(x^2+y^2))*G_a`.

The endpoint fields `G_0,G_1` satisfy the repository's actual smooth `IsMaassEigenfunction (1/4)` predicate. This predicate includes smoothness and the eigen-equation, not automorphy or cuspidality. The symmetric field satisfies `G_(1/2)^2=G_0*G_1` and the strict pointwise inequality `Delta G_(1/2) > G_(1/2)/4` everywhere.

For every natural `n`,

`G_(1/2)((n+1)+i) < G_(1/2)(i)=1`.

Thus every positive integer translation changes this local supersolution. Translation invariance is a real missing condition in applying its positive correction to automorphic fields.

## Dependency-closed paper proof

Writing `D=x^2+y^2`, the logarithmic derivatives are `-a*x/D` and `1/(2*y)-a*y/D`. Differentiating once more gives

`partial_xx(log G_a)+partial_yy(log G_a)=-1/(2*y^2)`.

The sum of their squares is `1/(4*y^2)+(a^2-a)/D`. The exponential chain rule yields the displayed Laplacian identity. Positivity follows from the real exponential; `y>0` makes all denominators positive. Substituting `a=1/2` gives the strict positive correction. Substituting the two stated points yields the translation inequality because `log((n+1)^2+1)>0`.

## Lean implementation and verification

Module: `GaloisForLFunctions.RHTower.SelbergGeometricBlend`.

The implementation derives actual real Frechet derivatives, transports them through `UpperHalfPlane.ofComplex` using equality on a neighborhood, and invokes the exact `positiveHyperbolicLaplacian` definition from the Maass correspondence. The gradient and differential equation are proved, not supplied as structure fields or assumed hypotheses.

Public capstones include `positiveHyperbolicLaplacian_field`, `field_smooth`, `half_strict_quarter`, `half_sq_eq_endpoints`, `half_translatedBasePoint_ne`, and both endpoint eigenfunction theorems.

- Foreground scratch and direct module checks passed without warnings.
- `lake build GaloisForLFunctions.RHTower.SelbergGeometricBlend` passed; only the new target was rebuilt. No umbrella build ran.
- The module is imported by the `RHTower` umbrella.
- Five scratch `#print axioms` checks report only `propext`, `Classical.choice`, and `Quot.sound`.
- No numerical experiment or computational certificate was used.
- Formal lint passed, with existing large-file warnings elsewhere in the corpus.

## Insight carried forward

Geometric interpolation creates an explicit positive local potential, while the translation test prevents silently treating that local gain as an automorphic gap. The next construction must preserve useful disagreement between the local logarithmic gradients while satisfying the group action. The parent loop records the next conjecture and its proof attempt.
