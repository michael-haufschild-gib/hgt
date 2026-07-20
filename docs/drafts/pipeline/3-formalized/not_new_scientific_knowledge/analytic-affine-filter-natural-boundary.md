# Analytic affine filters preserve natural boundaries

- **ID:** `analytic-affine-filter-natural-boundary`
- **Stage:** 3-formalized/not-new-scientific-knowledge
- **Type:** `[BRIDGE] [SIGNAL PROCESSING] [SOURCE EXTRACTION]`
- **Parent:** `../../2-fully-proven/needs-audit/electrical-optical-law-application-census.md`
- **Lean:** `formal/GaloisForLFunctions/U0/AnalyticAffineFilterNaturalBoundary.lean`

## Theorem

Let `f : C -> C` fail to continue analytically across `z0` from a domain `D`.  If `a` and `b` are
analytic at `z0` and `a(z0) != 0`, then the analytically affine-filtered signal

```text
g(z) = a(z) f(z) + b(z)
```

also fails to continue across `z0` from `D`.

Consequently, if `a` and `b` are analytic at every point of the unit circle and `a` is nowhere zero
there, then `a*u0+b` has the same complete unit-circle natural boundary as the dyadic Mahler source
`u0`.  A finite rational transfer function with no pole or zero on the unit circle is a special case.

## Proof

Suppose `g` had an analytic continuation `G` at `z0`.  Since `a(z0) != 0`, continuity makes `a`
nonzero on a smaller neighbourhood.  Then

```text
F = (G-b)/a
```

is analytic at `z0` and agrees with `f` on the `D`-side neighbourhood, contradicting the assumed
continuation obstruction.  Applying this pointwise to the compiler-checked theorem
`u0_natural_boundary` gives the global unit-circle result.

## What this closes

The electrical/optical census previously said only that finite filters were too small to manufacture
an HT or natural-boundary source.  The theorem gives the exact unconditional converse needed by the
corpus: whenever the output of a locally invertible analytic affine filter has a natural boundary,
that obstruction comes from its input, and filtering `u0` cannot erase it.

## Novelty and limitation

This is a reusable formal bridge and a stronger corpus statement, not new scientific knowledge.
It is an elementary analytic-inversion argument.  It neither constructs a physical circuit nor says
that non-invertible, active, nonlinear, or genuinely infinite/cofinal filters preserve the boundary.

## Formal declarations

- `U0.continuesAcross_of_continuesAcross_analyticAffine`
- `U0.not_continuesAcross_analyticAffine_of_not_continuesAcross`
- `U0.u0_analyticAffineFilter_naturalBoundary`

