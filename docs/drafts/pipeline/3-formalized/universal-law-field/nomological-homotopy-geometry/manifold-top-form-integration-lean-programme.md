# Lean programme: integration of top forms on closed oriented manifolds

- **Stage:** 3 — formalized (programme complete; consumer card promoted)
- **Consumer:** ULF row 63 —
  `2-fully-proven/universal-law-field/nomological-homotopy-geometry/length-three-partial-flattening-holonomy-spectrum-recurrence-and-properness-law.md`
- **Base:** vendored `DifferentialGeometry` (forms `DifferentialForm IM M k` as smooth sections,
  wedge, `exteriorDerivative` with `d² = 0` and pullback naturality, `ManifoldOrientation`,
  `chartAtlasPOU`); mathlib `extDeriv`, change of variables, integration by parts.
- **Missing (to build):** the oriented integral of a top form, its locality/independence, Stokes on
  closed manifolds, Fubini on products, product orientation.

## Module plan (formal/GaloisForLFunctions/HTGeometry/)

| # | Module | Content | Status |
|-|-|-|-|
| 1 | `EuclideanCompactStokes` | `∫ (dF)(v) dμ = 0` for compactly supported `C¹` forms on a finite-dim space, any Haar `μ` |DONE |
| 2 | `TopFormDeterminantScaling` | `f(L∘b) = det L · f(b)` for top alternating maps; orientation sign vs `det`; change of variables of top-form densities between open sets |DONE |
| 3 | `ManifoldTopFormIntegral` | chart sign of an orientation; `∫_M ω` via `chartAtlasPOU`; linearity; locality (support in one chart ⇒ chart integral) |DONE |
| 4 | `ManifoldClosedStokes` | `∫_M dα = 0`, `M` compact boundaryless oriented |DONE |
| 5 | `ManifoldProductFubini` | product orientation; `∫_{M×N} π₁*ω ∧ π₂*η = ∫ω ∫η` |DONE (+ ManifoldProductOrientation) |
| 6 | `NomologicalHomotopyGeometry/PartialFlatteningPeriodSpectrum` | card 63 theorems (+ `GradedLieLaw`, `LawValuedForms`, `CotangentDoubleCyclicCompletion`) |DONE (card promoted) |

## Log

- 2026-10-06 — programme opened after row 94; upstream `differential-geometry` checked: no form
  integration/Stokes upstream (it has `ProductOrientation`, `Exterior/Leibniz`).
- 2026-10-06 — modules 1–5 built and axiom-audited (propext/choice/Quot.sound only): locality, Stokes on closed manifolds, product orientation, Fubini for π₁*γ∧π₂*η.
