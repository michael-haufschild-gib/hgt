# Fundamental theorem of Riemannian geometry (Levi-Civita connection)

- **ID:** levi-civita
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** classical Riemannian geometry; absent from mathlib
- **Statement:** on every Riemannian manifold there is one and only one covariant derivative on the
  tangent bundle that is torsion free and compatible with the metric.

## Goal
Mathlib (v4.32.2) has the *vocabulary* — `CovariantDerivative`, `CovariantDerivative.torsion`,
`CovariantDerivative.IsMetricCompatible`, `RiemannianBundle`, `IsContMDiffRiemannianBundle` — but
no Levi-Civita connection and no existence/uniqueness theorem: `grep -ri "levi.civita" Mathlib`
returns nothing, and `Mathlib/Geometry/Manifold/VectorBundle/CovariantDerivative/Basic.lean` still
carries the TODO "deduce that `C^k` connections always exist".  This card supplies the theorem,
unconditionally, on top of mathlib's own definitions, so the statement is mathlib-native and not a
private reformulation.

## Gates
- [x] 0 → 1  in-progress
- [x] 1 → 2  fully-proven on paper (Koszul formula)
- [x] 2 → 3  formalized: 3 Lean modules, `lake build` green, `#print axioms` =
      `{propext, Classical.choice, Quot.sound}` on every capstone, no `sorry`
- [ ] 3 → 4  publication-ready

## Capstone: `GaloisForLFunctions.HTGeometry.LeviCivita.Fundamental`

Hypothesis stack (all of it mathlib's own spelling of "Riemannian manifold"):

```lean
{E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
{H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
{M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M]
[RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
[IsContMDiffRiemannianBundle I 1 E (fun (x : M) ↦ TangentSpace I x)]
```

| theorem | content |
|---|---|
| `fundamental_theorem_of_riemannian_geometry` | `∃ cov, cov.torsion = 0 ∧ cov.IsMetricCompatible ∧ ∀ cov', torsion-free → metric → (agrees with `cov` on every section differentiable at the point) ∧ `cov'.difference cov = 0`` |
| `leviCivita I M` | the connection itself, a bundled `CovariantDerivative I E (TangentSpace I)` |
| `torsion_leviCivita` | `(leviCivita I M).torsion = 0` |
| `isMetricCompatible_leviCivita` | `(leviCivita I M).IsMetricCompatible` |
| `inner_covLC` | the Koszul formula `⟪∇_X Y, Z⟫ = ½ K(X, Y, Z)` — the *definition* of the connection |
| `koszulForm_eq_two_inner` | *any* torsion-free metric connection satisfies `K(X, Y, Z) = 2⟪∇_X Y, Z⟫` |
| `eq_leviCivita` | hence it agrees with `leviCivita` on every section differentiable at the point |
| `difference_leviCivita_eq_zero` | the difference tensor of the two connections vanishes identically |
| `covLC_sub_covLC` | `∇_X Y − ∇_Y X = [X, Y]` (classical form of torsion freeness) |
| `mvfderiv_gPair_eq` | `X⟪Y, Z⟫ = ⟪∇_X Y, Z⟫ + ⟪Y, ∇_X Z⟫` (classical form of metric compatibility) |

Non-vacuity is certified in the file: every finite-dimensional real inner product space with its
canonical Riemannian structure satisfies the whole instance stack.

## Module map

- `HTGeometry/LeviCivita/Koszul.lean` — the Koszul form
  `K(X,Y,Z) = X⟪Y,Z⟫ + Y⟪Z,X⟫ − Z⟪X,Y⟫ + ⟪[X,Y],Z⟫ − ⟪[X,Z],Y⟫ − ⟪[Y,Z],X⟫`
  and its five structural laws: the torsion identity `K(X,Y,Z) − K(Y,X,Z) = 2⟪[X,Y],Z⟫`, the metric
  identity `K(X,Y,Z) + K(X,Z,Y) = 2 X⟪Y,Z⟫`, additivity and the Leibniz rule in the middle slot,
  and `TensorialAt` in each outer slot.
- `HTGeometry/LeviCivita/Connection.lean` — `covLC`: at a point where the section is
  differentiable, `TensorialAt.mkHom₂` turns `K(·, σ, ·)` into a bilinear form on `T_xM` and
  `formRiesz` (already owned by `HTGeometry/FiltrationNumberForm.lean`) represents half of it;
  `isCovariantDerivativeOn_covLC` verifies mathlib's two axioms; `leviCivita` bundles it.
- `HTGeometry/LeviCivita/Fundamental.lean` — torsion freeness, metric compatibility, the Koszul
  formula for an arbitrary such connection, uniqueness, and the packaged theorem.

## Approach
The proof is entirely intrinsic; no charts, no Christoffel symbols, no partition of unity.  The two
tensorialities of `K` in its outer slots are exactly what mathlib's tensoriality criterion needs,
so the Koszul form descends to a bilinear form on each tangent space and Riesz representation
produces the connection directly.  Torsion freeness and metric compatibility are then the two
algebraic identities of `K`, and uniqueness is the observation that they force the Koszul formula.

## Sharpness note
Uniqueness cannot be stated as equality of the bare functions.  `IsCovariantDerivativeOn`
constrains `cov σ x` only when `σ` is differentiable at `x`; a section that is nowhere
differentiable is never a sum `σ + σ'` or a product `g • σ` of differentiable data, so its value
may be changed arbitrarily without breaking any axiom.  Literal `∃!` is therefore **false**, and
the correct sharp uniqueness statements are the two given: pointwise agreement on differentiable
sections, and vanishing of the difference tensor.

## Open residue
- Smoothness of the connection (`ContMDiffCovariantDerivative`) is not proved; it is not part of the
  fundamental theorem, and would need the regularity of `formRiesz` in the base point.
- Curvature (Riemann tensor, sectional/Ricci/scalar curvature) at manifold level remains open; the
  corpus currently owns it only in orthogonal coordinates (`GaussBonnetRiemann`).

## Log
- 2026-08-21 — created directly at 3-formalized; 3 modules landed, axiom-clean, wired into
  `GaloisForLFunctions.HTGeometry`.
