# 130 — The Sonin/{σ_p}-boundary seam defect: the commutator model collapses [PROVED HERE]

Formal home: `formal/GaloisForLFunctions/RHTower/SoninSeamDefect.lean`
(all endpoints axiom-clean: `[propext, Classical.choice, Quot.sound]`; full `MainTheorems` gate green).
Companion (the category extension, concurrent): `MPlusTorsionSeam.lean`;
criterion base: `FittingSeamBoundary.lean`;
cutoff-crossing companion: `CutoffCochain.lean`;
object-packaging companion: `CutoffTorsionSeam.lean`.

Doc 129 §3 named the one ζ-free, lane-attemptable test: build the boundary defect of `(∂_log − ρ,
{σ_p})` on the Sonin space as a seam presentation and check whether its `{σ_p}`-defect is fake
(collapses) or non-fake (survives). This document runs the first, decisive step of that test on the
natural model of the defect — and it collapses, sharpening exactly what a live defect must be.

## 1. The setup (the §13 extension, built)

The bare `𝓜⁺` is finite-free; the surviving shape is a **torsion seam presentation**
`R[X]ⁿ --A--> R[X]ⁿ`, `det A = Xᵐ`, with `{σ_p}`-defects `Δ_p` and boundary class
`tr(adj(A)·Δ_p) mod Xᵐ` (charter §13). That extension is now a category object
(`MPlusTorsionSeam.lean`: `TorsionSeamPresentation`, `MPlusTorsionSeamObject`, morphisms, and a
positive coefficient-witness of non-fake defects `boundaryClass_ne_zero_of_coeffWitness`). The
question is what the `{σ_p}`-defect `Δ_p` on such a presentation can be.

## 2. The natural model, and its collapse [PROVED HERE]

The natural first model of a `{σ_p}`-defect is the **commutator**
`Δ_p = σ·A − A·σ` (`commutatorDefect`) — the failure of the `{σ_p}` action `σ` to preserve the
divisor presentation `A`. It is **always fake**:

- `fittingBoundaryTrace_commutatorDefect`: `tr(adj(A)·(σA − Aσ)) = 0`, for **every** `A` and **every**
  `σ`. The adjugate identities `adj(A)·A = A·adj(A) = det(A)·1` and trace cyclicity make the two
  cyclic traces both equal `det(A)·tr(σ)`, so they cancel.
- `fittingBoundaryClass_commutatorDefect`: hence the boundary class in `R[X]/(Xᵐ)` is `0` — fake, at
  every level `m`.
- `nonzero_fittingBoundaryClass_not_commutator`: a live boundary defect (nonzero class) is therefore
  **never** a commutator.

So no failure of `{σ_p}` to commute with the presentation produces a live pinned obstruction.

## 3. Non-fake defects exist — the collapse is a real restriction [PROVED HERE]

`exists_nonfake_fittingBoundary`: a one-slot presentation `A = [X²]` (`det A = X²`) with defect
`Δ = 1` has boundary class `1 ≠ 0` in `ℚ[X]/(X²)` — a non-fake defect. So §2 is a genuine
restriction, not vacuity: non-fake defects exist, and by §2 every one of them is a **non-commutator**.
(This is the negative complement of the concurrent positive witness `BoundaryCoeffWitness`: both
confirm the extended category is non-empty; §2 pins that a live defect is never the commutator model.)

## 4. Why the commutator collapses — the same unit-triviality

At a pinned strip point the `{σ_p}` action is multiplication by the unit `p^(−s)` — nonvanishing
there (doc 127: the prime side is a unit at every strip point). A unit is a **scalar**; it commutes
with the presentation `A`, so its commutator defect is `0`. The commutator no-go is the
**presentation-level shadow** of the disjoint-carrier / freeness collapse (docs 127–128): `{σ_p}`
acting locally by a unit is deck-invisible / commuting / fake, all three the same fact. Every pinned
*local* model of the `{σ_p}`-defect — free reference (doc 128), unit multiplier (doc 127),
commutator (here) — collapses for one reason: `{σ_p}` acts on the germ by a unit.

## 5. What this sharpens, and hands forward

A live `{σ_p}`-boundary defect must be a **non-commutator cross-boundary cochain**: not `σA − Aσ`,
but the `{σ_p}` action pushing mass **across a cutoff** `|x| = λ` (the Sonin condition
`f|_{|x|<λ} = 0`, `f̂|_{|x|<λ} = 0`). That cochain is exactly the coefficient-witness shape
(`MPlusTorsionSeam.BoundaryCoeffWitness`) — a boundary term read off a specific low-order coefficient,
not a commutator. The commutator no-go removes the naive candidate and leaves the cross-boundary
cochain as the only surviving form.

The remaining open core is unchanged in location but sharper in shape: the `{σ_p}` action that
produces such a non-commutator cochain is **non-local** — it moves mass across the Sonin cutoff, so
it is not a pinned-germ action but a trace-level / adelic one (doc 129: adèle-class meeting is
trace-level; germ-level intrinsic is the missing-Weil apex). The lane has now proved that **every
pinned-germ model of the `{σ_p}`-defect is fake** (three independent collapses: freeness, unit,
commutator), which is itself the reason a live defect must be non-local: it explains *why* the only
known constructions (Connes' trace formula) are trace-level rather than germ-level.

The abstract cutoff algebra has now been formalized in `CutoffCochain.lean`: for every `m > 0` there
is an idempotent cutoff `e`, a crossing action `sigma`, and a torsion seam presentation `A` with
`det A = X^m` such that `sigma * e != e * sigma` and `Delta = (1-e) sigma e` is
determinant-transverse, not a commutator, and satisfies both `Delta ∉ A End + (X^m)` and
`Delta ∉ End A + (X^m)`. `CutoffTorsionSeam.lean` packages the same witness as a one-label
`TorsionSeamPresentation`, and over any inhabited regular base as an `MPlusTorsionSeamObject`.
Therefore the next construction is no longer abstract algebraic existence or object-layer
integration; it is realization from the actual semilocal Sonin `{sigma_p}` boundary action —
without importing ζ.
