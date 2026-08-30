# FZZ sparse unbounded-jet density route kill (2026-08-30)

Formalized a single fixed completed FZZ response with unbounded node-dependent finite jet contact and an off-critical zero.

Key construction: cubic physical nodes `m_k=(k+1)^3`, multiplicity index `Σ k, Fin(k+1)`, centered nodes `λ_k=m_k+3/2`, genus-one canonical product `C`; raw response-reflection-even product `R(z)=C(z+3/2)C(-z-3/2)`; Schwarz product `Q=R·R#`. Exact orders: `ord_{m_k} R=k+1`, `ord_{m_k} Q=2(k+1)`. A centered real quadratic interpolates `i/(B(a)Q(a))` at `a=-5/4+i`; positive-square gauge `1+(P B)^2` preserves the full completed response package. Difference from Xi contains `Q^2`, so every `iteratedDeriv j` agrees at `m_k` for `j≤k`, yet response vanishes at `a` and is noncanonical.

Lean modules:
- `formal/GaloisForLFunctions/HTGeometry/SparseUnboundedMultiplicityCanonicalProduct.lean`
- `formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingFZZSchwarzschildSparseUnboundedJetDensityNoGo.lean`

Main theorem: `RHTower.completed_response_sparseUnboundedJet_route_noGo`.
Positive survivor: `RHTower.sparseJetCanonicalProduct_package` (exact multiplicity, reciprocal summability, local finiteness, order-one envelope).
Reusable bridge added: `RHTower.iteratedDeriv_eq_zero_before_analyticOrderAt_eq`, converting exact analytic order to mathlib `iteratedDeriv` vanishing via global factorization.

Verification: direct `lake env lean` both files passed; targeted `lake build` both modules passed; axiom audit only `[propext, Classical.choice, Quot.sound]`; no task-owned Lean process remained. Global `formal_tools.py lint` was nonzero solely for many unrelated shared-worktree modules currently unwired; neither new module was reported unreachable or for forbidden markers.

Card promoted to `docs/drafts/pipeline/3-formalized/fzz-sparse-unbounded-jet-density-no-go.md`. Frontier map was not edited.

Consequence: kills `unbounded pointwise-finite sparse physical jets -> uniqueness/zero control -> RH`. Surviving local mechanism must impose cumulative weighted jet density/full germ/nonlocal data.