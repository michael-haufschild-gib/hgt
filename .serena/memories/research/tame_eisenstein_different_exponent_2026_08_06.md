# Exact tame ramification exponent formalized (2026-08-06)

Card: `docs/drafts/pipeline/2-fully-proven/new_scientific_knowledge/other/stable-coframe-log-calabi-yau-rigidity.md`
(still stage 2 — see "what still blocks stage 3").

## New module

`GaloisForLFunctions/HTGeometry/TameEisensteinDifferentExponent.lean`

For a discrete valuation ring `B`, a uniformizer `x`, and
`eisensteinPoly e c = X^e + ∑_{i<e} C (c i) * X^i` with `∀ i < e, e ≤ addVal B (c i)` (the
Eisenstein presentation of a totally ramified extension) and `addVal B (e : B) = 0` (tame):

| statement | declaration |
|---|---|
| valuation lower bound for a finite sum | `le_addVal_sum` |
| `addVal (x^n) = n` for a uniformizer | `addVal_pow_uniformizer` |
| derivative / its evaluation | `derivative_eisensteinPoly`, `eval_derivative_eisensteinPoly` |
| **`addVal (g'(x)) = e - 1` exactly** | `addVal_eval_derivative_eisensteinPoly` |
| `addVal (g'(x)) + 1 = e` | `addVal_eval_derivative_eisensteinPoly_succ` |
| **local different `= m^(e-1)`** | `span_eval_derivative_eisensteinPoly` |

All axiom-clean (`propext`, `Classical.choice`, `Quot.sound`).

## Why this matters

mathlib has only the **lower** bound `pow_sub_one_dvd_differentIdeal : P^e ∣ pB → P^(e-1) ∣ 𝔡`,
plus `dvd_differentIdeal_iff` (`P ∣ 𝔡 ↔ ramified`).  It does **not** have the tame upper bound.
The exact exponent is what makes the `e - 1` of the card's local law
`c_E = e_E c_F + (e_E - 1)` exact rather than an inequality — i.e. it is the precise sense in
which the `+1` of `c + 1 = e (c' + 1)` is the Jacobian contribution of ramification.

Proof mechanism: ultrametric strict minimum.  Tameness makes `addVal (e x^{e-1}) = e - 1` while
every other term has `addVal ≥ e`; then `AddValuation.map_add_of_distinct_val` gives the min.

## Lean API notes

- `IsDiscreteValuationRing.addVal R : AddValuation R ℕ∞`; `addVal_uniformizer`,
  `addVal_le_iff_dvd` (`v a ≤ v b ↔ a ∣ b`).
- **`map_pow` does NOT apply to `AddValuation`** (values are additive).  Prove
  `addVal (x^n) = n • addVal x` by induction with `AddValuation.map_mul`; there is no
  `AddValuation.map_sum_le`, so `le_addVal_sum` had to be built by `Finset.induction` +
  `AddValuation.map_add` (`min (v x) (v y) ≤ v (x+y)`).
- `Polynomial.eval_finset_sum` is deprecated → `Polynomial.eval_finsetSum`.
- `derivative` is a linear map, so `map_sum` handles the sum of the presentation.

## What still blocks stage 3

The remaining algebraic-geometric inputs: the eigenvolume identity (7) from `f^*|W`, the passage
from this **local** different to the **global** divisor pullback formula (8) on a smooth
projective variety, and the int-amplified eigenvalue bound giving `e_E > 1`.  These need Weil
divisors, the canonical divisor of a finite morphism, and `N^1` with amplified pullback
eigenvalues.  The combinatorial-arithmetic core downstream of (9) is already fully closed in
`EigenvolumeRamificationSystem.lean` — see
`research/eigenvolume_ramification_core_formalized_2026_08_05`; do not re-derive it.

## Repo hazard hit this session

The `HTGeometry` umbrella was broken by a *concurrent agent's* untracked new file
`CompactMomentWeakConvergence.lean`, which declared
`GaloisForLFunctions.HTGeometry.integrable_continuousMap` — a name already taken by the tracked
`InfiniteTorusEquidistribution.lean`.  Lean reports this as
"import ... failed, environment already contains ...".  Fixed by renaming the new one to
`integrable_continuousMap_of_compactSpace` (5 occurrences).  When an umbrella build fails with
that message, look for a freshly added untracked module reusing a generic name.
