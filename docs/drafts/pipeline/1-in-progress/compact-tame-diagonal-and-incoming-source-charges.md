# Compact tame diagonal and incoming source charges

- **ID:** critical-rigidity-compact-tame-diagonal
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Question:** Does every failure of energy-continuity of the prime generator come from incoming divisor charges?

## Exact target

Write `λ_m=log m+tameDifferent(m)` and `τ_m=tameDifferent(m)`. Prove

`τ_m²/λ_m → 0` as `m→∞`,

and its finite-packet consequence: for every `ε>0`, some `R` satisfies

`Σ_(m>R) τ_m² a_m² ≤ ε Σ_m λ_m a_m²`.

This makes the diagonal part of the literal generator compact from adjunction energy to coefficient square mass. A coefficient family escaping every fixed conductor then has vanishing diagonal output whenever its adjunction energy stays bounded.

## Existing input and proposed mechanism

`ArithmeticIntersectionTheory.tameDifferent_le_split` gives

`τ_m ≤ 2 log K+2 log 4+2 log m/K` for every integer `K≥1`.

Taking `K=ceil(log m)` gives `τ_m=O(log log m)`, hence the target. The corpus already proves `τ_m/log m→0` in `CompletedArithmeticForms.ConductorLogLaw`; that weaker limit alone does not prove the squared relative bound. Searches for a squared relative limit or compact tame diagonal found no matching theorem.

## Receiving-charge interpretation

The prospective exact conductor decomposition is

`(Ga)_r=−τ_r a_r+Σ_(r|m) Λ(m/r) sqrt(φ(r)/φ(m)) a_m`.

Compactness would isolate the noncompact phenomenon in incoming divisor transport. The separate conductor-indexed charge candidate asks whether every finite receiving packet is approximable by generator outputs of inputs with vanishing adjunction energy. Neither that classification nor a complete-Weil consequence follows from diagonal compactness alone.

## Status

The split estimate and sublogarithmic theorem have been read. The sharper limit, finite-packet tail bound, and exact operator decomposition remain to be formalized.
