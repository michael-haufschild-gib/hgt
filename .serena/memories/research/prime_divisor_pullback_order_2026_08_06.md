# Pullback law for orders at prime divisors (2026-08-06)

Card: `docs/drafts/pipeline/2-fully-proven/new_scientific_knowledge/other/stable-coframe-log-calabi-yau-rigidity.md`
(stage 2).  **11th module in this card's lineage.**

## New module

`GaloisForLFunctions/HTGeometry/PrimeDivisorPullbackOrder.lean`

| statement | declaration |
|---|---|
| complement condition making the local map exist | `primeCompl_le_comap` |
| induced map of local rings | `localMapAt`, `localMapAt_algebraMap` |
| nonzero stays nonzero locally | `algebraMap_localization_ne_zero` |
| **`ord (pullback of a) at P = e · ord a at Q`** | `orderAt_map_eq_mul_ramification` |

For `φ : A →+* B` between Noetherian integrally closed domains and prime divisors `P` of `B`,
`Q` of `A` with `Q = comap φ P`.  This is the `e` half of (8) for **genuine prime divisors**,
not just an abstract pair of DVRs.  mathlib has **no** pullback law for orders of vanishing.
All axiom-clean; umbrella green (14923 jobs).

## Key construction

`localMapAt := IsLocalization.map _ φ (primeCompl_le_comap ...)`, with
`IsLocalization.map_eq` giving `localMapAt (algebraMap a) = algebraMap (φ a)`.  Then
`addVal_map_eq_mul_ramification` (from `LocalRamificationOrderLaw.lean`) applies directly and
`orderAt` unfolds definitionally on both sides.

## Lean traps

- `Ideal.primeCompl I` takes `[I.IsPrime]` as an instance argument, so `rw [hQ]` inside
  `x ∈ Q.1.primeCompl` fails with "motive is not type correct".  **Reason on raw membership
  instead**: `have hx' : x ∉ Q.1 := hx`, then `Submonoid.mem_comap.mpr`, `show φ x ∉ P.1`, and
  only rewrite inside `x ∈ Q.1` (no instance there).
- Making `isDiscreteValuationRing_primeDivisor` an **`instance`** (was a theorem) is what lets
  `addVal (Localization.AtPrime P.1)` appear in *statements* of downstream theorems; with a
  theorem you can only `haveI` it inside proofs, which is too late for the statement.
- After changing a declaration to an `instance`, **`lake build` the module before
  `lake env lean`-ing its dependents** — otherwise they read the stale olean and the instance is
  invisible.
- `omit ... in` must precede the docstring (hit this twice now).

## Card lineage (11 modules, all axiom-clean)

... + `PrimeDivisorPullbackOrder`.

## Next brick

Capstone: the divisor-below map `PrimeDivisor B → PrimeDivisor B` for a self-map and the final
application of `eigenvolumeOrder_eq_neg_one_of_someRamified`.  Still blocked on the
`Algebra B B` clash; plan is `comap`-phrased hypotheses discharged separately by the `Algebra`
versions in `PrimeDivisorLyingOver.lean`.  Then only the scheme-level passage remains.

## Repo hazard

Lint reports two other agents' unwired untracked modules
(`HTGeometry.PolyannulusTorusUniqueness`, `RHTower.MobiusCriticalPacketTransport`).
