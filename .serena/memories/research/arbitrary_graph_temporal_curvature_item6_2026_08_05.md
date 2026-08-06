# Arbitrary-graph quantum temporal-curvature law — CARD COMPLETE (2026-08-06)

Card moved `2-fully-proven` → `docs/drafts/pipeline/3-formalized/arbitrary-graph-quantum-temporal-curvature-law.md`.
Formal status `[FORMALIZED]`. All six "still required before stage 3" items `[DONE]`.

## What closed it (final two modules)

`formal/GaloisForLFunctions/HTGeometry/InfiniteNetworkExhaustion.lean` — equation `(20)`
- `ambientRestrictedGoodSet` / `_residual` / `measure_compl_ambientRestrictedGoodSet_eq_zero`:
  generalization of `ambientRestrictedMaximalSet_*` (in `SubsystemAtlasProjectiveGenericityLaw.lean`)
  from maximal-projectivity sets to an ARBITRARY countable family of good sets
  `Good : ∀ a, Set (Fin (n a) → ℝ)` read through injective selectors `e a : Fin (n a) → ι`.
  This generalization was necessary because `allSubsystemGenericSet` is a
  `polynomialMatrixProjectiveGenericSet`, NOT a `polynomialHermitianMatrixMaximalSet`.
- `card_le_of_strictMono`, `tendsto_atTop_prod_sub_one_of_strictMono` (product ≥ 2^card).
- `finiteInducedGraphTemporalRank_univ` (connected ⇒ ∏ q − 1); proved with
  `(SimpleGraph.Iso.comap (Equiv.subtypeUnivEquiv h) G).connected_iff.mpr`.
- `VolumeSite` / `volumeLocal` / `volumeGraph` abbrevs: finite volume of an infinite `V : Type`
  is the coe-sort `↥(W k)`; all instances (`Fintype`, `DecidableEq`, `DecidableRel comap Adj`) fire.
- capstone `infiniteNetworkExhaustion_temporalRank_tendsto_atTop`.

`formal/GaloisForLFunctions/HTGeometry/ConnectedNetworkRecurrenceLaw.lean` — equations `(3)`, `(9)`
- `maximallyProjectiveEnergy_of_multiset_eq`: CROSS-TYPE root-packet relabelling
  (`RootPacketRelabelling.maximallyProjectiveEnergy_of_rootMultiset` only handles one index type).
- `componentPackets_univ_of_connected : componentPackets G univ = {Finset.univ}` +
  `@[reducible] def uniqueComponentPacketUniv` (a `Unique` instance, `default.1 ≡ Finset.univ` by rfl).
- `maximallyProjective_subsystemBlock_univ_of_connected` — the key bridge: at
  `p ∈ subsystemComponentGenericSet A G univ` with `G` connected, the WHOLE network spectrum is
  maximally projective.  Route: `maximallyProjectiveEnergy_eigenvalues_of_mem_polynomialMatrixGenericSet`
  on `blockDiagonal'`, then `charpoly_blockDiagonal' + Fintype.prod_unique` collapses to the single
  block, then the cross-type relabelling.
- `anchoredTemporalRank_(add_one_)subsystemBlock_univ_of_connected` = `(3)`.
- `anchoredProjectiveReturnFrequency_of_connected`,
  `no_nonzeroExactAnchoredReturn_of_connected` = `(9)`, by instantiating the pre-existing generic
  `maximallyProjectiveEnergy_anchoredProjectiveReturnFrequency` and
  `MaximallyProjectiveEnergy.no_nonzeroExactAnchoredReturn` (`AnchoredProjectiveReturnDensityLaw.lean`).

## Audit result
`#print axioms` on all 11 capstones: only `propext, Classical.choice, Quot.sound`.
`lake build GaloisForLFunctions.HTGeometry.ConnectedNetworkRecurrenceLaw` (9153 jobs) ✓.
`scripts/formal_tools.py lint` ✓.
Both modules wired into `GaloisForLFunctions/HTGeometry.lean`.

## Traps hit
- `rw ... at ha` where `ha : ↑a ∈ componentPackets ...` and `a`'s TYPE mentions the same term →
  motive not type correct.  Use `Finset.ext_iff.1 h x |>.1` instead of rewriting.
- A `def` producing a class instance must be `@[reducible]` or the linter warns (lint gate fails).
- `Finset.prod_attach T f` turns `∏ v : ↥T, f v.1` into `∏ v ∈ T, f v`; needs explicit args or
  `CommMonoid ?m` gets stuck.
- Fully-applied `Nat.lt_two_pow_self` (no explicit arg) + `omega` closes `k ≤ ∏ − 1`.
- `Fintype.card_ne_zero` needs `Nonempty (A v)`; recover it from the anchor `r : ∀ v : ↥univ, A v.1`.

## Not mine — concurrent session
`GaloisForLFunctions/HTGeometry/QuadraticTransportCost.lean` is UNTRACKED and currently fails to
build (`+GaloisForLFunctions.HTGeometry` therefore fails).  Leave it alone.
