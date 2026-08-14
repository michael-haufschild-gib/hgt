# Singular autonomous ADEs obey a finite Kolchin-frequency law — formalized

- **ID:** `singular-autonomous-ade-kolchin-frequency-law-formalized`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Paper proof:** `singular-autonomous-ade-kolchin-frequency-law.md`
- **Umbrella import:** `GaloisForLFunctions.HTGeometry`

## Lean modules

| Module | Content |
|---|---|
| `HTGeometry/KolchinSlopeDichotomy.lean` | the finite jet packets, the algebraic-matroid jet rank, and the exact DA/HT slope dichotomy |
| `HTGeometry/KolchinJetCapacity.lean` | `kolchinJetCapacity`, and finiteness of the capacity as the exact criterion for differential algebraicity — the one-reporter form of `(6)` |
| `HTGeometry/KolchinCapacityMinimalOrder.lean` | **new** — the capacity **is** the minimal differential order: `kolchinJetCapacity F x = differentialOrder F x` |
| `HTGeometry/BohrFrequencyRankLaw.lean` | the frequency-rank law: the rational Bohr rank of a quasiperiodic carrier is at most the order of any nonzero autonomous algebraic differential equation it satisfies |
| `HTGeometry/AutonomousMinimalOrderBudget.lean` | **new** — the budget at the *minimal* order: `rank ≤ κ`, the prime capacity floor `π′(N) ≤ κ`, and the observable form |
| `HTGeometry/PrimePhaseBudgetRank.lean` | `ℚ`-independence of the prime logarithms and the prime budget `(37)`–`(38)` |
| `HTGeometry/CoveringDimension.lean`, `HTGeometry/EuclideanCompactCoveringDimension.lean` | Lebesgue covering dimension, the inverse-limit refinement bound, and finite dimension of Euclidean compacta |
| `HTGeometry/HullJetEmbedding.lean`, `HTGeometry/BohrHullDimension.lean` | the finite jet-sample embedding of a compact hull and the transfer of a dimension bound through it |
| `HTGeometry/HullFiniteCoveringDimension.lean` | **new** — a jet-separated compact hull has finite covering dimension, i.e. `(11)`–`(13)` in finite form |

## Audited declarations

Each resolves and `#print axioms` reports exactly `propext`, `Classical.choice`, `Quot.sound`.

- `nonempty_kolchinJetBoundSet_iff` — `(6)`: the finite jet ranks of a reporter are uniformly
  bounded exactly when the reporter is differentially algebraic; `not_exists_bound_of_hypertranscendentalOver`
  is the hypertranscendental converse;
- **`kolchinJetCapacity_eq_differentialOrder`** — the Kolchin jet capacity equals the minimal
  differential order: above that order every jet is algebraic over the length-`n₀` prefix, so no
  finite packet has rank more than `n₀`; below it every jet is transcendental over its own prefix,
  so the first `n₀` jets are algebraically independent and already realise the rank;
- `kolchinJetRank_le_differentialOrder`, `algebraicIndepOn_jets_lt_differentialOrder` — the two
  halves;
- `rank_bohrFrequencyModule_le_of_exists_realAutonomousAnnihilator` — the frequency-rank law for a
  **singular implicit** equation: `RealAutonomousAnnihilator f n P` is a polynomial relation among
  `f, f′, …, f⁽ⁿ⁾` along the real axis with no separant, regularity or uniqueness hypothesis;
- **`rank_bohrFrequencyModule_le_autonomousMinimalOrder`** — `(14)`: the rational Bohr-frequency
  rank of the carrier is at most its minimal autonomous order, i.e. at most its Kolchin jet
  capacity (constant `1`, sharper than the paper's `2`);
- **`primeCounting_le_autonomousMinimalOrder`** — `(18)`: a carrier retaining every prime logarithm
  below `N` has capacity at least `π′(N)`; `not_realAutonomousAnnihilator_of_lt_primeCounting` is
  the contrapositive cofinal law;
- `rank_bohrFrequencyModule_le_of_bohrSpectrum_subset`, `rank_bohrFrequencyModule_mul_self_le` —
  `(16)` in observable form: an observable whose Bohr spectrum lies in the carrier's frequency
  module inherits the budget, and squaring the carrier creates no new rational frequency
  directions;
- **`exists_hasCoverDimLE_of_continuous_injective`**, **`exists_hasCoverDimLE_bohrHull`** —
  `(11)`–`(13)` in finite form: a compact hull injecting continuously into `ℂ^N` is homeomorphic to
  a compact subset of a `2N`-dimensional real normed space, and compact subsets of Euclidean space
  have finite covering dimension, so the hull does;
- `CoveringDimension.HasCoverDimLE.of_refinedByStages` — the inverse-limit dimension bound `(12)`;
- `primeLog_primesBelow_linearIndependent_rat`, `primeCounting_le_rank_of_primeLog_mem` — the prime
  side: `rank_ℚ Λ_N = π′(N)`.

## Verification

```text
lake env lean GaloisForLFunctions/HTGeometry/KolchinCapacityMinimalOrder.lean
lake env lean GaloisForLFunctions/HTGeometry/AutonomousMinimalOrderBudget.lean
lake env lean GaloisForLFunctions/HTGeometry/HullFiniteCoveringDimension.lean
lake build GaloisForLFunctions.HTGeometry.AutonomousMinimalOrderBudget
```

## What closed last

The audit on the paper card found the interface `SingularKolchinFrequencyInput` to be a purely
numerical structure — three naturals and two inequalities — so the theorem built on it was
arithmetic rather than the card's statement.  That interface is no longer load-bearing anywhere in
the chain.

Its place is taken by two genuine identifications.  First, the Kolchin jet capacity of a reporter is
its minimal differential order: this is what makes `κ` a computable invariant of the equation rather
than a name for a dimension.  Second, the frequency-rank law applies at that minimal order, giving
the budget `rank_ℚ Γ(f) ≤ κ` directly — with constant `1`, sharper than the paper's `2κ`, because
the algebraic route bypasses the real-versus-complex dimension count.  The prime-cutoff floor
`π′(N) ≤ κ` follows, and the topological half `(11)`–`(13)` is closed in finite form by the jet
embedding.

## Boundary

- The paper's general Bohr-hull route to `(14)` — the *equality* `rank_ℚ Γ(f) = dim_cover X_f` —
  rests on Pontryagin–Takahashi dimension/rank duality for compact connected abelian groups, which
  is cited, not formalized.  No theorem listed above uses it: the budget is obtained algebraically.
- The paper's `κ(P)` for a general radical differential ideal in several unknowns rests on
  Ritt–Raudenbush finite prime decomposition and the Kolchin dimension polynomial, both cited.  The
  one-reporter capacity used here is unconditional.
- The sharp constant `dim_cover K ≤ 2N` for a compact `K ⊆ ℂ^N` (rather than the volumetric
  `5^{2N} − 1`) needs the product/sum theorem of dimension theory, which is not formalized; only
  finiteness is used.
- The cross-literature priority audit is external and remains open.
