# Order along prime divisors + concrete finite support (2026-08-06)

Card: `docs/drafts/pipeline/2-fully-proven/new_scientific_knowledge/other/stable-coframe-log-calabi-yau-rigidity.md`
(stage 2).  **10th module in this card's lineage.**

## New module

`GaloisForLFunctions/HTGeometry/PrimeDivisorOrder.lean`

| statement | declaration |
|---|---|
| prime divisors (height-one primes) | `PrimeDivisor` |
| each carries a DVR | `isDiscreteValuationRing_primeDivisor` |
| order of an element along one | `orderAt` |
| **order ≠ 0 ↔ element lies in the prime** | `orderAt_ne_zero_iff` |
| **nonzero element has finite divisorial support** | `finite_orderAt_support` |

Closes the loop between the valuation layer (`LocalizationAtPrimeDivisorDVR`) and the finiteness
layer (`DivisorSupportFinite`): `hfin` is now proved for the **concrete** order function attached
to a ring element, not assumed for an abstract order assignment.

Key mathlib lemma: `IsLocalization.AtPrime.isUnit_to_map_iff S I x : IsUnit (algebraMap R S x) ↔
x ∈ I.primeCompl`, combined with `addVal_of_isUnit` / `isUnit_of_addVal_eq_zero`
(`RingOrdRamification.lean`).

Design note: `orderAt` uses `haveI := isDiscreteValuationRing_primeDivisor P` inside the `def`.
That is safe because `IsDiscreteValuationRing` is a **Prop**-class, so proof irrelevance makes the
resulting term well defined; all downstream lemmas re-introduce the same `haveI` and everything is
defeq.

## Card lineage (10 modules, all axiom-clean)

`RamificationPoleFixedPoint`, `EigenvolumeRamificationSystem`, `TameEisensteinDifferentExponent`,
`TopExteriorPowerDeterminant`, `LocalRamificationOrderLaw`, `RingOrdRamification`,
`DivisorSupportFinite`, `PrimeDivisorLyingOver`, `LocalizationAtPrimeDivisorDVR`,
`PrimeDivisorOrder`.

## Next brick

The capstone assembly over `PrimeDivisor B` with the self-map `φ : B →+* B`.  `PrimeDivisor B` and
`orderAt` now exist, so the remaining work is:
1. the divisor-below map `PrimeDivisor B → PrimeDivisor B`, `P ↦ ⟨comap φ P, _⟩`, using
   `under_height_eq_one_of_height_eq_one` — **needs the `Algebra` instance from `φ.toAlgebra`,
   which clashes with the identity `Algebra B B`**; plan is to restate the two needed lemmas for a
   bare `RingHom` with `RingHom.IsIntegral`, or take well-definedness/surjectivity as explicit
   `comap`-phrased hypotheses (both are already proved in the `Algebra` formulation);
2. `hlaw` at each prime divisor, from `ramificationShiftLaw_frac` applied to the induced local map
   `IsLocalization.map` between `B_{comap φ P}` and `B_P` (φ sends `(comap φ P).primeCompl` into
   `P.primeCompl`, so the map exists);
3. apply `eigenvolumeOrder_eq_neg_one_of_someRamified`.

Beyond that, only the scheme-level passage remains.

## Repo hazard

Lint gate reports another agent's unwired untracked `HTGeometry.CharacterLatticeFrequencyRank`.
