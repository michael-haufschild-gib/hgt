# Parikh--Wilczek complete-evaporation aggregate no-go

- **ID:** PW-B-CEA
- **Stage:** 3-formalized
- **Type:** EXACT GLOBAL AGGREGATE + NO-GO + LIFETIME LAW
- **Parent:** PW-B
- **Statement:** `[LEAN-PROVED] [NEW] [NO-GO]` Exact dyadic Schwarzschild shell durations sum to remaining lifetime `1/(3α)`. Complete finite-mass evaporation multiplies Parikh--Wilczek recoil phase and quadratic reflection-orbit energy by this positive scalar, so neither can cancel off critical wall.

## Goal

Attack PW-B literal open core: derive balance or holonomy flatness from source-first finite-mass
evaporation. Compute complete physical time aggregate rather than postulate copywise balance.

## Gates

- [x] 0 → 1 in-progress: complete-evaporation aggregate conjecture frozen after corpus search
- [x] 1 → 2 fully-proven: total lifetime and exact phase/energy persistence proved
- [x] 2 → 3 formalized: direct Lean, targeted build, umbrella, axiom audit
- [ ] 3 → 4 publication-ready: external priority review

## Exact frozen claims

For `α≠0`, normalized dyadic shell duration satisfies

`Δu_n = 7/(24α) · (1/8)^n`,

therefore

`Σ_n Δu_n = 1/(3α)`.

At Borel grade `k`, exact recoil phase `D_k(s)` and quadratic reflection-orbit energy `Q_k(s)`
are shell-independent dimensionless invariants. Hence

`Σ_n Δu_n D_k(s) = D_k(s)/(3α)`,

`Σ_n Δu_n Q_k(s) = Q_k(s)/(3α)`.

For physical `α>0`, either aggregate vanishes in nonreal open strip iff `Re s=1/2`. Universal
quadratic aggregate flatness on Xi divisor support is exactly RH.

## Complete paper proof

Existing exact mass-loss clock gives shell duration as `7/(24α)` times dyadic mass cubed.
`M_n=2^{-n}` makes cube `(1/8)^n`; geometric series sums to `8/7`, producing `1/(3α)`.
Both PW recoil observables are independent of shell index, so linearity of absolutely convergent
series factors them out. Positive total lifetime is nonzero. Existing PW16 quadratic-energy and
holonomy classifiers then give exact critical-wall zero locus; Xi-support endpoint yields global
RH equivalence.

## Hostile review and novelty verdict

- This is literal source-time aggregation, but uses self-similar semiclassical mass clock and
  shell-independent dimensionless Borel holonomy.
- Result disproves cancellation; it does not establish flatness.
- Reflection-pair signed phase can still cancel, but PW16 proves that cancellation blind even off
  wall. Quadratic energy cannot cancel under positive time weights.
- Exact lifetime identity is expected from telescoping/geometric clock; novel content is its weld
  to physical PW recoil holonomy and rigorous exclusion of complete-evaporation averaging.
- Literature audit found no statement of this PW Borel holonomy history law or RH-related orbit
  energy classification.

Verdict: geometric lifetime sum `[REDISCOVERED]`; coefficient-faithful PW complete-history no-go
`[NEW]`, external priority provisional.

## No-go closure

- **Exact killing mechanism:** positive shell durations sum to nonzero finite lifetime, while
  recoil phase/energy is constant across self-similar shells. Integration is scalar multiplication,
  not dissipative dynamics.
- **Strongest positive survivor:** complete-history quadratic energy is exact positive lifetime
  multiple of faithful orbit energy and remains an RH-equivalent global receiver.
- **New insight:** source-first finite mass, including full endpoint rather than finite cutoff, is
  insufficient. Any viable PW-B producer must introduce shell-dependent relative channel mixing,
  memory/nonlocality, greybody interaction, or singular boundary incidence.
- **Status:** dependency-closed paper proof and Lean formalization complete. Self-similar
  evaporation producer retired; non-self-similar/interacting finite-mass dynamics remains open.

## Lean formalization

- Module:
  `formal/GaloisForLFunctions/RHTower/ThetaCusp/ThetaCuspHawkingParikhWilczekCompleteEvaporationAggregateNoGo.lean`
- Total lifetime: `tsum_schwarzschildEvaporationDyadicShellDuration`
- Phase persistence: `schwarzschildParikhWilczekCompleteEvaporationPhase_eq`
- Quadratic persistence:
  `schwarzschildParikhWilczekCompleteEvaporationQuadraticEnergy_eq`
- Exact zero locus:
  `schwarzschildParikhWilczekCompleteEvaporationQuadraticEnergy_eq_zero_iff`
- Global endpoint:
  `riemannHypothesis_iff_schwarzschildParikhWilczekCompleteEvaporationQuadraticEnergy_zero`
- Direct `lake env lean` passed.
- Targeted build
  `lake build GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingParikhWilczekCompleteEvaporationAggregateNoGo`
  passed (`11557/11557`).
- `#print axioms`: only `propext`, `Classical.choice`, `Quot.sound`.
- Umbrella import wired in `formal/GaloisForLFunctions/RHTower.lean`.

## Log

- 2026-08-27 — conjectured from exact shell-duration corpus and PW recoil holonomy.
- 2026-08-27 — lifetime sum, complete-history persistence, no-go, and Lean proof completed.
