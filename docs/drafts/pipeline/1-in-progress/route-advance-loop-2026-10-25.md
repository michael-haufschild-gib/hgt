# Route-advance conjecture loop (2026-10-25)

- **ID:** route-advance-loop-2026-10-25
- **Stage:** 1-in-progress
- **Type:** CONJECTURE LOOP
- **Source:** `docs/reports/rh-current-frontier-map.md`, `docs/reports/rh-killed-routes.md`
- **Statement:** Find and formalize contributions that discharge a premise of a route theorem or
  answer a question on the critical path of a route's open problem.

## Goal
Each counted contribution must be unconditional Lean, `lake --old env lean` green, axioms within
`[propext, Classical.choice, Quot.sound]`, wired into its umbrella. Numbers, no-gos and
reformulations do not count.

## Gates
- [x] 0 → 1  frontier read; premise scan done; loop started
- [ ] 1 → 2  a counted contribution with complete paper proof
- [ ] 2 → 3  formalized

## Frontier facts (established before conjecturing)
1. Every route's stated open estimate is RH- or zero-free-strip-strength (map "Open / obstacle"
   lines; corpus equivalences). Only scoped side questions are below that strength.
2. Premise scan (all corpus `Prop` defs used as hypotheses, never concluded; restricted to the
   353 route source modules): the open premises are RH-equivalent (packet boundedness =
   off-line blindness; `OffLineDepthLocallyBounded` = no clustering of off-line zeros; ground
   overlap can vanish under parity switch), structural predicates, or already discharged
   (`ZetaGrowthExponent` at every θ > 1/4).
3. The map's "binder defects" (`∑ i ∈ s, f i + g` read as `∑ i ∈ s, (f i + g)`) are false:
   Mathlib parses the body at precedence 67, so `∑ i ∈ s, f i + g = (∑ i ∈ s, f i) + g` by `rfl`
   (checked). Affected statements are correct as written: `criticalPrimeEnergy_biUnion_range`,
   `sum_range_moebiusWindowRow`, `sum_Ioc_two_pow_mul_eq`, `abs_kernelValue_sub_sum_le_of_windows`,
   `abs_sum_moebius_mul_kernelTerm_sub_le`, `hasMeanValue_of_rate`,
   `exists_abs_sqrt_patternReceiver_sub_le_of_rate`. Audit finding, not a contribution.

## Conjecture ledger
| # | Route | Conjecture | Verdict | Lean | Insight |
|---|---|---|---|---|---|
| 1 | SRT | The generic-width premise of the lag receiver, rate law and orbit laws can be removed | PROVED (#1) | `EveryWidthDecidesTheCriticalLine`, `TheSplineOrbitDecidesTheCriticalLine` | Only off-line spectral points matter; real-rooted box splines see all of them at every width |
| 2 | SZ | One shift threshold `ω₀` for all high dyadic scales | NOT PURSUED | — | `ω₀` comes from compactness on a fixed sphere; the first-variation error grows with the scale, so uniformity is likely false (no-go, not counted) |
| 3 | WL/MC | Discrete Beurling systems with periodic counting error | PARKED | — | Periodic error forces the system to be `ℕ` (elementary rigidity); a selectivity fact, not route progress |
| 4 | HF/ACS | Generic-test index laws (`cyclic_pontryagin_law`, two-prime and rational Hecke orbits) hold for the cubic spline | PROVED (part of #1) | `zeta_splineOrbit_negIndex_law`, `riemannHypothesis_iff_splineTwoPrime_negIndex_eq_zero`, `riemannHypothesis_iff_splineOrbit_negIndex_le_one` | Only right zeros enter the negative index; RH iff no spline Gram has two negative squares |
| 5 | SRT/RW | Grid laws without the resonant-step exception | NOT DISCHARGEABLE | — | Resonance involves all zero heights; no explicit step is certifiable without arithmetic of ordinates |
| 6 | WD | Arithmetic head formula without `Ξ(t) ≠ 0` | NOT A PREMISE | — | The normalized coefficient `Σ Re((z_q − t)⁻²)` has genuine poles at zero ordinates |
| 7 | HF | S/L>45 without the second-moment premise | NOT PURSUED | — | Premise is dischargeable (`f ∈ C²_c`), but the inequality is auxiliary and does not sign the ground minimum |
| 8 | SZ | `MangoldtLogHaarCapacity` (`Σ_{d≤n} Λ(d)/d ≤ log n`) | NOT PURSUED | — | Small `n` need explicit Mertens errors or finite checks; feeds a side transport lemma only |

## Log
- 2026-10-25 — created.
