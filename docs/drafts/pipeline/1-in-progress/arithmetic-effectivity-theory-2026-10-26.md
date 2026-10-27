# Arithmetic Effectivity Theory programme

- **ID:** aet
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean) programme
- **Source:** docs/reports/review-2610/fable.md §5 ("Arithmetic effectivity theory"); frontier summary
  docs/reports/review-2610/hard-obstacles-summary.md
- **Statement:** Develop real-valued cohomology and effectivity over `Spec ℤ` and its correspondence
  surface: signs from integers, every inequality a comparison of two computations of one Euler
  characteristic, integers as log-orders of finite groups and log-volumes of lattices.

## Goal
Lean folder `formal/GaloisForLFunctions/ArithmeticEffectivityTheory/`, umbrella
`ArithmeticEffectivityTheory.lean`, foundational README. Answer the questions of fable §5.1 and the
emptiness tests of §5.9 by theorems or sharp no-gos with survivors; build the tools of §5.6–5.8.

Territory split with the sibling programme `ArithmeticPolarization` (APol, other agent): APol owns
local types, elliptic localizers, twists, collision law, diagonal collapse of lattice counts, the
first gauge charge. AET owns: real-valued effectivity calculus, Tate limits / naive heights,
log-torsion dictionary and the product formula as Bézout, the theta surface with characteristic,
the Stepanov method over `ℤ` (Siegel abundance + integrality floor), the base axioms, emptiness tests.

## Gates
- [x] 0 → 1  in-progress
- [ ] 1 → 2  paper proofs for each pillar
- [ ] 2 → 3  each pillar in Lean, audited with `lake --old env lean`

## Pillars and modules

| Pillar | Module | Status |
|---|---|---|
| E1 effectivity calculus, abundance rate | `TheEffectivityCalculus` | Lean |
| E2 the base does not extend | `TheBaseDoesNotExtend` | Lean |
| E3 Tate limits, naive heights, rounding | `TatesLimitLaw`, `NaiveHeightsAreTraces` | Lean |
| E4 horizon log-torsion, Q1 | `TheHorizonTorsion` | Lean |
| E5 theta surface, soft polarization | `TheThetaSurface` | Lean |
| E6 torsion characteristics, Gauss sums | `TheTorsionCharacteristics` | Lean |
| E7 Stepanov / Nair | `TheStepanovMethodOverZ` | Lean |
| E8 `ℙ¹ × ℙ¹` calibration; split hyperelliptic curves unitary by counting | `TheProjectiveSquareCalibration`, `TheHyperellipticCalibration`, `RHTower.Hyperelliptic*` | Lean |
| E9 golden base countermodel, five currencies | `TheBaseAxioms` | Lean |
| E10 the prime side is an intersection of torsion orbits; renormalized torsion energy | `TheLogEnergyOfRootsOfUnity`, `TheIntersectionOfTorsionOrbits`, `TheWeilPrimeKernelIsARenormalizedTorsionEnergy` | Lean |
| open: selective (non-soft) polarization; naive height of trace type on `ℤ[G]`; integer Chebyshev limit | — | open |

## Key paper facts
- Riemann inequality `h(x) + h(κ − x) ≥ ½ x·(x − κ) + χ₀` + values of `h` bounded on degree
  levels ⇒ Hodge index (scale `x ↦ n x` on `x·A = 0, x² > 0`). Conversely Hodge index with
  `κ ∈ ⟨H, V⟩` ⇒ `h = max(0, χ)` works.
- A function of the degree with `o(t²)` growth never satisfies the quadratic Riemann inequality:
  `χ(nA) = n² − O(n)` on the ample ray.
- Tate: `|h(2x) − 4h(x)| ≤ C` ⇒ `q = lim 4^{−n} h(2^n x)` exists, `|q − h| ≤ C/3`; approximate
  parallelogram ⇒ `q` quadratic; `h` bounded below ⇒ `q ≥ 0`.
- Nair/Chebyshev: `P ∈ ℤ[X]`, `deg P ≤ n` ⇒ `lcm(1..n+1) ∫₀¹ P ∈ ℤ`.

## Log
- 2026-10-26 — created; README first draft; E1–E9 formalized, README updated with pillars and answers.
- 2026-10-27 — E10 formalized; `𝔽_q` Stepanov comparison cites `RHTower.Stepanov`; loop in `logs/aet-250-contributions-2026-10-26.md`.
- 2026-10-27 — curve calibration: RH for split odd-degree hyperelliptic curves (card `3-formalized/rh-split-hyperelliptic-by-counting.md`) and `TheHyperellipticCalibration`.
