# Voronin universality of ζ on small discs of the strip

- **ID:** bag-voronin-universality
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** docs/reports/rh-current-frontier-map.md §BAG (open obstacle: recurrence at a point not known to be zero-free); walls 2, 7
- **Statement:** For `1/2 ≤ Re z₀`, `2ρ − 2Re z₀ < −1`, `3ρ < 1 − Re z₀`, `K = {|z − z₀| ≤ ρr₁}` with `1/2 < Re z₀ − 2ρr₁`, `Re z₀ + 2ρr₁ < 1`: every `g` analytic and nonvanishing on `|z − z₀| < ρR₂` (`R₂ > 1`) is approached by `ζ(· + iτ)` on `K` within any `ε` on a set of heights of positive lower density. Every point of the strip carries such a disc; on it the orbit closure of `ζ` contains every nonvanishing analytic target and no target with an interior zero and boundary floor.

## Goal
Connect the dots of the BAG lane: universality of the finite Euler products for exponential targets
(`FiniteEulerProductUniversalityOnDiscs.exists_pos_density_eulerTargetReturnSet_exp`), the cutoff-uniform
density mechanism on the prime torus (`UniformEulerTargetDensityOnZeroFreeDiscs`, proved there only for
the ζ target on zero-free discs), and the Euler tail law (`EulerProductDiscUniformCarlsonTail`). None of
the three uses a zero of ζ; composed for a general target they give Voronin's universality theorem for
ζ on small discs, which the corpus did not have (it had universality of `E_y`, and ζ self-return on
zero-free discs only).

What this says for the BAG obstacle: the approximation mechanism (Euler phases + tail law) works at
**every** point of the strip, including a hypothetical off-line zero; the only thing that can fail at a
point is the admissibility of `ζ|_K` itself as a target, which is exactly "ζ has no zero on the fourfold
disc" (`zeta_orbit_closure_dichotomy` + the local Bagchi criterion). RH is the statement that ζ never
leaves its own universality class. Units: nonselective (holds whether or not RH); it sharpens the
description of the obstacle, it does not move it.

## Gates
- [x] 0 → 1  well-posed, source-pure
- [x] 1 → 2  paper proof: composition (uniform density for exp targets replicates the ζ-target argument with the target's continuity and base density; subtraction of the tail-bad set; analytic log + Hardy-disc representation as in the ζ-target transfer)
- [x] 2 → 3  Lean: `formal/GaloisForLFunctions/RHTower/ZetaVoroninUniversalityOnSmallDiscs.lean`; `lake env lean` green; `#print axioms` standard on all eight declarations; wired into `GaloisForLFunctions/RHTower.lean` after `ZetaDiscRecurrenceOnZeroFreeDiscs`
- [ ] 3 → 4  not pursued

## Theorems
- `continuousOn_expHardyTarget`; `exists_uniform_pos_density_eulerTargetReturnSet_exp` (cutoff-uniform density for exponential targets);
- `eulerTargetReturnSet_diff_eulerDiscTailBadSet_subset_zetaTargetReturnSet` (tail-good Euler-target heights are ζ-target heights, any target);
- `exists_pos_density_zetaTargetReturnSet_exp` (ζ-universality for exponential targets);
- `exists_pos_density_zetaTargetReturnSet_of_analyticOnNhd` (Voronin universality: nonvanishing analytic targets);
- `exists_radius_zeta_universal` (universal disc `r = ρ/2`, `ρ = min((Re z₀ − 1/2)/4, (1 − Re z₀)/8)` about every strip point, margins `1/2 < Re z₀ − 4r`, `Re z₀ + 4r < 1`);
- `exists_pos_density_zetaTargetReturnSet_const` (every nonzero constant);
- `zeta_orbit_closure_dichotomy` (positive density for nonvanishing targets; density zero for targets with an interior zero and boundary floor, via `eventually_volume_zetaTargetReturnSet_le`).

## Limits
Discs are the Pechersky discs (`3ρ < 1 − Re z₀`); the natural-rate replacement is being built in `ExponentialTypeNotSummableOnPrimeLogsNaturalRate` by another agent. No Rouché step (exact value-taking `ζ = w`) is included. Nothing about the self-target at a point not known to be zero-free.

## Log
- 2026-10-21 — created directly in 3-formalized; compiled, olean built single-threaded, umbrella wired, lint clean for the module.
