# Route R sub-quantum gap criterion (2026-08-06)

Two new modules, both unconditional, axioms `[propext, Classical.choice, Quot.sound]`.

## `HTGeometry/CofinalUnitProfileResidue.lean` — the universal reading law

`HasReferenceResidue h a c := Summable (fun i => a i - c * (h i : ℂ))`.

- `HasReferenceResidue.unique` — divergence of `h` ALONE forces uniqueness of `c`. No reporter, no
  enumeration. This strictly simplifies `RouteRCofinalSieveHarmonicResidue`'s
  `routeRPrimeHarmonicAsymptotic_unique`, which routes through the sieve reporter.
- `IsCofinalUnitProfile h mu` — the only three properties a reader needs: `0 ≤ mu ≤ 1`,
  `HasSum (fun i => mu N i * h i) 1`, and `∀ s : Finset ι, ∀ᶠ N, ∀ i ∈ s, mu N i = 0`.
- `profileAverage mu N a = ∑' i, (mu N i : ℂ) * a i`; `tendsto_profileAverage` — every such family
  reads the residue. The restarted Euler sieve is one instance.
- `unitWindowProfile` + `exists_isCofinalUnitProfile` — non-vacuity by an explicit construction: fill
  consecutive indices with weight 1 until accumulated mass first reaches 1, give the last index the
  fractional weight `(1 - S)/h(m)`. Minimality of `m` gives `S < 1` and `S + h(m) ≥ 1`, so the
  fractional weight is in `[0,1]`.
- `exists_isCofinalUnitProfile_of_equiv` transports to any countable index set;
  `exists_isCofinalUnitProfile_primeHarmonic` gives the prime case for `h p = 1/p`.

## `RHTower/RouteRHarmonicQuantumGapCriterion.lean` — the Route R payoff

Residue of the first-wall field is `-1` (t>0), `0` (t=0), `+1` (t<0) for EVERY profile, so:

- `eq_zero_of_eventually_norm_profileAverage_le` — `‖A_N(W_t)‖ ≤ r` eventually with `r < 1` forces
  `t = 0`.
- `tendsto_profileAverage_criticalWall_zero_iff` — device-free version of the sieve-specific iff.
- `riemannHypothesis_of_eventually_norm_profileAverage_lt_one` — RH from a per-zero strict bound
  `∃ r < 1, ∀ᶠ N, ‖profileAverage mu N (routeRPrimeGammaXiCriticalWallField rho)‖ ≤ r`.
- `riemannHypothesis_of_forall_xiDivisorSupport_re_eq_half` — reusable connector that was missing
  (only `XiZeroCopy`-indexed variants existed).

## Frontier delta

Old open core (`route-r-cofinal-sieve-harmonic-residue`): exact limit `S_N(W_{t_rho}) → 0` for the
Euler sieve. New open core `ROUTE_R_FIRST_WALL_SUB_QUANTUM_GAP`: ANY bounded cofinal unit profile
plus ANY threshold `r < 1`. Producers now aim at a strict inequality and may pick their own reader.

Card: `docs/drafts/pipeline/3-formalized/route-r-harmonic-quantum-gap-criterion.md`. Parent card
`cofinal-bockstein-polarized-adelic-stokes.md` updated.

Caveat: this remains a re-encoding of RH per zero (see `mem:rh/route-r-novelty-classification-2026-08-03`
and the criterion-re-encoding template). What is genuinely new is the widened producer target and the
device-independence, not a step outside the equivalence class.
