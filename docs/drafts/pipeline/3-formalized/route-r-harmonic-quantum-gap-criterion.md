# Route R harmonic quantum gap criterion

- **ID:** route-r-harmonic-quantum-gap-criterion
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `cofinal-bockstein-polarized-adelic-stokes.md` · first-wall open core, via
  `route-r-cofinal-sieve-harmonic-residue`
- **Statement:** The oriented first-wall harmonic residue is read by every bounded, unit-mass,
  cofinally escaping prime profile, and its values are quantized in `{-1,0,1}`; hence a strict
  modulus bound below one — not exact annihilation — already forces critical placement.

## Goal

Replace the producer obligation "make one explicit reporter converge to zero" by an open condition.
The previous open core asked for an exact limit `S_N(W_{t_rho}) -> 0`. Because the limit is a
quantized coordinate, any device-independent bound `limsup |average| <= r < 1` excludes both
orientations and therefore forces `t_rho = 0`. This widens the class of admissible source producers
from those achieving an equality to those achieving any strict inequality, and removes the
dependence on the particular Euler-sieve device.

## Gates

- [x] 0 → 1 in-progress: well-posed, source-pure, attack idea
- [x] 1 → 2 fully-proven: complete paper proof, no open dependency
- [x] 2 → 3 formalized: Lean theorems below, targeted `lake build` green, axiom audit clean
- [ ] 3 → 4 publication-ready: standalone paper and refreshed external novelty audit

## Internal corpus audit

- `[CORPUS]` `RouteRCriticalWallOrientedHarmonicQuantization` proves the oriented three-value law
  for the first-wall coefficient modulo `ell^1`.
- `[CORPUS]` `RouteRCofinalSieveHarmonicResidue` builds one concrete reader — the restarted Euler
  sieve — and proves it recovers the coefficient. Its uniqueness lemma is proved through that
  reader.
- `[CORPUS]` No module isolated the properties of a reader actually used, and none stated a
  criterion weaker than exact vanishing.
- `[NEW]` `HTGeometry/CofinalUnitProfileResidue` isolates them: bounded by one, unit reference mass,
  supports escaping every finite set.
- `[NEW]` `RHTower/RouteRHarmonicQuantumGapCriterion` derives the gap criterion and the RH endpoint.

## Complete paper proof `[PROVED HERE]`

Let `h` be a weight on an index set and call `c` the *residue* of a field `a` over `h` when
`a - c h` is summable.

**Uniqueness.** If `a - c h` and `a - d h` are both summable then `(d - c) h` is summable. When `h`
is not summable this forces `c = d`. No averaging device occurs; divergence alone suffices. This
strictly simplifies the corpus uniqueness argument, which routed through a reporter and a fixed
prime enumeration.

**Reading law.** Call `mu_N` a *cofinal unit profile* for `h` when `0 <= mu_N <= 1` pointwise,
`sum_i mu_N(i) h(i) = 1`, and for every finite set `s` the stage `mu_N` vanishes on `s` for all
large `N`. Write `A_N(a) = sum_i mu_N(i) a(i)`. Then `A_N(h) = 1` exactly, and for summable `b`,
`|A_N(b)| <= sum_i mu_N(i)|b(i)| <= sum_{i notin s}|b(i)|` once `mu_N` vanishes on `s`; choosing `s`
with small complementary mass gives `A_N(b) -> 0`. Hence `A_N(a) -> c` whenever `a` has residue `c`.
Only the three listed properties are used, so every such device reads the same coordinate.

**Non-vacuity.** For strictly positive divergent `h` on the natural numbers, let `m(N)` be the least
index at which the accumulated tail mass from `N` first reaches one. Give weight `1` to the indices
`N, ..., m(N)-1` and weight `(1 - sum_{N <= i < m(N)} h(i)) / h(m(N))` to `m(N)`. Minimality gives
`sum_{N <= i < m(N)} h(i) < 1` and `sum_{N <= i <= m(N)} h(i) >= 1`, so the top weight lies in
`[0,1]` and the total mass is exactly one. Supports lie in `[N, m(N)]`, so they escape. Transport
along an equivalence carries this to any countable index set, in particular to the primes with
`h(p) = 1/p`.

**Quantum gap.** For the Route R first-wall field `W_t`, the corpus orientation theorems give
residue `-1` for `t > 0`, `+1` for `t < 0`, and `0` at `t = 0`. Let `mu` be any cofinal unit profile
for `p -> 1/p` and suppose `|A_N(W_t)| <= r` eventually with `r < 1`. Continuity of the norm and the
reading law give `|residue| <= r`, excluding `-1` and `+1`. Hence `t = 0`.

**Endpoint.** Specializing `t` to `2 Re rho - 1` at a Xi divisor point and using the corpus
identification of neutral grade with critical placement, a sub-quantum gap at every divisor point
gives the Riemann hypothesis. The threshold `r` may depend on the divisor point.

## Lean

Module `formal/GaloisForLFunctions/HTGeometry/CofinalUnitProfileResidue.lean`:

- `HasReferenceResidue`, `HasReferenceResidue.unique`, `HasReferenceResidue.of_summable_sub`
- `IsCofinalUnitProfile`, `profileAverage`, `tendsto_profileAverage`
- `unitWindowProfile`, `exists_isCofinalUnitProfile`, `exists_isCofinalUnitProfile_of_equiv`
- `primeHarmonicWeight`, `primeHarmonicResidue_unique`,
  `exists_isCofinalUnitProfile_primeHarmonic`

Module `formal/GaloisForLFunctions/RHTower/RouteRHarmonicQuantumGapCriterion.lean`:

- `routeRPrimeHarmonicAsymptotic_iff_hasReferenceResidue`
- `tendsto_profileAverage_criticalWall_neg_one_of_pos`,
  `tendsto_profileAverage_criticalWall_one_of_neg`,
  `tendsto_profileAverage_criticalWall_zero`
- `eq_zero_of_eventually_norm_profileAverage_le`
- `tendsto_profileAverage_criticalWall_zero_iff`
- `xiDivisorSupport_re_eq_half_of_eventually_norm_profileAverage_le`
- `riemannHypothesis_of_forall_xiDivisorSupport_re_eq_half`
- `riemannHypothesis_of_eventually_norm_profileAverage_lt_one`
- `exists_isCofinalUnitProfile_primeHarmonic_nthPrime`

Axioms: `[propext, Classical.choice, Quot.sound]` for every listed capstone.

## Hostile audit

- No RH premise, divisor criticality, or source-flatness hypothesis occurs anywhere in the two
  modules. The reading law and the window construction are pure summability statements.
- The criterion is not a disguised assumption of its conclusion: its hypothesis is an inequality
  about an explicitly constructed average, and both orientations are proved to violate it.
- It is not vacuous in either direction. Profiles exist unconditionally, and at neutral grade the
  average provably tends to zero, so the hypothesis is satisfiable exactly on the critical line.
- It does not close Route R. What is gained is a strictly larger target set for producers: exact
  annihilation is replaced by any uniform gap below the harmonic quantum, and the reading device is
  now arbitrary rather than the Euler sieve.
- Novelty status `[NOVELTY UNVERIFIED]`. The reading law is a Banach-limit-style extraction of a
  coefficient modulo `ell^1`; the parent literature is standard summability theory. No priority is
  claimed for the general law; the Route R application is corpus-internal.

## Door / frontier delta

Old open core: `Tendsto (fun N => S_N(W_{t_rho})) atTop (nhds 0)` for the restarted Euler sieve.

New open core: for **some** bounded cofinal unit profile `mu` on the primes and **some** `r < 1`,

`eventually ‖profileAverage mu N (routeRPrimeGammaXiCriticalWallField rho)‖ ≤ r`.

Any pre-divisor Stokes/Cartier producer may now be tested against a strict inequality, and may
choose its own reading device.

## Log

- 2026-08-06 — created directly in stage 3: general reading law and window construction proved and
  formalized in `HTGeometry`, Route R gap criterion and RH endpoint formalized in `RHTower`,
  targeted builds green, axiom audit clean.
