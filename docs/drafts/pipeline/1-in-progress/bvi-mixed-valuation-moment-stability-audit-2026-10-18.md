# BVI: mixed-valuation moment recovery — prior-work audit

- **ID:** bvi-mixed-valuation-moment-stability-audit-2026-10-18
- **Stage:** 1-in-progress
- **Type:** CANDIDATE / NOVELTY AUDIT
- **Source:** 100-contribution programme; explicit user instruction to search the Lean corpus before claiming new work.
- **Statement:** Determine whether noisy recovery across all two-adic valuation classes, modulo one actual translation, adds anything beyond existing sieve-moment recovery. No novelty claim or new contribution is accepted.

## Goal and gates

- [x] Search the corpus through the documented research command.
- [x] Read the exact existing fifth-order and sixth-order readout statements.
- [x] Detect existing noise stability, raw-observation protocols, and sharpness results.
- [ ] Finish the cross-field search and inspect every relevant result page.
- [ ] Identify a substantive native BVI consequence, beyond combining known ingredients.
- [ ] If a candidate survives, complete its paper proof and external novelty audit before new Lean code.
- [ ] Formalize only the exact surviving statement; audit original source, axioms, imports, index and lint.

## Existing work: do not re-prove or count

All paths below are under `formal/GaloisForLFunctions/`.

| Existing capability | Source / declaration |
|---|---|
| Modes six and ten: all moments through degree five miss a relative sign; degree six resolves it up to common sign | `BiScaleUncertainty/SixthSievePhaseRecovery.lean`: `evenPair_through_five_flip`, `evenPair_sixth_flip_difference`, `evenPair_recovery_iff`; already exposed to BVI by `bvi_evenPair_sixth_moment_sign_hierarchy` |
| Arbitrary fixed two-adic valuation class: sixth readouts recover a common sign, including zero coordinates | `BiScaleUncertainty/SixthValuationPhaseRecovery.lean`: `sixth_readouts_eq_iff_valuation_sign`, `sixth_moments_recover_valuation_block` |
| Mixed classes: fifth readout is exactly the lower coordinate cubed times the higher coordinate squared | `BiScaleUncertainty/MixedValuationQuintic.lean`: `fifthReadout_eq`, `fifthReadout_and_upper_sq_iff`; the latter includes the exact zero exception |
| Uniform noise stability without a support/nonvanishing assumption | `BiScaleUncertainty/SixthReadoutStability.lean`: `CubedGram.stability`, `primeFamily_sixth_stability` |
| Literal raw observations control normalized sixth-readout noise and recovery | `BiScaleUncertainty/PrimeRawMomentRecovery.lean`: `noise_comparison`, `raw_stability` |
| Adaptive finite raw-observation protocol | `BiScaleUncertainty/PrimeAdaptiveMomentRecovery.lean`: interfaces found; exact scope under review |
| Sharp power-law barriers at zero and at a vanishing mode | `BiScaleUncertainty/PrimeReadoutSharpness.lean`: interfaces found; exact scope under review |

The previous proposal of fixed-block sixth-root stability is therefore a duplicate. It earns **zero credit**. The mixed fifth-order resonance is also already formalized.

## Remaining question, not an established result

For all divisor-sieve coordinates at once, can small errors in translated moments of orders two, three, five and six control the literal signal distance after one physical dyadic translation, uniformly across changing support and valuation strata?

A tentative paper mechanism uses a noise-dependent amplitude threshold. Cubic observations orient odd modes; fifth observations orient a lower active valuation class using a higher active class; sixth observations align signs within the highest significant class. One dyadic translation should realize the remaining sign, while small higher classes contribute an explicitly bounded error. This mechanism still needs a complete source comparison, exact normalization, and a native significance audit. No Lean implementation has started.

## Search coverage and limits

Completed searches include `sixth recovery` (all 31 lexical hits, two pages), `fifth readout` (all seven lexical hits), `sixth stability` (all 17 lexical hits), and a BVI-scoped deep search whose 20 candidate lemmas and 20 source arguments were inspected. The latter reported complete file inventory but substantial pending/stale compiler metadata; ranked results do not prove absence. Its proposed Selberg-inversion ingredient set does not itself recover signs from moments.

A whole-corpus deep query for mixed valuation, noisy phase recovery and physical translation is in progress. Broad first-page searches are exploratory only; they are not evidence that no existing theorem exists.

## Classical baseline

The qualitative sixth-order reconstruction threshold has precedent in Grünbaum–Moore, *Acta Crystallographica A* 51 (1995), 310–323, DOI [10.1107/S0108767394009827](https://journals.iucr.org/paper?buy=yes&cnor=gr0371). The rational/cyclotomic restrictions matter; this is not a uniform theorem for arbitrary real cyclic signals. [Keleti–Kolountzakis](https://eigen-space.org/mk/ps/three.pdf) explains the Fourier zero-sum-product mechanism and the distinction.

## Closure discipline

This is a prior-work audit, not a mathematical no-go. Existing positive recovery and stability theorems remain usable and already formalized. If the remaining proposal is only their routine assembly, record that conclusion and retire the candidate without manufacturing a new theorem or contribution count.
