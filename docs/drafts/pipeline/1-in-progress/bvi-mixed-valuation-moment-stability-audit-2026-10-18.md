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
- [x] Finish the bounded cross-field search and inspect every relevant result page; no semantic-completeness claim.
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
| Adaptive finite raw-observation protocol | `BiScaleUncertainty/PrimeAdaptiveMomentRecovery.lean`: `adaptive_raw_count`, `adaptive_observations_iff_common_sign`, `decode_selected_actual`; exact-data protocol, not a noisy adaptive guarantee |
| Sharp power-law barriers at zero and at a vanishing mode | `BiScaleUncertainty/PrimeReadoutSharpness.lean`: `one_mode_power_barrier`, `two_mode_power_barrier`; exact statements and normalization checked |

The previous proposal of fixed-block sixth-root stability is therefore a duplicate. It earns **zero credit**. The mixed fifth-order resonance is also already formalized.

## Remaining question, not an established result

For all divisor-sieve coordinates at once, can small errors in translated moments of orders two, three, five and six control the literal signal distance after one physical dyadic translation, uniformly across changing support and valuation strata?

A tentative paper mechanism uses a noise-dependent amplitude threshold. Cubic observations orient odd modes; fifth observations orient a lower active valuation class using a higher active class; sixth observations align signs within the highest significant class. One dyadic translation should realize the remaining sign, while small higher classes contribute an explicitly bounded error. This mechanism still needs a complete source comparison, exact normalization, and a native significance audit. No Lean implementation has started.

## Search coverage and limits

Completed searches include `sixth recovery` (all 31 lexical hits, two pages), `fifth readout` (all seven lexical hits), `sixth stability` (all 17 lexical hits), and a BVI-scoped deep search whose 20 candidate lemmas and 20 source arguments were inspected. The latter reported complete file inventory but substantial pending/stale compiler metadata; ranked results do not prove absence. Its proposed Selberg-inversion ingredient set does not itself recover signs from moments.

The whole-corpus deep query and a subsequent BiScale-scoped deep query both completed with `partial=false`, no errors, and 20 candidate plus 20 source statements each. Both inventories were reviewed. The former's proposed certificate-genealogy argument is irrelevant; the latter's proposed valuation-block argument does not establish mixed-support noise stability. An automated sufficiency label is not an applicability certificate.

Further lexical audits reviewed every hit: `valuation stability` (56 unique rows, three pages), `valuation translation` (72 unique rows, four pages), BiScale-scoped `stability` (130 unique rows, seven pages), and `translatedMoment` (eight rows). The latter search matches names/docs and does not inventory all uses: an exhaustive `rg` reference scan found 12 source files at that snapshot. Their relevant public interfaces were checked, including raw protocols and collision witnesses. Whole-tree source state must still be refreshed because concurrent work changes the frontier.

The last scoped deep snapshot inventoried 74,246 files with no pending inventory files, but semantic completeness was unmeasured; compiler metadata included 57,012 pending and 2,658 stale entries. File inventory completeness does not prove theorem applicability, freshness of every proof, or absence of prior work.

## 2026-10-19 current-state correction

A fresh worktree review found additional concurrent sources absent from the earlier snapshot:

- `SieveValuationPhaseRecovery.coordinates_eq_or_highest_flip`: fifth and sixth arrays leave only the highest active valuation sign.
- `SieveCanonicalTranslation.sieveSeq_companion`: that coordinate companion is a literal shift by `canonicalShift`.
- `SieveHalfPeriodTranslation.shift_representable_iff`: a shifted sieve stays in the divisor-sieve family exactly when twice the shift is a period.
- `SieveAffineTranslationAnchoring.fifth_sixth_eq_iff` and `all_translated_eq_iff_fifth_sixth`: exact complete translated-data classification. Their original source statements and proofs were inspected, including the actual companion identity. A fresh documented lexical search finds all nine declarations in `SieveValuationPhaseRecovery`.

Thus the exact mixed-support question is already answered in the current corpus. The earlier field-programme open-item text is stale for that question.

The active [physical-translation stability card](../3-formalized/biscale-physical-translation-stability-2026-10-19.md) also already pursues a stronger fifth/sixth-only uniform noise bound, with the threshold idea credited to this audit and an earlier stratum-obstruction card. Its paper argument and stated open gates were read. It is concurrent proposed work, not an established Lean theorem, and will not be duplicated here. The card's main claim is a uniform literal-signal error at most `5*(sum φ(q))*ε^(1/6)` for raw error ε≤1, with physical-translation sharpness still to formalize.

**Decision:** retire this as a separate BVI implementation candidate. Keep the audit here for existing cross-links and programme continuity. The positive exact recovery statements already exist in Lean; the quantitative survivor is tracked by the concurrent card. No negative mathematical theorem is asserted. Accepted contribution count remains **0 / 100**.

## Classical baseline

The qualitative sixth-order reconstruction threshold has precedent in Grünbaum–Moore, *Acta Crystallographica A* 51 (1995), 310–323, DOI [10.1107/S0108767394009827](https://journals.iucr.org/paper?buy=yes&cnor=gr0371). The rational/cyclotomic restrictions matter; this is not a uniform theorem for arbitrary real cyclic signals. [Keleti–Kolountzakis](https://eigen-space.org/mk/ps/three.pdf) explains the Fourier zero-sum-product mechanism and the distinction.

## Closure discipline

This is a prior-work audit, not a mathematical no-go. Existing positive recovery and stability theorems remain usable and already formalized. If the remaining proposal is only their routine assembly, record that conclusion and retire the candidate without manufacturing a new theorem or contribution count.
