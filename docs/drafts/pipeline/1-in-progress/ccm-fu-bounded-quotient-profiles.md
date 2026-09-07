# CCM-FU: bounded quotient profiles

- **Stage:** 1-in-progress
- **Parent:** [source-local two-prime comparison](ccm-fu-two-prime-local-blocks.md)
- **Objective:** Eliminate the bounded quotient profiles left by the universal large-quotient factor-two theorem. Retain unbounded dilation and the exact clipped phase.

## Frozen diagnostic

Read the existing complete unit-clock CSV through1024; do not recompute divisor defects, channels, subsets or paths. Test the candidate global envelope `K_1(N)<=sqrt(N)/8`, record its largest normalized value, and test the sufficient ordinary-prefix envelope `sum_(k=1..N) D(k)<=(N+1)/8`. These are separate questions: failure of the prefix envelope need not refute the channel envelope. Numerical outcomes guide analytic proofs only and supply no Lean premise.

## Analytic target

The normalized clipped channel is a convex combination of the two normalized adjacent unit endpoints, with weights adjusted by the square-root masses. Thus a global normalized unit envelope transfers to every dilation. A sufficiently small such envelope, together with the strictly stronger eventual unit lower coefficient already proved, would close all dilations at sufficiently large parent cutoffs. The actual small parent regime would still need an analytic proof.

Current status: the candidate global envelope and the remaining bounded quotient comparisons are unproved. The universal large-quotient comparison remains closed; no all-cutoff ceiling or SD1 conclusion is claimed.

## Saved-data outcome and analytic continuation

All 1024 saved unit endpoints satisfy the proposed one-eighth channel envelope. The largest normalized value is about 0.111093 at cutoff120. The sufficient prefix envelope fails at 16 saved cutoffs, with worst deficit about 2.28849 at119. These are numerical diagnostics only. A second summation must retain the original terminal prefix multiplied by the endpoint clock; it cannot silently replace the failed first-prefix bound.

The [large first-prime orientation theorem](../3-formalized/ccm-fu-large-prime-orientation.md) closes the entire sector `M<=5p` at every sufficiently large parent cutoff. The exact unit endpoints through5 have a one-fifteenth square-root ceiling, using only analytic logarithm, Euler-constant and rational square-root inequalities. Clipped interpolation transfers this ceiling to all dilations in the sector. Only cofactors one through four can have nonzero child channels, and every parent channel has the matching eventual lower bound. Thus `K_(pd)(M)<=K_d(M)` holds for every cofactor. A first prime in this sector preserves every retained sign; any second prime contracts energy and meets the original ceiling.

For one universal parent threshold, every original two-prime ceiling failure requires both `5p<M` and `5q<M`. Combining this with the existing quotient-tail theorem confines large-parent unit factor-two failures to `5<=M/p<T`. The finite parent regime and these remaining middle quotient profiles are still open. This controls two operations, not an entire growing schedule.

The diagnostic is reproducible from the [saved-vector reanalysis](../2-fully-proven/computations/ccm-fu-adaptive-prime-energy-2026-09-06/bounded_quotient_profile_reanalysis.py) and its [result](../2-fully-proven/computations/ccm-fu-adaptive-prime-energy-2026-09-06/bounded-quotient-profile-reanalysis.json). It regenerates no arithmetic channel.
