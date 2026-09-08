# CCM-FU: bounded quotient profiles

- **Stage:** 1-in-progress
- **Parent:** [source-local two-prime comparison](ccm-fu-two-prime-local-blocks.md)
- **Objective:** Resolve the finite unit-cutoff head remaining after uniform eventual factor-two comparison. Retain unbounded dilation and the exact clipped phase.

## Frozen diagnostic

Read the existing complete unit-clock CSV through1024; do not recompute divisor defects, channels, subsets or paths. Test the candidate global envelope `K_1(N)<=sqrt(N)/8`, record its largest normalized value, and test the sufficient ordinary-prefix envelope `sum_(k=1..N) D(k)<=(N+1)/8`. These are separate questions: failure of the prefix envelope need not refute the channel envelope. Numerical outcomes guide analytic proofs only and supply no Lean premise.

## Analytic target

The normalized clipped channel is a convex combination of the two normalized adjacent unit endpoints, with weights adjusted by the square-root masses. The [global unsigned envelope](../3-formalized/ccm-fu-global-unsigned-envelope.md) is now closed in Lean: `K_d(M)<=a*sqrt(M)` for every M,d, where `a=log(2*pi)/2-gamma-1/6<9/50`. The unit asymptotic coefficient is strictly greater than 9/100. Consequently, there exists N0 such that `K_d(N)<=2K_1(N)` for every N>=N0 and every dilation d, with no quotient restriction.

The weighted complete-block ceiling and terminal partial-block control are both closed. Source reflection orientation, an exact square-root clock covariance bound, and global source positivity extend the [optimal unweighted smooth ceiling](../3-formalized/ccm-fu-signed-smooth-block-ceiling.md) to every actual Abel cutoff. No numerical premise is used. The sharper one-eighth envelope from the frozen diagnostic remains unproved; it is unnecessary for the eventual factor-two comparison.

There also exists P0 such that `K_(pd)(M)<=2K_d(M)` for every integer p>=P0 and every M,d. Any two sufficiently large distinct active primes satisfy the original complete energy ceiling at every parent cutoff and every prime ratio. A unit factor-two failure therefore has N<N0; an original two-prime ceiling failure must involve at least one prime from a fixed finite head. The parent cutoff in that energy failure can still be unbounded. No explicit threshold, arbitrary processed-state extension, or SD1 conclusion is claimed.

## Saved-data outcome and analytic continuation

All 1024 saved unit endpoints satisfy the proposed one-eighth channel envelope. The largest normalized value is about 0.111093 at cutoff120. The sufficient prefix envelope fails at 16 saved cutoffs, with worst deficit about 2.28849 at119. These are numerical diagnostics only. A second summation must retain the original terminal prefix multiplied by the endpoint clock; it cannot silently replace the failed first-prefix bound.

The [large first-prime orientation theorem](../3-formalized/ccm-fu-large-prime-orientation.md) closes the entire sector `M<=5p` at every sufficiently large parent cutoff. The exact unit endpoints through5 have a one-fifteenth square-root ceiling, using only analytic logarithm, Euler-constant and rational square-root inequalities. Clipped interpolation transfers this ceiling to all dilations in the sector. Only cofactors one through four can have nonzero child channels, and every parent channel has the matching eventual lower bound. Thus `K_(pd)(M)<=K_d(M)` holds for every cofactor. A first prime in this sector preserves every retained sign; any second prime contracts energy and meets the original ceiling.

For one universal parent threshold, the orientation result still forces both `5p<M` and `5q<M` in an original two-prime ceiling failure. The global envelope additionally closes every middle quotient profile once the unit cutoff is sufficiently large. Remaining obligations are the finite unit-cutoff head, energy interactions involving a small prime, and arbitrary processed signed states needed for an exhaustive schedule. The raw unsigned comparison and two operations from the empty state do not establish that schedule.

The diagnostic is reproducible from the [saved-vector reanalysis](../2-fully-proven/computations/ccm-fu-adaptive-prime-energy-2026-09-06/bounded_quotient_profile_reanalysis.py) and its [result](../2-fully-proven/computations/ccm-fu-adaptive-prime-energy-2026-09-06/bounded-quotient-profile-reanalysis.json). It regenerates no arithmetic channel.
