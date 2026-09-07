# CCM-FU: source-derived late-prime head neutralization

- **Stage:** 3-formalized
- **Type:** constructive local source control; paper and Lean proofs closed
- **Parent:** [adaptive prime ceiling](../1-in-progress/ccm-fu-adaptive-prime-ceiling.md)
- **Boundary:** no final signed energy bound or complete interleaving is assumed or claimed.

## Finite selector and energy release

For finitely many nonnegative weights w_p bounded by a, a nonnegative target h covered by their total mass admits a subset L with

`0 <= sum_L w_p-h <= a`,
`(sum_L w_p-h)^2 <= sum_L w_p^2`.

One proof takes weights until their sum first reaches h. The excess is at most the last weight, whose square is part of the selected square sum. Finite induction gives the same selection without assuming a favorable energy endpoint.

Apply this to an unprocessed late-prime set and its actual positive weights K_p(M). Its scalar head becomes `h-sum_L K_p`. The exact source block law then gives

`Q_(P union L) <= Q_P-h^2 = V_P`.

Thus the selected block releases the entire initial head square, while leaving a head whose magnitude is at most one maximum late coefficient. Every intermediate subset of that selected block stays below Q_P by the proved arbitrary-subset endpoint law. This provides a concrete local balancing operation, including control of its intermediate states.

## Unconditional initial availability

The literal initial head is nonnegative. Each active late coefficient has the exact first-block form `K_p(M)=(sqrt(M)-sqrt(p))*D(1)` and lies between zero and sqrt(M), because `0<D(1)<1`. The quadratic diagonal bounds the initial head by 27M. The proved source law `T(4N)/(4N)->+infinity` therefore supplies enough late mass at every sufficiently large cutoff 4N.

Consequently, without any energy-budget premise, a selected initial late-prime block exists at those cutoffs with head in `[-sqrt(M),0]`, head square at most M, complete energy at most the original nonempty energy, and every intermediate subset below the original diagonal. This is an initial operation, not an all-cutoff proof of SD1. Later smaller-prime steps still require the open joint signed budget and a growing interleaving.

## Lean certificate and verification

`RHTower.MobiusDivisorHeadNeutralization` contains nine public theorems. `exists_mass_cover_with_square_reserve` proves finite selection; `exists_mobiusDivisorLatePrime_head_neutralization` proves the exact local energy release under explicit availability conditions. The first-block identity, coefficient bound, initial-head identity, positivity and linear bound discharge those conditions from the source. `eventually_mobiusDivisorLatePrimeMass_covers_initial_head` supplies eventual availability, and `eventually_exists_mobiusDivisorInitialHeadNeutralization` is the unconditional capstone along cutoffs 4N.

Scratch verification and the exact leaf check with `lake env lean` passed. The leaf is wired once into `RHTower.lean`; no umbrella, dependency or full build was run. All nine new declarations were axiom-audited once and use only `propext`, `Classical.choice` and `Quot.sound`; no added axiom, proof placeholder or numerical premise occurs. `scripts/formal_tools.py lint` passed.
