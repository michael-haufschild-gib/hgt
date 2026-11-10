# Flat-packet contacts are overlap lengths

- **ID:** A80-contact-bridge
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:** Directed ratio-`k` contacts between `(aN,bN]` and `(cN,dN]`, divided by `N`, converge to `max(min(b,d/k)−max(a,c/k),0)`. For one window this equals its flat-packet autocorrelation at `log k`, divided by `exp(log k/2)`.

## Proof

The contact set is the integer interval with lower endpoint `max(aN,⌊cN/k⌋)` and upper endpoint `min(bN,⌊dN/k⌋)`. Natural subtraction gives its exact cardinality. The normalized floors converge to their real endpoints; finite weighted sums preserve the limit. The existing flat-packet autocorrelation formula identifies the self-contact limit.

A flat packet is the difference of two bounded monotone capped exponential steps, hence has bounded variation. With `B=⌊N/R⌋` and `B≥max(R,Q)`, Euclidean division gives `RB≤N≤(R+1)B` and `QN≤(Q+1)RB`. Thus `(N,QN]` lies in a fixed family of complete blocks eventually.

## Formalization

- Module: `HodgeTheoryOfAFixedPart/TheContactsOfFlatPacketsAreTheirOverlapLengths.lean`.
- `flatContactPoints_eq`, `tendsto_flatContactPoints_card_div`, `tendsto_weighted_flatContactPoints`.
- `packetAutocorr_flatPacket_log_div_exp`, `tendsto_flatContactPoints_self_autocorr`.
- `boundedVariationOn_flatPacket`, `scaledWindow_subset_completeBlocks`, `eventually_completeBlock_padding`.
- Direct Lean check passed; axiom audit omitted as requested.
- Imported by `HodgeTheoryOfAFixedPart.lean`.

The full comb-to-block-form convergence and eventual positivity remain open on the assembly card.
