# Prime coherence boundary charge at vanishing energy

- **ID:** critical-rigidity-prime-boundary-charge
- **Stage:** 1-in-progress
- **Disposition:** Paused with the parent programme. No further research authorized.
- **Type:** CANDIDATE
- **Question:** Which source data must survive an adjunction-energy limit?

## Proved concentration family

Normalize the coherent prime witness by `B_Q=Σ_(p≤Q)log p/p`:

`a_p(Q)=sqrt(p−1)/(p B_Q)` for primes `p≤Q`.

The exact response and energy identities give `P_Q(a)=1` and `L_Q(a)=1/B_Q→0`. On prime-supported packets, the generator decomposes as `G F_a=P_Q(a)−F_(τa)`. Its centered part has squared norm at most `(log 2/2)L_Q(a)`, hence tends to zero. Thus the actual generator output converges to a nonzero constant while input adjunction energy vanishes. The finite-tolerance construction for every real charge, preserved by actual harmonic projection, is formalized in `VanishingEnergyCharge.lean`; see `3-formalized/arithmetic-source-charge-at-vanishing-energy.md`.

This is a concrete source-concentration profile, not a hypothetical negative Weil state. Adjunction-energy convergence alone does not preserve the arithmetic generator's receiving charge.

## Positive survivor and stronger target

The complete-period output quotient by constants has a unique bounded prime-sector extension, with sharp squared norm `log 2/2`. The missing datum is precisely the coherent constant charge. A stronger target is an exact graph-closure classification: prime-sector limits consist of the bounded diagonal output together with an independently retained constant charge.

Composite fibres `rp` may create the same phenomenon at every receiving conductor `r`; this remains the separate nonconstant-fibre candidate. If true, source-preserving concentration theory must retain conductor-indexed charges rather than a single global pole reading.

## Physical-horizon target

The stronger statement for every `N≥Q` has a dependency-closed proof and Lean draft in `2-fully-proven/physical-horizon-source-charge-at-vanishing-energy.md` and `PhysicalHorizonCharges.lean`; verification is pending. Existing `harmonicConductorPacket_le_log` bounds a packet's harmonic square by `[log N+17(1+log Q)]` times coefficient mass, hence by `52log N` times that mass when `N≥Q≥2`. The actual pole projection contracts the input's horizon square, by `sum_sq_poleProj`; the excitation gap bounds its unprojected coefficient mass in adjunction energy.

The stronger target is thus pole-neutral inputs with both adjunction energy and normalized physical norm tending to zero, while the complete arithmetic generator approaches a prescribed pole profile in normalized physical norm. This would exclude a small-horizon sampling explanation of the source-charge phenomenon. It still concerns the complete arithmetic dilation generator, whose finite-horizon scalar and complementary-row corrections must be retained when comparing with the actual prime matrix.

## Required audit

Complete the physical-horizon audit and prove the graph-closure statement before promoting it beyond a target. No conclusion about negative complete states, Gamma cancellation, or RH follows without those additional source restrictions.
