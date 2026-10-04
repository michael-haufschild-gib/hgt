# Route PM: actual tested scale transform from a complete-source bound

- **ID:** pm-ramanujan-band-tested-scale
- **Stage:** 3-formalized
- **Type:** THEOREM (paper and Lean)
- **Continuation:** `../1-in-progress/pm-ramanujan-band-spectral-escape.md`.

## Exact statements and paper proof

Let F_X be the actual normalized complete-band critical Mellin vector, W_X its literal cutoff-phase translate, and q_h(X)=<h,W_X> for an arbitrary L2 frequency test h. The existing leaves identify their representatives and their exact complete signed-energy norms.

The phase pairing for each fixed band is continuous: its frequency integrand is dominated by the integrable product of two L2 representatives, and the scalar phase is continuous. The natural cutoff pair (floor X,floor(2X)) is measurable and countable-valued. Composing the jointly measurable countable family with that pair and the actual log phase proves q_h measurable. The guarded literal moving trace is jointly measurable in cutoff and frequency by the same countable-family construction. Its pairing with h is integrable at every X>=1 and equals q_h(X).

On each finite interval [1,B], the natural band takes finitely many vector values; X^epsilon is bounded there when epsilon>=0. Thus W_X is locally bounded. If F_X tends in norm to a fixed F, its tail is bounded; the finite-interval result and the phase isometry then give a global bound for W_X on [1,infinity). This is a consequence inside the proposed convergence contradiction, not an unconditional growing-cutoff bound.

Given this global bound C, the full cutoff-frequency integrand for Re(z)>1/2 is integrable. Joint measurability was proved above. Each frequency slice is an L2 product. The integral of its absolute value is at most ||h||^2+C^2, by the pointwise square inequality and exact L2 norm identity. The remaining cutoff weight is X^(-Re(z)-1/2), integrable on [1,infinity). Fubini therefore applies to the actual representatives. It gives integrability of the tested scale integrand and its exact frequency-first formula.

Set the tested source to zero below cutoff1 and compose with inversion. This reciprocal source is measurable, globally bounded, locally integrable and zero above1. It is O(1) near0 and has every exponential upper bound at infinity. The corpus Mellin differentiability theorem shows its transform holomorphic on Re(s)>0. The exact reciprocal Mellin identity identifies it with the actual tested scale transform at s=z-1/2. Thus the tested transform is holomorphic on Re(z)>1/2 under the proposed fixed-profile convergence, with all regularity and bounds derived internally.

For epsilon>0 and Re(z)>1, Fubini and the audited literal moving-band identity give the complete zeta-cleared arithmetic identity after testing. The displayed quotient requires r=epsilon+1/2+i*tau-z nonzero where the test is nonzero; this explicit support condition will be discharged by the compact test interval and the continuation tube. No arithmetic factor or mixed term is dropped.

## Contribution and remaining hard problem

This closes the actual-source side of the proposed analytic continuation argument. Arithmetic-side compact-kernel holomorphy, analytic uniqueness at the boundary, the variable-profile Abel remainder and the spectral-escape conclusion remain. The RH-producing complete signed-energy ceiling as epsilon decreases to zero is unchanged. No RH proof or falsification is claimed.

## Verification

2026-10-03 extension: holomorphy now has a separate `differentiableAt_pmRamanujanBandTestedScale_integral_of_bound` export. The old convergence theorem derives that bound and invokes it. This exposes the exact existing proof requirement for the compact-profile contradiction; it does not supply the unknown arithmetic bound. Fourteen exports total. Targeted old-mode leaf build passed (211 seconds); final actual-file Lean passed with no diagnostics. Both new theorem and changed wrapper passed separate axiom queries with only propext, Classical.choice and Quot.sound.

All thirteen public declarations and private dependencies passed foreground scratch Lean with exit0 and no diagnostics. No new axioms, assumptions of RH, heartbeat changes or computations. The leaf is promoted and wired once. Targeted `lake --old build GaloisForLFunctions.RHTower.PMRamanujanBandTestedScale` passed (only the new leaf built, 17 seconds). Mandatory `lake env lean GaloisForLFunctions/RHTower/PMRamanujanBandTestedScale.lean` passed with no diagnostics. All thirteen exports passed separate /tmp axiom queries with only propext, Classical.choice and Quot.sound. Lint has ten unrelated unreachable modules, none own. No umbrella build or heartbeat increase.
