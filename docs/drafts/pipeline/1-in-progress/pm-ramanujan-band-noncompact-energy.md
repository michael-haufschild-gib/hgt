# Route PM: noncompact energy of the complete normalized bands

- **ID:** pm-ramanujan-band-noncompact-energy
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** actual complete-band cleared identity, positive residue test, new audited uniform fixed-profile separation.

## Hard target

For every epsilon>0, find c>0 such that for every compact set K in the actual critical-frequency L2 carrier and every real B, some X>=B has distance at least c from every member of K. Equivalent useful formulation: every finite family of profiles misses a cofinal actual vector by a common positive radius.

This is stronger than failure of convergence to one fixed vector. It would show that no compact collection of normalized profiles accounts for the complete source energy. It still would not exclude a bounded noncompact family or prove the damping-margin upper ceiling needed for RH.

## New proof mechanism to test

For fixed L2 h and F, the literal phase pairing <h,U_u F> is the Fourier transform of the L1 product conj(h)*F. Riemann-Lebesgue would make it tend to0 as u tends to infinity. The uniform norm bound on these functionals makes this convergence uniform over a compact set of profiles, by a finite epsilon-net.

If the actual normalized vectors F_X had a relatively compact tail, then q_h(X)=<h,U_(log X/(2*pi)) F_X> would tend to0. The tail would be bounded; finite-cutoff source bounds supply the remaining global bound. Measurability is already proved for the actual scalar q. The bounded-null Abel lemma then gives delta times the actual tested scale integral tending to0 after multiplication by exp(-i*gamma*u).

The existing source-side holomorphy and complete continued identity were stated under proposed strong convergence, but their actual proofs use only its internally derived global source bound. Expose the same proofs with that bound derived from relative compactness; do not assume an unproved arithmetic estimate. The positive Hardy zero and full positive residue test then give the same contradiction. No simplicity assumption is needed.

To obtain a single separation radius uniform in both K and the tail start B, prove the actual normalized image of every bounded cutoff interval totally bounded: only finitely many floor pairs occur, and each corresponding vector is multiplied by the continuous scalar X^epsilon on a compact interval. If arbitrarily small finite coverings existed on suitable tails, these finite heads would make the whole range totally bounded. Its compact closure in complete L2 would contradict the preceding argument.

## Checks still required

Search157 targets literal phase weak mixing and uniform convergence on compact sets. The Riemann-Lebesgue applicability, bounded-source continuation interface, actual-tail compactness contradiction and finite-head total boundedness must be proved, not inserted as premises. Current unconditional fixed-profile separation is in `PMRamanujanBandSpectralEscape`. Physical-carrier transfer is undergoing final audit; integer transfer has a separate paper proof. Do not retire the fixed-profile approach as a completed no-go before auditing the strongest positive noncompact-energy survivor exposed here.
