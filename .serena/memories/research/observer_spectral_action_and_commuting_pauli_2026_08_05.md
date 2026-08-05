# Observer–spectral action frontier (2026-08-05)

Master goal remains Brown–Susskind full growth–plateau–recurrence law for ordinary static local Hamiltonians plus permanent locality/Haar separation.

## Exact progress

Formalized all-pairwise-commuting Pauli carrier exclusion:
- module: `formal/GaloisForLFunctions/HTGeometry/CommutingPauliObserverRankDominance.lean`
- card: `docs/drafts/pipeline/3-formalized/commuting-pauli-observer-rank-dominance.md`
- fixed-support fibre bound: at most `2^|S|-1`
- global bound: `r <= sum_{k<=q}(2^k-1) choose(n,k)`
- observer dominance: commuting-carrier codimension `m-r >= v_(n,q)=2 sum choose(n,k)`
- exact support sum/binomial identity formalized
- targeted `lake env lean`, axiom audit, repo lint, and final `lake build GaloisForLFunctions.HTGeometry.CommutingPauliObserverRankDominance` pass
- axioms only propext/Classical.choice/Quot.sound
- no stale Lean processes

This closes all pure commuting Pauli frames and Pauli-coordinate mixed continuous/periodic carriers. Live structured threat requires genuinely noncommuting cancellation in observer-stationary kernel.

## Conjecture jump

New Stage-1 card:
`docs/drafts/pipeline/1-in-progress/observer-spectral-shortcut-action-law.md`

Proposed master action:
`A(t,R)=min(v_(n,q) log t, I^comp_(n,q,eps)(R))`,
where `I^comp` is negative log of exact circuit-easy target Haar mass on each Hamiltonian's completed projective spectral phase closure, averaged over Gaussian ensemble.

The initial version incorrectly used full Fubini–Study target mass. Hostile attack rejected this: fixed-q endpoint ensemble has only polynomial coefficient dimension, and no ensemble-transfer theorem proves Fubini–Study target mass. Fubini–Study cost remains a separate desired comparison theorem.

Interpretation: observer-rank growth, completed-orbit plateau, and recurrence are regimes of one information action. Still a wild conjecture; no paper/Lean claim authorized.

## RHTower structural relation

Exact shared mechanism: cancelled/kernel directions cannot be discarded. Successful RHTower routes prove them harmless or make them reappear as transverse/exceptional mass; failed routes leave cancellation debt. Quantum analogue: stationary directions pay observer codimension; spectral/refocusing directions pay completed-orbit target information. The missing theorem is selector-uniform exceptional-carrier completeness.

Promising reduction: isotropic Gaussian coefficients split radial/angular and `H(r omega)=rH(omega)`. For fixed direction, large time is radial averaging along one spectral phase flow; nontrivial characters are damped by radial Fourier transform. Stationary/near-resonant angular directions are where completion is slow. Exact remaining frontier appears to be a uniform angular small-divisor/sublevel-volume theorem strong enough for the circuit selector union.

## Files changed

- active observer-rank card: now local/pre-capacity branch of master action
- master `static-local-complexity-law.md`: append-only research log
- HTGeometry umbrella import added
- new conjecture card and Stage-3 theorem card
