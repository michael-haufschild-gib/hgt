# Prime-torsion recurrence-polygon advance (2026-08-14)

## Mathematical delta

Created `docs/drafts/pipeline/2-fully-proven/prime-torsion-recurrence-polygon-complexity-law.md`.

For the equal-amplitude phase state
[
\Phi(z)=D^{-1/2}\sum_a z_a f_a
]
and projective torsion group (Q_{D,k}=\mu_k^D/\mu_k^{diag}), every finite target dictionary (Y) of size (N) satisfies
[
|E^{(k)}_{Y,\delta}|\le 4Ne^{-(1-4\delta^2)D/4}k^{D-1},\qquad 0<\delta<1/2.
]
Proof selects one captured torsion point per target; two points in the same trace-distance ball have relative root coordinates with empirical mean modulus at least (sqrt{1-4\delta^2}); real/imaginary Hoeffding yields the bound.

For prime (k), all nonzero power maps are automorphisms. If
[
4(k-1)Ne^{-(1-4\delta^2)D/4}<1,
]
then a positive fraction at least (1-4(k-1)Ne^{-\gamma D}) of torsion points generate complete order-(k) polygons whose every nonidentity power avoids all targets. If the reference is in the dictionary, good points partition into generator orbits of size (k-1), giving an explicit lower count on distinct polygons.

Maximal projective rational spectral rank shadows any selected polygon at arbitrarily late times: with (R=k\tau), the endpoint returns arbitrarily accurately and every exact rational slice (jR/k), (1\le j<k), remains (delta)-hard.

For bounded-dependence local circuit heaps,
[
N\le (s+1)\binom{M+s-1}{s}2^{\Delta s}.
]
With (D=2^n), (M=O(n)), (Delta=O(1)), (s=cD), and (c\Delta\log2<\gamma_\delta), Bertrand permits primes (k_D=e^{\eta D+o(D)}) for every (eta<\gamma_\delta-c\Delta\log2). One selected recurrence cycle has exponentially many equally spaced (Theta(D))-hard interior slices.

Formal corpus composition is exact only for ordinary trace-zero onsite-plus-edge qubit path Hamiltonians: dense residual full-measure maximal projective rank plus the explicit finite-size two-query Pauli separator yields permanent distinguishability from Haar on the same Hamiltonian and times.

## Hostile boundary

This is recurrence anatomy, not Brown onset. It does not control first polygon time, initial monotone/linear growth, every recurrence, the continuous interval between samples, or ambient (D^2) Choi complexity. Prime order and finite gate alphabet are load-bearing. Novelty remains unverified externally; targeted search found Brown–Susskind growth/recurrence and fractional-revival literature but no complete hard torsion polygon theorem. No Lean was written or run because shared corpus refactor remained active and other agents had live Lean processes.

## Master log

Appended exact advance and limits to `docs/drafts/pipeline/1-in-progress/static-local-complexity-law.md`.
