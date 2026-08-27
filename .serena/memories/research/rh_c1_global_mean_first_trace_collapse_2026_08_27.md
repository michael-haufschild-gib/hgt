# C1 global-mean Pluecker first-trace collapse (2026-08-27)

Frontier map is read-only for this task.

Files:
- formal/GaloisForLFunctions/HTGeometry/InfiniteHilbertDispersion.lean
- formal/GaloisForLFunctions/RHTower/GammaSewnMobiusApertureStokesGlobalMeanFirstTrace.lean
- docs/drafts/pipeline/1-in-progress/c1-global-mean-pluecker-first-trace.md

Results:
1. Generic unconditional theorem `GaloisForLFunctions.HTGeometry.tsum_pairwise_hilbert_dispersion` extends finite Hilbert dispersion to summable infinite families.
2. C1 ordered double packet-mean dispersion collapses exactly to weighted second moment minus squared barycenter norm.
3. Local Bernoulli covariance plus global mean dispersion telescopes to `globalTraceMass = rawFirstMoment - ||globalMeanBarycenter||^2`.
4. Physical incidence is local: four neighboring packets per interior cell, one contribution at `(0,0)`; barycenter is nonzero.
5. Every packet's four coordinate means sum exactly to `2` (rank-two occupation conservation).
6. Coordinate node bounds plus rank-two occupation sharpen packet and global raw ceilings from `2/25` to `8/125`.
7. Define node-free physical occupation `occupation(u)`. It is nonnegative, summable, and `sum_u occupation(u)=2`.
8. Square-root incidence factors exactly: `incidence(u) = sqrt(physicalNode(u)) * occupation(u)`. Therefore `collisionEnergy = sum_u physicalNode(u) * occupation(u)^2`.
9. Every finite physical window obeys local and global reciprocal-node Cauchy. Every packet deposits at least `2*a_z` in its four labels. Packet resistance is exactly `((e+1)^2+(e+2)^2) * (1/Bp + 1/Bq)`.
10. Reverse incidence has multiplicity at most four. Summing local packet windows yields the unconditional additive capacity `sum_z a_z^2 / R_z <= collisionEnergy`; a closed prime/depth denominator form is in Lean.
11. Stronger constructive-interference law: `collisionEnergy >= sum_z a_z^2 * sum_i node(z,i)*mean(z,i)^2`. This is exact packet self-collision, with no overlap loss.
12. Coordinate Cauchy proves each packet self-collision is at least `4*a_z^2/R_z`; Lean therefore proves the exact self-collision sum dominates the additive capacity sum.
13. Completed trace bounds:
    `traceMass <= rawFirstMoment - packetSelfCollision <= rawFirstMoment - additiveCapacity`.
14. Exact Xi landing remains equivalent to `rawFirstMoment - collisionEnergy = thetaCuspNormalizedEvenMoment 1 / 2`.

Verification:
- direct `lake env lean` passes;
- exact builds pass: InfiniteHilbertDispersion 1935/1935, C1 module 12792/12792;
- expanded axiom audit passes: only `propext`, `Classical.choice`, `Quot.sound`;
- formal lint reaches new module and reports no forbidden declarations there; repo-wide exit remains red only on unrelated concurrent unreachable sieve modules;
- no full or umbrella build run.

Novelty discipline:
- Generic covariance identities, nonnegative-square interference, fixed-size/projection-DPP rank conservation, and finite Cauchy are classical; no novelty claimed there.
- Candidate novelty is only corpus-specific arithmetic realization: exact adjacent-prime/depth Pluecker occupation conservation, exact self-collision and additive capacity lower bounds, and completed-Xi coefficient reduction.
- Literature audit found fixed-size DPP background but no source for this prime-depth family or exact trace inequalities.

Remaining open core:
- compare `rawFirstMoment - packetSelfCollision` with `thetaCuspNormalizedEvenMoment 1 / 2`;
- quantitative routes: direct control of normalized squared denominator terms `a_z^2`, or a cofinal-denominator upper bound strong enough for a finite packet prefix to separate the audited theta interval;
- `8/125` alone remains compatible with theta bounds.
