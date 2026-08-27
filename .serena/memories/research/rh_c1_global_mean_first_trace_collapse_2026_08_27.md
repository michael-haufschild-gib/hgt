# C1 global-mean Pluecker first-trace collapse (2026-08-27)

Frontier map is read-only for this task.

Files:
- formal/GaloisForLFunctions/HTGeometry/InfiniteHilbertDispersion.lean
- formal/GaloisForLFunctions/RHTower/GammaSewnMobiusApertureStokesGlobalMeanFirstTrace.lean
- docs/drafts/pipeline/1-in-progress/c1-global-mean-pluecker-first-trace.md

Results:
1. Generic unconditional theorem `GaloisForLFunctions.HTGeometry.tsum_pairwise_hilbert_dispersion` extends finite Hilbert dispersion to summable infinite families.
2. C1 ordered double packet-mean dispersion collapses exactly to weighted second moment minus squared barycenter norm.
3. Local Bernoulli covariance plus global mean dispersion telescopes to
   `globalTraceMass = rawFirstMoment - ||globalMeanBarycenter||^2`.
4. Physical incidence is local: four neighboring packets per interior cell, one contribution at `(0,0)`; barycenter is nonzero.
5. Every packet's four coordinate means sum exactly to `2` (rank-two occupation conservation).
6. Coordinate node bounds plus rank-two occupation sharpen packet and global raw ceilings from `2/25` to `8/125`.
7. Define node-free physical occupation `occupation(u)`. It is nonnegative, summable, and `sum_u occupation(u)=2`.
8. Square-root incidence factors exactly:
   `incidence(u) = sqrt(physicalNode(u)) * occupation(u)`.
   Therefore
   `collisionEnergy = sum_u physicalNode(u) * occupation(u)^2`.
9. Every finite physical window obeys a reciprocal-node resistance/capacity inequality. Every packet `z` deposits at least `2*a_z` in its four labels, yielding `(2*a_z)^2 <= resistance(z) * collisionEnergy`. Packet resistance is closed exactly as `((e+1)^2+(e+2)^2) * (1/Bp + 1/Bq)` for the two depth-zero prime nodes.
10. Exact Xi landing is equivalent to
   `rawFirstMoment - sum_u physicalNode(u)*occupation(u)^2 = thetaCuspNormalizedEvenMoment 1 / 2`.

Verification:
- direct Lean check passes;
- exact builds pass: InfiniteHilbertDispersion 1935/1935, C1 module 12792/12792;
- new theorem axiom audits: only `propext`, `Classical.choice`, `Quot.sound`;
- formal lint reaches new module; repo-wide failure only unrelated concurrent unreachable Sieve/HTGeometry modules.

Novelty discipline:
- Generic covariance identities, fixed-size/projection-DPP rank conservation, and finite Cauchy capacity are classical; no novelty claimed there.
- Candidate novelty is only arithmetic specialization: exact prime-depth Pluecker occupation conservation, collision factorization/capacity certificate, and completed-Xi coefficient reduction.
- Literature audit found standard projection-DPP/fixed-size rank facts but no source for this arithmetic prime-depth family or exact Xi landing law.

Remaining open core:
- prove/refute the conserved-occupation scalar identity.
- Immediate quantitative route: bound one explicit block-weight/four-cell-resistance certificate or sharpen the raw weighted node expectation enough to separate the audited theta interval.
- `8/125` alone remains compatible with theta bounds.