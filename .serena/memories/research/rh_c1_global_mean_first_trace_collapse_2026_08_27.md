# C1 global-mean Pluecker first-trace collapse (2026-08-27)

Frontier map is read-only for this task.

Files:
- formal/GaloisForLFunctions/HTGeometry/InfiniteHilbertDispersion.lean
- formal/GaloisForLFunctions/RHTower/GammaSewnMobiusApertureStokesGlobalMeanFirstTrace.lean
- docs/drafts/pipeline/1-in-progress/c1-global-mean-pluecker-first-trace.md

Results:
1. Generic unconditional theorem `GaloisForLFunctions.HTGeometry.tsum_pairwise_hilbert_dispersion` extends finite Hilbert dispersion to summable infinite families.
2. C1 ordered double packet-mean dispersion collapses exactly to weighted second moment minus squared barycenter norm.
3. Packet mean norm has exact coordinate formula `sum_i node(z,i) * mean(z,i)^2`.
4. Local Bernoulli covariance plus global mean dispersion telescopes to:
   `globalTraceMass = rawFirstMoment - ||globalMeanBarycenter||^2`,
   where `rawFirstMoment = sum_z a_z sum_i node(z,i) mean(z,i)`.
5. Full positive global trace is strictly less than `2/25`.
6. Exact Xi first-coefficient landing is equivalent to the single scalar equality
   `rawFirstMoment - ||globalMeanBarycenter||^2 = thetaCuspNormalizedEvenMoment 1 / 2`.

Verification:
- direct Lean checks pass;
- exact builds pass: InfiniteHilbertDispersion 1935/1935, C1 module 12791/12791;
- axiom audits: only propext, Classical.choice, Quot.sound.
- global lint remains red only because unrelated concurrent unreachable Sieve/HTGeometry modules.

Novelty discipline:
- Generic covariance/variance identity is classical and not novel.
- Candidate corpus novelty is arithmetic specialization/exact source telescope.
- Barycenter coordinate incidence is now explicit: each interior cell receives exactly four neighboring packet terms, `(0,0)` exactly one strictly positive term. Parseval gives the barycenter penalty as the tsum of squared incidence amplitudes. Barycenter is nonzero, so `globalTraceMass < rawFirstMoment` strictly.
- Remaining open core: sharply estimate the explicit four-neighbor collision penalty and prove/refute exact scalar equality. Current `< 2/25` ceiling does not separate known theta interval.