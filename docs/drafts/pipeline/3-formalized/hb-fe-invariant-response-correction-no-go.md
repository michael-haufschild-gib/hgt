# HB functional-equation-invariant response correction no-go

- **ID:** HB-FE-INVARIANT-RESPONSE-NOGO
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `rh-current-frontier-map.md` HB canonical FE--Schwarz source core
- **Statement:** Any scalar response correction invariant under functional-equation reflection satisfies `corrected current = 0 <-> correction = 0 or Re(rho) = 1/2`; every everywhere-nonzero such response cancels exactly on the critical wall.

## Goal

Kill the whole source-independent, copywise FE-invariant scalar response class as a completion of the HB third-order `++-` source. Proof chain: literal reduced Einstein--Teukolsky source -> response-corrected reflected BM current -> critical-wall rigidity -> RH receiver. Noncircularity: reflection covariance and nonvanishing constrain response law, not Xi zero locations.

## Gates

- [x] 0 -> 1  in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [x] 1 -> 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [x] 2 -> 3  formalized: Lean module and theorem, targeted `lake build` green, axiom audit PASS
- [ ] 3 -> 4  publication-ready: standalone paper (theorem + proof + Lean certificate + Door-2)

## Paper proof

Let `A(q)` be literal unsquared Einstein--Teukolsky source amplitude, `lambda(q)` exact complementary BM exponent, and `K(q)` arbitrary scalar correction. Corrected reflected current is the sum of the two reflected terms carrying `A(q)K(q)` and `A(rq)K(rq)`. If `K(rq)=K(q)`, distributivity gives

`J_K(q) = K(q) J_1(q)`.

Existing literal-source orientation rigidity proves `J_1(q)=0 <-> Re(q)=1/2`. Hence

`J_K(q)=0 <-> K(q)=0 or Re(q)=1/2`.

If `K` is everywhere nonzero, its cancellation locus is exactly the critical wall; universal cancellation is equivalent to RH. This argument imposes no analyticity, boundedness, rank, rationality, spectral-gap, or perturbative-degree condition.

## No-go closure

- **Exact killing theorem/mechanism:** `d4BMXiSecondHarmonicFEInvariantNonzeroResponseCorrectionRouteKilled` universally quantifies over every FE-invariant, everywhere-nonzero divisor response and proves exact critical-wall cancellation.
- **Strongest positive survivor:** off wall, a cancelling FE-invariant response must vanish. The existing nonzero division-free cross-pair compensator instead necessarily breaks FE invariance; its global FE invariance is equivalent to RH.
- **New insight:** regularity or nonsingularity does not separate successful HB compensators. Necessary escape is reflection-nonlocal orientation data. Remaining HB source must read or transport the reflected copy, or leave scalar-response form.
- **Status:** paper proof dependency-closed; Lean module `ThetaCuspHawkingBMFEInvariantResponseCorrectionNoGo`. Internal novelty audit found the prior constant-response dichotomy in `ThetaCuspHawkingBMSourceIndependentResponseDichotomy`; new theorem strictly removes divisor-independence and permits arbitrary divisor-dependent corrections subject only to FE invariance. External audit against Birmingham--Mokhtari exact QNMs, AIME, nonlinear Teukolsky-source, and Peierls literature found no prior arithmetic FE-pair response classification. Novelty remains a best-effort negative literature claim.

## Lean certificate

- Module: `GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMFEInvariantResponseCorrectionNoGo`
- Sharp classification: `d4BMXiSecondHarmonicPeierlsResponseCorrectedReflectionCurrent_eq_zero_iff_of_feInvariant`
- Route kill: `d4BMXiSecondHarmonicFEInvariantNonzeroResponseCorrectionRouteKilled`
- RH receiver: `forall_d4BMXiSecondHarmonicPeierlsResponseCorrectedReflectionCurrent_eq_zero_iff_rh_of_feInvariant_of_ne_zero`
- Positive survivor: `d4BMXiSecondHarmonicCrossPairResponseCorrection_feInvariant_iff_rh`
- `lake env lean GaloisForLFunctions/RHTower/ThetaCusp/ThetaCuspHawkingBMFEInvariantResponseCorrectionNoGo.lean`: PASS
- `lake build GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMFEInvariantResponseCorrectionNoGo`: PASS
- `#print axioms`: only `propext`, `Classical.choice`, `Quot.sound`
- Umbrella: wired into `GaloisForLFunctions.RHTower`
- Repository lint: new module reachable and clean; global command remains red solely on unrelated shared-tree modules already absent from umbrellas.

## Log

- 2026-08-30 — compact-Hardy producer conjecture rejected: compact range allows unit kernels through unbounded preimages, and false RH need not supply infinitely many off-wall nodes.
- 2026-08-30 — L2-eigenstate conjecture rejected: nonlinear source is inhomogeneous and Xi singularities are resonances, not an ordinary L2 eigenspace.
- 2026-08-30 — FE-invariant response classification proved on paper and in Lean; route class killed; cross-pair nonlocal survivor classified.
