# EWU: single smooth source density in every exact arithmetic fibre

Formalized 2026-10-16 in five modules under `formal/GaloisForLFunctions/RHTower/`: `EvenSectorSmoothApproximation`, `EvenSectorScalarizationMoments`, `EvenSectorSmoothTraceCorrection`, `EvenSectorSmoothFibreDensity`, `EvenSectorSingleSourceFibreRecovery`. All five are wired into `RHTower.lean`.

New unconditional capstones, namespace `RHTower.EvenSector`:
- `smooth_single_source_exact_fibre_density (c : WeilEvenPolarTestFn →₀ ℝ≥0)`: a sequence of single actual smooth compact even-polar sources, every whole arithmetic trace exactly equal to the input mixture trace at every stage, actual archimedean energies converging to the mixture energy, and entire autocorrelations converging pointwise to the mixture profile.
- `exists_single_smooth_trace (v : LogIndex →₀ ℝ)`: every finitely supported arithmetic trace is realized by one smooth even-polar source.
- `full_mixture_single_smooth_recovery (c : WeilTestFn →₀ ℝ≥0)`: single smooth even-polar sources in the exact original full-source trace fibre, with energy below full mixture energy + 1/(n+1).
- `singleSmooth_energy_fibre_closure_eq (v : LogIndex →₀ ℝ)`: closure of the single-smooth-source energy epigraph equals closure of the full C² positive-mixture energy epigraph, in every exact arithmetic fibre.

Mechanism: direct smoothing changes trace, so smoothing alone fails. Even normalized compact mollification preserves the literal pole zero. Existing `XiGaussianHeatWindowNyquistExclusion` gives actual zeta Weil-energy convergence. Common compact support gives one fixed finite arithmetic support; dominated convergence gives whole-profile pointwise convergence. The unconditional explicit formula plus the finite von Mangoldt pairing gives archimedean energy convergence. Existing signed coordinate tests are finite translates of smooth bumps. Normalize them to traces ±e_j and append positive coefficients max(defect_j,0), max(-defect_j,0). The whole trace becomes exact. Every linear observable of this fixed finite correction tends to zero, without assuming nonnegative correction energy. Exact smooth scalarization then supplies one actual source per stage. Existing full→even-polar exact-fibre recovery supplies the full-source epigraph result.

Limits: no blind-fibre positivity or RH proved; no exact smooth factorization of arbitrary C² profiles claimed. Full C² mixture recovery is an upper-energy statement, not equality or convergence of energy to the original full-source mixture. Joint pointwise-profile and energy convergence is proved for C² even-polar mixtures. This removes the regularity and finite-mixture gap in EWU fibre recovery.

Audits: targeted `lake --old build GaloisForLFunctions.RHTower.EvenSectorSingleSourceFibreRecovery` passed; all five final `lake env lean <file>` checks passed without diagnostics; all 195 referenced Mathlib constants passed #check and explicit `have := @Name` probes. Four capstones' #print axioms only propext, Classical.choice, Quot.sound. Five oleans current. No full/umbrella builds, added axioms, stubs, computations, or heartbeat increases. Global formal lint at audit time had only eight unrelated concurrent unwired CHMDStationary*/OddWeil modules; own modules/wiring clean. No commit/push. Owned scratch artifacts cleaned after audit.

Paper proof, conjecture failures and exact scope: `docs/drafts/pipeline/3-formalized/ewu-single-source-fibre-recovery-2026-10-16.md`.

Builds on `mem:rh/ewu-smooth-exact-scalarization-2026-10-16`.