# EWU exact actual moment realization — 2026-10-16

New unconditional capstone in `formal/GaloisForLFunctions/RHTower/EvenSectorExactMomentRealization.lean`:

`RHTower.EvenSector.full_mixture_single_smooth_exact_moments (c : WeilTestFn →₀ ℝ≥0)` produces `f : SmoothEvenPolarTestFn` with exactly the full arithmetic trace and exactly the actual archimedean energy of `nonnegativeRealCoefficients c`. No RH, sign, factorization, approximation, or attainment premise. `singleSmooth_energy_fibre_eq (v : LogIndex →₀ ℝ)` identifies the ACTUAL single-smooth-source energy fibre with `WeilOneSided.nodeFibre v`; neither closure nor epigraph is used.

This strengthens the moment aspect of `mem:rh/ewu-single-source-fibre-recovery-2026-10-16`. It does not assert exact whole-profile realization of arbitrary full C² mixtures, nor blind positivity/RH.

Proof mechanism:
1. `EvenSectorCompactBoundaryRigidity.lean`: `compact_source_eq_zero_of_transform_zero` uses SuzukiTitchmarshUniqueness on F(z)=paperFT(f)(-z), finite exponential type from compact support, and continuous Fourier inversion. Under RH, absolute convergence and nonnegative weighted-square Weil summands imply a zero-energy compact source is zero. Therefore any positive mixture with a nonzero active row has strictly positive canonical excess. `exists_full_mixture_strict_descent` uses this plus ArchimedeanNodeValueFunction's infimum theorem in the RH branch; in the other branch every fibre is unbounded below. Its conclusion has no RH premise.
2. `EvenSectorPositiveBlindEnergy.lean`: `smoothPolarBump j` uses the corpus three-bump pole cancellation, equals 1 at zero, and has support radius 3*r_j. Choose j so small-aperture positivity applies and autocorrelation support lies below log 2. `exists_positive_blind_smooth_source` gives an actual smooth even pole-free source with zero whole trace and positive actual energy, unconditionally.
3. Existing single-smooth fibre recovery produces energy A strictly below target E. Add the blind source with positive coefficient (E-A)/B and apply existing exact smooth scalarization. `exists_smooth_source_energy_raise` realizes every E≥A exactly in the same fibre. Zero-active-row mixtures are handled separately.

All three new modules wired into RHTower.lean. Individual `lake --old build` targets succeeded; all three final `lake env lean <file>` audits exited 0 without diagnostics. All 132 referenced Mathlib constants checked with #check and explicit `have := @Name` probes in /tmp. #print axioms audited all 16 public declarations: only propext, Classical.choice, Quot.sound. No proof holes, custom axioms, numerical experiments, heartbeat changes, full builds, or umbrella builds.

Last global lint snapshot failed only on four unrelated concurrently developed unwired modules: CHMDArchMomentPullback, CHMDOperatorCutoffCommutator, CHMDOperatorCutoffForm, CHMDPrimeWindowTail. No EWU lint errors. Preserve concurrent foreign edits.

Paper/conjecture record: `docs/drafts/pipeline/3-formalized/ewu-exact-moment-realization-2026-10-16.md`.