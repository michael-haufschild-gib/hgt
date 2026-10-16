# EWU single-source arithmetic fibre recovery

Status: formalized; five modules built and directly audited; capstone axioms audited.

Goal: overcome the remaining source-realization obstruction after exact smooth
autocorrelation scalarization. Existing exact-fibre recovery returns C² finite
mixtures; scalarization currently accepts smooth mixtures.

Evidence: current Lean sources `EvenSectorExactFibreRecovery`,
`EvenSectorSmoothSourceScalarization`, and the explicit positive/negative
pole-free coordinate tests. Whole-corpus deep searches were run; both reported
partial semantic coverage with complete source inventory. Relevant candidates
are checked against Lean source. No old research Markdown, web, numerical
experiments, or novelty audit.

Conjecture loop:

1. Direct smoothing preserves the exact arithmetic fibre. FALSE as a general
   mechanism: convolution changes autocorrelation samples at log n. Survivor:
   a fixed compact support window leaves only finitely many changed samples.
2. Smooth exact-fibre recovery with one actual even pole-free source exists
   for every full C² positive finite mixture, with arbitrarily small energy
   excess. SURVIVES: correct all finite arithmetic defects by positive smooth
   coordinate rows with vanishing correction cost; then scalarize the
   corrected mixture exactly. For full-source mixtures this is upper-energy
   recovery, not a claim of convergence to their exact energy.
3. For C² even-polar mixtures, the same construction recovers the entire
   profile pointwise and the actual energy as limits, while every whole
   arithmetic trace is exact at every stage. PROVED IN LEAN in
   `exists_single_smooth_exact_fibre_limit`.

Mechanism: even compact mollification preserves the literal pole
zeros; Weil-energy convergence and the explicit formula recover archimedean energy convergence;
uniform support gives a fixed finite coordinate set; signed coordinate rays
correct the entire trace using nonnegative coefficients tending to zero;
exact smooth scalarization produces a single source. This targets a source
construction and exact-fibre closure law, not a positivity receiver.

All five modules are wired into the RHTower umbrella. All five direct
`lake env lean` checks, four capstone axiom audits, and the explicit
Mathlib-name probe passed.

## Dependency-closed paper proof

For each C² even-polar source f, convolve with the normalized even bump of
radius 1/(n+1). Existing `XiGaussianHeatWindowNyquistExclusion` proves global
smoothness, support enlargement by that radius, preservation of evenness,
the entire Fourier product identity, and convergence of the actual zeta Weil
energy. The Fourier product identity preserves the zero at i/2 exactly.

All these approximants have support in one fixed compact interval. Normalized
nonnegative convolution bounds their sup norms by the sup norm of f and
converges pointwise to f. Dominated convergence in the autocorrelation integral
therefore gives convergence of every logarithmic sample. Fixed support makes
all samples outside one finite set identically zero, simultaneously for every
approximant and the limit. The unconditional explicit formula writes the
pole-plus-archimedean energy as the zeta Weil energy plus the finite von Mangoldt
sample pairing. Both terms converge, so the actual archimedean energy converges.

Apply this rowwise to any finite positive even-polar mixture. Its smoothed
trace defect has one fixed finite support and every coordinate tends to zero.
The corpus's positive and negative coordinate tests are finite translates of
smooth bumps, hence are themselves smooth. Normalize their autocorrelations
to traces +e_j and -e_j. For each defect d_j, append the positive row with
coefficient max(d_j,0) and the negative row with coefficient max(-d_j,0).
The resulting positive smooth mixture has exactly the original whole trace.
Its correction cost is a finite sum of fixed real energies times coefficients
tending to zero; no sign assumption on those energies is needed. Its energy
thus converges to the original mixture energy.

Exact smooth scalarization now replaces each corrected mixture by one actual
smooth compact even-polar source, preserving both trace and energy. Finally,
apply existing `exists_evenPolar_exact_fibre_recovery` to a full-source positive
mixture, then use this exact-fibre smooth recovery with a smaller energy margin.
This yields one smooth even-polar source in the same whole arithmetic fibre
at every strict epigraph height. Inclusion in the full-source cone and this
construction give equality of the closed fibre epigraphs for single smooth
even-polar sources and arbitrary full-source positive mixtures.

All steps use unconditional existing identities or elementary finite positive
combination and dominated-convergence arguments. Blind-fibre positivity is
neither assumed nor proved. Exact equality of arbitrary C² autocorrelation
profiles with smooth profiles is not claimed.

Stronger survivor exposed during formalization: the corrected single-source
autocorrelations converge pointwise to the entire original C² even-polar
mixture profile, while every arithmetic coordinate is already exact and the
actual energy converges. Thus the result can state density inside every exact
arithmetic fibre, jointly for profile evaluation and energy, rather than only
an upper-energy recovery inequality.

## Formal statements

- `EvenSectorSmoothApproximation.lean`: smooth pole-free approximation,
  pointwise autocorrelation convergence, one common finite arithmetic support,
  actual archimedean energy convergence.
- `EvenSectorScalarizationMoments.lean`: exact scalarization preserves the
  entire profile, whole arithmetic trace, and actual energy.
- `EvenSectorSmoothTraceCorrection.lean`: positive smooth correction of any
  finite signed trace defect; every linear observable of the correction
  vanishes when that defect tends to zero on a fixed finite support.
- `EvenSectorSmoothFibreDensity.lean`: exact-fibre single-source density,
  jointly for the whole pointwise profile and actual energy.
- `EvenSectorSingleSourceFibreRecovery.lean`: unconditional bundled-data
  capstones `smooth_single_source_exact_fibre_density`,
  `exists_single_smooth_trace`, `full_mixture_single_smooth_recovery`, and
  `singleSmooth_energy_fibre_closure_eq`.

The last closure identity holds for every finitely supported arithmetic
trace v. It identifies the closed energy epigraph of actual single smooth
even-polar sources in that exact fibre with the full C² positive-mixture
epigraph closure. This removes the regularity and convexification obstruction
in fibre recovery; it is a source realization theorem, not an RH receiver.

## Verification

All five modules built via the targeted
`lake --old build GaloisForLFunctions.RHTower.EvenSectorSingleSourceFibreRecovery`.
Every module passed final direct `lake env lean <module>.lean` checking,
sequentially, with no diagnostics. All five oleans are current. No full or
umbrella build was run.

All four unconditional capstones were checked with `#print axioms` in a
`/tmp` scratch file. Their only axioms are `propext`, `Classical.choice`, and
`Quot.sound`. No added axioms, proof stubs, numeric experiments, or heartbeat
increases occur. All 195 Mathlib constants referenced by the five `.ilean`
files passed both `#check` and an explicit `have := @Name` probe against
this toolchain. `git diff --check` passed for the owned changes.

`scripts/formal_tools.py lint` reports no errors in these five modules or their
wiring. Its eight errors are unrelated concurrent unwired modules:
`CHMDStationaryGenerators`, `CHMDStationaryGroundDomain`,
`CHMDStationaryGroundEquivalence`, `CHMDStationaryGroundGraph`,
`CHMDStationaryGroundPotential`, `CHMDStationaryOperatorDomain`,
`OddWeilLineKernel`, and `OddWeilSpectralMeasure`.
