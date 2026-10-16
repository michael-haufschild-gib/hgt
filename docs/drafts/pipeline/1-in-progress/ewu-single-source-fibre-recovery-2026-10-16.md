# EWU single-source arithmetic fibre recovery

Status: conjecturing; no new theorem claimed.

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
   for every full C² positive finite mixture, with energy converging to its
   original cost from the epigraph. SURVIVES PRELIMINARY ATTACK: correct all
   finite arithmetic defects by positive smooth coordinate rows with vanishing
   correction cost; then scalarize the corrected mixture exactly.

Proposed mechanism: even compact mollification preserves the literal pole
zeros; Fourier multiplier domination controls the actual archimedean energy;
uniform support gives a fixed finite coordinate set; signed coordinate rays
correct the entire trace using nonnegative coefficients tending to zero;
exact smooth scalarization produces a single source. This targets a source
construction and exact-fibre closure law, not a positivity receiver.

Remaining audits: finish the dependency-closed paper proof; formalize; build
only needed leaf targets with `--old`; direct `lake env lean` checks; axiom
checks in `/tmp`; umbrella wiring; formal lint; cleanup.

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

Formal progress: `EvenSectorSmoothApproximation.lean` passed direct Lean
checking. Its common finite trace support and actual energy convergence have
no positivity or RH premise.
