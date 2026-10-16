# EWU fixed-window purification

Status: formalized and audited. Scope: unconditional exact rank removal for actual smooth even pole-free sources, with the original support window retained.

## Corpus frontier

`EvenSectorSmoothSourceScalarization` produces a single smooth compact even pole-free source with the whole mixture autocorrelation. Its inverse-transform construction only proves some compact support: `EvenEntireAxisType.quadratic_strip_bound_of_axes` enlarges the imaginary-axis type by two, and the mixture type is accumulated over rows. `EvenSectorExactMomentRealization` preserves arithmetic trace and energy for general C² mixtures but supplies no window or whole-profile preservation.

This prevents those theorems from removing rank constraints inside a fixed aperture, where changing the domain changes the variational problem.

## Conjecture loop

1. Exact full-profile scalarization of arbitrary C² mixtures into smooth sources: rejected as a target. A smooth source has smooth autocorrelation; the current finite-regularity data does not give that. Even for an output merely C², the available spectral decay does not justify two continuous inverse derivatives. No such inference is used.
2. Fixed-window purification of smooth even pole-free mixtures: proved on paper and in Lean. The mixture identity controls the factor on the imaginary axis by the common aperture, independently of the number of rows. Dilation removes the additive type loss in the existing contour argument. The inverse factor therefore remains in the original interval.
3. Positive survivor/capstone: the actual fixed-window autocorrelation image is closed under arbitrary finite nonnegative mixtures. Every affine profile constraint, including blind trace, normalization, and archimedean energy, is preserved by a single source in the same window. No assertion of RH or blind positivity.
4. Strict-interior purification: a finite union of input supports is compact. Adjoin the origin and maximize absolute value on that compact set. Its maximum is strictly below the aperture. Closed-window purification at this attained radius therefore stays in the original open window. This retains the compact smooth interior domain used by aperture variational problems.

## Paper proof plan

Let every input source be supported in [-a,a]. Its transform on iy is bounded by its L¹ norm times exp(a y). The exact sum-of-squares identity on both axes gives the same type a for the entire even factor Q. Real-axis rapid decay and subquadratic global growth are already proved for this actual factor.

For any b >= 1, apply the corpus strip theorem to Q(b z). Its recovered type is ab+2. Rescaling the inverse integral gives zero at u whenever a+2/b < |u|. Given |u|>a, choose b sufficiently large. Thus the literal inverse vanishes outside [-a,a], with no enlargement. Fourier inversion identifies this inverse with the smooth source furnished by the existing factor theorem. The complete autocorrelation identity follows from Fourier injectivity as before.

The stronger source statement is proved: every smooth even scalarization with that profile must have the same window, irrespective of which entire factor was selected. Consequently finite-mixture convexification adds no feasible profile at fixed aperture. The result is exact rank removal in the actual source domain, rather than an energy estimate or a receiver for a future factorization assumption.

## New modules

- `formal/GaloisForLFunctions/HTGeometry/EvenEntireWindowSource.lean`: dilation, localized inverse, and inversion identification. Direct Lean check passed; individual olean build passed.
- `formal/GaloisForLFunctions/RHTower/EvenSectorWindowPurification.lean`: common-window factor geometry, forced source localization, closed-window and strict-interior purification, equality of actual source/mixture profile images, convexity. Leaf build and final direct audit passed.

Main unconditional capstones in `RHTower.EvenSector`:

- `exists_window_purification (a : ℝ≥0) (c : WindowedSmoothEvenPolarTestFn a →₀ ℝ≥0)`.
- `window_profile_range_eq_mixture_range (a : ℝ≥0)` and `convex_window_profile_range (a : ℝ≥0)`.
- `exists_interior_window_purification (a : {r : ℝ // 0 < r}) (c : InteriorWindowedSmoothEvenPolarTestFn a →₀ ℝ≥0)`.

All return actual source/profile statements. No RH, Weil sign, spectral-factor existence, completion, or attainment premise is used. Blind positivity remains open; the new result removes finite-mixture rank relaxation within each original aperture.

## Corpus search

Three documented deep queries examined the current EWU moment frontier, compact even factors, and finite regularity. All reported `partial = false`; the first inventory covered 72,806 indexed files. Compiler metadata included pending/stale entries, so applicable declarations were read from their Lean sources and checked by Lean. A lexical EvenSector search identified the existing scalarization and window modules. No web, old research reports, numerical experiments, or novelty search was used.

## Completed audits

- Both individual `lake --old build` targets succeeded and produced fresh oleans. Cached dependency output was replayed; no full or umbrella build ran.
- Final `lake env lean GaloisForLFunctions/HTGeometry/EvenEntireWindowSource.lean` and `lake env lean GaloisForLFunctions/RHTower/EvenSectorWindowPurification.lean` each exited 0 with no diagnostics.
- All 126 Mathlib constants referenced by the compiled new modules were checked with `#check` and explicit `have := @Name` probes in /tmp.
- `#print axioms` audited all 19 public declarations in /tmp: only `propext`, `Classical.choice`, and `Quot.sound`.
- Each new module is imported once in its theorem-area umbrella. `git diff --check` passed. No proof holes, numerical experiments, added axioms, heartbeat changes, or tree-resident audit commands.
- Global `scripts/formal_tools.py lint` reported no errors for either new module. Its final snapshot failed on 18 unrelated concurrently developed unwired modules: seven `CHMDStationary*` modules, six `PaperTheta*` modules, `WeilCutEvenMeanZeroDeficit`, `XiGaussianHeatRegularKernel`, `XiGaussianHeatRegularKernelBlocks`, `HTGeometry.BoundedVariationKernelIntegral`, and `HTGeometry.MomentInverseKernel`. Those foreign files were preserved.
- Owned /tmp research, probe, and build scratch files were removed after recording audit results; final sources and oleans retained.
