# EWU fixed-window purification — 2026-10-16

Two new audited modules:
- formal/GaloisForLFunctions/HTGeometry/EvenEntireWindowSource.lean
- formal/GaloisForLFunctions/RHTower/EvenSectorWindowPurification.lean

Unconditional capstones in RHTower.EvenSector:
`exists_window_purification (a : ℝ≥0) (c : WindowedSmoothEvenPolarTestFn a →₀ ℝ≥0)` produces one actual smooth even pole-free source in [-a,a] with exactly the full finite-mixture autocorrelation.
`window_profile_range_eq_mixture_range a` identifies ACTUAL single-source and finite-positive-mixture profile images at that fixed aperture; `convex_window_profile_range a` proves the actual image convex.
`exists_interior_window_purification (a : {r : ℝ // 0 < r}) (c : InteriorWindowedSmoothEvenPolarTestFn a →₀ ℝ≥0)` retains compact support strictly inside (-a,a), preserving the original interior source domain.

Structural gain beyond prior exact moment realization: rank removal now takes place in the original source window while preserving the ENTIRE autocorrelation. Thus normalization, every arithmetic observation, and actual archimedean energy can be constrained simultaneously without a finite-mixture rank gap or aperture enlargement. No RH, Weil sign, factor-admission, or attainment premise. Does not prove blind positivity/RH, or smooth whole-profile scalarization of arbitrary C² inputs.

Proof mechanism derived from current Lean corpus: any compact source transform is subquadratic. Exact even Hermitian factor identity on the imaginary axis gives the COMMON input aperture a (rank independent). Apply the existing quadrant estimate to Q(bz); its explicit type is ab+2. The inverse scaling identity gives zero beyond a+2/b. For every u>a choose b large, hence literal support in [-a,a]. Fourier inversion identifies the inverse with ANY existing smooth scalarization. For strict interiors, maximize |x| on the finite union of supports with 0 adjoined; the attained radius is strictly less than a, so closed-window purification stays inside the same open window.

Relevant APIs:
HTGeometry.SubquadraticType.comp_real_mul
HTGeometry.angularInverse_comp_pos_mul
HTGeometry.angularInverse_zero_outside_axis_window
HTGeometry.compactInverse_tsupport_subset_axis_window
HTGeometry.compactInverse_eq_of_paperFT
RHTower.EvenSector.paperFT_subquadratic
RHTower.EvenSector.factor_common_window
RHTower.EvenSector.scalarization_tsupport_subset
RHTower.EvenSector.scalarization_tsupport_subset_interior

Audits complete: individual `lake --old build` targets, both final direct `lake env lean <file>` checks (exit 0, no diagnostics), 126 Mathlib constants via #check and explicit @Name probes, all 19 public declarations #print axioms (only propext, Classical.choice, Quot.sound). Both umbrellas wired once; no full/umbrella builds, experiments, holes, custom axioms, heartbeat hacks, or commits by this agent. Global lint snapshot failed only on 18 unrelated concurrently developed unwired modules (CHMDStationary*, PaperTheta*, WeilCutEvenMeanZeroDeficit, two XiGaussianHeatRegularKernel modules, HTGeometry.BoundedVariationKernelIntegral and MomentInverseKernel). Preserve foreign work. Owned /tmp scratch cleaned; oleans retained.

Paper/conjecture record: docs/drafts/pipeline/3-formalized/ewu-fixed-window-purification-2026-10-16.md.