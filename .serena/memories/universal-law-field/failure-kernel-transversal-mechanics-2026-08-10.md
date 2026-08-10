# Failure-kernel transversal mechanics (2026-08-10)

Higher pivot: interpret corpus as atlas of minimal derivation/failure kernels, not collection of RH routes. Missing field mechanism is doctrine revision by simultaneous transversals.

Paper theorem:
- docs/drafts/pipeline/2-fully-proven/universal-law-field/failure-kernel-transversal-mechanics/finite-failure-kernel-transversal-revision-observer-saturation-and-cofinal-barrier-law.md
- ID ULF-FKT-1, [LEAN CLOSED]

Program:
- docs/drafts/pipeline/1-in-progress/universal-law-field/failure-kernel-transversal-mechanics/failure-kernel-transversal-law-revision-program.md

Formalization:
- formal/GaloisForLFunctions/HTGeometry/ConstitutiveFailureKernelTransversal.lean
- imported by formal/GaloisForLFunctions/HTGeometry/UniversalLawField.lean
- Stage3 record: docs/drafts/pipeline/3-formalized/universal-law-field/failure-kernel-transversal-mechanics/finite-failure-kernel-transversal-revision-observer-saturation-and-cofinal-barrier-law-formalized.md

Closed laws:
1. revision succeeds iff it hits every minimal failure kernel;
2. inclusion-minimal successful revision has a private/core-retainment witness for each removed element;
3. quotient observer transports repairs by fibre saturation and may over-remove;
4. swapped symmetry can forbid deterministic minimal repair while symmetric fractional relaxation exists;
5. triangle gives integral repair cost 2 vs fractional cost 3/2;
6. cofinal singleton kernel birth forbids finite global repair and forces unbounded repair growth.

Lean verification:
- direct lake env lean module: pass
- scripts/formal_tools.py lint: pass
- final lake build GaloisForLFunctions.HTGeometry.UniversalLawField: pass
- axiom audit: only propext, Classical.choice, Quot.sound
- no task-owned Lean process left running
- git diff --check: pass

Interpretive frontier predictions:
- singular descent: quotient merges kernels; pullback repair is saturated;
- oscillatory transport: signed repair must hit cancellation kernels before norm/absolute-value projection;
- adaptive orientation: flags index kernels; fixed testing is insufficient absent compact finite basis;
- coercivity: escape sequences form cofinal kernel family; finite seed tests cannot close it;
- positive carrier: fractional solution is relaxation; an integrality/effectivity theorem is required for exact carrier.

Open higher gate: define presentation-invariant failure kernels and exchange/composition laws across doctrine classes, then prove that five current-frontier obstruction types instantiate those laws without route-specific fitting. Do not regress to individual endpoint repairs.

Relevant prior memories: `mem:universal-law-field/frontier-map-adopted-re-aim-2026-08-09`, `mem:universal-law-field/weird-fork-tournament-2026-08-09`, `mem:universal_law_field/ulf_gtm_3_formation_completion_exchange`.
