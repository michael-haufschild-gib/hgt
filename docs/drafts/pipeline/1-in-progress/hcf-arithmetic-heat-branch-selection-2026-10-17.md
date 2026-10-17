# HCF: arithmetic heat branch selection

- **ID:** HCF-SOURCE-2026-10-17
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Source:** Read-only `docs/reports/rh-current-frontier-map.md`, HCF.
- **Statement:** Find an unconditional source mechanism that removes a hard obstacle to the no-transition branch of the actual archimedean-minus-prime Gaussian heat trace.
- **Contribution credit:** None yet. Improved estimates, new RH receivers, and reformulations do not qualify.

## Plan

1. Inspect the literal source, heat flow, and existing singular Hankel transition laws.
2. Attack competing arithmetic branch-selection mechanisms; retain the full prime, Gamma, and polar terms.
3. Write a dependency-closed paper proof before Lean. Verify any resulting module directly, audit axioms, wire imports, and clean owned scratch.

Corpus-only mathematical evidence. No numerical experiments, web, novelty audit, historical research Markdown, added analytic premises, full builds, or heartbeat increases. One owned foreground Lean process at a time. Preserve concurrent work.

## Initial questions

- Does the original heat source have a positive evolution or invariant cone that survives all ranks?
- Do exact singular-block laws expose an arithmetic incompatibility with a first negative transition, rather than just describe that transition?
- Can a source-domain or signed decomposition obstacle be removed independently of RH?

## Source audit

The source realization is already substantially complete. `XiGaussianHeatBottomSourceReceiver`
identifies the heat trace on the entire open right heat half-plane with the literal Gaussian
bottom-edge logarithmic-derivative integral. `XiGaussianHeatArchPrimeHankel` identifies every
polynomial Hankel form with the archimedean-minus-prime form plus its exact rank-one polar term.
`HedenmalmCriticalFeaturePrimeGammaDecomposition` gives the full four-term absolute-Euler
prime--Gamma realization of critical-feature polarization, including both same-orientation terms.
These are existing results, not contributions of this turn.

The hard unresolved step is source sign across all ranks, or the corresponding cancellation in
the vertical prime chirp. A construction using a positive moment form, an RH field, or an
unproved arithmetic covariance ceiling would assume the missing step.

## Conjecture and failure ledger

1. **Continue fixed-rank positivity to all times.** `hcf_first_contact_resolution` gives exact
   positive quadrature at a first contact, but `HeatFirstContact.exists_successor_earlier` puts
   the next-rank contact strictly earlier. The unconditional window is `a * n ≤ κ`; it is not
   a positive interval shared by every Hankel rank. No global first finite-rank contact follows.
2. **Positive quadrature determines a positive successor.**
   `HTGeometry/HankelBoundaryExtension.exists_boundaryPerturbation_coupling_eq` changes the
   first omitted coupling arbitrarily while preserving the current finite Hankel block. The
   PSD successor forces that coupling to vanish. This is a generic extension obstruction;
   it does not prove that the actual arithmetic heat trajectory crosses its boundary.
3. **Toda continuation or signed projections select the positive branch.**
   `XiGaussianHeatTodaMultiplicity`, `XiGaussianHeatBlockInertia`,
   `XiGaussianHeatAdmissionContinuation`, and `XiGaussianHeatRegularKernelProjections` already
   resolve singular blocks, their contact orders, continuation, and signed orthogonal
   projections. Their exact laws accommodate negative inertia; none supplies its exclusion.
4. **All scalar moments positive implies all Hankel forms positive.**
   `XiHeatMomentSmallTimePositivity.exists_heatMoment_re_pos_small_time` already proves
   positivity of every scalar moment on one common small-time interval. This controls the
   individual moments, not arbitrary polynomial cross terms. The all-rank heat form remains
   the RH criterion. No implication between these two distinct positivity requirements was
   established.
5. **Absolute heat dissipation yields a relative phase budget.**
   `XiGaussianHeatChannelTransfer` controls absolute positive-channel gains.
   `XiGaussianHeatRetentionObstruction.exists_xiGaussian_principalIdeal_unit_heat_collapse`
   disproves the fixed-step, degree-uniform retention needed for this bootstrap: unit energy
   can collapse below any positive tolerance at every later time, inside any nonzero
   principal ideal. Exact pole cancellation does not repair it.
6. **A finite spectral head controls all polynomial orders.**
   `XiGaussianUniformTailObstruction.exists_xiGaussian_allTime_full_tail` supplies one
   nonzero annihilator whose whole positive native energy is in the tail, simultaneously at
   every positive time. `not_xiGaussian_uniform_relative_tail` rules out a degree-independent
   strict relative cutoff. The positive survivor, exact full-tail localization, is already
   formalized.
7. **Complete the raw prime-minus-Gamma form in native energy.**
   `XiGaussianPolarSourceCancellation` proves that polar evaluation is unbounded in native
   energy. Polar-normalized annihilators have energy tending to zero while their literal
   prime-minus-Gamma source tends to `2 * π * exp(t / 4)`. The completed residual does tend
   to zero. Thus cancellation or an additional polar coordinate is indispensable; completing
   the raw form silently loses a real source term.
8. **Real physical tests make the trace a sum of positive squares.**
   `XiGaussianHeatPhysicalRealForm.heatHankel_map_eq_tsum_sq` gives ordinary complex squares
   of transformed evaluations, not modulus squares. Reflection proves reality, not positivity.
9. **Identify Gaussian prime curvature with a positive Gamma-conductor Schur residual.**
   `GammaConductorGaussianHeatDiagonalNoGo` proves the exact sign mismatch outside the
   Gaussian aperture. Real diagonal congruence cannot make this identification; mixed
   prime, Gamma, and polar terms cannot be discarded.
10. **Remove a critical-feature source-domain obstruction.** The four-term source realization
    in `HedenmalmCriticalFeaturePrimeGammaDecomposition` already removes it. Repackaging the
    source cup or same-orientation terms would add no new producer.
11. **The translated “poleGamma” covariance is only a Gamma term.** False reading of the
    definition: `criticalFeaturePositiveShiftPoleGammaDensity` uses
    `continuedPrimeArchSourceRelativeTrace`. The arithmetic continuation remains present.
    `HedenmalmCriticalFeatureTranslatedSourcePlemeljCovariance` closes the translated
    decomposition and negligible normalized von-Mangoldt correction, not the remaining
    covariance ceiling.
12. **Alias selection or positive-shift rendering proves the desired variance ceiling.**
    `HedenmalmCriticalFeaturePhaseAveragedPositiveShiftPiGate` already supplies a source-only
    positive-shift schedule and exact gates for a three-quarters critical-line statement.
    The arithmetic upper/lower gates remain hypotheses; the renderer does not establish them.
13. **Complete a positive continuous feature frame to obtain the holomorphic source trace.**
    `HedenmalmCriticalFeatureWardGreenPlancherelFracture` proves the exact discrepancy:
    Hermitian mass is `2π / (1 - Im(z)^2)`, holomorphic polarization is `2π`, and their excess
    is `2π * Im(z)^2 / (1 - Im(z)^2)`. Frame completion retains precisely the transverse
    information absent from the holomorphic pairing. This exact positive survivor is already
    formalized, not a new source-sign argument.
14. **Invert the heat transform to bypass the omitted moment.**
    `XiShiftedHankelHeatResolventBridge` already constructs the integrable Gamma--Laplace
    transform, factorial-Volterra null flag, and exact first-omitted-coupling integral. It
    transports the sign problem to a signed heat integral; it does not remove it.
15. **Use the sharp heat-window transition to select the unlimited branch.**
    `XiGaussianHeatWindowExactTransition.hcf_exact_window_transition` already proves the
    exhaustive alternative: RH with every window constant, or one finite exact transition
    aperture. Choosing the former still needs the same all-aperture even-Weil source sign
    encountered in RW. It is not an independent HCF producer.
16. **Apply generic form comparison and Hilbert-basis completion.** The global-domain corpus
    search returned `HTGeometry/FormInverseAntitone` and a deck eigenbasis construction.
    The former explicitly assumes PSD and form comparison; the latter assumes an orthogonal
    complete family. Neither search result constructs these properties for the actual HCF
    source. The proposed ingredient chain therefore does not discharge the missing premise.

## Positive-survivor and significance audit

The strongest survivors of these attempts are exact omitted-coordinate freedom, principal-ideal
heat collapse, all-time full-tail localization, exact polar cancellation, and the continuous-frame
fracture. Each already exists in the Lean corpus. The second pass through source-domain completion,
heat--resolvent inversion, scalar complete monotonicity, and full-frame polarization yielded no
new dependency-closed positive theorem. **NO NEW POSITIVE SALVAGE FOUND in this tested batch.**
This does not retire HCF or assert that its actual source positivity is impossible.

No independent branch selector or hard-obstacle removal has been proved. Do not award significant
contribution credit, create a wrapper theorem, or promote this card to stage 2 or 3.

## Search record

Three documented deep searches, each with a 300-second request budget:

- `Gaussian heat trace Hankel rank uniform positivity arithmetic prime chirp transition source`
- `first contact null polynomial omitted moment signed heat evolution arithmetic source positivity`
  with `--module XiGaussianHeat`
- `Gaussian native energy heat generator Hilbert closure all polynomials source realization`

All returned `partial: false`, no errors, and no unfinished stages. Source inventory was complete
(73,160 files in the first snapshot; 73,162 in the later snapshots). Compiler enrichment was not
complete: later snapshots reported 56,075 pending and 2,659 stale entries, with background refresh
running. Candidate lemmas, source arguments, proof ideas, and ingredient sets were inspected;
only Lean source evidence was used. The returned first-contact/kernel ingredient set was already
formalized; the global form-comparison chain left its PSD and source-identification obligations
open. Source reads and direct Lean checks, not search metadata, determine applicability.

## Verification

- All 22 cited modules had compiled artifacts with modification times not older than their
  corresponding sources at audit start.
- The combined scratch import failed with:
  `import GaloisForLFunctions.RHTower.XiSpectralSupportCriterion failed, environment already contains 'RHTower.xiSpectralPointSupport_im' from GaloisForLFunctions.RHTower.SpectralBlaschkeMatching`.
  Both tracked source files contain that declaration. The import-graph audit isolated the
  criterion branch to `HedenmalmCriticalFeaturePhaseAveragedPositiveShiftPiGate` in this set;
  ten selected modules reach the matching branch and eleven reach neither branch. This
  pre-existing cross-family integration failure remains unfixed; do not claim a combined
  import or umbrella pass.
- Separate scratch checks covered **all 36 selected declarations**: 34 in the main family,
  two in the criterion family. Both `lake --old env lean /tmp/…` commands exited 0. Every
  `#print axioms` result contained only `propext`, `Classical.choice`, and `Quot.sound`.
- Final direct source audit:
  `lake --old env lean GaloisForLFunctions/RHTower/XiGaussianHeatRetentionObstruction.lean`
  exited 0 with empty output.
- No Lean source edits, new declarations, umbrella edits, or full builds. No new theorem
  exists to index or promote. The frontier map was not modified by this turn.
- All 13 owned search, audit, manifest, and log files were removed and their absence verified.
  All owned search and Lean process handles reached terminal results. Persistent memory:
  `rh/hcf-arithmetic-heat-source-audit-2026-10-17`.

## Gates

- [x] Original source and norms inspected.
- [x] Existing-declaration audit, including every selected theorem and import limitation.
- [ ] Independent producer or substantive obstruction removed.
- [ ] Dependency-closed paper proof.
- [ ] Exact Lean theorem, direct audit, umbrella wiring, and cleanup.
- [ ] Significant-contribution audit.

## Log

- 2026-10-17 — Selected previously unworked HCF. Started documented deep search `Gaussian heat trace Hankel rank uniform positivity arithmetic prime chirp transition source`, budget 300 seconds.
- 2026-10-17 — Completed the 16-mechanism batch and second positive-survivor pass. No qualifying
  contribution; HCF and the cross-route objective remain incomplete. Separate axiom audits and
  final direct module audit passed; combined-import collision recorded above.
