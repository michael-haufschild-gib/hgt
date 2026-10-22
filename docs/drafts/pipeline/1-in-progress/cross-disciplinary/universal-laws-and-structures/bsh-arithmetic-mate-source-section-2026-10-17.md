# BSH: arithmetic section before mate-curvature detection

- **ID:** BSH-SOURCE-2026-10-17
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Source:** Read-only `docs/reports/rh-current-frontier-map.md`, BSH.
- **Statement:** Construct a literal prime–Gamma section and prove its mate law without prescribing the radial character or assuming a critical-line conclusion.
- **Contribution credit:** None yet. Existing curvature diagnostics and their reformulations do not meet the requested contribution standard.

## Goal

Remove a source-level obstruction in arithmetic mate curvature. Retain the original prime–Gamma source, all degrees, both framed channels, and the full divisor. No numerical experiments, external literature, added analytic premises, or RH receiver as substitute.

## Plan

1. Read the exact Lean source of the framed curvature and Gamma comparison; search the local corpus for independent arithmetic section and mate mechanisms.
2. Form competing source-level conjectures. Reject mechanisms that only rename the radial factor, quotient it away, or infer a norm conclusion from finite traces.
3. Prove a dependency-closed positive survivor, if one is found. Formalize that exact theorem, audit its axioms, run direct module checks, wire imports, refresh indexes, and clean owned scratch.

## Evidence read

- `DeningerOneSidedFramedMateCurvatureTransgression.lean`: the gain is explicitly `exp ((2 * s.re - 1) * log n)`; one-sided curvature is its multiplicative composition defect. Polarization gives the existing radial mate curvature.
- `DeningerCalderonWittGammaTensorSquareMateIdentification.lean`: the ordered `(2,3)` Gamma coefficient is a strictly positive calibration of the same degree-six radial curvature.
- `PaperDeningerMateProfile.lean`, `PaperDeningerFramedCurvature.lean`, `PaperDeningerMateOperator.lean`: normalized curvature is a hyperbolic tangent with signed cofinal limit; compactness is exactly the critical-line condition.
- `PaperDeningerFiniteCurvature.lean`, `PaperDeningerSolidObservation.lean`: all finite positive-power traces vanish; even uniform masked observation of each fixed history tends to zero off-line. Operator-norm error stays one.
- `DeningerCalderonWittGammaGreenQuadraticMateCurvature.lean`: composing Gamma admission with completed Green provenance squares the fracture, leaving a strictly positive off-line curvature. Odd-factor cancellation is unavailable.

## Conjecture ledger

- **B1: finite arithmetic trace identities force the completed curvature to vanish. Rejected by existing source.** Finite traces vanish for every parameter, while the completed compact-ideal class distinguishes the two off-line sides. No new theorem claimed.
- **B2: reflection cancellation annihilates Gamma-admitted Green provenance. Rejected by existing source.** The two odd factors multiply into a positive square on each off-line fibre. No new theorem claimed.
- **B3: the forced finite-face metric supplies source/dagger compatibility. Rejected by existing source.** `DeningerFailureNerveSingularCartierMetric.lean` constructs the actual Euler gauge `G = (1-p^(-s))/(1-p^(-(m+1)s))`, its normalized face metric, and its uniqueness. Purification cancels only the Euler gauge; the radial half-density factor remains.
- **B4: mixed-cobar exactness annihilates the mate defect. Rejected by existing source.** `DeningerFailureNerveMixedDaggerCoboundary.lean` proves `S-A = delta_(S,A)(1)` at every parameter, including off-line ones. The source inverse is `Q^(-1) lambda^(-1)` and the Hermitian adjoint is `Q^(-1) conj(lambda)`. Their ratio is `norm(lambda)^(-2)`. Exactness therefore does not give the required quadratic cancellation.
- **B5: centered-flow countertransport repairs the section. Rejected by existing source.** `DeningerCenteredFlowCountercharacterRelativeCurvatureNoGo.lean` makes the absolute transport flat for every parameter by multiplying the gain by its inverse. The raw-to-flat relative class still recovers the literal Gamma coefficient. Discarding it changes the target.
- **B6: a literal arithmetic continuation of the finite Euler gauges supplies the missing mate law. Insufficient.** At depth one the inverse Euler core is `1+p^(-s)`. `SquarefreeDiscrepancyMellin.moment_eq_quotient` already provides the literal discrepancy integral representing `zeta(s)/zeta(2*s)` for `Re(s)>1/2`, with its density pole retained. This gives analytic source data but no equality of source reversal and Hermitian adjoint. Repackaging it would be a bridge, not a qualifying contribution. No new continuation theorem claimed.
- **B7: all finite prime Green-domain conditions plus reflection force the mate law. Rejected by existing source.** `DeningerFinitePrimeGreenDomainXiJets.lean` realizes arbitrary full finite Xi jets in every selected finite prime-domain list. In particular it retains the reflected Gaussian's nonzero Gamma/flux discrepancy. Finite prime admission does not constrain the needed cancellation.
- **B8: adaptive cofinal landing supplies annihilation missing at finite stages. Insufficient.** `DeningerMeyerReflectedGaussianPrimeGammaCauchyLanding.lean` already gives the literal two-sided Cauchy reconstruction and Bochner admission. `DeningerMeyerAdaptiveHarmonicGreenBoundary.lean` identifies its fractured boundary integral with the limit of adaptive prime-normal Green columns. Both land on the same Green detector; neither proves it zero.
- **B9: continuously extend the old oriented arithmetic boundary to obtain the conservative Gamma annihilator. Rejected by existing source.** `deningerCalderonWittCrossPrimeContinuousOrientedBoundaryExtension_eq_zero` proves every such extension is identically zero, because the actual witness span is dense and the old boundary kills it. It cannot detect the retained off-line relative class.

## Surviving open core

Source existence, finite-face gauge purification, linear mixed null-homotopy, and cofinal Green landing are already available separately. The missing result is compatibility of an independently constructed arithmetic Hermitian mate with the retained relative Gamma class. The source-defined lower/upper Cauchy cup is not already a positive diagonal: `DeningerPrimeGammaEulerSectorObstruction.lean` proves conjugation changes the Cauchy pole, and `DeningerPrimeGammaLowerCauchyPositivity.lean` shows that asserting all finite lower-packet Weil positivity is itself an RH gate.

The next substantive conjecture would need a source operation that proves this compatibility before divisor restriction, while retaining the relative raw-to-flat class. Naming a new Ward identity, demanding Gamma annihilation of the Gaussian Green vector, or demanding compactness of the framed operator would only rename the unresolved conclusion. No independent mechanism or dependency-closed proof was obtained here.

## Positive-survivor audit

This turn does not retire BSH. Existing positive survivors are the unique actual finite-face metric, the retained relative curvature, and the common adaptive/Cauchy Green boundary. Their proofs already exist in the cited Lean modules. No new positive theorem is claimed; no new Lean module is warranted by this audit. Significant-contribution credit remains **none**.

## Search coverage

Three documented deep searches used only returned Lean declarations and arguments:

1. `arithmetic section framed mate curvature prime Gamma radial character`: 73,145 inventoried files; `partial=false`; no errors.
2. `source inverse adjoint arithmetic mate section`: 73,146 inventoried files; `partial=false`; no errors. Mostly unrelated inverse/adjoint hits; these were not treated as a solution.
3. `prime Gamma source Hermitian adjunction radial mate`, filtered to `Deninger`: 73,147 inventoried files; `partial=true`; `filter_and_judge` reported `local model returned incomplete or malformed JSON`. Available source hits supplied the adaptive boundary and finite-prime-domain leads above.

All inventories were complete; compiler coverage was largely pending/stale. Refresh reported `background_indexer_running`. Generated ingredient suggestions were not accepted as proofs. No external search, novelty audit, or historical research Markdown was used.

## Verification

`lake --old env lean /tmp/hgt_bsh_audit.lean` exited 0 with no errors or warnings. The scratch audit imported the relevant existing modules and checked ten exact declarations, including finite metric uniqueness, mixed-cobar exactness, quadratic Gamma–Green composition, the zero-extension obstruction, the explicit RH-equivalent annihilation statement, cofinal adaptive/Cauchy landing, full operator-norm error, masked-history convergence, and the squarefree Mellin identity. Every axiom report contained only `propext`, `Classical.choice`, and `Quot.sound`.

This verifies existing compiled evidence, not a new theorem. No repository Lean file was changed, no umbrella/full build was run, and no numerical experiment was performed. Index and formal lint refresh are unnecessary for a card-only change; no global lint pass is claimed. All three search jobs and the sole owned Lean process have terminated. All five owned temporary search/audit files were removed and their absence verified.

## Gates

- [x] Existing frontier and literal diagnostic definitions inspected.
- [ ] Precise new positive conjecture with an independent arithmetic mechanism.
- [ ] Dependency-closed paper proof.
- [ ] Exact Lean theorem and direct final verification.
- [ ] Significant-obstacle contribution audit.

## Log

- 2026-10-17 — Selected previously unworked BSH for this goal turn. Started documented deep search `arithmetic section framed mate curvature prime Gamma radial character`, budget 300 seconds. No Lean changed or built.
- 2026-10-17 — Completed three searches and source-level attacks B1–B9. No candidate removed the original arithmetic mate obstruction. Kept the card in progress and contribution credit at zero.
- 2026-10-17 — Direct Lean evidence audit passed for ten existing results; standard logical axioms only. The cross-route goal remains active and incomplete.
