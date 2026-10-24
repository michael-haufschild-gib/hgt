# Arithmetic local divisor geometry

- **ID:** arithmetic-local-divisor-geometry
- **Stage:** 1-in-progress
- **Type:** RESEARCH PROGRAMME
- **Source:** `docs/reports/review-2410/astra.md`, §§7–9; user attachment `pasted-text-1.txt`
- **Statement:** Develop exact local-factor and arithmetic source-certificate mathematics for Ward orientation, retaining multiplicities, contour transitions, signed mixed terms and the correct heat endpoint.

## Completion criterion

The user requested completion of unfinished Lean work and paper proofs awaiting formalization. This resumption covers the source-transition and sharp-Hermite cards and their stated corollaries. The broader arithmetic programme remains incomplete. Its endpoint is an independently proved arithmetic source theorem answering the questions in Astra §9.4. A full coefficient certificate, cofinal horizontal charge below two, collision mass below four approaching heat zero, cap cancellation, or source-forced zeroth-order contact would close WD. None is established here. Generic polynomial results and receiver bridges do not discharge their arithmetic premises.

All new Lean leaves belong to `formal/GaloisForLFunctions/ArithmeticLocalDivisorGeometry/`, with sibling umbrella `ArithmeticLocalDivisorGeometry.lean`, already imported by `MainTheorems.lean`. The foundational README explains the programme, all nine original questions, mechanisms, traps, relations and contribution criteria. It is not a progress ledger.

## Verified contributions

- [Exact local coefficient repair](../3-formalized/local-divisor-coefficient-repair.md): pair geometry, sharp one-factor repair, exact parity-sensitive equal-factor multiplicity laws, central shifts and impossibility of repair at an adverse ordinate. Lean: `LocalFactors`, `DivisorTransitions`, `BinomialMultipliers`, `GeometricMultipliers`.
- [Universal reflectors](../3-formalized/universal-coefficient-reflectors.md): positive monomials are exactly universal coefficient-cone reflectors. Every other nonzero cone multiplier masks a noncone polynomial strictly positive on the positive axis, with an explicit degree bound. Lean: `UniversalReflectors`. [Failed route and positive survivor](../5-failed/universal-positive-shell-cancellation.md).
- [Full masked-pair heat cone](../3-formalized/central-multiplicity-full-heat-cone.md): exact finite quadratic-index criterion for `X^(2m)(X²−a)²`, all-real classification `s≥0 ∧ cone(E_s P) ↔ max(a,0)τ_m≤s`, sharp inverse-multiplicity scale, strict decrease with multiplicity and `(8m)τ_m→1`.
- [Exact middle contact](../3-formalized/masked-pair-middle-order-contact.md): radical formula for `τ_m`; unique active even degree `m+2+(m mod 2)` and strictly positive constant coefficient; exact Gaussian moment normalization and full moment-cone threshold. Lean: `MaskedHeatIndex`, `MaskedHeatContactIndex`, `HeatConeEvolution`, `MaskedPairHeatCone`, `MaskedPairHeatThreshold`, `MaskedPairHermite`.
- [Universal zeroth-order contact is retired](../5-failed/universal-zeroth-order-heat-contact.md). Its exact positive survivor is the full classification above. Arithmetic source rigidity remains open.

All eleven listed model leaves passed final plain `lake --old env lean` checks and are wired into the sibling umbrella. Key transitive `#print axioms` audits use only `propext`, `Classical.choice` and `Quot.sound`. Temporary prints were removed. No numerical experiments or trusted-computation shortcuts were used.

## Current proof work

1. [Unnormalized Xi divisor transitions](../2-fully-proven/unnormalized-xi-divisor-transitions.md): dependency-closed paper proof of the exact source polynomial, positive canonical normalization, even/odd Taylor coefficients and signed convolution through copy-set changes. Arbitrary carriers represent `sliceTrunc S`; radius heads are already pairing-stable. Central copies are retained without dividing by `XiC(t)`. Lean `SourceLocalFactors.lean` awaits corrected check; no source coefficient sign is asserted.
2. [Sharp heat-root barrier](../2-fully-proven/sharp-even-heat-root-barrier.md): complete paper proof that a degree `2d` nonnegative polynomial with coefficient-positive heat at `λ/2` has positive roots at most `sqrt(λ)` times the largest zero of `He_(2d−1)`. Evenness is unnecessary and is forced at equality. Equality gives a shifted even Hermite extremizer, exactly two double real roots and exact first heat time. The stronger stationary-point engine, elementary largest-root asymptotic, asymptotic optimality of constant four and factor-two comparison with central masking are proved on paper. Lean implementation is underway; these are not yet formalized results.
3. `HermiteHeatNormalization.lean` supplies classical unit heat/Hermite conversion. Its corrected plain check did not run before the goal was cleared. `HermiteRootEdge.lean` is a complete unchecked draft. Complete unchecked drafts `HermiteSonin.lean`, `PolynomialHeatDilation.lean` and `HermiteHeatRootBarrier.lean` are preserved in the programme folder, unwired. The barrier draft includes arbitrary positive Gaussian scale and equality rigidity. `HermiteExtremizers` and `HermiteEdgeAsymptotics` remain paper-only. Additional API scratch `/tmp/aldg_extra_api.lean` has not run. No placeholders or unproved analytic interfaces were added.

## Verification state for continuation

- User explicitly requires no Python. Use Lean, direct corpus-search command, shell reads and patch edits; no Python jobs or file-edit scripts.
- Owned batch `97689` is terminal. Final plain checks passed for `GeometricMultipliers`, `MaskedPairHermite`, `DivisorTransitions`, `BinomialMultipliers`, `MaskedHeatIndex`, `MaskedHeatContactIndex`, `HeatConeEvolution`, `MaskedPairHeatCone`, `MaskedPairHeatThreshold`. Its only failure was `SourceLocalFactors`.
- Source failures were complex cast normalization, an overbroad scalar rewrite and the wrong antidiagonal namespace. All three fixes are applied. The pair identity and `Finset.HasAntidiagonal.antidiagonal` were verified in `/tmp/aldg_edge_api.lean` (exit 0). The corrected source retry was interrupted when the user cleared the goal; its empty log is not a pass. Temporary axiom prints were removed. On resumption audit `exists_pos_xiFiniteHead_normalization`, `xiFiniteHead_even_taylor`, `xiFiniteHead_odd_taylor` and `localDivisorPolynomial_split_coeff`.
- **Active resumption batch: session `42691`.** Sequential checks: pending `/tmp/aldg_extra_api.lean`, corrected source plain check with axiom audit, required missing oleans for `HermiteHeatNormalization`, `HermiteRootEdge`, `PolynomialHeatDilation`. All three are imported by the actual barrier/Sonin drafts. Logs and statuses: `/tmp/aldg_<leaf>_resume.log` and `.exit`. No second owned Lean until the batch exits. The earlier interrupted batch `85707` is terminal; no pass was inferred from its cancellation.
- Resume sequence: verify `/tmp/aldg_extra_api.lean`; check corrected source and unit normalization; check the new root, dilation, Sonin and barrier leaves in dependency order. Build each missing olean only when required by an actual downstream import, never rebuild an existing olean. Finish extremizer attainment/root multiplicity/exact heat ray and the elementary edge asymptotic before promoting the sharp-barrier card.
- Required oleans already exist for `LocalFactors`, `DivisorTransitions`, `BinomialMultipliers`, `MaskedHeatIndex`, `MaskedHeatContactIndex`, `HeatConeEvolution`, `MaskedPairHeatCone`, `MaskedPairHeatThreshold`. Never rebuild them. Other model leaves need no olean until a new file imports them.
- Old completed API scratches and duplicate proof drafts were removed from `/tmp`. Pending `/tmp/aldg_extra_api.lean` is retained for resumption; audit logs remain as verification evidence. Complete proof drafts are in the programme folder.
- No umbrella/full builds. Every check/build is foreground `lake --old env lean`, from `formal/`, one owned process at a time. Other workspace actors edit and commit independently; preserve their files and commits. A shared commit may include our drafts.

## Existing inputs and duplication boundaries

- `XiSliceGaussianFiniteHeadPositivity`: exact positive tail, unconditional real-axis positivity, coefficient-cone receiver, canonical scalar positivity. Radius one suffices.
- `XiSliceHeatFiniteHeadReduction`: heated-head transfer, central-height continuity and existing normalized signed transition laws.
- `XiMassPolynomialFiniteContour`, `XiMassPolynomialEulerContourSourceIdentity`: source reconstruction; reconstruction alone is not new source positivity.
- `DeBruijnCollisionJumpLaw`, `DeBruijnNonrealCountRightLimit`, and another actor's `DeBruijnCollisionMassAndCriticalHeat`: collision bookkeeping and threshold receivers. Preserve those files.
- `XiSliceHeatMaskedPairThreshold`: existing all-order moments, top-order threshold, small-multiplicity examples and actual-Xi cofactor-error receiver. Our exact growing-order optimization does not bound that cofactor error.
- `HTGeometry/OffLinePairDetectionNewtonSharp`: sharp own-ordinate detection against positive real factors. `SliceRootHolomorphy`: contour reconstruction and holomorphic symmetric functions through multiple roots. `FiniteSignedValueDefect`: finite negative-mass identity. These are inputs.
- `RHTower/XiWardGlobalCapAndFiniteHeadArithmetic`: another actor's large source-specific module already contains heat inversion, general degree obstruction, head cardinality/normalization, first-coefficient Prime–Cesàro identity and pure-quadratic width receiver. No import/compilation of that unbuilt module was needed. Our short semigroup support is not a novelty claim. The receiver requires actual heated-head positivity at `λ≤δ₀²/[320 log(180|t|)]`, all `|t|≥73/5`, with radius in `[1/2,1]`; no producer is supplied here.
- Classical Hermite inputs: `HermiteRealRoots`, `HermitePerturbationRealRoots`, `SpurHermite`, `HermiteGaussianMomentBounds`. Largest-root asymptotics and Sonin critical-value monotonicity are classical, checked against DLMF. The sharp barrier card includes independent symbolic proofs instead of importing external analytic premises.
- Corpus search `polyHeat natDegree` located `natDegree_polyHeat` in `HTGeometry/PolynomialHeatNonrealCount.lean:257`; inspect before using. Generic heat dilation had no exact hit in the completed corpus search.

## Literature and novelty

Motzkin–Straus (1969), Theorems 2.1 and 2.6, already give optimal arbitrary quadratic-multiple degree and a sufficient equal-factor law. The local parity-sensitive iff, exact growing-multiplicity heat threshold/contact and proposed Hermite equality law are the programme contributions under audit. General multiplier positivity, heat monomials, Hermite roots and Sonin monotonicity are classical. Targeted searches do not prove worldwide novelty; no such claim is made.

## Remaining arithmetic work

Retain all nine original questions and full source quantifiers from the README/report. Next tools must connect the exact unnormalized head to signed arithmetic coefficient functionals, identify selective source restrictions on extremal local shapes, and prove source inequalities rather than add them as assumptions. Central multiplicities and positive tails cannot be deleted before heat. Any new no-go must retain and formalize its strongest nontrivial positive survivor. The programme is not complete while its arithmetic endpoint is open.
