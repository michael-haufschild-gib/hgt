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

1. [Unnormalized Xi divisor transitions](../3-formalized/unnormalized-xi-divisor-transitions.md): paper proof and Lean verification complete for the exact source polynomial, positive canonical normalization, even/odd Taylor coefficients and signed convolution through copy-set changes. Arbitrary carriers represent `sliceTrunc S`; radius heads are already pairing-stable. Central copies are retained without dividing by `XiC(t)`. `SourceLocalFactors.lean` passed its plain check and four standard-only transitive axiom audits, and is wired. No source coefficient sign is asserted.
2. [Sharp heat-root barrier](../2-fully-proven/sharp-even-heat-root-barrier.md): complete paper proof that a degree `2d` nonnegative polynomial with coefficient-positive heat at `λ/2` has positive roots at most `sqrt(λ)` times the largest zero of `He_(2d−1)`. Evenness is unnecessary and is forced at equality. Equality gives a shifted even Hermite extremizer, exactly two double real roots and exact first heat time. The stronger stationary-point engine, elementary largest-root asymptotic, asymptotic optimality of constant four and factor-two comparison with central masking are proved on paper. Lean implementation is underway; these are not yet formalized results.
3. Required dependency checks passed for `HermiteHeatNormalization`, `HermiteRootEdge` and `PolynomialHeatDilation`. All exact paper claims now have complete Lean drafts in the programme folder: `HermiteSonin`, `HermiteHeatRootBarrier`, `HermiteExtremizers`, `HermiteExtremizerFactorization`, `HermiteEdgeAsymptotics`, `EvenPolynomialHeatCone`, `HermiteOptimalHeat` and `SourceDivisorGeometry`. Unchecked drafts are not wired or claimed formalized. No placeholders or unproved analytic interfaces were added.

## Verification state for continuation

- Independent attainment/asymptotics task: `HermiteEdgeAsymptotics` built successfully, including
  the direct `hermiteEdge (2*d-2)^2/(2*d) → 4` statement; standard-only transitive axiom audit.
  Its olean exists and must be preserved. Session `86575` is terminal: final plain checks of
  `HermiteEdgeAsymptotics`, `HermiteHeatNormalization`, `HermiteRootEdge`, and `PolynomialHeatDilation`
  all passed (exit 0), and all four are wired into the umbrella. Results:
  `/tmp/hgt_<leaf>_final.log` and `.exit`. Do not duplicate these checks without a proof change.
  Only the asymptotic module-purpose comment was restored afterward; its theorems are unchanged.
  Additional audit `18946` passed: the direct `2d` edge limit, global nonnegativity, exact real
  roots, Gaussian normalization, and monicity all use only the three standard axioms.
  Evidence: `/tmp/hgt_hermite_axioms.log` and `.exit`; temporary audit source/script removed.
- The independent factorization retry passed: exact scaled double roots and monic positive even
  cofactor have standard-only axiom audits (`/tmp/hgt_HermiteExtremizerFactorization_final.log`).
  Redundant tactics and temporary prints were removed. Its clean final plain check is active:
  `/tmp/hgt_HermiteExtremizerFactorization_clean_final.log` and `.exit`. Avoid duplicating it.
- User explicitly requires no Python. Use Lean, direct corpus-search command, shell reads and patch edits; no Python jobs or file-edit scripts.
- Earlier batches `97689`, `85707` and `42691` are terminal. The interrupted batch was not counted as a pass. Source cast/scalar/convolution fixes subsequently passed the plain check and four standard-only axiom audits in `42691`; source card promoted and umbrella wired.
- Batch `60153` is terminal. Corrected dilation and the required source olean passed. Sonin failed only at explicit interval membership; corrected. Barrier failed at `C 0` simplification and three beta-reduced polynomial evaluations in local-minimum proofs; corrected without changing statements. These failures are not passes and their `sorryAx` diagnostics are not accepted audits. Logs `/tmp/aldg_<leaf>_resume2.log` and `.exit`.
- Batch `2369` is terminal. Corrected Sonin/barrier and `EvenPolynomialHeatCone` required oleans passed, each with standard-only axiom audits. Extremizers failed only at simplification of `(-1)^4` and a missing explicit `coeff_C` rewrite; both corrected. The existing asymptotic olean was preserved. Logs `/tmp/aldg_<leaf>_check3.log` and `.exit`; API `/tmp/aldg_remaining_api.log`.
- **Active batch `27858`:** builds the still-missing corrected `HermiteExtremizers` olean, then performs plain checks of `SourceDivisorGeometry`, `HermiteExtremizerFactorization`, `HermiteOptimalHeat`, `HermiteSonin`, `HermiteHeatRootBarrier`, `EvenPolynomialHeatCone`, `HermiteExtremizers`, in that order. Dependent leaves are skipped if extrema still fail. Logs `/tmp/aldg_HermiteExtremizers_retry.log` and `/tmp/aldg_<leaf>_check4.log`, with corresponding `.exit` files. Temporary axiom prints remain. No second owned Lean until this batch exits. The independent actor owns the other four final plain checks listed above.
- Corrected `HermiteExtremizers` required olean passed in `27858`; `coeffNonneg_heat_scaledHermiteExtremizer_iff` and `nonnegative_boundary_eq_scaledHermiteExtremizer` have standard-only audits. Preserve this olean. The batch has moved to the plain checks.
- `SourceDivisorGeometry` first plain check failed at a redundant natural cast in the cardinality sum and at the real-to-complex algebra map in the own-ordinate root. Both normalization fixes are applied; the final source retry remains. The current batch is checking factorization and optimality before its support-file final audits. No theorem statement changed.
- Factorization's first plain check found only local normalization/elaboration errors: a derivative identity reduced to a trivial disjunction, negative-square positivity, explicit unfolding of `IsRoot`, and `rw` on a local polynomial `let`. Corrections passed the independent retry and standard-only audits listed above. Its clean final check is owned by that actor; do not repeat it.
- `HermiteOptimalHeat` final plain check passed in `27858`. The attained least heat, optimal constant four and actual central/optimal heat-time ratio limit all have standard-only transitive axiom audits. Only redundant terminal `ring` tactics were warned about; no mathematical failure.
- Remaining API verified all used names except nonexistent `Finset.not_mem_range`; replaced with `Finset.mem_range` under negation. `coeff_X_pow` tests coefficient index equal to exponent, so the two finite-sum off-diagonal branches now use `hki.symm`. Scratch failure was removed; no need to repeat the successful API queries.
- Another workspace actor completed the `HermiteEdgeAsymptotics` olean (observed retry PID `71861`, parent `98093`, now exited; `.olean` exists). Their first check proved recurrence/block bounds and exposed four limit elaboration failures, now corrected; the direct degree-`2d` limit was added. Our batch must preserve this existing olean. Final plain audit still required unless the other actor supplies its successful final-check evidence.
- Corrected `HermiteSonin` and `HermiteHeatRootBarrier` required oleans passed in `2369`. Audits of `hermite_edge_strict_min_nonneg`, `nonnegative_root_le_sqrt_mul_hermiteEdge`, `scaled_nonnegative_edge_root_rigidity` and `exists_first_heat_time_of_even_nonnegative_root` use only `propext`, `Classical.choice`, `Quot.sound`.
- Next API scratch: `/tmp/aldg_remaining_api.lean`. All new proof drafts were moved from `/tmp` to the programme folder. `HermiteExtremizerFactorization` proves exact double multiplicities and a monic even strictly positive cofactor at every scale. `HermiteOptimalHeat` proves the attained least heat over the fixed-depth class, optimal constant four, and factor-two central-masking limit. These drafts remain unchecked.
- `EvenPolynomialHeatCone` proves eventual full-cone entry and a positive attained first heat time for the paper's even nonnegative positive-root class. Each coefficient is a polynomial in heat; positive leading coefficient gives positivity beyond its finite root set. No extra analytic premise is used. This generic support was not found in completed corpus searches; it is classical support, not a novelty claim.
- Finish dependency checks, then check all remaining leaves in dependency order. Required oleans for `HermiteExtremizers`, `HermiteEdgeAsymptotics` and `EvenPolynomialHeatCone` are justified by the actual factorization/optimality imports. Final plain audits of all new leaves and transitive axiom audits remain before promoting the sharp-barrier card.
- Required oleans already exist for `LocalFactors`, `DivisorTransitions`, `BinomialMultipliers`, `MaskedHeatIndex`, `MaskedHeatContactIndex`, `HeatConeEvolution`, `MaskedPairHeatCone`, `MaskedPairHeatThreshold`. Never rebuild them. Other model leaves need no olean until a new file imports them.
- Required oleans also exist for `HermiteHeatNormalization`, `HermiteRootEdge` and `PolynomialHeatDilation`; never rebuild them. Old completed API scratches may be removed after the final audit; logs remain as verification evidence.
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
