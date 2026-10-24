# Arithmetic local divisor geometry

- **ID:** arithmetic-local-divisor-geometry
- **Stage:** 1-in-progress
- **Type:** RESEARCH PROGRAMME
- **Source:** `docs/reports/review-2410/astra.md`, §§7–9; user attachment `pasted-text-1.txt`
- **Statement:** Develop exact local-factor and arithmetic source-certificate mathematics for Ward orientation, retaining multiplicities, contour transitions, signed mixed terms and the correct heat endpoint.

## Completion criterion

The requested formalization of the source-transition and sharp-Hermite cards, including their stated corollaries, is complete. The broader arithmetic programme remains incomplete. Its endpoint is an independently proved arithmetic source theorem answering the questions in Astra §9.4. A full coefficient certificate, cofinal horizontal charge below two, collision mass below four approaching heat zero, cap cancellation, or source-forced zeroth-order contact would close WD. None is established here. Generic polynomial results and receiver bridges do not discharge their arithmetic premises.

All new Lean leaves belong to `formal/GaloisForLFunctions/ArithmeticLocalDivisorGeometry/`, with sibling umbrella `ArithmeticLocalDivisorGeometry.lean`, already imported by `MainTheorems.lean`. The foundational README explains the programme, all nine original questions, mechanisms, traps, relations and contribution criteria. It is not a progress ledger.

## Verified contributions

- [Exact local coefficient repair](../3-formalized/local-divisor-coefficient-repair.md): pair geometry, sharp one-factor repair, exact parity-sensitive equal-factor multiplicity laws, central shifts and impossibility of repair at an adverse ordinate. Lean: `LocalFactors`, `DivisorTransitions`, `BinomialMultipliers`, `GeometricMultipliers`.
- [Universal reflectors](../3-formalized/universal-coefficient-reflectors.md): positive monomials are exactly universal coefficient-cone reflectors. Every other nonzero cone multiplier masks a noncone polynomial strictly positive on the positive axis, with an explicit degree bound. Lean: `UniversalReflectors`. [Failed route and positive survivor](../5-failed/universal-positive-shell-cancellation.md).
- [Full masked-pair heat cone](../3-formalized/central-multiplicity-full-heat-cone.md): exact finite quadratic-index criterion for `X^(2m)(X²−a)²`, all-real classification `s≥0 ∧ cone(E_s P) ↔ max(a,0)τ_m≤s`, sharp inverse-multiplicity scale, strict decrease with multiplicity and `(8m)τ_m→1`.
- [Exact middle contact](../3-formalized/masked-pair-middle-order-contact.md): radical formula for `τ_m`; unique active even degree `m+2+(m mod 2)` and strictly positive constant coefficient; exact Gaussian moment normalization and full moment-cone threshold. Lean: `MaskedHeatIndex`, `MaskedHeatContactIndex`, `HeatConeEvolution`, `MaskedPairHeatCone`, `MaskedPairHeatThreshold`, `MaskedPairHermite`.
- [Universal zeroth-order contact is retired](../5-failed/universal-zeroth-order-heat-contact.md). Its positive survivors are the full classification above and the sharp Hermite optimization below. Arithmetic source rigidity remains open.

All eleven listed model leaves passed final plain `lake --old env lean` checks and are wired into the sibling umbrella. Key transitive `#print axioms` audits use only `propext`, `Classical.choice` and `Quot.sound`. Temporary prints were removed. No numerical experiments or trusted-computation shortcuts were used.

## Completed formalization

1. [Unnormalized Xi divisor transitions](../3-formalized/unnormalized-xi-divisor-transitions.md): exact source polynomial, positive canonical normalization, even/odd Taylor coefficients and signed convolution through copy-set changes. Arbitrary carriers represent `sliceTrunc S`; radius heads are pairing-stable. Central copies remain without dividing by `XiC(t)`. `SourceLocalFactors.lean` passed its plain check and four standard-only transitive axiom audits.
2. [Sharp heat-root barrier](../3-formalized/sharp-even-heat-root-barrier.md): stationary-point bound, equality rigidity, global attainment, exactly two double real roots, positive even cofactor and exact first heat time. The elementary largest-root asymptotic, optimality of constant four, attained fixed-depth minimum and factor-two comparison with central masking are formalized.
3. `SourceDivisorGeometry.lean`: exact symmetrized-copy degree, monicity, evenness, real-axis nonnegativity and own-ordinate root for the unnormalized Xi divisor. `radiusHead_depth_sq_le_hermite_edge` applies the sharp Hermite obstruction to an actual radius head, preserving central multiplicity. Its heat-cone premise remains explicit; no arithmetic coefficient-sign estimate is proved.

## Final verification

All 23 programme leaves passed individual foreground `lake --old env lean` checks from
`formal/` and are imported by the sibling umbrella. `MainTheorems.lean` imports that
umbrella; no umbrella or full build was run. No Python jobs, numerical experiments,
placeholders, new axioms, hidden analytic premises or proof-limit overrides were used.

| Final plain checks passed | Evidence |
|---|---|
| Eleven original model leaves | Their formalized cards and earlier audit logs |
| `SourceLocalFactors` | `/tmp/aldg_SourceLocalFactors_resume.log` |
| `HermiteHeatNormalization`, `HermiteRootEdge`, `PolynomialHeatDilation`, `HermiteEdgeAsymptotics` | `/tmp/hgt_<leaf>_final.log` and `.exit` |
| `HermiteSonin`, `HermiteHeatRootBarrier`, `EvenPolynomialHeatCone`, `HermiteExtremizers` | `/tmp/aldg_<leaf>_check4.log` and `.exit` |
| `HermiteExtremizerFactorization` | `/tmp/hgt_HermiteExtremizerFactorization_clean_final.log` and `.exit` |
| `HermiteOptimalHeat` | `/tmp/hgt_HermiteOptimalHeat_clean_final.log` and `.exit` |
| `SourceDivisorGeometry` | `/tmp/aldg_SourceDivisorGeometry_final2.log` and `.exit` |

Key transitive audits contain only `propext`, `Classical.choice` and `Quot.sound`.
These cover sharp bound/rigidity, global nonnegativity, exact real roots, Gaussian
normalization, monicity, scaled double multiplicities, positive even cofactor, first heat
time, optimal constant four, actual factor-two heat-time ratio and exact Xi divisor
degree/receiver. Additional audit evidence: `/tmp/hgt_hermite_axioms.log`,
`/tmp/hgt_HermiteExtremizerFactorization_final.log`,
`/tmp/aldg_HermiteOptimalHeat_check4.log` and
`/tmp/aldg_HermiteExtremizers_retry.log`.

All check sessions are terminal. Temporary audit prints and owned scratch proof files
were removed; audit logs remain. Required dependency oleans were preserved.
`SourceDivisorGeometry`, `HermiteExtremizerFactorization` and `HermiteOptimalHeat`
need no olean because no further proof leaf imports them.

The requested formalization is complete. Both completed cards are in `3-formalized`;
the README, no-go survivor and frontier reports record their exact scope. The broader
arithmetic source-sign endpoint remains open.

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
