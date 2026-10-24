# Arithmetic local divisor geometry

- **ID:** arithmetic-local-divisor-geometry
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Source:** `docs/reports/review-2410/astra.md`, §§7–9
- **Statement:** Develop exact local-factor and source-certificate mathematics for Ward orientation, retaining multiplicities, contour transitions, mixed terms and the correct heat endpoint.

## Goal

Develop the full programme requested in the attachment. Its endpoint is an independently proved arithmetic source theorem answering the questions in §9.4, not a renamed RH criterion. In particular, a complete coefficient certificate at all heights, cofinal horizontal charge below two, heat collision mass below four approaching heat zero, cap cancellation, or source-forced zeroth-order threshold contact would close WD. None is presently established here.

All new Lean leaves belong to `formal/GaloisForLFunctions/ArithmeticLocalDivisorGeometry/`, with sibling umbrella `ArithmeticLocalDivisorGeometry.lean`. A foundational README must explain motivation, objects, language, mechanisms, traps, research questions, tools, pillars, relations, success criteria and contribution criteria. It must not become a working log.

## Gates

- [x] Scope and original report read; source-specific producer distinguished from existing receivers.
- [ ] Exact local coefficient functionals and normalization developed from existing source identities.
- [ ] Multiplicity-exact contour transition tools, including central zeros.
- [ ] Small-block calibration and selective arithmetic certificate audit.
- [ ] Nontrivial growing-degree certificate families and quantitative clustering costs.
- [ ] Source inequality at the full endpoint, with every height/heat quantifier discharged.
- [ ] Foundational README, umbrella wiring, module checks and transitive axiom audit.

Each dependency-closed theorem receives a separate paper proof and Lean audit. The programme card remains in progress while the source endpoint is open. Compilation uses `lake --old env lean`, never umbrella or full builds.

## Existing inputs and duplication boundaries

- `XiSliceGaussianFiniteHeadPositivity`: exact positive tail, unconditional real-axis positivity, coefficient-cone criterion. Radius one already suffices.
- `XiSliceHeatFiniteHeadReduction`: heated head transfer and continuity at central-zero heights.
- `XiMassPolynomialFiniteContour`, `XiMassPolynomialEulerContourSourceIdentity`: contour source reconstruction already exists; reconstruction alone is not a contribution.
- `DeBruijnCollisionJumpLaw`, `DeBruijnNonrealCountRightLimit`: global collision bookkeeping and right-limit classification already exist.
- `XiSliceHeatThresholdTouching`: threshold contact alternative already exists.
- Pre-existing untracked `RHTower/DeBruijnCollisionMassAndCriticalHeat.lean` contains further collision and threshold results; preserve it and avoid duplication.

## Research record

Initial investigation: inspect exact finite-head and heat APIs, then establish which coefficient-transition and quantitative local-factor results are absent. Candidate directions must preserve signs and growing multiplicity. Universal algebra is a tool, never an arithmetic source-sign theorem.

The initial long natural-language corpus search returned a semantic-runtime timeout and no lexical hits. Follow-up lexical searches use actual declaration stems. This is a search limitation, not evidence of novelty.

### Developed mathematics

- `local-divisor-coefficient-repair.md`: complete paper proofs of exact one-factor repair and sharp equal-factor multiplicity costs. `LocalFactors.lean`, `DivisorTransitions.lean`, and corrected `BinomialMultipliers.lean` have passed module checks/builds. Raw geometric scaling in `GeometricMultipliers.lean` remains unchecked.
- `../3-formalized/universal-coefficient-reflectors.md`: constructive classification of every universal coefficient-cone multiplier as a positive monomial, with strictly positive witnesses and a sharp degree bound. Plain check and standard-only axiom audit passed. `../5-failed/universal-positive-shell-cancellation.md` records the retired generic mechanism and exact positive survivor; WD itself is not retired.
- `ArithmeticLocalDivisorGeometry/README.md` supplies the foundational account and retains all nine original research questions. Its arithmetic endpoints remain open.
- Additional existing inputs found: `HTGeometry/OffLinePairDetectionNewtonSharp.lean` gives the sharp own-ordinate detection order against positive real factors; `HTGeometry/SliceRootHolomorphy.lean` already proves contour-moment reconstruction and holomorphic symmetric functions through multiple roots; `HTGeometry/FiniteSignedValueDefect.lean` already supplies the finite total-variation/negative-mass identity. Do not repackage those as new theorems.
- `../2-fully-proven/central-multiplicity-full-heat-cone.md` proves an exact quadratic-index criterion and rational heat-threshold bracket for `X^(2m)(X²−a)²`. The resulting scale is `a/(8m)`, whereas the top adverse coefficient alone sees `a/m²`. The existing masked-pair moment and cofactor-error receiver are retained as inputs; no source error estimate is claimed.
- Literature audit found Motzkin–Straus (1969), Theorems 2.1 and 2.6: arbitrary quadratic-multiple optimal degree and a sufficient equal-factor bound are classical. The exact odd-degree improvement and formalized local interpretation are the relevant distinction. README and repair card now name this antecedent.

### Verification state and next work

- `LocalFactors.lean` passed `lake --old env lean GaloisForLFunctions/ArithmeticLocalDivisorGeometry/LocalFactors.lean` with exit 0 and no diagnostics. Its required olean build also passed. API/axiom audit `57732` passed: `coeffNonneg_pairFactor_iff`, `exists_linear_repair_iff`, and `pairFactor_boundary_repair` depend only on `propext`, `Classical.choice`, and `Quot.sound`.
- The scratch API check completed: coefficient-shift and binomial names are valid; guessed `coeff_X_mul_succ` and `eval_pos` do not exist and are not used by the new sources.
- `LocalFactors` plain check `46938`, required olean build `65997`, API/axiom check `57732`, corrected `DivisorTransitions` build `27588`, and corrected `BinomialMultipliers` build `36240` passed. All three module oleans exist. `UniversalReflectors` plain retry `42425` passed with standard-only axioms for classification, positive counterexample, sparse sharpness, and central/scale transitions. Temporary print commands were removed without changing proofs; no universal-reflector olean was needed. Its first failed run `55457` is superseded.
- `GeometricMultipliers` plain check `65695` failed at two polynomial composition/map rewrites. Retry `57453` fixed the pair identity but exposed an incorrectly targeted `map_pow` rewrite in the whole block. A named scalar-power identity now targets the intended occurrence; retry pending. Temporary axiom prints must be removed after a clean pass. Both normalized binomial parity theorems passed their transitive axiom audit with standard axioms only. Final plain-file checks of corrected `BinomialMultipliers` and `DivisorTransitions` remain required.
- API check `38516` verified convolution, finite sums, power comparison, and polynomial composition names. `natDegree_le_iff_coeff_eq_zero` and natural floor lemmas need the additional imports now added to `/tmp/aldg_mathlib_check.lean`; their declarations were found in mathlib. Pending new API checks are appended there.
- `MaskedHeatIndex.lean` contains square completion, upper positivity, and the explicit floor detector. First required olean build `8449` stopped at an unnecessary nonexistent `Mathlib.Tactic.NormCast` import; that import was removed and the build retried. `MaskedPairHeatCone.lean` now drafts the full monomial recurrence, signed coefficient identities, exact finite-index cone criterion, upper positivity and floor-selected negative coefficient. All remain pending checks.
- Corrected `MaskedHeatIndex` required olean build `5314` passed with no diagnostics. The only subsequent corrections were explicit real cast types in two arithmetic proofs. Its final plain check remains. `MaskedPairHeatThreshold.lean` now imports the index/contact/heat-cone leaves and drafts threshold attainment, the closed-ray criterion, rational bounds, positivity and exact depth scaling; those imports authorize missing dependency oleans as needed. The threshold module remains unchecked and still needs its asymptotic and exact-contact conclusions.
- Efficient completion of the heat bridge: prove the recurrence `(r+1−j)c_(r+1,j)=(2r+2)(2r+1)s c_(r,j)` for `j≤r`, using only two numerator factorial successors and one denominator successor. With `k=m+1−j`, it yields `k(k+1)[X^(2j)]E_(at)P_m = a² c_(m,j) F_t(k)`. The prefactor is positive for `a,t>0`, giving the sign equivalence without repeatedly expanding four factorials. Handle `j=m+1` separately by the coefficient `a(Ct−2)`, `j=m+2` by one, and higher/odd coefficients by zero. This gives the full all-order cone criterion and the explicit signed margin from `maskedHeatIndex_floor_le`.
- `SourceLocalFactors.lean` now contains the former source scratch: unnormalized actual-Xi polynomial, exact evaluation on `sliceTrunc`, radius-head symmetry, canonical-head identity and exact even Taylor coefficients. Expansion/heat API scratch `93483` passed. Source module check is pending; no source coefficient sign is asserted.
- `HeatConeEvolution.lean` drafts the polynomial heat semigroup via the `X` commutator, cone preservation, monotonicity and closedness. Corpus searches found no existing semigroup declaration for this operator; the generic closed-upset threshold theory already exists in `HTGeometry/LeeYangForcingThreshold` and is not claimed as new. `/tmp/aldg_order_api.lean` awaits its scratch check.
- `MaskedHeatContactIndex` required olean build `8638` passed without diagnostics, including exact middle minimization, strict lower-end negativity, monotonicity of the active index and the parity-sensitive contact degree. Final plain and axiom checks remain. API scratch `84065` verified order/continuity/infimum/IVT/square-root names; only two unused guessed names failed (`Continuous.finset_sum`, `Filter.Tendsto.atTop_add_const_right`), and both were removed. No application code uses them.
- `../2-fully-proven/masked-pair-middle-order-contact.md` gives the full audited paper proof of the stronger theorem exposed by the index argument: throughout the entire threshold bracket the unique minimizing integer is exactly `m/2`, yielding an explicit radical threshold and one active even contact order `j=m+1−m/2`. Existing masked-pair APIs were checked; the general heat-monomial mechanism is classical and no worldwide novelty claim is made. `MaskedHeatContactIndex.lean` drafts the exact minimization argument; it is unchecked. The card also records the exact Hermite normalization still to formalize.
- Owned scratch files remaining: `/tmp/aldg_mathlib_check.lean` (passed), `/tmp/aldg_next_api.lean` (pending expansion/heat APIs and DivisorTransitions axiom checks), `/tmp/aldg_source_work.lean` (pending actual-source normalization and exact even Taylor identity). Obsolete universal drafts, heat paper scratch, and import sample were removed.
- `DivisorTransitions.lean` contains central shifts, positive scaling, strict positive evaluation, and the exact own-ordinate obstruction; its corrected required olean build passed. A final plain-file check and its axiom audit remain.
- Finish and audit existing formalizations, then formalize the raw geometric multiplicity law, central-factor/own-ordinate laws, and exact universal multiplier classification. Wire only finished modules into a new sibling umbrella and the existing aggregate; never compile umbrellas.
- Actual-source integration: construct the unnormalized real polynomial from `sliceTruncCrit` and `sliceTruncUp`, prove its complex evaluation equals the product over `sliceTrunc`, then show `sliceTrunc (xiSliceGaussianRadiusHead t R)` equals the original head by spectral conjugation. The inverse equivalence handles lower copies without importing a separate involution theorem. Identify the exact finite head as its positive scalar times evaluation at `z²`. This retains central zeros but does not claim a new arithmetic sign theorem.
- Other workspace actors are editing and committing independently. Initial unrelated changes were preserved; a later shared commit included the new files. Do not interpret an empty scoped `git status` as absent work or revert those commits.
- The sibling umbrella imports checked `LocalFactors`, `DivisorTransitions`, `BinomialMultipliers`, and `UniversalReflectors`, and is wired into `MainTheorems.lean`. Extend it only as further leaves pass; do not compile either umbrella.

## Completion audit

The full original task remains open until all named research questions have substantive answers and the required tools exist. A foundations batch, generic polynomial theorem, or receiver bridge does not satisfy the endpoint. Unproved source inequalities must remain recorded here rather than becoming hypotheses of purported unconditional results.
