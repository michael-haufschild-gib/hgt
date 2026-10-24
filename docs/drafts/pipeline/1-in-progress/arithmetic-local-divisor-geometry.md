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
- API checks verified convolution, finite sums, power comparison, polynomial composition, degree bounds, natural floors, expansion and heat coefficient names. The real floor instance uses `Mathlib.Algebra.Order.Archimedean.Real.Basic`.
- Corrected `MaskedHeatIndex` required olean build `5314` passed with no diagnostics, after removing a nonexistent redundant tactic import and specifying real cast types. It contains square completion, uniform upper positivity, the floor margin and explicit negative index. Final plain and axiom checks remain; its olean exists.
- `MaskedPairHeatCone.lean` is unchecked. It drafts the recurrence `(r+1−j)c_(r+1,j)=(2r+2)(2r+1)s c_(r,j)`, scaled coefficient identity `k(k+1)[X^(2j)]E_(at)P_m=a²c_(m,j)F_t(k)`, the separate top orders, exact sign/vanishing transfer, the full finite-index cone criterion, upper positivity and floor-selected negative coefficient. `MaskedPairHeatThreshold.lean` imports it, authorizing its missing olean.
- `SourceLocalFactors.lean` now contains the former source scratch: unnormalized actual-Xi polynomial, exact evaluation on `sliceTrunc`, radius-head symmetry, canonical-head identity and exact even Taylor coefficients. Expansion/heat API scratch `93483` passed. Source module check is pending; no source coefficient sign is asserted.
- `HeatConeEvolution.lean` supplies the polynomial heat semigroup via the `X` commutator, cone preservation, monotonicity and closedness. A later corpus search surfaced `RHTower/XiWardGlobalCapAndFiniteHeadArithmetic`, which already contains the semigroup/inversion and general finite-degree root detector. These are existing inputs, not new claims. The short generic support proofs here avoid importing that large source-specific module into polynomial-only leaves. Generic closed-upset threshold theory also already exists in `HTGeometry/LeeYangForcingThreshold`.
- `MaskedHeatContactIndex` required olean build `8638` passed without diagnostics, including exact middle minimization, strict lower-end negativity, monotonicity of the active index and the parity-sensitive contact degree. Final plain and axiom checks remain. API scratch `84065` verified order/continuity/infimum/IVT/square-root names; only two unused guessed names failed (`Continuous.finset_sum`, `Filter.Tendsto.atTop_add_const_right`), and both were removed. No application code uses them.
- `HeatConeEvolution` first build `37720` failed because an unqualified scalar rewrite hit an inner heat term. Explicit arguments fixed it; required olean retry `58915` passed. Its olean now exists. Final plain and axiom checks remain.
- Required `MaskedPairHeatCone` olean retry `48021` passed. Its first build `44648` reported only a redundant `ring` after `field_simp` had closed the recurrence proof; that line was removed. It includes exact sign/strict-sign/vanishing transfer and the all-order cone criterion. Final plain and axiom checks remain. `MaskedPairHeatThreshold` drafts the whole closed-ray/scale/bounds/strict-multiplicity/contact/radical/asymptotic proof and unconditional all-real classification `(0≤s ∧ cone(E_s P_a)) ↔ max(a,0)τ_m≤s`; it remains unchecked. `MaskedPairHermite.lean` imports it and drafts exact Hermite conversion, the full moment cone threshold `λ≥2b²τ_m` and a negative order below it. These imports authorize the missing threshold olean. Narrow API check `/tmp/aldg_hermite_api.lean` is process `62168`; poll before starting the threshold build.
- Additional duplication boundary: `XiWardGlobalCapAndFiniteHeadArithmetic` already proves radius-head conjugation/cardinality, normalized-head degree bounds, a pure-quadratic finite-head detector, normalized finite-head identification away from `XiC(t)=0`, and the first coefficient's Prime–Cesàro source identity. Keep those as inputs. Our source representation retains central copies without division; the new exact model threshold/contact results remain distinct from its universal degree obstruction.
- Narrow API check `62168` verified factorial cancellation, vanishing of descending factorials, and the finite-set product/disjointness lemmas used here. An unused guessed name `Finset.inter_union_sdiff` failed and was removed; the source split instead has a direct extensional proof. The required `MaskedPairHeatThreshold` olean check now includes temporary axiom prints for its exact value, unconditional classification, exact contact and asymptotic. Remove prints after a clean pass. The larger `XiWardGlobalCapAndFiniteHeadArithmetic` has no olean present and was not compiled or imported by this task; its source statements were inspected for duplication and interface accounting.
- `SourceLocalFactors` now also drafts odd Taylor vanishing, a reusable exact complex head polynomial, disjoint-set multiplicativity and unconditional copy-set splitting with its full signed coefficient convolution. The latter adapts the already existing normalized transition proof from `XiSliceHeatFiniteHeadReduction`; no new set-algebra principle is claimed. Source module remains unchecked.
- `../2-fully-proven/masked-pair-middle-order-contact.md` gives the full audited paper proof of the stronger theorem exposed by the index argument: throughout the threshold bracket the unique minimizing integer is `m/2`, yielding an explicit radical threshold and one active even degree `m+2+(m mod 2)`. Existing masked-pair APIs were checked; the general heat-monomial mechanism is classical and no worldwide novelty claim is made. The card records the exact Hermite normalization still to formalize: `maskedPairMoment b λ m j = λ^j (2j)! [X^(2j)]E_(λ/2)P_(b²,m)`.
- Owned scratch files: `/tmp/aldg_mathlib_check.lean` (passed), `/tmp/aldg_next_api.lean` (passed), `/tmp/aldg_order_api.lean` (all remaining names verified; two unused failed guesses removed). The source scratch was moved to `SourceLocalFactors.lean`. `/tmp/aldg_limits_api.lean` was removed unused. Clean up the remaining owned scratches after final audits.
- Final plain-file checks of corrected `DivisorTransitions` and `BinomialMultipliers` remain. Their required olean builds and key transitive axiom audits passed. `UniversalReflectors` already passed its final plain and axiom audit; trailing blank-line cleanup changed no proof.
- Next: finish the live heat-evolution build; build the missing heat-coefficient bridge olean; check the complete threshold/contact leaf; retry geometric scaling; check actual-source normalization; formalize the Hermite bridge; run final plain/axiom audits and extend the umbrella. Preserve the full arithmetic endpoint as open until its source inequalities are proved.
- Actual-source integration: construct the unnormalized real polynomial from `sliceTruncCrit` and `sliceTruncUp`, prove its complex evaluation equals the product over `sliceTrunc`, then show `sliceTrunc (xiSliceGaussianRadiusHead t R)` equals the original head by spectral conjugation. The inverse equivalence handles lower copies without importing a separate involution theorem. Identify the exact finite head as its positive scalar times evaluation at `z²`. This retains central zeros but does not claim a new arithmetic sign theorem.
- Other workspace actors are editing and committing independently. Initial unrelated changes were preserved; a later shared commit included the new files. Do not interpret an empty scoped `git status` as absent work or revert those commits.
- The sibling umbrella imports checked `LocalFactors`, `DivisorTransitions`, `BinomialMultipliers`, and `UniversalReflectors`, and is wired into `MainTheorems.lean`. Extend it only as further leaves pass; do not compile either umbrella.

## Completion audit

The full original task remains open until all named research questions have substantive answers and the required tools exist. A foundations batch, generic polynomial theorem, or receiver bridge does not satisfy the endpoint. Unproved source inequalities must remain recorded here rather than becoming hypotheses of purported unconditional results.
