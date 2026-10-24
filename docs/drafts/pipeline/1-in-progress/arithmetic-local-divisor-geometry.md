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

- `local-divisor-coefficient-repair.md`: complete paper proofs of exact one-factor repair and sharp equal-factor multiplicity costs. `LocalFactors.lean` passed its check. The first `BinomialMultipliers.lean` check reported only a constant-coefficient simplification failure; that proof was corrected, and the next check remains pending.
- `../2-fully-proven/universal-coefficient-reflectors.md`: constructive classification of every universal coefficient-cone multiplier as a positive monomial. Lean formalization remains required.
- `ArithmeticLocalDivisorGeometry/README.md` supplies the foundational account and retains all nine original research questions. Its arithmetic endpoints remain open.
- Additional existing inputs found: `HTGeometry/OffLinePairDetectionNewtonSharp.lean` gives the sharp own-ordinate detection order against positive real factors; `HTGeometry/SliceRootHolomorphy.lean` already proves contour-moment reconstruction and holomorphic symmetric functions through multiple roots; `HTGeometry/FiniteSignedValueDefect.lean` already supplies the finite total-variation/negative-mass identity. Do not repackage those as new theorems.
- `../2-fully-proven/central-multiplicity-full-heat-cone.md` proves an exact quadratic-index criterion and rational heat-threshold bracket for `X^(2m)(X²−a)²`. The resulting scale is `a/(8m)`, whereas the top adverse coefficient alone sees `a/m²`. The existing masked-pair moment and cofactor-error receiver are retained as inputs; no source error estimate is claimed.
- Literature audit found Motzkin–Straus (1969), Theorems 2.1 and 2.6: arbitrary quadratic-multiple optimal degree and a sufficient equal-factor bound are classical. The exact odd-degree improvement and formalized local interpretation are the relevant distinction. README and repair card now name this antecedent.

### Verification state and next work

- `LocalFactors.lean` passed `lake --old env lean GaloisForLFunctions/ArithmeticLocalDivisorGeometry/LocalFactors.lean` with exit 0 and no diagnostics. Its required olean build also passed. API/axiom audit `57732` passed: `coeffNonneg_pairFactor_iff`, `exists_linear_repair_iff`, and `pairFactor_boundary_repair` depend only on `propext`, `Classical.choice`, and `Quot.sound`.
- The scratch API check completed: coefficient-shift and binomial names are valid; guessed `coeff_X_mul_succ` and `eval_pos` do not exist and are not used by the new sources.
- The `LocalFactors` plain check `46938` and required olean build `65997` both passed. First `BinomialMultipliers` check `27849`, API check `38516`, and first `DivisorTransitions` build `64572` are terminal. The latter reported only the coefficient-two simplification in `pairFactor_ne_zero`; it was corrected with targeted coefficient rewrites, and unused simp arguments were removed. Only `LocalFactors.olean` exists. The owned live Lean process is `57732`, running the expanded API and LocalFactors axiom check. Revalidate handles before waiting or replacing them. One Lean process at a time.
- API check `38516` verified convolution, finite sums, power comparison, and polynomial composition names. `natDegree_le_iff_coeff_eq_zero` and natural floor lemmas need the additional imports now added to `/tmp/aldg_mathlib_check.lean`; their declarations were found in mathlib. Pending new API checks are appended there.
- `UniversalReflectors.lean` now contains the entire constructive classification, strict axis positivity, and the sharp sparse-shell lower degree law. No check has run yet. `GeometricMultipliers.lean` contains the full raw geometric parity laws, including the zero-distance case; no check has run yet. It imports `BinomialMultipliers` and `DivisorTransitions`, authorizing their missing oleans once checked.
- `/tmp/aldg_heat_index_work.lean` contains the algebraic heat-index square completion, upper positivity, and explicit floor detector, pending scratch check. It must be connected to actual polynomial heat coefficients before it constitutes the full heat theorem.
- `/tmp/aldg_source_work.lean` contains the unnormalized actual-Xi polynomial, exact evaluation on `sliceTrunc`, radius-head symmetry, and canonical-head identity. It is pending API verification and module checking; no source coefficient sign is asserted.
- Scratch files `/tmp/aldg_mathlib_check.lean`, `/tmp/aldg_universal_work.lean`, and `/tmp/aldg_universal_tail.txt` are owned. The universal drafts are superseded by the new main file. `/tmp/aldg-heat-paper.txt` is superseded by the heat card. `/tmp/aldg-lean-sample.txt` is an owned diagnostic. Remove these after verification.
- `DivisorTransitions.lean` now contains central shifts, positive scaling, strict positive evaluation, and the exact own-ordinate obstruction, pending its first check. Build `LocalFactors` once because this new file imports it.
- Finish and audit existing formalizations, then formalize the raw geometric multiplicity law, central-factor/own-ordinate laws, and exact universal multiplier classification. Wire only finished modules into a new sibling umbrella and the existing aggregate; never compile umbrellas.
- Actual-source integration: construct the unnormalized real polynomial from `sliceTruncCrit` and `sliceTruncUp`, prove its complex evaluation equals the product over `sliceTrunc`, then show `sliceTrunc (xiSliceGaussianRadiusHead t R)` equals the original head by spectral conjugation. The inverse equivalence handles lower copies without importing a separate involution theorem. Identify the exact finite head as its positive scalar times evaluation at `z²`. This retains central zeros but does not claim a new arithmetic sign theorem.
- Other workspace actors are editing and committing independently. Initial unrelated changes were preserved; a later shared commit included the new files. Do not interpret an empty scoped `git status` as absent work or revert those commits.
- The sibling umbrella now imports the checked `LocalFactors` module and is wired into `MainTheorems.lean`. Extend it only as further leaves pass; do not compile either umbrella.

## Completion audit

The full original task remains open until all named research questions have substantive answers and the required tools exist. A foundations batch, generic polynomial theorem, or receiver bridge does not satisfy the endpoint. Unproved source inequalities must remain recorded here rather than becoming hypotheses of purported unconditional results.
