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

## Completion audit

The full original task remains open until all named research questions have substantive answers and the required tools exist. A foundations batch, generic polynomial theorem, or receiver bridge does not satisfy the endpoint. Unproved source inequalities must remain recorded here rather than becoming hypotheses of purported unconditional results.
