# Exact subpower criterion for the Möbius divisor Abel source

- **ID:** CCM-FU-ABEL-SUBPOWER
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:** RH is equivalent to `∀ ε > 0, ∃ Cε ≥ 0, ∀ M ≥ 2, |S(M)/M| ≤ Cε M^ε`, where `S` is the literal `mobiusDivisorSquareRootAbelMoment`.

## Purpose and remaining obstacle

This permits logarithmic or other subpower losses in an arithmetic estimate for the exact signed source. The source estimate is **unproved**. The equivalence supplies no unconditional RH proof and no bound for a growing prime core. Constants may depend on ε, but not on M. A fixed positive exponent gives only a positive-width conclusion through this argument.

## Dependency-closed paper proof

Write `A(M)` for the coherent Selberg Abel moment, `L(M)` for its polar lattice defect, and `R(t)` for `criticalMellinChebyshevResolventSource t`. Existing exact identities give, for `M ≥ 2`,

```
S(M) = A(M) + 2γ(√M − 1),
R(log M) = 2(A(M) + L(M))/M,
|L(M)| ≤ √M.
```

Because `1 ≤ √M ≤ M`,

```
|R(log M)| ≤ 2|S(M)/M| + 2(|2γ| + 1).
```

If `|S(M)/M| ≤ C M^α` and `α ≥ 0`, then `M^α ≥ 1`, so
`|R(log M)| ≤ 2(C + |2γ| + 1) exp(α log M)`. The existing theorem
`exists_global_exponential_bound_criticalMellinChebyshevResolventSource_of_log_nat_exponentialBound`
extends this to `|R(t)| ≤ B exp(αt)` for every `t ≥ 0`, with the same exponent. The existing theorem
`xiZeroHalfPlaneBound_of_criticalMellinChebyshevResolventSource_exponentialBound`
then places every Xi zero in `Re ρ ≤ 1/2 + α` when `0 ≤ α < 1/2`.

For every `ε > 0`, choose `α = min(ε, 1/4)`. The assumed source estimate yields `Re ρ ≤ 1/2 + ε`. Taking all positive ε gives the zero-width bound, equivalent to RH by `xiZeroHalfPlaneBound_zero_iff_rh`.

Conversely, `riemannHypothesis_iff_mobiusDivisorSquareRootAbelBounded` gives a constant bound under RH. Multiplication by `M^ε ≥ 1` proves the stated subpower condition.

## Search and scope audit

Broad deep OR search: `Holomorphic continuation from arbitrarily small power bounds on partial sums`, no module filter, 180-second budget. It returned 117,562 lexical matches across 27,818 modules; 18 declarations, 18 candidate lemmas, 18 source arguments; no generated proof ideas or ingredient sets. Partial result: text/source retrieval interrupted and ranking deadline expired. Semantic inventory: 2,168,265 / 2,331,274 ready; compiler/source coverage pending. Candidate/source sections were inspected, not treated as checked proofs.

Generic Dirichlet convergence, Laurent approximation, and conditional continuation results do not supply the literal arithmetic bound. Source inspection instead identified the existing arbitrary-width resolvent and log-mesh interpolation theorems above. Their signatures were checked against cached Lean modules and used in the closed proof. No numerical experiment is needed for this exact analytic implication.

### Broad follow-up searches for the arithmetic estimate

`subpower` (one concept, deep, 120-second budget) completed in 61.27 seconds with 357 matches across 122 modules, 20 declarations, 20 candidates, 20 source arguments, no generated proof ideas, and one proposed ingredient set. No runtime errors; semantic coverage remains partial (2,168,425 / 2,331,276 ready). Source/compiler inventory includes 43,712 pending compiler records and 43 stale snapshots. The proposed ingredient set connects other RH-equivalent conditions and does not produce a source bound.

`bootstrap contraction` (deep OR, no module filter, 120-second budget) returned 1,661 matches across 582 modules, 20 declarations, 20 candidates, 20 source arguments, no generated proof ideas or ingredient sets. Partial: malformed/incomplete local-model JSON and deadline-interrupted retrieval. Candidate statements and source arguments were inspected despite those limitations.

Applicability checks against source:

- `bourgain_powerScale_iterate` needs an actual recurrence `b(x) ≤ C x^δ b(x^α)`. It proves how losses accumulate; it does not prove that recurrence for this Abel moment. The weighted parabola estimates retain a sum over moment fibers; no source identity found converts the literal pointwise signed sum into that energy with subpower cost.
- `abstract_energy_bootstrap` requires an exact energy-increment decomposition, a primitive dominated by energy, and small total drift/control. None of those source-specific inequalities follows from its abstract conclusion.
- **Direct Erdős–Selberg contraction test:** `m_window_contraction_of_ratio` bounds `|psiRemainder(t)|/t` by a coefficient `a`. Its hypotheses require `δ ≤ a`, `40/δ + 2 < log Q`, and `8Q ≤ c`, `cx₁ ≤ N`, `x₁ ≥ 8`, hence `Q ≤ N`. These imply `40 < a log N`. Consequently it cannot be directly instantiated with `a = N^(−1/2+ε)` once `a log N ≤ 40`. This rejects that direct parameter substitution; it does not rule out retaining more signed information or another contraction theorem.
- The underlying `abs_psiRemainder_recursion` controls `|R(N) log N + Σ Λ(k) R(⌊N/k⌋)|` by `400N`. Taking its absolute error through a square-root Abel sum still leaves a power-sized forcing term. The signed recursion and its forcing would need a stronger joint estimate before it could supply the new subpower criterion.

These are source-applicability findings, not a claimed no-go for every bootstrap and not a proved arithmetic estimate. No predictable numerical experiment was run.

## Verification

- [x] Complete paper implication in both directions, with existing named dependencies.
- [x] Scratch proof of the exact source criterion (`lake env lean`, exit 0).
- [x] Exact-leaf build, new-theorem axiom audit, lint, umbrella import.

Module: [CCMFUSuzukiMobiusDivisorAbelSubpower.lean](../../../../formal/GaloisForLFunctions/RHTower/CCM/CCMFUSuzukiMobiusDivisorAbelSubpower.lean).
Public theorems: `abs_resolvent_log_nat_le_mobiusDivisorSquareRootAbel` and
`riemannHypothesis_iff_mobiusDivisorSquareRootAbelSubpower` in namespace `RHTower`.
The criterion has no external premise; it is an equivalence, not a proof of either side.
Both new theorem closures use only `propext`, `Classical.choice`, and `Quot.sound`.

[Validation](ccm-fu-abel-subpower-criterion/validation.txt),
[new-theorem axioms](ccm-fu-abel-subpower-criterion/axioms.txt),
[continuation search](ccm-fu-abel-subpower-criterion/continuation-search.json),
[subpower search](ccm-fu-abel-subpower-criterion/subpower-search.json),
[bootstrap search](ccm-fu-abel-subpower-criterion/bootstrap-search.json).

The frontier map remains read-only. No source estimate is promoted from hypothesis to theorem.
