# Signed damping continuation of the actual Möbius receiver

- **ID:** astra-opportunity1
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** ../../../reports/review-2110/astra.md, Opportunity 1
- **Statement:** For every `0<a<1/2`, the complete signed damping work of the literal centered Möbius divisor prefix admits a horizon-uniform integrable logarithmic-energy majorant on `[a,1/2]`.

## Goal

Work fully through Opportunity 1: derive and audit the exact arithmetic mechanism, prove the source estimate or establish its exact obstruction, extract strongest positive survivor if obstructed, and formalize dependency-closed unconditional results. Do not substitute a conditional RH receiver for the missing arithmetic producer.

Let `Aε(n)=Σ_{d≤n} μ(d)d^(-ε) floor(n/d)−n/ζ(1+ε)` and `E_T(ε)=Σ_{1≤n≤T} Aε(n)^2/(n(n+1))`. Existing corpus proves `A′ε=Bε`, uniform half-damping admission, and RH iff cofinally small positive dampings admit horizon-uniform budgets.

Exact target (C): for every `0<a<1/2`, some nonnegative `b_a∈L¹[a,1/2]` satisfies `−E′_T(ε)≤b_a(ε)(1+E_T(ε))` for every horizon, almost everywhere. The elementary backward continuation implication is known on paper; the arithmetic inequality is **[OPEN CORE]**.

## Gates

- [x] In-progress: exact source, quantifiers and receiver identified.
- [x] Current internal frontier checked, including stronger/equivalent work.
- [ ] External primary-source novelty and parent-theory audit completed.
- [ ] Exact producer conjecture survives adversarial audit or receives scoped verdict.
- [ ] Dependency-closed paper proof of substantive result.
- [ ] Exact theorem formalized without unproved arithmetic premises, `sorry`, custom axioms, computation certificates or heartbeat increases.
- [ ] Targeted foreground `lake env lean <module>` final audit; only required dependencies, `--old` where supported; new imports wired, no full umbrella build.
- [ ] Completion audit covers original opportunity, not merely auxiliary identities.

## Approach

1. Test the one-sided work against analytic-family/zero-width parent theories and known monotonicity failures.
2. Derive exact finite arithmetic covariance/dilation identity with density and fractional-part/tail terms retained.
3. Investigate the positive multiplicative divisor coefficient `∏_{p|n}(1−p^(-ε))`, its tangent and centering; test whether complete signed covariance yields an independently proved bound.
4. Compare complementary-sector cancellation with signed work; retain all cross terms and quantifier order.
5. Complete paper proof before Lean. Generic continuation alone is a bridge, not completion.

## No-go closure

The full source-specific target (C) remains open. Scoped obstructions: unsigned dilation and total-variation bounds stop at half damping; generic backward quadratic control fails on exact fractional-part eigenprofiles with rates `log d`, including after uniformly equivalent quadratic corrections. These failures do not kill (C).

Positive survivors: an explicit arithmetic Markov generator, transition kernel and entrance law; a centered compact semigroup on `c0`, holomorphic for positive real part; exact signed finite-energy flux; and a square-summable observable tail despite the total-variation obstruction. The actual signed interior discrepancy remains unpaid. The finite generator/energy balance and ordered zero-damping trace have passed clean targeted Lean audits and are umbrella-wired. Kernel and entrance-law audits are in progress. The stronger infinite-dimensional claims remain paper results.

The continuation criterion has exact open threshold `Delta=Theta−1/2`: `a>Delta` implies (C) on `[a,1/2]`, and (C) implies `a>=Delta`. Thus its all-positive-damping version is equivalent to RH. Holomorphic damping jets above `Delta` and generic energy-growth exponents are paper deductions, not unconditional estimates below the existing frontier.

## Log

- 2026-10-22 — Goal activated. Prior report phase complete; this is new proof research. Earlier no-build restriction superseded by user's explicit Lean audit requirements.
- 2026-10-22 — Current Opportunity 1 read; key source files have no tracked changes. Architecture/testing documents absent. Serena memories topic `pm` empty; Lean symbolic support to be tested (project reports Python language).
- 2026-10-22 — hgtl7 applied. Parallel research: exact threshold/analytic parent; actual arithmetic signed work; external primary literature. Logs `logs/astra-opportunity1-{threshold,arithmetic,literature}.txt`.
- 2026-10-22 — No `update_plan` tool exposed; this card tracks plan and phase gates. Previous goal turn: initial goal turn, no prior goal work to classify. Prior report work is completed evidence, not current-goal completion.
- 2026-10-22 — Primary literature identifies the receiver/half-damping starting point with Burnol's 2002 family and the underlying downward divisor process with the 2026 von Mangoldt-chain paper. No worldwide novelty claim. Cesàro conjugation and entrance subtraction expose exact structure but do not themselves improve receiver energy.
- 2026-10-22 — Agent owns only new `DampingWorkAsArithmeticMarkovBoundaryFlux.lean`; root will wire umbrella after final audit. Strongest remaining question: source-specific cancellation in the complete centered boundary flux. Main goal not complete.
- 2026-10-22 — Finite generator and exact original-energy balance passed clean targeted `lake --old env lean`, exit 0. Root inspected source and wired BVI umbrella. Core `.olean` exported for the dependent kernel module. No full/umbrella build.
- 2026-10-22 — Follow-up proof scopes: route_opportunities owns `ZeroDampingSignedWorkHasFiniteHarmonicTrace.lean`; unification_audit owns `ArithmeticDampingTransitionKernel.lean`; root owns `ArithmeticDampingEntranceLaw.lean`. All are disjoint. Strong infinite-dimensional survivor must retain its paper/formal distinction.
- 2026-10-22 — Strongest owned Type-II/dual/complementary theorems re-audited: genuine growing-packet uniformity, but residual errors, absent damping-derivative/cofactor control, and mismatch with complete-energy normalization remain. No source producer extracted. Report records exact gap and quantitative bounds.

- 2026-10-22 — New dependency-closed paper survivor: residual-energy linear cusp forced by any critical zero; finite-horizon trace −4γ differs from any finite full-energy right derivative. Positive escaping covariance does not refute negative-work (C). Classical Hardy-evaluation mechanism; exact source already Bagchi2005, novelty unestablished. route_opportunities owns PowerDampedResidualHasLinearCusp.lean for exact unconditional formalization.
- 2026-10-22 — killed_audit owns ArithmeticDampingCenteredOperator.lean: shifted positive states, compact c0 operator norm≤2 via existing ScheffeCounting. Root owns entrance mass/tail/coordinate limit. Kernel finite semigroup passed first complete audit; clean export pending.

- 2026-10-22 — ArithmeticDampingTransitionKernel and ArithmeticDampingEntranceLaw now both clean-audited, exported, umbrella-wired. Entrance includes exact mass and reciprocal tail plus all coordinate limits. Downstream compact/tail audits unblocked. Root no active build.
