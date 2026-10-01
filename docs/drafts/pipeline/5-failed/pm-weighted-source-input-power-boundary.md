# Sharp power boundary of the weighted analytic source inputs

- **ID:** pm-weighted-source-input-power-boundary
- **Stage:** 5-failed
- **Type:** PROVED ANALYTIC-INPUT NO-GO; POSITIVE CLASSIFICATION FORMALIZED
- **Source:** Route PM; weighted endpoint; exact auxiliary mean/variance split
- **Scope:** Test the strength of the analytic inputs used so far. This is not a
  counterexample for the actual Chebyshev function, Möbius coefficients, or RH.
- **Status:** Failed inference from analytic inputs to critical variance; exact positive survivor fully formalized and audited.

## Why this is the next audit

The actual canonical logarithmic Fermi error must control the intrinsic variance
of `ψ(x)/x`. Complete corpus searches returned PNT error integrability, a global
linear bound, Selberg recursions with an `O(N)` remainder, and exact signed-work
balances. None supplies the critical variance upper bound. Before trying to derive
one from the already used analytic inputs, check whether those inputs can imply it.

The candidate below preserves nonnegativity, monotonicity, the global linear bound,
vanishing on `(0,1]`, PNT normalization, absolute `e/x²` integrability and square
`e²/x³` integrability. Yet its optimally centered canonical variance can grow as a
positive power. Thus those analytic properties alone cannot discharge the remaining
arithmetic estimate. No claim about Selberg recursion is included without a separate
proof; no prime-support or divisor-convolution identity is asserted for the model.

## Literal model and input checks

For `0<σ<1`, define

`P_σ(x)=0` if `x≤1`, and `P_σ(x)=x+x^σ` if `1<x`.

For `x≥0`, `0≤P_σ(x)≤2x`; `P_σ` is measurable and monotone. Moreover,

- `P_σ(x)/x → 1` as `x→∞`;
- `∫_(1,∞) |P_σ(x)−x|/x² dx = 1/(1−σ)`;
- `∫_(1,∞) (P_σ(x)−x)²/x³ dx = 1/[2(1−σ)]`.

Local extension to `(1/2,∞)` is bounded. The exact dyadic mode for `x>2` is

`P_σ(x)−2P_σ(x/2) = (1−2^(1−σ))x^σ`.

These are symbolic power-integral identities, not numerical experiments.
For every `0<α<1`, the model also obeys the stronger envelope
`|P_σ(x)−x|≤x exp(−(log x)^α)` eventually, including the corpus exponents `1/10`
and `1/2`. Indeed `(log x)^(α−1)→0`, so `(log x)^α≤(1−σ)log x` eventually;
exponentiation gives the inequality. Lean proves this envelope for every real `α<1`, including nonpositive exponents.

## Strong positive survivor: exact optimal variance and its threshold

For `R≥1`, put `f_σ(x)=P_σ(x)/x`,

`m_σ(R)=R⁻¹∫_(0,R)f_σ(x) dx`,
`V_σ(R)=∫_(0,R)(f_σ(x)−m_σ(R))² dx`.

Finite integrability follows from `0≤f_σ≤2`. For every real scalar `B`,

`∫_(0,R)(B−f_σ)² = R(B−m_σ(R))² + V_σ(R)`.

Thus `m_σ(R)` is the unique minimizing scalar. The exact first moment is

`I₁(R)=R−1+(R^σ−1)/σ`, and `m_σ(R)=I₁(R)/R`.

For `σ≠1/2`, the second moment is

`I₂(R)=R−1+2(R^σ−1)/σ+(R^(2σ−1)−1)/(2σ−1)`.

Therefore `V_σ=I₂−I₁²/R`. Write `a=1/σ`, `b=1+1/σ`, `d=2σ−1`. Expansion gives

`V_σ(R) = [(1−σ)²/(σ² d)] R^d + 1−1/d + 2ab R^(σ−1) − b²/R`.

At `σ=1/2` the removable power-integral singularity instead gives

`V_(1/2)(R)=log R−3+12 R^(-1/2)−9/R`.

The strongest resulting classification for `0<σ<1` is:

- `σ<1/2`: `V_σ(R)→1+1/(1−2σ)`;
- `σ=1/2`: `V_σ(R)−log R→−3`;
- `σ>1/2`: `V_σ(R)/R^(2σ−1)→(1−σ)²/[σ²(2σ−1)]>0`.

Hence `V_σ(R)/(log R)²→0` exactly when `σ≤1/2`; for `σ>1/2` it tends to infinity.
No scalar renormalization can remove that supercritical growth. This is the positive
survivor to formalize before closing the analytic-input no-go. The actual prime
profile has additional arithmetic structure; using it remains the RH task.

## Dependency-closed paper proof

Split every finite integral at `1`, where the profile is zero. On `(1,R)`, integrate
`1+x^(σ−1)` and its square termwise; these functions are continuous there and locally
bounded at `1`. Their primitives give the displayed moments. Expand around the mean
and use the vanishing centered first moment to obtain the unique minimum. Ordinary
power limits prove the three asymptotic cases; positive powers dominate logarithms
in the final supercritical ratio. Tail power integrals prove the analytic input
checks independently; the stretched-log envelope follows from the negative power
limit just displayed. The dyadic formula follows directly on `x>2`.

## Corpus/novelty audit

- The precursor's deep square-error and Selberg searches were complete and returned
  no matching unconditional critical variance producer. Each had all 20 candidate
  and 20 source-argument statements reviewed; proposed ingredient sets were not
  accepted as proofs.
- A fresh hybrid power-model query completed with `partial=false`, no errors and
  full 63,557-file inventory. All 20 candidate and 20 source-argument statements
  were read. It returned the actual PNT inputs and conditional stronger power
  estimates, but no matching model classification. Compiler metadata was mostly
  pending/stale; no source-only hit was treated as compiled evidence.
- Exhaustive relevant power/Chebyshev/PNT model-name source search found no earlier
  matching declaration. The final direct statement/definition audit was completed before Lean; no matching
  classification was found. This is a corpus audit, not a publication novelty claim.

## Gates

- [x] State exact analytic hypotheses and preserve the actual arithmetic task.
- [x] Dependency-closed paper proof, including the strongest positive survivor.
- [x] Final novelty/source audit and scratch API probes.
- [x] Formalize input checks, exact optimal variance and the sharp threshold.
- [x] Targeted build, direct actual-leaf, all axioms, wiring/index/lint audits.
- [x] Record the exact survivor and move this analytic-input no-go to its proper stage.


## Located APIs for the next scratch pass

- `Mathlib/Analysis/SpecialFunctions/ImproperIntegrals.lean`: actual definitions of
  `integrableOn_Ioi_rpow_of_lt` and `integral_Ioi_rpow_of_lt`.
- `Mathlib/Analysis/SpecialFunctions/Integrals/Basic.lean`: `integral_rpow` and
  the logarithmic primitive at exponent `-1`.
- `Mathlib/Analysis/SpecialFunctions/Pow/Asymptotics.lean`: `tendsto_rpow_atTop`,
  `tendsto_rpow_neg_atTop`, and `isLittleO_log_rpow_rpow_atTop` (the last
  statement was read directly and controls arbitrary log powers by a positive power).
- Exact namespaces/types must still be probed against this toolchain in scratch
  before reuse. No assumption is made from the name alone.

## Current formalization log

- Final hybrid power-profile query: `partial=false`, no errors, 63,567-file inventory;
  all 20 candidate and 20 source-argument statements reviewed. Exhaustive relevant
  model-name search plus direct source inspection found no matching classification.
- Input scratch passed Lean with no output. The stretched-log proof works for every
  real `α<1`; no positive lower bound on `α` is required. This strengthens the stated
  envelope without changing the paper argument.
- Created `PMAnalyticPowerModel.lean`; targeted build pending.
- Next: exact finite moments, integral-defined variance, unique minimizer, three
  asymptotic regimes, logarithmic threshold, then complete leaf/axiom/wiring audits.

- Input leaf targeted `--old` build passed (30 seconds; one owned leaf).
- Exact variance scratch passed Lean with no output: finite integrability, first
  and second moments, scalar decomposition, unique minimum, power formula and
  half-exponent logarithmic formula. Created `PMAnalyticPowerVariance.lean`; build pending.
- Asymptotic boundary scratch drafted; not yet checked.

- Variance leaf targeted `--old` build passed (42 seconds; one owned leaf).
- Boundary scratch passed Lean with no output: all three asymptotic regimes, exact
  `V/log²→0` iff `σ≤1/2`, divergence for every centering function above the boundary,
  both input integrals extended to `(1/2,∞)`, and an unconditional existential
  analytic-input obstruction instantiated at the exact rational exponent `3/4`.
- Created `PMAnalyticPowerBoundary.lean` and wired all three leaves into `RHTower`.
  No umbrella build. Final audits pending.

## Final certificate (2026-10-01)

- `PMAnalyticPowerModel.lean`: 18 declarations / 146 lines.
- `PMAnalyticPowerVariance.lean`: 16 declarations / 196 lines.
- `PMAnalyticPowerBoundary.lean`: 12 declarations / 201 lines.
- Each targeted `lake --old build +<module>:olean` passed (30, 42, 42 seconds).
- Each final `lake env lean GaloisForLFunctions/RHTower/<leaf>.lean` passed with
  empty output. All 46 `#print axioms` checks passed; only `propext`,
  `Classical.choice`, `Quot.sound`. Source bodies match verified scratch.
- All 46 names and generated API entries unique; all three umbrella imports unique.
  Index refresh passed. `scripts/formal_tools.py lint --check-generated` reports
  only 11 unrelated unwired modules, with no own-leaf or proof-debt finding:
  `CCMApertureChainProfile`, `CCMApertureTranslationChains`,
  `CCMExponentialRampPrimeMoment`, `CCMExponentialRampSourceDissipation`,
  `CCMExponentialRampTerminalEntropy`, `CCMRetainedChainKernelLower`,
  `MoebiusMollifiedCriticalMoment`, `MoebiusMollifiedErrorThreeLines`,
  `ThetaMovingShellFirstOrderPhase`, `XiDerivRightCountLe`,
  `ZetaZeroDensityPowerSaving`.

**Exact new insight:** the stated analytic PNT inputs, even with every stretched-log
error envelope of exponent below one, admit every supercritical power in `(1/2,1)`.
Optimal scalar subtraction does not remove the corresponding power variance.
The exact positive survivor is the unique-minimizer decomposition, closed moments,
three asymptotic regimes and sharp `V/log²→0` iff `σ≤1/2` classification above.
Paper proof: dependency-closed. Lean status: fully formalized and audited.

`exists_pm_analytic_inputs_with_divergent_variance` is an unconditional existence
certificate using the exact rational exponent `3/4`. It preserves both integrals
on `(1/2,∞)` and quantifies over every centering function. No numerical experiments,
new axioms, holes, heartbeat increase, umbrella build, commit or push.

Only the inference from these analytic inputs is retired. The literal arithmetic
Möbius approximation and RH goal remain open. Follow-up:
`1-in-progress/pm-selberg-recursion-power-response.md` tests the actual Λ-weighted
recursion estimate without asserting a false prime-support identity for the model.
