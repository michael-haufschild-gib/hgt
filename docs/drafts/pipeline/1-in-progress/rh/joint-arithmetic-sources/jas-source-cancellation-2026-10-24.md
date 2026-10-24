# JAS: source cancellation at the power budget

- **ID:** jas-source-cancellation-2026-10-24
- **Stage:** 1-in-progress
- **Type:** CONJECTURE research
- **Source:** `docs/reports/rh-current-frontier-map.md`, JAS; `rh-killed-routes.md`.
- **Statement:** Prove the literal arithmetic JAS source estimate needed for
  level-one positivity or the square-shell finite-power bound, without adding
  an analytic premise.

## Goal and gates

The requested endpoint is an unconditional Lean proof of RH. A new receiver,
numerical improvement, negative result, or conditional wrapper does not meet
that endpoint or the requested intermediate contribution.

- [x] Inspect current route, exact Lean receivers, source formulas, prior failures.
- [ ] Obtain a dependency-closed paper proof of an actual source estimate that
  removes a significant JAS obstacle.
- [ ] Formalize that proof; check canonical leaf with `lake --old env lean`;
  inspect transitive axioms; wire its umbrella without building the umbrella.
- [ ] Establish the full unconditional RH theorem.

External searches and novelty checks are excluded by the user. No external
novelty claim is made. No numerical experiments are authorized.

## Exact open target

For `P_m = {p prime : m² < p ≤ 2m²}`, put

`U_m(s) = Σ_{p∈P_m} p^(s−3/2)`,
`V_m(s) = U_m(s)/(s+1)²`, and
`D(m,k) = jasShellRieszSum (m²) k`.

The existing arithmetic identity is

`D(m,k) = Σ_ρ V_m(ρ)^k/[ρ(1−ρ)]`, for `k≥1`.

The required arithmetic assertion is: for every `ε>0`, infinitely many `m`
satisfy `|D(m,k)|≤m^(εk)` for every natural
`m<k≤m+m/log(m+1)`. The established theorem
`riemannHypothesis_iff_squareShellRiesz_finitePowerWindow` identifies this with
RH. It does not prove the inequality.

The alternative is actual level-one prime-product Weil positivity at the
power-sized prime budget. `JointAncestryEndpointBudgetProducer` proves only the
coupled logarithmic budget. `JointAncestryLevelOneDensity*` constructs the full
signed density and its finite conditional expectations, but not nonnegativity.

## Evidence and research direction

Read the JAS sections of both route ledgers, the exact square-shell, damped-shell
and level-one capstones, the Riesz integral source, the endpoint budget proof,
the prior exceptional-alignment investigation, and the producer-conjecture
sweep. Corpus searches were run before inspecting possible mathlib machinery.

Existing obstructions rule out treating L² admission, small prime budgets,
typical phases, flat creation, or reversible sewing as a sign proof. In
particular, replacing complete mixed amplitudes by pure moments is invalid
unless using the separately proved pure-moment RH receiver above.

Current investigation: retain the signed prime-minus-polar source inside the
Riesz averaging and inspect exact arithmetic energy identities for a mechanism
that pays the complete exceptional alignment. The first candidate lead is
`PrimeSamplingMeanSquareIdentity.sum_vonMangoldt_mul_lagPrimeSide_eq`.

`[OPEN CORE]`: no estimate currently bounds the full signed Riesz sum at every
positive power exponent, and no source-derived positivity-preserving prime
insertion law has been proved.

## Status

Research active. No new theorem, qualifying source estimate, or RH proof yet.
Existing unrelated working-tree changes are preserved.

## First source-level investigation

### Prime-sampled energy

The exact existing identity was read in Lean, including its endpoint and
integrability proofs. With `E(t)=ψ(t)−t`,
`J(t)=ψ(t)/t+log t−γ−1−Σ_{n≤t}Λ(n)/n`, and
`H(t)=E(t)J(t)/√t−√t J(t)²/4`, it states

`Σ_{n≤X} Λ(n)J(n)/√n = H(X)−H(1)
  + ∫₁ˣ [J(t)/√t+J(t)²/(8√t)+E(t)²/(t²√t)] dt`.

The last two terms are nonnegative. Dropping them gives only the already
formalized one-sided inequality. It does not bound the signed linear integral
or the terminal expression `H(X)`. It also does not identify the repeated
prime-product/Riesz average with this single prime-weighted sum. A proposed
iteration must prove that transfer and pay its boundary terms; neither step
has been supplied. Verdict: **BRIDGE, not a source estimate**.

### What the exact smoothing actually does

For the arithmetic function
`f(u)=exp(−u/2) lagPrimeSideExt(exp u)`, define, at a fixed shell `N`,

`T_N f(x)=Σ_{N<p≤2N} (1/p) ∫₀∞ t exp(−3t/2) f(x+log p−t) dt`.

Substitution in the existing order-`2k` Riesz formula yields the candidate
operator identity `D(N,k)=T_N^k f(0)` for `k≥1`. The convolution kernel for `k` steps is
`t^(2k−1)exp(−3t/2)/(2k−1)!`; its mass is `(4/9)^k`.
The identity needs a written Fubini/convolution justification before it is a
formalization target; no new theorem is claimed here.

This representation explains precisely why a small kernel mass is insufficient:
the operator translates by `log p`. On `f(u)=exp(a u)` its multiplier is

`[Σ_{N<p≤2N}p^(a−1)]/(a+3/2)²`.

For the zero mode `a=ρ−1/2`, this is exactly the existing damped amplitude
`V_ρ(N)`. Thus the fixed Riesz denominator cannot by itself erase a positive
horizontal exponent. Bounding `f` before applying the contraction would insert
the missing critical estimate. Replacing the order `2k` by an order growing
like `k log N` changes the receiver and has not been justified.

This is a diagnostic for the ongoing attempt, not a new criterion or a result
credited toward RH. The positive kernel remains a way to retain signed source
cancellation, rather than replace it by an absolute majorant.

### Gamma--theta alternative

Read `GammaThetaFullSupportSource` and `GammaThetaFullSupportCreation` in full.
They admit all formation parameters, phases and actual grades; their exact
insertion identity already gives the occupied-support preimage by division by
a nonzero prime amplitude. That algebra does not establish reflection
transport or a prime-Poisson intertwiner.

The prior `JointAncestryGammaThetaDivisorGaugeTrivialization` and the
separate-normalization/reflection-prefix cards explain why a diagonal reversal
is inadequate: the support dependence is a coboundary, and uniformly
conditioned reflected diagonal prefixes hold only at the critical line. The
corpus search also returned the precise inverse-source/square-zero-target
landing obstruction. No additional creator lemma would resolve the current
source sign. Verdict: **existing construction, unresolved arithmetic landing**.

### Conditional prime insertion

The existing `riemannHypothesis_iff_ae_re_jasLevelOneDensity_nonneg` was read
through its proof. Its conditional-expectation argument explicitly starts from
nonnegative full density; its positive integral is only the scalar mean.
Neither result proves nonnegative conditional coefficients.

For a finite head `P` and a fresh prime `p`, a positive Toeplitz law for the
conditional `p`-Fourier coefficients would preserve the sign through insertion.
The missing assertion is that law for the **actual** prime–Gamma–polar source,
including coefficients where the head density vanishes. The earlier
exceptional-alignment card already isolates this target. Restating it or
assuming it is not progress.

## Continuation target and assessment

Continue with the exact arithmetic action of `T_N` on the compensated
prime-minus-polar source. Test whether multiplicative identities for `Λ`
produce a coercive signed recurrence for the *complete* iterates. A valid
derivation must retain the cutoff `n≤(p₁⋯p_k)exp(−t)` in `lagPrimeSide`;
replacing it by the divisibility relation `n | p₁⋯p_k` would be invalid.

The hard sign estimate was investigated directly; no route was retired and no
weaker theorem was substituted for the requested contribution. No closed paper
proof exists to formalize. The current batch therefore establishes **no
qualifying mathematical advance**. No Lean source was added, and no compilation
or axiom audit is claimed. The full goal stays active.

## Continuation after the complete Suzuki first variation

The complete compact-source Suzuki first variation and its application to the
APT critical family are certified separately in
`../../../3-formalized/sz-complete-source-first-variation-assembly-2026-10-24.md`.
They are established inputs, not new progress credited to this continuation.

### Attempt: use APT positivity on the JAS Euler tests

Read `CompactCriticalSourceWeilPositivity` and `JointAncestryWeilEulerBridge`
at their literal definitions. The compact APT sources are collared combinations
of factorial frequency differences in `v = exp(-x)`. The JAS source is the
infinite Euler vector `m ↦ e_w(m) m^(-σ)` on the positive `P`-smooth integers,
where `e_w(m) = ∏_{p∈P} w_p^(v_p(m))`. At the required level, `σ = 1`.

Block positivity for the former does not identify the latter as a source in
that block. Nor does it control the mixed terms of a proposed decomposition
across blocks. APT's own receiver analysis identifies the growing `log M`
archimedean gain as the reason its positive family does not yet pay the
critical prime–polar estimate. No containment, complete-form approximation
with a uniform lower bound, or mixed-term estimate was established here.
Verdict: **existing positive family, unpaid transfer**.

### Attempt: close the source recurrence by Selberg cancellation

The search also found and the source inspection verified
`criticalSecondGradeSignedRieszMass_eq_selbergPrefixDiscrepancy` and
`tendsto_normalized_criticalSecondGradeSignedRieszMass` in
`CCMFUSuzukiCriticalChordMeasure`. These already pair the second-grade
`Λ * Λ` prefix with its exact polar counterterm
`X (log X - 1 - 2γ)`, then transport the signed discrepancy by the square-root
Riesz mesh. The normalized cancellation theorem is already available.

This is not the shell functional `D(m,k)`: its arithmetic coefficient is
`Λ * Λ`, whereas the JAS expression samples `lagPrimeSideExt` at products of
shell primes after an order-`2k` integral. No identity or estimate transferring
the existing normalized discrepancy to the required finite power window was
found. In particular, fixed-grade relative cancellation does not establish
the required estimate for powers growing with `m`.
Verdict: **existing signed cancellation, unpaid uniform power window**.

### Attempt: use positive finite prime covariance

`RHTower.RoutePWindow.covariance_insert` in `RoutePFinitePrimeCovariance`
gives an exact insertion rule for a sum of cofactor squares, with nonnegative
occupation weights. Its finite-horizon comparison retains a product of causal
recovery costs. Read the definition and insertion proof: they concern that
square covariance, not the actual JAS Weil aggregate. Identifying the latter
with this positive covariance would itself require the missing signed
prime–Gamma–polar identity; no such identity was proved. This does not replace
the conditional Toeplitz input recorded above.

### Assessment

This continuation produced no qualifying new mathematical theorem. It did
not improve the JAS power budget or discharge its source sign. No Lean file,
compilation, or axiom audit is claimed for this batch. No route is retired.
Research stays directed at the literal signed arithmetic estimate, retaining
the boundary terms, the linear term, and the mixed shifted terms of any
attempted iteration. External novelty checks and numerical experiments were
not run, as requested.
