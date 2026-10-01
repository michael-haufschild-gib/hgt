# Sublinear Selberg response and the surviving power variance

- **ID:** pm-selberg-sublinear-response-boundary
- **Stage:** 5-failed
- **Type:** DISPROVED INPUT INFERENCE; PROVED EXACT RESPONSE CLASSIFICATION
- **Source:** Route PM, PM-28 exact prime-weighted response.
- **Scope:** Actual prime weights applied to comparison sequences; no replacement
  of the actual Chebyshev function in an arithmetic identity.

## Question

Does strengthening the coarse Selberg residual from `O(N)` to `o(N)` eliminate
the supercritical power comparison family? PM-28 exposes a tunable linear
response. Audit this stronger inference before pursuing it as a source estimate.

## Dependency-closed paper argument to check

For `0<σ<1`, retain the proved response series `Sσ>1`. For `c>0`, define

`P_(σ,c)(x)=0` for `x≤1`, and `x+c x^σ` for `x>1`.

This is nonnegative and monotone on the nonnegative axis, has PNT normalization,
and retains the finite initial zero interval. Its integer remainder is

`r_(σ,c)(N)=c N^σ−(1+c)·1_(N=1)`.

The exact actual-prime floor sum is

`ΣΛ(k)r_(σ,c)(floor(N/k))
 = c Tσ(N)−(1+c)[ψ(N)−ψ(floor(N/2))]`.

Thus the normalized signed Selberg residual tends to

`c Sσ−(1+c)/2 = c(Sσ−1/2)−1/2`.

The unique positive amplitude with zero limit is therefore

`cσ=1/(2Sσ−1)`.

This arithmetic check must use the full floor fibre at one. In PM-28 the
coefficient is `−2`, whose normalized response is `−1`; replacing the amplitude
changes that coefficient to `−(1+c)`, not to `−2c`. Since `Sσ>1`, `0<cσ<1`.
Consequently all previous analytic bounds with upper amplitude one survive.

For `σ>1/2`, every scalar-centered canonical variance still diverges after
division by `log²R`. Put `f_c=P_(σ,c)/x` and `f=Pσ/x`. Then

`f_c = c f + (1-c)·1_(x>1)`.

For arbitrary `B(R)`, let `B'(R)=(B(R)-1+c)/c`. The errors obey

`c(B'−f) = (B−f_c) − (1-c)·1_(x≤1)`.

On `(0,R)`, `R≥1`, integration of `(u+v)²≤2u²+2v²` gives

`c² ∫(B'−f)² ≤ 2∫(B−f_c)² + 2(1-c)²`.

PM-27 gives divergence on the left after dividing by `log²R`; the bounded
initial-cell term vanishes. Hence the rescaled model retains the obstruction
while its literal signed Selberg residual is `o(N)`.

The same `400`, `800`, `2900` inequalities remain available because `0<cσ<1`
and `|r_(σ,cσ)(N)|≤N^σ` for `N≥1`; at `N=1` the remainder remains `−1`.

## Positive survivor and audit gates

The survivor is the exact affine response law, its unique positive cancelling
amplitude, and stability of supercritical variance under this rescaling and
finite initial-cell correction. These are paper claims pending independent
algebra, corpus and Lean audits; no new code yet.

- [x] Record literal definitions, exact floor-fibre correction and paper proof.
- [x] Complete corpus search and compare returned statements; no exact match found.
- [x] Verify amplitude, continuous model and variance-transfer identities in Lean.
- [x] Prove unconditional explicit sublinear-residual/variance counterexample.
- [x] Targeted builds, direct actual-leaf, axiom, wiring, index and lint audits.
- [x] Record the positive survivor before retiring the stronger inference.

No conclusion about actual Chebyshev variance or RH follows. Exact arithmetic
self-consistency of the error with its prime weights is absent from comparison
models and must remain explicit in subsequent source work.

## Search checkpoint

Direct deep query `Selberg floor power response finite initial correction
sublinear signed residual` is running, budget 300 seconds. Results have not yet
been inspected. Prior instantaneous-energy search was complete: all 20 candidate
and 20 source statements reviewed; proposed half-power ingredient assumed RH or
a power-spectrum premise. The returned uniform Euler-force coefficient energy
bound is logarithmic but explicitly leaves signed time-domain reconstruction
uncontrolled. Its whole 120-line source was read; it does not close PM variance.

- Search completed: `partial=false`, errors empty, complete 63,600-file inventory.
  All 20 candidate and 20 source-argument statements read. Results mainly concern
  Selberg sieves or unrelated residuals; their proposed radial-minimization
  ingredient does not apply. No matching affine power-response classification
  occurred in these hits. Exact scope remains provisional; source proof uses the
  audited PM-28 identities, not an inferred theorem from these search results.
- Paper algebra rechecked: the limiting correction is `(1+c)/2`; hence the
  cancelling amplitude is `1/(2Sσ−1)`. It is strictly below one because `Sσ>1`.
  The fixed-unit-cell error in the variance transfer is independent of `B(R)`.

- Draft `/tmp/pm_scaled_model_1008.lean` records the continuous rescaling, global
  positivity/monotonicity, PNT normalization, preserved error envelope, finite
  initial-cell variance transfer, and unique cancelling amplitude. Not compiled;
  PM-28 final audits currently hold the single foreground Lean slot.
- Additional actual-source audit located and read
  `CCMFUSuzukiSecondGradeAsymptotic.tendsto_vonMangoldt_selfConv_summatory_sub_polar_div`:
  `Σ_(n≤N)(Λ*Λ)(n)=N(log N−1−2γ)+o(N)` is already formalized. Also read
  `MertensVonMangoldtEulerConstant.tendsto_real_sum_vonMangoldt_div_sub_log`
  and `MobiusDivisorLatePrimeHeadAsymptotic.tendsto_psiDefect_mul_log_div`.
  These constants matter: the unshifted actual remainder's Selberg response is
  expected to have limit `−2γ`, not zero. The current `o(N)` test is hypothetical
  comparison-input strengthening; it is not asserted for the actual unshifted
  remainder. A direct corpus query for that exact response is running.

- Draft `/tmp/pm_scaled_response_1008.lean` adds exact affine floor response,
  uniqueness of the sublinear amplitude, both unchanged-constant inequalities,
  and an unconditional existential divergence capstone. It imports the planned
  `PMScaledPowerVariance` leaf, which does not yet exist: do not compile this
  second scratch until the first scratch passes and that leaf has been built.
  Both drafts remain unverified.

- Actual-response query completed with partial results: complete 63,602-file
  inventory, but Qdrant timed out, the local judge returned malformed JSON and
  the deadline prevented later queries. All 20 candidate and 20 source statements
  reviewed. Available hits do not supply a direct normalized-response limit.
  Use the already inspected second-grade asymptotic and exact constants; do not
  infer absence of a theorem from this partial search.

- PM-28 is now fully audited and retired only as a coarse-input inference; all
  20 completed `1007` files cleaned. Its final certificate is in Stage 5.
- First PM-29 model scratch reported local API/rewrite issues: generic probe
  universe levels, indicator membership simplification, triangle-inequality
  signature, finite-measure argument, pointwise function addition, and a rewrite
  entering the centering scalar inside an integral. All were corrected in the
  scratch; second check running. No mathematical counterexample found, no
  source-tree promotion, no heartbeat or tactic-depth increase.

- First scratch now passes with empty diagnostics. Created the 232-line,
  21-declaration leaf `PMScaledPowerVariance.lean`; targeted old-mode build
  passed in 11s. The second prime-response scratch is now checking against it.
  Final actual-leaf and axiom audits remain pending.

- Second scratch initially reported only a natural-to-real cast rewrite in the
  limiting constant and a definitional mismatch in the second-inequality bound.
  Both corrected; second check running. Exact affine response, uniqueness and
  divergence packaging have no reported mathematical obstruction.

- Second scratch passed empty. Created `PMSelbergSublinearPowerBoundary.lean`
  (155 lines / 11 declarations); targeted old-mode build passed in 12s.
- Two leaves / 32 declarations / 387 lines are wired and indexed. First final
  direct actual-leaf check passed empty; second running; all-axiom audit queued.
- `lint --check-generated` reports only 11 unrelated unwired modules, including
  newly concurrent `WeilConeMultiplesOfPrimeLaw`; no own or stale-index finding.
- Next source obligation now has a dedicated card:
  `pm-log-mobius-boundary-multiplicity.md`. Its simplicity implication is
  conjectural and has no new Lean implementation.

- Both final direct actual-leaf checks passed with empty diagnostics. Every
  name/API entry and both imports are unique; both source bodies match passing
  scratch. All 32 axiom checks are now running in `/tmp`.

## Final formal certificate — PM-29

The hypothetical inference from a sublinear signed Selberg response to the
canonical variance budget is false, even for the retained monotone power family
and literal prime weights. This is not a claim that the actual unshifted
Chebyshev remainder has sublinear response. Its arithmetic constants remain
separate, as recorded above.

The strongest positive survivor is the exact affine response law, its unique
cancelling amplitude `cσ=1/(2Sσ−1)` with `0<cσ<1`, and the quantitative
finite-cell variance comparison valid for every scalar centering. Both original
Selberg inequalities retain their unchanged constants for the explicit
`σ=3/4` cancelling model. The unconditional existential capstone has no
RH, simplicity, prime-cancellation or other hypothesis parameter.

- `PMScaledPowerVariance.lean`: 232 lines / 21 declarations.
- `PMSelbergSublinearPowerBoundary.lean`: 155 lines / 11 declarations.
- Both old-mode targeted builds passed (11s, 12s); only owned leaves rebuilt.
- Both final direct actual-leaf `lake env lean` checks passed empty.
- All 32 declaration axiom reports checked; only `propext`, `Classical.choice`,
  `Quot.sound`. Both source bodies match their passing scratch.
- All 32 names/API entries and both imports unique; index regenerated.
- `lint --check-generated` exits 1 solely for 11 unrelated unwired modules:
  `CCMApertureChainProfile`, `CCMApertureTranslationChains`,
  `CCMExponentialRampPrimeMoment`, `CCMExponentialRampSourceDissipation`,
  `CCMExponentialRampTerminalEntropy`, `CCMRetainedChainKernelLower`,
  `MoebiusMollifiedCriticalMoment`, `MoebiusMollifiedErrorThreeLines`,
  `ThetaMovingShellFirstOrderPhase`, `WeilConeMultiplesOfPrimeLaw`,
  `ZetaZeroDensityPowerSaving`. No own-leaf, proof-debt or stale-index finding.

Positive survivor has a dependency-closed paper proof and complete Lean audit.
No full/umbrella build, numerical experiment, added axiom, hole, heartbeat
increase, commit or push. Next source task:
`3-formalized/pm-log-mobius-boundary-multiplicity.md`. Its necessary simplicity
implication is now audited in Lean. Actual critical variance and unconditional
RH remain open.

Cleanup complete: all 21 owned `1008` scratch, research and audit files removed;
all associated processes finished. Active `1009` work retained separately.
