# Exact power response of the actual Selberg prime-weighted floor operator

- **ID:** pm-selberg-recursion-power-response
- **Stage:** 5-failed
- **Type:** ARITHMETIC-INPUT AUDIT; POSITIVE OPERATOR CLASSIFICATION
- **Source:** Route PM; PM-27 analytic-input boundary; literal Selberg recursion
- **Status:** Coarse-input inference disproved; exact positive response survivor fully formalized and audited.
- **Scope:** Actual von Mangoldt weights, applied to explicit comparison sequences.
  No claim that the comparison sequence is the actual Chebyshev remainder.

## Question and exact corpus input

Can the already proved Selberg recursion estimate supply the missing canonical
variance bound, once added to the analytic inputs audited in PM-27?

`RHTower.abs_psiRemainder_recursion` in `PsiRemainderRecursion.lean` proves for actual `R(N)=ψ(N)−N`

`|R(N) log N + Σ_(k≤N) Λ(k) R(floor(N/k))| ≤ 400N`, `N≥1`.

`RHTower.selberg_second_inequality` in `SelbergSecondInequality.lean` further proves

`|R(N)| log²N ≤ Σ_(k≤N)(Λ(k)log k+(Λ*Λ)(k)) |R(floor(N/k))|
               +800N log N+2900N`.

Both exact statements and the first proof were inspected. The second proof retains
absolute-value and floor-error losses. Separately, the inspected chronological
prime-work balance retains signed work with no upper estimate; positivity gives a
lower bound, not the needed upper bound.

## Candidate obstruction with the same actual weights

Retain the already formalized `Pσ`, `fσ` and `Vσ` from PM-27. Put

`rσ(N)=Pσ(N)−N`, and `Tσ(N)=Σ_(k=1)^N Λ(k) floor(N/k)^σ`, `0<σ<1`.

For every integer `j≥1`, `|rσ(j)|≤j^σ`: at `j=1`, the error is `−1`; for `j>1`,
it is exactly `j^σ`. Thus the zero initial interval of PM-27 is preserved.

The proposed operator bound below implies

`|rσ(N) log N+Σ_(k≤N)Λ(k)rσ(floor(N/k))| ≤ 8N/(1−σ)`.

For the exact rational choice `σ=3/4`, this is `≤32N≤400N`. The same model already
satisfies all PM-27 analytic inputs and has divergent optimally centered canonical
variance. Hence even the literal Λ-weighted `400N` recursion inequality, by itself,
does not remove the analytic obstruction. This does not alter the definition of
actual `R`, its exact arithmetic identities, or the RH goal.

The second inequality also holds for this comparison sequence: `log²N≤64N^(1/4)`
for `N≥1`, so `|r_(3/4)(N)|log²N≤64N≤2900N`. Its convolution term and `800NlogN`
are nonnegative. Formalize this only after checking all actual weight conventions.

## Strong positive survivor: exact prime-weighted response

Set `Δσ(j)=j^σ−(j−1)^σ` for integers `j≥1`. Finite double-sum rearrangement gives

`Tσ(N)=Σ_(j=1)^N Δσ(j) ψ(N/j)`.

This uses actual von Mangoldt weights and the exact equivalence
`j≤floor(N/k) ↔ jk≤N`; no smooth replacement of the prime weights is made.
For all `N≥1`, the corpus bound `ψ(x)≤7x` and `Δσ(j)≥0` yield

`0≤Tσ(N)/N≤7 Σ_(j≥1) Δσ(j)/j = 7Sσ ≤7/(1−σ)`,

where

`Sσ := Σ_(j≥1) Δσ(j)/j = Σ_(j≥1) j^σ/[j(j+1)]`.

The equality follows by finite summation by parts and the vanishing boundary
`N^σ/(N+1)→0`. For the bound, on each `[j,j+1]`,

`j^σ/[j(j+1)] = ∫_j^(j+1) j^σ/x² dx ≤ ∫_j^(j+1) x^(σ−2) dx`.

Sum and integrate the tail to obtain `1≤Sσ≤1/(1−σ)`; strict `Sσ>1` follows from
positive increments after the first. This is symbolic analysis, not computation.

For each fixed `j`, actual PNT gives `ψ(N/j)/N→1/j`. The summable majorant
`7Δσ(j)/j` permits dominated convergence in the counting measure, extending the
finite sum by zero beyond `j=N`. Therefore

`Tσ(N)/N → Sσ`.

The local term satisfies `N^(σ−1)logN→0`. The comparison remainder differs from the
power sequence only at `j=1`, by `−2`. Its floor-convolution correction is therefore
`−2 Σ_(N/2<k≤N) Λ(k) = −2(ψ(N)−ψ(N/2))`, since all these floor quotients equal one.
Actual PNT makes this correction divided by `N` tend to `−1`. Hence the literal
signed recursion response of `rσ`, divided by `N`, tends to **the positive constant
`Sσ−1`**, not `Sσ`. Strict positivity follows from `Sσ>1` above. This exact arithmetic
response, including the non-negligible initial-cell correction, is the positive
survivor to formalize before retiring the recursion-only candidate.

For the uniform `8/(1−σ)` estimate, use `log x≤x^(1−σ)/(1−σ)` for `x≥1` and the
operator bound. For the second inequality use the same bound with exponent `1/8`
and square it: `log²x≤64x^(1/4)`.

## Corpus audit and applicability

- Deep query `Selberg recursion exact signed work Chebyshev squared error critical
  variance`: `partial=false`, no errors, complete 63,579-file inventory. All 20
  candidate and 20 source-argument statements inspected. It returned the actual
  second inequality and signed-work identities, not a critical upper estimate.
  Its proposed GHS/variance ingredient set does not discharge the missing estimate.
- Follow-up `psiRemainder recursion signed remainder --module Selberg`:
  `partial=false`, no errors, complete 63,580-file inventory; all 40 statements
  inspected. Many hits concern unrelated Selberg operators. Exact first recursion
  located by exhaustive `rg` and read directly in `PsiRemainderRecursion.lean`.
- Direct deep query `vonMangoldt power floor convolution asymptotic` completed:
  `partial=false`, no errors, 63,581-file inventory. All 20 candidate and 20
  source-argument statements plus the proposed ingredient set were inspected. No
  matching operator response was returned. A generic hyperbola-transfer query is
  following up to avoid duplicating existing summation infrastructure.
- Compiler metadata of research hits is mostly pending/stale. Applicable statements
  must be checked in the current toolchain before relying on them in Lean.

## Gates

- [x] Literal question, exact corpus inputs and comparison-vs-arithmetic scope.
- [x] Dependency-closed paper argument for the proposed obstruction and survivor.
- [x] Final novelty audit; check exact PNT, floor, summation and power APIs.
- [x] Formalize finite identity, summability, uniform bound and exact limiting response.
- [x] Formalize the same-constant recursion and second-inequality counterexample.
- [x] Targeted builds, direct actual leaves, all axioms, wiring/index/lint audits.
- [x] Record survivor status before retiring the coarse-input inference.

No actual critical variance upper bound, source positivity, or RH conclusion has
been proved. Keep the original RH goal active.

## Implementation checkpoint

- Prior card `3-formalized/ccm-fu-abel-subpower-criterion.md` already observes that
  carrying the `400N` absolute remainder through a square-root Abel transform loses
  a power, and rules out one direct Selberg contraction parameter substitution.
  The proposed exact prime-weighted response and explicit same-constant comparison
  sequence go beyond that observation; no earlier matching classification found.
- Relevant existing proof pattern: `EulerDeletionLogPrimeForcing.lean` lines128–205
  proves a private dilated-psi PNT limit and applies
  `tendsto_tsum_of_dominated_convergence` to actual ψ floor fibres with a summable
  reciprocal-square majorant. Reuse that mechanism with the power increments;
  avoid importing the large deletion-carrier dependency solely for private lemmas.
- Actual PNT source read: `ChebyshevPsiErrorInputs.tendsto_psi_div_self` (declaration
  namespace `RHTower`). Root mathlib `Real.log_le_rpow_div` located through a current
  corpus proof; exact API still to probe. `CriticalPrimeSourceSchattenIdeal` also
  proves von Mangoldt times every negative power tends to zero, but its large
  dependency is unnecessary if the standard logarithmic majorant suffices.

- Generic transfer query completed with `partial=false`, no errors, 63,583-file
  inventory; all 20 candidates and 20 source arguments inspected. Located and read
  `SelbergDelangeConvolutionTransfer.lean`: existing complex arithmetic-function
  Tannery transfer. Its required summable majorant still needs the power-increment
  proof. `DirichletSummatorySwap.sum_Icc_mul_apply` is the existing finite hyperbola
  identity; preserve and reuse it.
- New series scratch `/tmp/pm_increment_series_1007.lean` is checking the increment
  majorant, summability, exact finite summation-by-parts identity and equality of
  the two response series. No new source-tree Lean yet for this card.
- A shorter paper proof of the same majorant uses Bernoulli concavity:
  `(x+1)^σ≤x^σ+σx^(σ−1)`, hence
  `((x+1)^σ−x^σ)/(x+1)≤σ/(1−σ)[x^(σ−1)−(x+1)^(σ−1)]` for `x≥1`.
  Telescoping after the first increment gives `Sσ≤1/(1−σ)`. This proves exactly
  the previously recorded bound with no new hypothesis or numerical check.
- All 24 owned completed `1006` scratch/search/audit files cleaned; no jobs remain
  for that suffix. Current scratch uses `1007`.

- Scratch API correction: Bernoulli lemma is root `rpow_one_add_le_one_add_mul_self`, not in namespace `Real`; exact signature verified by use. Series scratch is still under verification, with no source-tree promotion.

- Series scratch now passes Lean with no output, including strict `1<Sσ`, exact
  equality of response series and `Sσ≤1/(1−σ)`. Created
  `PMPowerIncrementSeries.lean`; targeted build running, final audits pending.
- Drafted `/tmp/pm_prime_floor_1007.lean` for literal finite hyperbola identity,
  uniform operator bound and actual PNT/Tannery response limit. Not checked yet.

- **Paper correction during implementation:** the old line `−2Λ(N)` confused an
  exact-divisor fibre with a floor fibre. The actual correction is the full
  half-interval prime mass `−2(ψ(N)−ψ(N/2))`. Thus the comparison remainder's
  normalized signed response is `Sσ−1>0`; the raw power operator still has limit
  `Sσ`. The uniform bounds, same-constant inequalities and variance obstruction are
  unchanged. No false statement was added to source-tree Lean.

- `PMPowerIncrementSeries` targeted build passed in 5.6 seconds.
- Prime-floor scratch passed Lean with no output: exact finite hyperbola identity,
  uniform `Tσ(N)/N≤7/(1−σ)`, dilated actual-ψ PNT, and exact `Tσ(N)/N→Sσ`.
  Created `PMPrimeFloorPowerResponse.lean`; build running, final audits pending.
- `/tmp/pm_selberg_comparison_1007.lean` drafted for the corrected half-interval
  response, `32N≤400N` comparison bound, and exact positive limit `Sσ−1`.
  Not checked yet. Second inequality and final packaging still to implement.

- `PMPrimeFloorPowerResponse` targeted old-mode build passed (34 seconds; only this owned leaf built, cached dependency messages replayed). Comparison scratch now includes both Selberg inequalities and unconditional divergence packaging; checking in Lean.

- The corrected comparison scratch retains the literal model's zero interval and
  actual Λ weights. The proof target uses the corpus's unchanged constants
  `400`, `800`, `2900`; it does not introduce a larger error allowance.

- All comparison scratch declarations now pass Lean with empty diagnostics. New
  `PMSelbergPowerInputBoundary.lean` contains the corrected exact half-interval
  identity, positive `Sσ−1` limit, both unchanged-constant inequalities, and
  unconditional divergence packaging. Its targeted old-mode build is running.
- All three new leaves are wired and indexed: 45 declarations / 541 lines.
  Exhaustive name audit and API/import uniqueness checks passed.
  `lint --check-generated` reports only 10 unrelated unwired modules; final
  actual-leaf and all-axiom audits are pending the last build.
- Stronger conjecture exposed by the affine response law is recorded separately
  in `pm-selberg-sublinear-response-boundary.md`. Its cancelling amplitude is
  `1/(2Sσ−1)`, retaining the unchanged zero initial interval. Do not retire that
  stronger inference before its paper/corpus/Lean audits.

- Third targeted build passed: `PMSelbergPowerInputBoundary` built in 444s;
  only the owned leaf rebuilt, cached dependency messages replayed.
- Final direct `lake env lean` checks passed for `PMPowerIncrementSeries` and
  `PMPrimeFloorPowerResponse`, both with empty diagnostics. Final third-leaf
  check is running; 45-declaration axiom audit remains queued.

- Third final direct actual-leaf audit passed with empty diagnostics. All three
  source bodies exactly match their passing scratch declarations. The complete
  45-declaration `#print axioms` audit is now running in `/tmp`.

## Final formal certificate — PM-28

The retired inference is that the listed analytic inputs plus the two coarse
Selberg inequalities force the canonical variance budget. The explicit model
proves that inference false. Actual Chebyshev arithmetic and RH remain open.

The strongest positive survivor is the exact literal prime-weighted response:
finite hyperbola law, summable positive response series and its bounds, actual
PNT/Tannery limit, full initial-cell floor-fibre correction, and the positive
normalized remainder response `Sσ−1`. These statements have both dependency-
closed paper proofs and complete Lean verification.

- `PMPowerIncrementSeries.lean`: 161 lines / 17 declarations.
- `PMPrimeFloorPowerResponse.lean`: 169 lines / 14 declarations.
- `PMSelbergPowerInputBoundary.lean`: 211 lines / 14 declarations.
- Three targeted old-mode builds passed (5.6s, 34s, 444s). Only owned leaves
  rebuilt; cached dependency diagnostics replayed.
- Three final direct actual-leaf `lake env lean` audits passed with empty output.
- All 45 declaration axiom reports checked, including definitions and every
  supporting theorem: only `propext`, `Classical.choice`, `Quot.sound`.
- All source bodies match passing scratch; all names/API entries/imports unique.
- Index regenerated. `lint --check-generated` exits 1 solely for these 10
  unrelated unwired modules: `CCMApertureChainProfile`,
  `CCMApertureTranslationChains`, `CCMExponentialRampPrimeMoment`,
  `CCMExponentialRampSourceDissipation`, `CCMExponentialRampTerminalEntropy`,
  `CCMRetainedChainKernelLower`, `MoebiusMollifiedCriticalMoment`,
  `MoebiusMollifiedErrorThreeLines`, `ThetaMovingShellFirstOrderPhase`,
  `ZetaZeroDensityPowerSaving`. No own-leaf, proof-debt or stale-index finding.

No full/umbrella build, numerical experiment, hole, new axiom, heartbeat change,
commit or push. Next inference is separately tracked in
`1-in-progress/pm-selberg-sublinear-response-boundary.md`; it is not retired here.

All 20 owned completed `1007` scratch/search/audit files cleaned; no `1007` jobs
remain. Active work uses `1008`.
