# Suzuki critical ordered Jordan cancellation

Status: `[FORMALIZED]` 2026-08-31; corpus/literature/falsity audits, dependency-closed paper proof,
and unconditional Lean proof passed.

## Exact RH proof chain

Exact signed Suzuki prime--archimedean curvature cells
→ floor-selected affine checkpoint current
→ bounded CCM-FU Suzuki checkpoint mixture
→ `riemannHypothesis_of_ccmFUSuzukiCheckpointAffineMixtureBound`
→ RH.

This theorem kills the shortcut that replaces the affine-current burden by scalar convergence of
the exact source after critical half-order damping. Scalar convergence already holds
unconditionally; RH-bearing content remains in uniform affine checkpoint cancellation before
scalarization.

## `[CORPUS]` frontier

- `suzukiCheckpointSignedCurvatureCell` is the literal cell
  `I_k - Λ(k)/sqrt(k)` at endpoint `k=N+1`.
- `abs_weighted_suzukiCheckpointSelbergArchRemainderCell_le` bounds the exact Gamma-cell defect
  `k(I_k-1/sqrt(k))` by `O((k-1)^(-1/2))`.
- `tendsto_sum_vonMangoldt_div_sub_log` proves Mertens' second theorem with exact constant `-γ`.
- `Real.tendsto_harmonic_sub_log` gives the matching harmonic constant `γ`.
- `summable_suzukiCheckpointSignedCurvatureJordan_powerDamping_iff` puts both Jordan sectors at
  exact abscissa `1/2`.
- Corpus search found no natural-order half-damped signed-curvature limit or conditional Jordan
  classification.

## `[PROVED HERE]` theorem

For `n≥0`, put `k=n+3`, let

`I_k = ∫_[log(k-1),log k] screwRegularKernel(t)dt`,

and define

`d_n = k^(-1/2)(I_k-k^(-1/2))`,

`c_n^crit = k^(-1/2)c_(k-1)`,

`C_N = sum_(0≤n<N) c_n^crit`.

Then `sum_n |d_n|<∞` and

`C_N → κ := sum_n d_n + 2γ - 3/2 + (log 2)/2`.

Nevertheless the critical signed family is not unconditionally summable, and each exact Jordan
sector has infinite critical mass:

`not Summable (N ↦ (N+1)^(-1/2)c_N)`,

`not Summable (N ↦ (N+1)^(-1/2)c_N^+)`,

`not Summable (N ↦ (N+1)^(-1/2)c_N^-)`.

Thus exact critical curvature has a canonical checkpoint-ordered Mertens--Gamma finite part but no
finite Jordan variation.

## Dependency-closed paper proof

### 1. Absolute Gamma correction

The corpus estimate gives, for `k≥3`,

`|k(I_k-k^(-1/2))| ≤ (5/3)(k-1)^(-1/2)`.

Since `sqrt(k-1)≥1`,

`|k(I_k-k^(-1/2))| ≤ 5/3`.

Dividing by `k sqrt(k)` yields

`|d_(k-3)| ≤ (5/3)k^(-3/2)`.

The shifted `3/2`-series converges, so `sum_n |d_n|<∞`.

### 2. Exact finite-prefix identity

For every `k≥3`, finite algebra inside the literal cell gives

`k^(-1/2)c_(k-1) = d_(k-3) + 1/k - Λ(k)/k`.

No infinite prime and archimedean series is separated here. Summing only finite prefixes with
`X=N+2` gives

`C_N = D_N + (H_X-log X) - (M_X-log X) - H_2 + M_2`,

where

`D_N=sum_(n<N)d_n`,

`M_X=sum_(1≤k≤X)Λ(k)/k`.

The omitted cells are retained exactly: `H_2=3/2` and `M_2=(log 2)/2`.

### 3. Ordered limit

Absolute summability gives `D_N→sum_n d_n`. Euler--Mascheroni convergence gives
`H_X-log X→γ`. Mertens' second theorem gives `M_X-log X→-γ`. Therefore

`C_N → sum_n d_n + γ - (-γ) - 3/2 + (log 2)/2 = κ`.

### 4. Failure of unconditional and Jordan summability

The exact Jordan-abscissa theorem already proves non-summability of both positive and negative
critical sectors. If the signed family were Lean `Summable`, its absolute-value family would be
summable. Since the nonnegative critical positive sector is pointwise bounded by that absolute
family, comparison would make the positive sector summable, contradiction. Finite deletion of the
first two cells transports the same obstruction to the canonical ordered tail.

## Hostile proof audit

- Indexing is source-exact: ordered term `n` is cell `N=n+2` and endpoint `k=n+3`; prefix endpoint
  is `X=N+2`.
- No rearrangement is used. Prime--archimedean cancellation occurs only after a finite cellwise
  identity and finite summation.
- Constants from deleting endpoints `1,2` are explicit, not absorbed into an unspecified constant.
- Natural-order `Tendsto` is kept distinct from Lean `Summable`, which is unconditional for real
  families.
- Both Jordan divergences are source theorems at the exact critical exponent, not consequences of
  a surrogate sign model.
- Proof uses no RH premise, zero-free hypothesis, added axiom, computation, or numerical estimate.

Verdict: `DEPENDENCY-CLOSED PAPER PROOF`.

## Novelty audit

Suzuki's screw-function papers and later finite-aperture work do not define this discrete critical
Jordan series or state its exact Mertens--Gamma ordered limit. Searches for Mertens, curvature,
Jordan decomposition, and the exact `Λ(k)/k` checkpoint cancellation found no matching theorem:

- https://arxiv.org/abs/2206.03682
- https://arxiv.org/abs/2209.04658
- https://arxiv.org/abs/2409.00888
- https://arxiv.org/abs/2606.09096

Verdict: `[CANDIDATE NEW SCIENTIFIC KNOWLEDGE]` pending external peer review.

## Route-class no-go and positive survivor

- **Exact killing theorem/mechanism:** critical scalar checkpoint convergence is unconditional, so
  its existence cannot discharge any RH premise.
- **Strongest positive survivor:** exact canonical Mertens--Gamma finite part `κ` inside a source
  with infinite positive and negative Jordan mass.
- **New insight:** scalarization erases the remaining RH information. A surviving CCM-FU/SP-E
  construction must control the floor-selected affine current uniformly before scalarization.
- **Status:** paper proof dependency-closed; exact survivor formalized in Lean.

## Lean closure

Module:

`formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiCriticalOrderedJordanCancellation.lean`

Unconditional public results:

- `summable_suzukiCheckpointCriticalArchCorrection`: exact Gamma correction is absolutely
  summable.
- `suzukiCheckpointCriticalOrderedTerm_eq`: cellwise harmonic-minus-Mertens decomposition.
- `suzukiCheckpointCriticalOrderedPrefix_eq_centered`: exact finite-prefix identity with deleted
  endpoint constants.
- `tendsto_suzukiCheckpointCriticalOrderedPrefix`: explicit checkpoint-order limit `κ`.
- `not_summable_suzukiCheckpointCriticalSignedCurvature`: full critical signed family is not
  unconditional.
- `suzukiCheckpointCriticalOrderedJordanCancellation`: closed convergence/non-summability/Jordan
  capstone killing the scalar route.

Verification:

- `lake env lean GaloisForLFunctions/RHTower/Suzuki/SuzukiCriticalOrderedJordanCancellation.lean`
  passed.
- `lake build GaloisForLFunctions.RHTower.Suzuki.SuzukiCriticalOrderedJordanCancellation` passed.
- Capstone and major-premise axiom audits report only `propext`, `Classical.choice`, and
  `Quot.sound`.
- Formal lint finds no forbidden declaration or reachability issue in this module. Repository-wide
  lint remains red only on unrelated concurrently unwired modules listed by the audit.
