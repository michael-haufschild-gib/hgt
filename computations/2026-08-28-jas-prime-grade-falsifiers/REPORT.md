# JAS prime–grade falsifier computations (2026-08-28)

## Purpose and provenance

Exploratory computation only: results select or retire research mechanisms and are never evidence in a Lean proof. Objects were transcribed from corpus definitions, not fitted:

- synchronized Gamma–LCM weights and insertion gains: `GammaSewnSynchronizedLcmContraction.lean`;
- positive Gamma multiplier and its fourth-power law: `GammaSewnMobiusValuationContraction.lean`;
- completed theta source and reflection: `ThetaCuspFinitePrimeSource.lean`, `ThetaCuspReflection.lean`;
- exact prime-Poisson character moments: `PrimePoissonProductState.lean`;
- bilateral sewing recurrence: `BilateralPrimeAnglePacketSewing.lean`.

Reproducer: `run_experiments.py`. Raw data: `results.json` (SHA-256 `0664b7b1b118f4ef0a08fdf852056615a023028e0e67dd16b63fd74b3f95fb19`). Full run used Python 3.12.3, NumPy 2.5.2, SciPy 1.16.1, mpmath 1.3.0, 80-decimal theta quadrature, 64 processes on 128 cores. Controls are included in raw data.

## Outcomes

### 1. Finite support-grade `*`-intertwiner search

On the Boolean support space for first `d=2,…,5` primes, define weighted insertion

`F_p(x)|P⟩ = W_x(P∪{p})/W_x(P) |P∪{p}⟩`.

For each aperture pair, linear systems imposed both `V F_p(x)=F_p(y)V` and `V F_p(x)^*=F_p(y)^*V` for every prime. Creation equations alone always had nullity `2^d`, confirming flat-cocycle similarity. Adding adjoints gave:

| aperture pair | `*`-intertwiner nullity for every `d=2,…,5` | smallest relative Gram eigenvalue at `d=5` |
|---|---:|---:|
| `0.5 → 0.5` (control) | 1 | numerical zero |
| `0.25 → 0.25` (control) | 1 | numerical zero |
| `0.25 → 0.75` | 0 | `1.028e-2` |
| `0.4 → 0.6` | 0 | `1.742e-3` |
| `0.5 → 1.0` | 0 | `5.176e-3` |

Independent direct SVD at `d=4` reproduced nullity `1` for `0.5→0.5` and nullity `0` for `0.4→0.6`; latter smallest singular value was `0.0388721`.

**Consequence.** Retire JAS mechanism “flat Gamma insertion cocycle integrates to unitary/`*` aperture sewing.” Flatness supplies nonunitary diagonal similarity only. Surviving sewing must add a defect/environment, change inner product, or abandon adjoint compatibility. Formal target suggested by data: classify actual finite support representations up to `*`-intertwining and prove unequal apertures are disjoint.

### 2. Mixed prime-character × completed-theta-grade Gram matrices

For every subset `P` of first `d` primes, packet was weighted by `W_x(P)`, squarefree character `χ_P`, and theta grade `exp(|P|x) thetaCuspFullSource(x)`. Exact Gram entries used

`∏_{p∈P△Q} p^{-σ} · ∫ exp((|P|+|Q|)x) thetaCuspFullSource(x)^2 dx`.

All matrices through `d=10` (`1024×1024`) were Cholesky positive definite in float64 for `σ∈{0.25,0.5,0.75}`. Thus no finite packet dependence appeared. Normalized condition numbers at `d=10` were:

| `σ` | condition number |
|---:|---:|
| `0.25` | `874,579` |
| `0.5` | `2,178.09` |
| `0.75` | `119.414` |

Changing Gamma aperture `x=0.25,0.5,0.75` left normalized matrices identical to at most `3.33e-16`, as expected from exact cancellation of nonzero diagonal weights.

**Consequence.** No finite-dimensional rank obstruction kills combined prime–theta packets. However scalar synchronized Gamma weights cannot select critical wall, improve normalized angular conditioning, or create missing cross-grade sewing: they only rescale coordinates. Any surviving JAS mechanism needs genuinely non-diagonal prime–grade coupling (or indefinite structure), not another scalar Gamma normalization.

### 3. Bilateral group completion of synchronized weights

For nested supports `P_n` of first `n` primes, computed actual `W_x(P_n)` to `n=1,000,000`. Naive group completion uses positive tail `W_x(P_n)` and inverse tail `W_x(P_n)^{-1}`. At final prime `15,485,863`:

| `x` | `log10 W_x(P_n)` | `-log W_x(P_n)/θ(p_n)` | `log10 Σ_{k≤n} W_x(P_k)^{-2}` |
|---:|---:|---:|---:|
| `0.25` | `-6,948,824.57` | `1.033619` | `13,897,649.13` |
| `0.5` | `-6,948,583.32` | `1.033583` | `13,897,166.65` |
| `0.75` | `-6,948,582.24` | `1.033583` | `13,897,164.49` |
| `1.0` | `-6,948,582.03` | `1.033583` | `13,897,164.07` |

Here `θ(p_n)=Σ_{k≤n} log p_k`. Also `-log W_x(P_n)/n≈16.0` and increases with cutoff; last-half fits have a stable nonzero `n log n` coefficient near `1.0704` with relative error below `7.4e-7`.

**Consequence.** Retire naive bilateral scalar group completion and every fixed exponential gauge `exp(αn)`: primorial-scale decay of one tail forces primorial-scale growth of inverse tail, far beyond polynomial moderation. Symmetric damping by `W_x(P_|n|)` would be square-summable but breaks exact group-completion/sewing recurrence. Surviving bilateral route must use a different topology, defect channel, or non-scalar completion.

## Research decision

These computations kill two broad scalar JAS constructions early: unitary integration of flat insertion gains and reciprocal bilateral completion. They preserve finite prime–theta packet independence while showing diagonal Gamma scaling cannot supply missing RH-bearing coupling. Highest-value next proof is exact `*`-intertwiner disjointness for actual synchronized insertion representations; if closed, it converts first numerical obstruction into unconditional Lean route closure.
