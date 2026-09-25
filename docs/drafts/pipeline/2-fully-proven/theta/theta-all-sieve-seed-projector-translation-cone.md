# Cofinal prime deletion recovers the hidden translation measure

- **ID:** theta-all-sieve-seed-projector-translation-cone
- **Stage:** 2-fully-proven (paper)
- **Type:** all-sieve Bernstein-cone classification, exact and quantitative charge rigidity, sharp off-line countermodels
- **Routes:** STC, CSB, U, MPLF, RG-HF, RHist; source-side comparison with RG and EDQ
- **Status:** [PROVED HERE ON PAPER] [LEAN FORMALIZATION OPEN] [NOT AN RH PROOF]
- **Dependencies:** the literal theta flux and finite-prime deletion formula in [theta-prime-deletion-spectral-escape.md](theta-prime-deletion-spectral-escape.md), the critical charge in [theta-euler-critical-boundary-mass-escape.md](theta-euler-critical-boundary-mass-escape.md), and finite Bernstein--Widder plus Laplace-measure uniqueness already available in the Lean corpus. No numerical computation is used.

## Set-up and all-sieve classification

Let `k` be the positive even completed theta source, `T_s k(x)=k(x+s)`, and `D_S=∏_(p∈S)(I−p^(−1/2)T_(log p))` for a finite prime set `S`. For a finite real signed Borel measure `μ` with

`∫_ℝ exp(|s|/2) d|μ|(s)<∞`,                               (1)

put `g_μ(x)=∫_ℝ k(x+s)dμ(s)`. Its normalized flux is

`b_f(t)=t^(−3/2)∫_[log(t)/2,∞) exp(x/2)f(x)dx`, `t>0`.

**All-sieve theorem.** The following are equivalent:

1. For **every** finite prime set `S`, the flux `b_(D_S g_μ)` is completely monotone on `(0,∞)`.
2. The signed translation measure `μ` is positive.

This applies to arbitrary real shifts, not only integer or rational scales. The decisive operation is cofinal prime deletion: its normalized flux converges to

`b_seed,μ(t)=2π∫_ℝ exp(5s/2) exp(−π exp(2s)t)dμ(s)`.        (2)

The rate map `s↦πexp(2s)` is injective. Complete monotonicity of (2) therefore exposes the sign of **each part** of `μ` through uniqueness of its Laplace measure.

## Proof of the all-sieve theorem

The literal deleted flux has the exact Gaussian expansion

`b_(D_S k)(u)=2π∑_(n≥1, gcd(n,∏_(p∈S)p)=1)n² exp(−πn²u)`. (3)

Translation and integration against `μ` give

`b_(D_S g_μ)(t)=∫_ℝ exp(5s/2)b_(D_S k)(exp(2s)t)dμ(s)`.   (4)

All integrals converge absolutely: `0≤b_(D_S k)(u)≤b_k(u)≤u^(−3/2)/2`, so the absolute integrand in (4) is at most `exp(−s/2)/(2t^(3/2))`, which is integrable by (1). If `μ≥0`, (3)--(4) are positive mixtures of exponentials and every flux is completely monotone.

Conversely, let finite sets `S_j` increase to all primes. For each fixed `u>0`, the coprime indicator in (3) tends to `1` only at `n=1`; dominated convergence in (3)--(4) gives (2). To pass complete monotonicity to this limit, differentiate (4) at any order `m`. Each Gaussian derivative is bounded by a constant depending on `m,t` times the same Gaussian at `t/2`, since `λ^m exp(−λt)≤C_(m,t)exp(−λt/2)`. After summing, the displayed `exp(−s/2)` majorant still applies. Dominated convergence proves convergence of every derivative, so the nonnegative alternating derivative signs pass to (2).

Fix `t₀>0` and apply the finite Bernstein--Widder representation to the shifted completely monotone profile `u↦b_seed,μ(t₀+u)`. Formula (2) also represents it by the finite **signed** measure obtained from the pushforward of `2πexp(5s/2)μ` under `s↦πexp(2s)`, weighted by `exp(−t₀λ)`. Laplace uniqueness makes that signed measure positive. Since both the weight and rate map are strictly positive/injective, `μ≥0`. This proves the equivalence.

## Two boundary charges and exact rigidity

For `L_w f=∫_ℝ exp(wx)f(x)dx`, the translation multiplier is

`L_w g_μ=M_μ(w)L_w k`, `M_μ(w)=∫_ℝ exp(−ws)dμ(s)`, `|Re w|≤1/2`. (5)

Suppose the all-sieve condition holds, the ordinary mass of `g_μ` equals that of `k`, and **both** critical boundary charges match:

`L_0g_μ=L_0k`, `L_(1/2)g_μ=L_(1/2)k`, `L_(-1/2)g_μ=L_(-1/2)k`. (6)

Then `μ` is a positive probability measure with

`∫ exp(s/2)dμ=∫ exp(−s/2)dμ=1`.

Their average is `∫ cosh(s/2)dμ=1`. Since `cosh(s/2)>1` whenever `s≠0`, one has `μ=δ₀` and `g_μ=k`. If `g_μ` is even, ordinary mass and only the `+1/2` charge in (6) suffice: evenness gives the reflected `−1/2` equality automatically. This proof needs no assumption that `μ` itself is symmetric.

## Sharp failure without the reflected charge

Fix any prime `p` and set `a=1/(√p+1)`, `b=√p/(√p+1)`,

`μ_p=a δ_(−log p)+b δ_(+log p)`.

This is a positive probability measure, so `g_(μ_p)>0` globally and **every** finite-prime-deleted flux is completely monotone. Its ordinary mass and `+1/2` charge equal those of `k`, since

`a+b=1`, `a√p+b/√p=1`.

Nevertheless its Mellin multiplier has the exact off-line zero

`M_(μ_p)(1/4+iπ/(2log p))=0`,                           (7)

because `M_(μ_p)(w)=a p^w+b p^(−w)` and `p^(2w)=−√p` at that point. The `−1/2` charge is larger than theta's: `a/√p+b√p>1`. Thus all-sieve positivity, global source positivity, ordinary mass and one exact boundary charge cannot orient zeros without the reflected charge or source evenness. This countermodel is not a zero of the actual Xi transform.

## Quantitative gap law and its sharp limit

Let `μ` be a positive **symmetric** probability measure. Put

`δ=M_μ(1/2)−1=∫(cosh(s/2)−1)dμ(s)≥0`.

If its nonzero shifts obey `|s|≥L>0` and `0≤σ<1/2`, define

`C_(L,σ)=sup_(u≥L) [cosh(σu)+1]/[cosh(u/2)−1]<∞`.       (8)

For every complex `w` with `|Re w|≤σ`, including **all imaginary heights**,

`|M_μ(w)−1|≤C_(L,σ)δ`.                                  (9)

Indeed symmetry gives `M_μ(w)=∫cosh(ws)dμ`; `|cosh(ws)|≤cosh(σ|s|)`, and the ratio in (8) bounds the integrand against the charge defect. If `C_(L,σ)δ<1`, the multiplier has no zeros in that closed substrip. Integer-scale shifts have the fixed gap `L=log 2`, so this gives a general positive-gauge version of the prime-power complex stability bound.

The gap condition is essential. Fix `0<σ<1/2`, let `ε>0`, set `θ_ε=[1+cosh(εσ)]^(−1)`, and take

`μ_ε=(1−θ_ε)δ₀+(θ_ε/2)(δ_ε+δ_(−ε))`.

Each source is positive and even, every deleted flux is completely monotone, and ordinary mass is exact. Both critical charges tend to the theta charge because `M_(μ_ε)(1/2)=1+θ_ε(cosh(ε/2)−1)→1`. Yet

`M_(μ_ε)(σ+iπ/ε)=1−θ_ε−θ_ε cosh(εσ)=0`              (10)

for **every** `ε>0`. Thus approximate boundary-charge matching cannot give an all-height zero-free strip without an arithmetic separation of nontrivial shifts. This is an exact analytic family, not a numerical experiment.

Writing the zero height as `T_ε=π/ε`, the standard local expansion of `cosh` gives the exact asymptotic `T_ε²[M_(μ_ε)(1/2)−1]→π²/16`. Hence even a charge error of order `T^(−2)` can coexist with a forced off-line zero at height `T` in this positive, even, all-sieve class. A source argument using only such an approximate scalar charge needs a stronger rate or a fixed arithmetic shift gap to address moving heights.

## Frontier meaning

All finite prime deletions act as an **arithmetic microscope**: after cofinal deletion, the `n=1` Gaussian seed remains, and its continuum of shifted rates identifies the hidden translation measure. This is stronger than undeleted Bernstein positivity, which the earlier [one-sided countermodel](theta-one-sided-bernstein-two-anchor-offline-zero.md) passes. The positive two-shift countermodel (7) shows that even this complete sieve condition plus one charge is insufficient without reflection. The family (10) shows why near-charge information is too weak at moving spectral height unless a fixed logarithmic shift gap is retained.

None of these statements orients the zeros of the unmodified theta source. Literal finite Euler smooth-number stages are not finite signed measures acting on `k`: their chronological coefficient mass grows, their reflection is created only at completion, and their critical charge has a boundary anomaly. The open mathematical step is to carry an arithmetic sign/complex-phase law through that singular completion, rather than infer it from the rigidity of regular translation gauges. Lean formalization and literature novelty of the combined results remain open.
