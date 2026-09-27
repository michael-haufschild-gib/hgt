# Adaptive wild-saddle depth and physical spectral relocation

- **ID:** WS2-ADAPTIVE-PHYSICAL-RELOCATION
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** WS2 depth-two source operator and smooth RVM quantile
- **Statement:** Every fixed logarithmic saddle depth has an unbounded physical-ordinate error, while a source-only rank-dependent depth has vanishing physical-ordinate error.

## Goal

Determine the accuracy of diagonal iterated-saddle coefficients before an exact WS2 determinant occurrence law can be attempted. The existing two-step operator is trace-class close in **reciprocal** coordinates to the ordered Xi operator. Exact determinant zeros live in **ordinate** coordinates, where that estimate does not control occurrence.

## Theorem and proof

Put `N_n = max(exp 3, n + 1/8)`, `L_n = log(N_n/e)`, and define the source-only iterates

```text
v₀,n = L_n,
vₖ₊₁,n = L_n - log(vₖ,n),
tₙ,ₖ = 2π N_n / vₖ,n.
```

Let `q_n` be the exact smooth RVM quantile and `u_n = log(q_n/(2πe))`. For all sufficiently large `n`, `N_n=n+1/8`, `L_n≥4`, `u_n+log u_n=L_n`, and `q_n=2πN_n/u_n`. Write `a_n=L_n-log L_n`. Then `a_n≥L_n/2`, and `u_n` and every `vₖ,n` lie in `[a_n,L_n]`. On this interval the map `F(x)=L_n-log x` is invariant, and the mean-value theorem gives

```text
|x-y|/L_n ≤ |F(x)-F(y)| ≤ (2/L_n)|x-y|.
```

Also `|v₀,n-u_n|=log u_n`, with `(log L_n)/2≤log u_n≤log L_n` for `L_n≥4`. Iteration and the identity for the difference of two reciprocals yield, for every `k≥0`,

```text
π N_n log L_n / L_n^(k+2)
  ≤ |tₙ,ₖ-q_n|
  ≤ 8π N_n log L_n / L_n² · (2/L_n)^k.       (1)
```

For each fixed `k`, the lower bound tends to infinity because `L_n∼log n`. Taking `k=n` in the upper bound gives `|tₙ,ₙ-q_n|→0`. More economically, **within this diagonal fixed-point family**, bounded physical error requires depth at least `(1-o(1)) log n/loglog n` by the lower bound, and a sufficiently large constant multiple of `log n/loglog n` suffices by the upper bound. Thus the necessary and sufficient depth **order** in this family is `log n/loglog n`.

The exact count defect at depth two is also source-visible. Set `v₁=L-log L`, `v₂=L-log v₁`, `v₃=L-log v₂`, `t₂=2πN/v₂`, and `C(t)=t/(2π) log(t/(2πe))+7/8`. Then

```text
C(t₂) = N·v₃/v₂ + 7/8,
(N+7/8)-C(t₂) = N·log(v₂/v₁)/v₂ > 0.       (2)
```

The first identity follows from `log(t₂/(2πe))=L-log v₂=v₃`; the second uses `v₂-v₃=log(v₂/v₁)`. Since `v₂-v₁∼log L/L` and `v₁,v₂∼L`, the defect in (2) is asymptotic to `N log L/L³`, or `n loglog n/(log n)³` after the cap is inactive. Equation (1) with `k=2` gives the corresponding physical gap of order `n loglog n/(log n)^4`.

The corpus already proves that the ordered Xi positive ordinate differs from `q_n` by an eventual constant bound. Consequently the depth-two pseudo-ordinate cannot have eventual rankwise occurrence with the ordered Xi ordinate, whereas the adaptive source sequence `tₙ,ₙ` is within that constant plus `o(1)` of it. This identifies a necessary correction **if the source operator remains this diagonal saddle family**; a genuinely new coupling could instead change its spectrum. It is not an exact Xi determinant identity or an RH proof.

There is a stronger count-scale statement using the corpus's unconditional RVM remainder `xiZeroCount(T)-C(T)=O(log T)`. Since `tₙ,₂∼2πn/log n`, that remainder is `O(log n)`, negligible against (2). Hence, without assuming RH,

```text
(n+1) - xiZeroCount(tₙ,₂)
  ∼ n loglog n / (log n)^3.
```

This quantifies how many ordered zero heights the two-step source spectrum misses at its own `n`th pseudo-ordinate. The adaptive iteration removes this deterministic count drift; an arithmetic correction is still needed for exact occurrence.

## Formal status and next obstacle

Paper proof of (1)–(2) and the count-scale corollary is dependency-closed. Lean formalization is open. The relevant existing declarations are `routeKRVMQuantile_logPhase_fixedPoint`, `routeKRVMQuantile_reciprocal_eq_logPhase_div`, `routeKSmoothRVMCount_quantile`, `exists_xiZeroCount_routeKSmoothRVMCount_log_remainder`, and `exists_eventually_abs_xiOrderedPositiveOrdinate_sub_routeKRVMQuantile_le`. The source-defined adaptive iterate still lacks the arithmetic fluctuation that would identify individual Xi zeros. Next attack: find an arithmetic, source-derived correction to the adaptive pseudo-ordinate or a determinant identity whose quotient has a proved zero-free gauge.

## Corpus audit

Broad hybrid searches for `wild saddle determinant occurrence spectrum Xi source`, `RVM count quantile`, and `iterated logarithm saddle quantile` located the two-step trace-class theorem, RVM count/quantile identities, and the existing bounded Xi–RVM ordinate discrepancy. They did not locate a rank-dependent source iteration or the physical error bounds (1)–(2). The first search was partial; this is an internal novelty observation, not an external priority claim.

## Lean formalization (2026-09-27)

`formal/GaloisForLFunctions/RHTower/WildSaddleAdaptiveDepthRelocation.lean` formalizes every
statement of the card unconditionally; direct check, `lake build --old`, and axiom audit pass (all
`[propext, Classical.choice, Quot.sound]`); wired into `RHTower`.

| Card item | Declaration |
|---|---|
| iterates `v_{k+1} = L − log v_k`, `t_{n,k} = 2πN_n/v_{k,n}` | `wildSaddleIterate`, `wildSaddleOrdinate` (`v₁, v₂` are the corpus `routePTwoStepWildSaddleFirst/SecondPhase`) |
| eventually `N_n = n+1/8`, `L_n ≥ 4`, `u_n + log u_n = L_n`, `q_n = 2πN_n/u_n` | `eventually_wildSaddle_quantile` |
| `a_n ≥ L_n/2`; `u_n, v_{k,n} ∈ [a_n, L_n]` | `half_le_sub_log`, `wildSaddle_fixedPoint_mem`, `wildSaddleIterate_mem` |
| two-sided Lipschitz bounds for `F(x) = L − log x` | `abs_log_sub_log_le`, `abs_sub_div_le_abs_log_sub_log` |
| `(log L)/2 ≤ log u ≤ log L`; contraction `log u/L^k ≤ \|v_k−u\| ≤ (2/L)^k log u` | `wildSaddle_fixedPoint_log_bounds`, `wildSaddleIterate_sub_fixedPoint_bounds` |
| **(1)** `πN log L/L^{k+2} ≤ \|t_{n,k} − q_n\| ≤ 8πN log L/L²·(2/L)^k` | `wildSaddle_ordinate_bounds`, `eventually_wildSaddleOrdinate_bounds` |
| fixed depth: error → ∞; depth `k = n`: error → 0 | `tendsto_abs_wildSaddleOrdinate_sub_quantile_fixed`, `tendsto_abs_wildSaddleOrdinate_sub_quantile_diagonal` |
| bounded error ⇒ depth ≥ `(1−ε) log n/log log n` eventually | `wildSaddle_depth_lower` |
| depth ≥ `8 log n/log log n` ⇒ error → 0 | `wildSaddle_depth_upper` |
| **(2)** `C(t₂) = N v₃/v₂ + 7/8`, `(N+7/8) − C(t₂) = N log(v₂/v₁)/v₂ > 0` | `routeKSmoothRVMCount_wildSaddleOrdinate_two`, `wildSaddle_countDefect_eq`, `wildSaddle_countDefect_pos` |
| defect `∼ N log L/L³ ∼ n log log n/(log n)³` (explicit ratio bounds `1 ≤ R ≤ (L/(L−log L))³`) | `wildSaddle_countDefect_ratio_bounds`, `isEquivalent_wildSaddle_countDefect`, `isEquivalent_wildSaddle_countDefect_rank` |
| depth-two physical gap `=Θ(n log log n/(log n)⁴)` | `isTheta_wildSaddleOrdinate_two_sub_quantile` |
| `t_{n,2} ∼ 2πn/log n` | `isEquivalent_wildSaddleOrdinate_two` |
| no fixed depth has eventual rankwise occurrence with `γ_n`; `t_{n,n}` within `D + ε` of `γ_n` | `tendsto_abs_wildSaddleOrdinate_sub_xiOrdinate_fixed`, `exists_eventually_abs_wildSaddleOrdinate_diagonal_sub_xiOrdinate_le` |
| count scale `(n+1) − N_ξ(t_{n,2}) ∼ n log log n/(log n)³`, unconditional | `isEquivalent_wildSaddle_missedZeroCount` |

## Gates
- [x] 1 → 2: complete paper proof
- [x] 2 → 3: every statement formalized, unconditional, axiom-clean

- 2026-09-27 — formalized in full; moved to 3-formalized.
