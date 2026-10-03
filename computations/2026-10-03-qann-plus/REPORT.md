# Majorant-side exact-null LP: scaling test of Q_ann⁺ (2026-10-03)

## Question
Does the one-sided cross-talk `OPT(n₀) = inf {Σ_{m≠n₀}(1+log m)|I(m)| : ĥ ≥ 0, I(n₀) = 1}` tend to 0? Here `I(m) = ∫Ξ²ĥ cos(t log m) dt` over Gaussian-bump bases. `OPT → 0` for every `n₀` is Q_ann⁺, which gives `λ ≤ Λ` for every producer, hence RH by Landau (bohr card row 83).

## Runs (n₀ = 2, M ≤ 3000, pod `157.157.221.30`)
| basis | T | solver OPT | verified OPTv (ν clipped and renormalised, objective recomputed) |
|---|---|---|---|
| σ = 1, Δ = 0.5 | 100 | 2.44e-4 | 5.67e-4 |
| σ = 1, Δ = 0.5 | 200 | 2.41e-4 | — |
| σ = 1, Δ = 0.5 | 400 | solver failure | — |
| σ = 2, Δ = 1 | 100 | 0.0 (garbage) | 28.0 |
| σ = 3, Δ = 1 | 100 | 4.9e-3 (IPM, inconsistent) | — |
| σ ∈ {1, 2}, {1, 2, 3} | 100, 200 | solver failure | — |

## Reading
- The LP is ill-conditioned. The useful cancellations sit at 1e-7, the size of the HiGHS tolerances, and solver-reported optima disagree with recomputed objectives by factors 2 to ∞. Only `OPTv` is a bound. It gives `λ(2) ≤ log 2 + 8e-4` for every producer (float, not certified), far weaker than the certified two-sided pinning `|λ(2) − log 2| ≤ 6.2e-9` (`certified-producer-pinning.md`).
- Structure: at σ = 1 the residual cross-talk sits at `m ≈ 264` (`log m ≈ 5.6`), the smoothness tail of the bump basis, not low `m`. The minorant side (`I(2) = −1`) is stuck at 1.31, with `I(3) ≈ 0.53`, at every T ≤ 400.
- **Not decisive.** For every finite set of constraints `m ≤ M`, `±e_{n₀}` lies in the closure of the cone, because a zero-mean finite cosine sum ≥ 0 vanishes identically. So any finite-truncation plateau is a window or basis artefact, and Q_ann⁺ is a purely infinite-dimensional statement (existence of an infinite witness). Numerics cannot decide it, and the spark pinning race already covers the finite-level content.
