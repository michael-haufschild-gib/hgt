# WD missing inputs: long-range depth pair correlation, long mollifiers, counting producer

- **ID:** wd-three-inputs-producer-loop
- **Stage:** 1-in-progress
- **Type:** CONJECTURE LOOP
- **Source:** wd-review-0111-closing-loop (rows 4–20); route-WD blocks 1, 3–6.
- **Statement:** Construct an unconditional input that makes the WD window energy `|𝒵(t)|²`
  grow sub-exponentially beyond `t = log T` on average over windows.

## Goal

Blocks 1 and 3–6 need information about `|𝒵_m(t)|²` for `t ≫ log m`, that is prime data of
length `T^α`, `α → ∞`, at the scale `1/log T` in depth. Block 3 (mean log-stage index
`o(log U)`) is the weakest open rung.

## The three inputs and the minimal input

Write `G(α) = N⁻¹ Σ_{ρ,ρ'} T^{α(ρ+ρ̄'−1)} w(γ−γ')` (depth-weighted Montgomery form, corpus
`averagedMontgomeryForm`), `δ = a/log T`.

1. **Long-range pair correlation.** Zeros deeper than `2a/log T` gain weight `e^{2aA}` in
   `∫_0^A e^{−2aα}(A−α)G(α)dα` against the damped on-line diagonal `A/(2a)`; tight deep pairs
   (ordinate gap `< C/(AL)`) can cancel at the end of the range and are `O(N/A)` by the
   Selberg–Fujii short-range count. But the long-range energy weights every zero by `e^{2αLδ}`, so
   a sub-exponential bound for all ranges `A` forces `N(½+η,T) ≤ T^{1−2Aη}N` for all `A`: quasi-RH.
   Long-range energy is the wrong currency for block 3.
2. **Long mollifiers.** Mollified mean squares at `σ₀ = ½ + b/log T` are depth-localized; with
   Littlewood and Jensen they bound `Σ(β−σ₀)₊`. The constant tends to `0` only as `θ → ∞`
   (corpus: `0.067V` at `θ = 21/50`; depth charge `O(log U)` for `c < ½`). For `θ > 1` even
   `∫_T^{2T}|M|²` is a sum of squares of Möbius sums over intervals of length `n/T`: the parity
   barrier. Kloosterman/Kuznetsov technology (in the corpus: Weil bound, DI large sieve for `Γ₀(Q)`)
   caps at `θ < 1`.
3. **Counting producer.** Over `𝔽_q` the window bound is `|𝒵(n log q)| ≤ 2g`, Stepanov's count.

**Minimal input for block 3.** By the corpus TFAE
(`dyadicMean_corridor_and_polynomialTheta_littleO_log_up_to_half_tfae`), the Selberg tail law
(`eventually_offLineTail_le_selberg`, rate `−log(1−e^{−2R/15}) → 0`) and Littlewood on the line
(`exists_zetaLine_logMean_sandwich`), block 3 is

  `∫_T^{2T} log|ζ(½+it)| dt = o(T)`, equivalently `Σ_{T<γ≤2T} m_ρ(β−½)₊ = o(T)`,

a logarithmic (not quadratic) functional of `ζ` on the line. Quadratic inputs reach it only
through mollifiers and Jensen.
## Ledger

| # | Conjecture | Verdict | Insight |
|---|---|---|---|
| 1 | Averaged Hardy–Littlewood (mean square over `h ≤ H`, Mikawa/Perelli–Pintz) gives `G(α) = e^{o(α)}` | refuted | the growth bound needs `Σ_{h≤H} φ̂(h/H)(S(h)−𝔖(h)x) ≪ x H^ε`, relative precision `H^{−1+ε}`; mean-square HL saves only `(log x)^{−A}` per shift |
| 2 | Upper-bound sieves (Selberg, `S(h) ≤ C𝔖(h)x`) bound `G(α)` | refuted | the main term `Σ 𝔖(h)x` cancels against the pole term; a factor `C` leaves `(C−1)H/log H = T^{α−1}`, the trivial bound |
| 3 | Height averaging localizes the long range to an accessible first moment | reduction | it becomes `Σ_n Λ(n)(ψ_φ(n;H) − H)` (Λ-weighted short-interval discrepancy), and the explicit formula returns it to `G(α)`: circular |
| 4 | Short-interval variance (Huxley range) bounds `G(α)` | refuted | Cauchy–Schwarz gives `G ≲ T^{(α−1)/2}`; still exponential in `α log T` |
| 5 | Tauberian `∫_b^{b+1} G ≪ 1` (Montgomery's RH argument, depth-damped so the form stays a square) | refuted | damping by the window's top depth makes the bound say `#top ≲ N`; `o(N)` needs `G_damped → 0`, which is the claim |
| 6 | Positive definite (Krein) extension of `G` from `[−1,1]` | refuted | depth weights destroy positive definiteness; under RH it gives `F(α) ≤ F(0) ~ log T` for free |
| 7 | Euler-product mollifier `∏_{p≤X}(1−p^{−s})` (mean of `log|P_X|` is exactly 0) | refuted | `E|ζ/P_X|² ≈ e^{−γ}log T/log X`; needs `X = T^θ`, a mollifier of length `e^{T^θ}` |
| 8 | Fractional moments / Jensen gap: `mean log|ζM| = ½ log E|ζM|² − J` | reduction | `J ≥ 0` is the log-variance of `ζM`; fourth moments improve constants only; `J = ½ log c − o(1)` is equivalent to the claim |
| 9 | Heat flow: Ki–Kim–Lee at `t > 0` transfers to ζ | refuted | KKL threshold `t ≍ 1/log T`; heat time `t` acts like depth `tL/8`; deep-zero persistence is proved only for `t ≤ δ²/L⁴` (corpus `exists_card_deep_le_mul_nonrealZeroCount`) |
| 10 | Turán power sums on `𝒵_m(t)`, `t ∈ [L, AL]` | refuted | loss `e^{−O(#zeros)} = T^{−c}`; detecting depth `a/L` needs `t ≳ L²/a` |
| 11 | Spectral families (GL(2)/GL(n) large sieve with Eisenstein slice) give long mollifiers | refuted | the large sieve loses the constant; dropping cusp forms costs the family size; Conrey's `4/7` is the limit of the Kuznetsov–Weil route |
| 12 | Parity-breaking inputs (Matomäki–Radziwiłł, log-Chowla) supply the off-diagonal | refuted | they give relative `o(1)` cancellation in short intervals; the growth bound needs square-root cancellation over shifts (variance asymptotics) |
| 13 | Linear combinations of L-functions as calibration | insight | they satisfy the functional equation, their zeros spread at depth `√(loglog T)/log T`, so block 3 fails for them: any input must use the Euler product at depth precision `o(1/log T)` |
| 14 | AFE main sum `A_t = Σ_{n≤√(t/2π)} n^{−s}` governs depths | reduction | right of the line `ζ ≈ A_t` (`|χ| = e^{−uL}`); a zero of `A_t` at depth `D/L` creates an off-line zero of the first-order model once `D` exceeds a constant. RH forces `A_t` to be (typically) zero-free beyond `C log L/L`; transfer is not uniform because `max|A*| ~ T^{1/4}` |
| 15 | Fermat/LTE auxiliary integers `a^{lcm(1..x)}−1` as a Stepanov producer | refuted | multiplicity `1+v_p(lcm)` on all `p ≤ x`, but the size `e^{ψ(x)}log a` is exponential in the count |
| 16 | Deligne amplification over ℤ: k-fold zero sums (Kurokawa tensor powers) with a k-uniform weak bound | reduction | over `𝔽_q` the error `+1` comes from the Lefschetz pencil base curve; over ℤ mean values give only the cap `kλ ≤ 1` and the Kurokawa Euler region has error `k/2`; detecting depth `a/L` through `|𝒵|^{2k}` needs range `t ≈ L log L/(2a)`, length `T^{2kα}` |
| 17 | Unconditional Montgomery simple-zero argument with depths gives ≥ 2/3 simple zeros on the line | refuted | an off-line reflected pair is a double ordinate in `F(α)` (block sum ≥ 4); shallow pairs cost `O((L(δ+δ'))²)`; deep pairs' off-diagonal `e^{2Lδ}` exceeds their diagonal `e^{2Lδ}/(4L²δ²)` and needs the depth charge at scale `L` restricted to depth `> η/L`, which is the block-3 quantity; with support `λ < ½` Montgomery's constant `1/λ+λ/3 > 2` gives nothing |
| 18 | Levinson structure through the AFE half: off-line zeros of `A+χA*` ≤ `2·#{zeros of A right of ½}` | reduction | this is Levinson's method with `G` the AFE half; the sharp half `1_{n≤√(t/2π)}` is badly mollifiable (truncation residues `≍ L`); smooth halves give Levinson–Conrey, `θ`-limited; Farmer's `θ = ∞` would give 100% |
| 19 | Micro-scale limits: subsequential limits `F` of `ζ(½+i(t₀+z/L))/√L` are real on ℝ with the CUE 2- and 4-point moments; block 3 ⟺ every limit has only real zeros | reduction | the known moments fix `E|F|²` and `E|F|⁴`, not `E log|F|`; real-rootedness needs the log-moment |
| 20 | Heat flow at time `τ/L²` (KKL threshold `e^{c/√t}`) | reduction | with dense real neighbours a pair at depth `a/L` dies by heat time `log(1+ca²)/(2cL²)`; KKL at time `τ/L²` would give the corridor (block 5), but at that time the effective series sits at depth `τ/(8L)`: the same critical problem |
| 21 | Jensen loss as the obstruction: `mean log|ζM| = ½ log E|ζM|² − J`, and `J` computable | reduction | for `Y = log|ζM(½+b/L+it)|`, `J ≈ Var Y ≈ ½E₁(2bθ)` from primes beyond `T^θ`; primes beyond `T` are dual to the zeros near `σ₀`, so `E Y` (not `Var Y`) is the depth sum; higher moments of `ζM` cannot improve the upper bound on `g'(0)` for the convex `g(k) = log E|ζM|^{2k}` |
| 22 | a-points as calibration | insight | `a`-points (`a ≠ 0`) have mean depth `≍ √(loglog T)/log T`; block 3 is the `o(1)` symmetry `E log⁺|ζ| − E log⁻|ζ| → 0` of the log-normal law of `|ζ(½+it)|`, invisible to Selberg's CLT (precision `o(√loglog T)`) |
| 23 | Family averaging (Conrey–Iwaniec–Soundararajan asymptotic large sieve) lengthens mollifiers | refuted for ζ | effective `θ > 1` exists only on average over a family of conductors; height averaging is one-dimensional and gives no extra room for a single `ζ` |

## Open core

An unconditional bound for the damped long-range energy, equivalently cancellation of size
`H^{1−ε}` in `Σ_{h≤H}(Λ(n)Λ(n+h) − 𝔖(h))` on average over `n`, or a ℤ-auxiliary with Frobenius-type
multiplicity. No mechanism above survives.

## Log
- 2026-11-02 — created; rows 1–23; minimal input identified (critical-line log-mean).
