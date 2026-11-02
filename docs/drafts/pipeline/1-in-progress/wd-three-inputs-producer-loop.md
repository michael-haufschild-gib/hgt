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

## The three inputs are one input

Write `G(α) = N⁻¹ Σ_{ρ,ρ'} T^{α(ρ+ρ̄'−1)} w(γ−γ')` (depth-weighted Montgomery form, corpus
`averagedMontgomeryForm`), `δ = a/log T`.

1. **Long-range pair correlation.** Block 3 at depth `a` follows from
   `limsup_T ∫_0^A e^{−2aα}(A−α) G(α) dα ≤ e^{o(A)}` (sub-exponential growth; the HL
   asymptotic `F → 1` is not needed). Zeros deeper than `2a/log T` gain weight `e^{2aA}` against the
   damped on-line diagonal `A/(2a)`; tight deep pairs (ordinate gap `< C/(AL)`) can cancel at the
   end of the range, and they are `O(N/A)` by the Selberg–Fujii short-range count.
2. **Long mollifiers.** The same growth bound is a mean value of a prime polynomial of length
   `T^A`; with mollifiers it is the off-line first moment `Σ_{γ≤V}(β−½)₊`, whose constant tends to
   `0` only as the mollifier exponent `θ → ∞` (corpus: `0.067V` at `θ = 21/50`,
   `eventually_offLineMoment_le_selberg_upper`; depth charge `O(log U)` for `c < 22/51`).
3. **Counting producer.** Over `𝔽_q` the same bound is `|𝒵(n log q)| ≤ 2g`, Stepanov's count.

All three equal one statement: infinite near-line density slope at the scale `1/log T`, that is
`#{δ_ρ > a/log T}/N → 0` for every fixed `a`.

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

## Open core

An unconditional bound for the damped long-range energy, equivalently cancellation of size
`H^{1−ε}` in `Σ_{h≤H}(Λ(n)Λ(n+h) − 𝔖(h))` on average over `n`, or a ℤ-auxiliary with Frobenius-type
multiplicity. No mechanism above survives.

## Log
- 2026-11-02 — created; rows 1–15.
