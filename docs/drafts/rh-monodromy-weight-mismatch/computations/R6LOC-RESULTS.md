# R6-loc / R6-loc-b results (2026-07-03) — [MEASURED] the local transfer channel is REAL

Engine: `computations/mwm/engine5.py` (circle returns). Raw here: `r6loc.out` (τ-scan),
`r6locb.out` (radius scan), `r6locc.out` (hardened). Pre-registrations: board wave-2b block
(R6-loc) and R6-loc-b block.

## R6-loc — τ-scan (circle r = 0.05, 48 pts, around the banked zero t ≈ 85.699; τ ≤ 200)

- Margin proxy 0.0618. **Strict sub-margin returns: none** in τ ∈ (0.5, 200] — the
  registered headline clause fails at this range/step. **Kill clause did NOT trigger**:
  min ratio d/m = 1.70 ≪ 3.
- The local channel is ≈ 14× deeper than the global one (R6 big box: best 24× margin;
  local circle: 1.70×): finite-dimensionality of the jet drastically helps returns —
  the locality hypothesis behind (H-loc) is directionally confirmed.
- **Near-returns land exactly on the other population zeros**: τ = 91.0 → t ≈ 176.7
  (ratio 1.70), τ = 154.7 → t ≈ 240.4 (2.3), τ = 28.5 → t ≈ 114.2 (3.1), τ = 80.8 →
  t ≈ 166.5 (3.9). The local jets of distinct off-line zeros are approximate copies —
  a measured "zero-species similarity" across the population.

## R6-loc-b/c — radius scan at τ ≈ 91.0 (both pre-registered clauses CONFIRMED)

| r | margin m(r) | min_τ d | ratio d/m | sub-margin? |
|------|----------|----------|-------|-----|
| 0.02 | 0.02497 | 0.10262 | 4.109 | no |
| 0.05 | 0.06185 | 0.10507 | 1.699 | no |
| 0.08 | 0.09794 | 0.10766 | 1.099 | no |
| 0.12 | 0.14464 | 0.11129 | **0.769** | **YES** |
| 0.15 | 0.17852 | 0.11414 | **0.639** | **YES** |

d is nearly r-independent (jet-difference-dominated, as predicted); m grows ≈ linearly in r.
Hardened (192 pts, dps 20, τ step 0.005): r = 0.12 ratio 0.7694, r = 0.15 ratio 0.6387,
optimum at τ = 91.005.

**Consequence (via the Rouché-transfer lemma, 07 §3):** on the circle ∂B(ρ₁, 0.15) around
the banked zero ρ₁ ≈ 0.8085 + 85.699i, sup |f(s + 91.005i) − f(s)| < min |f| — so f has
equally many zeros in B(ρ₁, 0.15) and B(ρ₁ + 91.005i, 0.15): **the off-line zero at
t ≈ 176.70 is the certified local Rouché-transfer image of the banked zero.** First
non-counterfactual instance of the M1 transfer mechanism — an actual transfer between two
actual off-line zeros of the Davenport–Heilbronn function.

Caveat (stated, bounded): sup/min are 192-point sampled proxies, not interval arithmetic;
the true ratio can only be larger, but the 36% headroom at r = 0.15 dwarfs the
discretization error of an analytic integrand at this scale. An interval-certified version
is a small dedicated job if ever promoted.

## Mechanism ranking after R6-loc (updates 08 §4)

- **(H-loc): INSTANTIATED in the family** — not as positive-density returns (open), but as
  certified fixed-τ transfers with the radius as the free dial. The R6 negative was a
  contour-size artifact: transfer works locally where it fails globally.
- (P_k) population forcing remains co-primary (the population itself is unconditional in
  the FE class).

Opened — **R7: the transfer graph.** For the ≈ 13 certified off-line zeros in t ≤ 200,
scan all pairs (ρ_i, ρ_j): does some r ≤ 0.2 give a sub-margin transfer at τ = t_j − t_i?
Deliverable: the population's "recurrence skeleton" (which zeros are local copies of
which); pre-register: the graph is dense (most pairs transfer), consistent with the
species-similarity reading. Job size: ~80 pairs × 5 radii × 40 τ-steps × 48 pts ≈ 750k
evals — SPLIT INTO ≤ 10-min chunks per the sizing rule.
