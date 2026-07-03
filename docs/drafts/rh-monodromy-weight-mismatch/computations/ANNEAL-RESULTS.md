# ANNEAL calibration — AFE-truncation domination (task #134)

Script: `computations/mwm/afe_domination.py` (pod run, mp.dps=30, 96 boundary samples
per circle). g_N(s) = Σ_{n≤N} n^{−s} + χ(s)Σ_{n≤N} n^{s−1}, N = ⌊√(T/2π)⌋; exact FE
g_N(1−s) = χ(1−s)g_N(s). Windows: center 1/2+iT, radii 0.20/0.35; T = 1000 fixed +
rng-drawn {468, 1304, 2506, 2697, 2790, 2795} (seed session 1749846374244417905).
q := max_{∂W} |ζ−g_N|/|g_N|; domination ⟺ q < 1.

## Results
| T | r=0.20: q | r=0.35: q | note |
|---|---|---|---|
| 468 | 0.131 | 0.278 | |
| 1000 | 0.746 | 0.237 | r=0.20 circle near g-zero (min\|g\|=0.15) |
| 1304 | 0.022 | 0.032 | |
| 2506 | 0.266 | **56.98 (FAIL)** | min\|g\| = 0.0034 ≪ 0.05·median — predicted mechanism |
| 2697 | 0.389 | 0.401 | |
| 2790 | 0.064 | 0.104 | |
| 2795 | 0.511 | 0.944 | |

## Pre-registered verdicts
- **PE PASS**: 7/7 of the r=0.20 circles dominated (needed ≥ 75%); the sole failure
  (r=0.35, T=2506) has min|g| = 0.0034 < 0.05·median = 0.099 — the predicted
  near-zero mechanism, movable by nudging the radius.
- **PF mostly confirmed** (6/7 heights have r=0.35 worse); exception T=1000 driven by
  a g-zero near the r=0.20 circle — at these heights the zero-proximity noise term
  dominates the systematic x^{−σ} error growth.

## Reading
Domination of ζ by its exact-FE symmetric truncation on r=0.20 line-centered window
boundaries is the ROBUST regime at accessible heights; exceptional windows are those
whose boundary passes near a truncation zero. This calibrates the (ANNEAL) reduction
of doc 22: on dominated windows the banked deck-transport machinery applies verbatim.
