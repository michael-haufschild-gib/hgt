# Ladder hiding search (2026-09-08)

**Question.** Can a family of several real-part bands of isolated (spaced) off-line zeros hide its pair-form energy at
*every* scale, better than a single band can? This is the open "ladder" class of the isolation dichotomy
(`1-in-progress/offline-isolation-dichotomy.md`, STATUS CANNOT-335/336/337): the window method proves a density bound for
any band that dominates the energy envelope over a scale window of length `1/D`; ladders are families in which no band
does. Reasoning could not decide whether cross-band cancellation of alias peaks can be sustained.

**Model** (`ladder_hiding.py`). Mean-spacing units: frequencies `u_j` with pairwise gaps `≥ D = 2`, amplitudes
`exp(α δ_j L)` with `L = log T = 30`, `S(α) = Σ_j exp(α δ_j L) e(u_j α)` on `α ∈ [0.1, 0.9]` (401 grid points).
Hiding ratio `H = max_α |S(α)|² / max_α Σ_j exp(2α δ_j L)`. Reference levels: single-band window floor
`exp(−2ℓδ_top L)` with `ℓ = 1/D + 0.05` (`log10 = −4.3`), perfect hiding `exp(−2δ_top L(1−η))` (`log10 = −7.0`).
Structures: single band (400 zeros at `δ = 0.30`), two bands (400 at 0.20, 60 at 0.30), ladder of 4 bands
(800/300/110/40 at 0.15/0.20/0.25/0.30), ladder of 8 bands (800…30 at 0.15…0.30), counts chosen so that the energy
crossovers are spaced below `1/D`. Smooth max (`temp = 0.05`) minimised by L-BFGS-B with analytic gradients (checked
against finite differences, relative error `1e-7`), 16 restarts per structure in parallel on 16 cores; run 1: random
spaced starts, 400 iterations; run 2: half random, half per-band quadratic chirps in disjoint ranges, 1500 iterations.

**Results** (`ladder_results_D2_random.json`, `ladder_results_D2.json`, logs).

| structure | run 1 best log10 H | run 2 best log10 H | window floor | perfect hiding |
|---|---|---|---|---|
| single band | −1.33 | −2.40 | −4.3 | −7.0 |
| two bands | −1.62 | −2.37 | −4.3 | −7.0 |
| ladder 4 | −1.45 | −2.54 | −4.3 | −7.0 |
| ladder 8 | −1.36 | −2.43 | −4.3 | −7.0 |

**Interpretation.** With structured seeds every structure reaches the same hiding level `≈ 10^{−2.4}`, the level of a
single chirped band (analytic estimate for one chirped progression: `≈ 10^{−2.1}`); the four- and eight-band ladders
gain at most `0.15` dex over one band and stay two decades above the window floor and five above perfect hiding. No
configuration in the optimiser's reach hides multi-band energy better than a single band does. This is evidence, not
proof: the objective is nonconvex and the search is local. Consequence for the programme: the conjecture "every
`D`-separated set of off-line zeros at distance `≥ δ` from the line has `≪ T^{1−c(D)δ}` elements" (full isolation law,
all bands, no dominance hypothesis) is not contradicted; ladders are not found to be an evader class, unlike tapered
blocks (which are proved evaders). No result here is used in any Lean proof.

**Runs.** Two runs, 5–150 s per structure, pod working directory removed after download.
