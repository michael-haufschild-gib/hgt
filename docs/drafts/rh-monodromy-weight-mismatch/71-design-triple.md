# 71 — The Effectivization Pass: the Design Triple (z₀\*, ℓ\*, N₀\*) and the Tier Table

**Register: SEARCH** (task #16). §2–§4 are arithmetic on doc 69's first-pass
constants and doc 70's transfer — machine-computed (z0_opt.py, archived);
§1/§6 record the literature mining (delegate-sourced; spot-check citations
at promotion). This is the document where the Route C-direct spine becomes
a table of numbers with named knobs.

## 1. Mining record [delegate-sourced — appended after the search agents]

(see §6 verdict; per-item citations below)

## 2. The optimization set-up [arithmetic, from docs 69–70]

Budget: creation fraction ≤ ε₀\* = c_deck/C′ = 1/512 (doc 69 first-pass).
Allocation α to the ζ-left-tail (doc 70 transfer), 1−α to taper Chebyshev
(factor 4 from the completed-Δ norm doubling):

- tail: P_tier(z₀) ≤ α·ε₀\* — P depends on the EFFECTIVITY TIER:
  - **Tier G** (needs a Berry–Esseen-effective Selberg CLT):
    P = Φ(−z₀);
  - **Tier M2k** (needs an effective 2k-th moment of log|ζ(½+it)| with
    Gaussian constant, slack 1+η): P = (2k−1)!!·(1+η)/z₀^{2k} by Markov.
- taper: ℓ = (1−α)·ε₀\*·λ₀²/4, λ₀ = e^{−z₀√(½ log log T)}, T = 2πN².
- onset N₀: the feasibility equality N·ℓ = 1, i.e.
  log N = log(4/((1−α)ε₀\*)) + 2z₀·√(½ log log 2πN²).
- R–S floor (must hold, not optimized): λ₀ ≥ 2c_G·(T/2π)^{−1/4}.
- z₀\* = smallest z passing the tail clause; α and (at tier M) the moment
  order k optimized numerically.

## 3. The tier table [computed; z0_opt.py]

| tier | η | α | z₀\* | log N₀ | T₀ | λ₀ | ℓ | λ₀/RS-floor |
|---|---|---|---|---|---|---|---|---|
| G | — | 0.44 | 3.13 | 16.6 | **10^15.2** | 1.5e−2 | 6.4e−8 | 30 |
| M2 | 0 | 0.97 | 22.97 | 84.8 | 10^74.5 | 1.0e−16 | 1.5e−37 | 131 |
| M4 | 0 | 0.82 | 6.58 | 28.1 | 10^25.2 | 8.5e−5 | 6.3e−13 | 53 |
| M6 | 0 | 0.69 | 4.73 | 21.9 | 10^19.8 | 1.5e−3 | 3.2e−10 | 41 |
| M8 | 0 | 0.59 | 4.17 | 19.9 | 10^18.1 | 3.4e−3 | 2.3e−9 | 35 |
| **M14** | 0 | 0.43 | **3.86** | **18.6** | **10^17.0** | 5.4e−3 | 8.1e−9 | 30 |
| M14 | 1 | 0.44 | 4.05 | 19.2 | 10^17.5 | 4.1e−3 | 4.6e−9 | 30 |

**The design triple at the moment tier: (z₀\*, ℓ\*, N₀\*) =
(3.86, 8.1×10⁻⁹, e^18.6), onset T₀ ~ 10^17** — with the flat-optimum
property: the M10–M16 plateau spans only 10^17.0–17.4, and a factor-2
slack in the moment constant (η = 1) costs 0.4 orders. The design is
INSENSITIVE to exactly which high moment is effectivized and to its
constant — only the ORDER band (≈ 10–16) matters.

## 4. The three readings

1. **Tier G is self-defeating at finite heights.** The BE-corrected tail
   Φ(−z₀) + δ_BE(T) needs δ_BE ≤ α·ε₀\* ≈ 10⁻³ at the onset; in-print
   rates are C·(log log T)^{−1/2}-shaped (§1), i.e. O(1)-grade at
   T ~ 10^15. The Gaussian tier certifies its own onset only at
   log log T ≳ (10³·C)² — never relevant. **The real currency at finite
   heights is effective MOMENTS**, and the table says: the 14th, give or
   take an order band.
2. **The R–S error never binds** (ratio ≥ 28 at every usable tier): the
   Gabcke-grade constant is a spectator in the design; it only needs to
   EXIST explicitly (§1 confirms).
3. **The meeting with the verified range is a constants problem.**
   Sensitivity: each factor 2 recovered in ε₀\* buys ≈ 1.1 orders in T₀
   (ε₀\* = 1/512 → 10^17.0; 1/256 → 10^15.9; 1/128 → 10^14.8;
   **1/64 → 10^13.7 ≈ the verified boundary**). C′ ≤ 32 and c_deck ≈ 1/16
   were deliberately generous (doc 69 §3); a factor 8 between them is the
   named target of the constants-promotion pass. So the no-gap statement
   ("verified below, designed tower above") needs exactly TWO finite
   deliverables, neither open-problem-shaped:
   - **(EFF-M14):** an effective 14th-moment (or any order in 10–16)
     bound E(log|ζ(½+it)|)^{2k} ≤ (2k−1)!!(½ log log T)^k(1+η), η ≤ 1,
     explicit T-threshold — Selberg's method with tracked constants;
   - **(TIGHT-C):** a factor ~8 in c_deck/C′ — placement bookkeeping.

## 5. What this opens

1. **(EFF-M14) is the new named object** — a fully finite, classically
   shaped effectivization project (Selberg's moment method, constants
   tracked, one fixed moment order). Its Lean shape is the same
   `SecondMoment.dpoly` substrate plus explicit prime sums — the first
   analytic-number-theory effectivization this lane would formalize.
2. The flat optimum (order band 10–16) means (EFF-M14) can pick whichever
   order minimizes ITS OWN constant bookkeeping — the design absorbs it.
3. The α-dial reads: at the optimum the budget splits ≈ 43% tail / 57%
   taper — nearly even. A future asymmetric design (taper with its own
   lognormal pricing instead of Chebyshev) attacks the 57% side without
   touching ζ-moments at all — a second, independent knob toward 10^13.
4. Every entry of the table moves ONLY through (ε₀\*, η, k): the spine is
   now literally arithmetic — any future improvement anywhere in the lane
   reprices the onset by rerunning one 80-line script.
