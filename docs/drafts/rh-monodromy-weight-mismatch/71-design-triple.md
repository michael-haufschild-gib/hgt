# 71 — The Effectivization Pass: the Design Triple (z₀\*, ℓ\*, N₀\*) and the Tier Table

**Register: SEARCH** (task #16). §2–§4 are arithmetic on doc 69's first-pass
constants and doc 70's transfer — machine-computed (z0_opt.py, archived);
§1/§6 record the literature mining (delegate-sourced; spot-check citations
at promotion). This is the document where the Route C-direct spine becomes
a table of numbers with named knobs.

## 1. Mining record [two delegate literature agents, 2026-07-04; each item read from a fetched source unless flagged UNVERIFIED — spot-check at promotion]

**A. Selberg-CLT rate / moments of log|ζ| (agent 1).**
1. **Selberg 1992** "Old and new conjectures…" (Amalfi), Thm 2 (2.6); proof in
   **Tsang 1984** Princeton thesis. Verbatim via Ivić (arXiv:math/0312097 eq 5):
   meas{0<t≤T : |ζ(½+it)| ≤ e^{y√(½loglogT)}} = Φ(y)·T + O(T(logloglogT)²/√(loglogT)),
   **uniform in y, unconditional**. [rate] — the uniform-in-y CLT: this is the
   Tier-G input, with the caveat in §6.
2. **Roberts 2022/24** (arXiv:2212.01411): Dudley distance
   ≤ C(logloglogT)²/√(loglogT) for log|ζ|/√(½loglogT), uni+multivariate,
   unconditional. [rate] — same rate SHAPE, C not numerized.
3. **Tsang 1986** (Acta Arith. 46) Thm 4 (verbatim via Dobner arXiv:2101.01747):
   ∫_T^{2T}(S(t+h)−S(t))^{2k}dt = A_k T(log(2+h logT))^k + O(T(ck)^k(…)),
   A_k=(2k)!/(2^k π^{2k} k!), all k≥1, **c absolute but NOT numerized**. [moments]
   — the even-moment method exists for S(t); the constant is not explicit.
4. **Simonič–Trudgian–Turnage-Butterbaugh 2020** (arXiv:2010.10675): fully
   explicit numeric 2nd+4th moment bounds for S(t+h)−S(t), unconditional
   (exact constants UNVERIFIED — body not fetched). [moments]
5. **Ivić 2002** (arXiv:math/0312097) Thm 1: meas{|ζ(½+it)| ≤ c} = T/2 +
   O(T(logloglogT)²/√(loglogT)), any fixed c>0, unconditional. [small-values]
6. **Bui–Florea 2024** (arXiv:2302.07226): negative moments — **CONDITIONAL (RH)**,
   shift a ≳ 1/logT. [small-values] — not usable unconditionally.
> **No in-print fully numeric constant for ∫(log|ζ(½+it)|)^{2k}dt, any k≥1.**

**B. Riemann–Siegel constant / verified height (agent 2).**
7. **Hiary–Patel–Yang 2024** (arXiv:2207.02366) Lem 2.1, verbatim: for t≥200,
   n₁=⌊√(t/2π)⌋, |ζ(½+it)| ≤ 2Σ_{n≤n₁}n^{−1/2} + R(t),
   **R(t) ≤ 1.48 t^{−1/4} + 0.127 t^{−3/4}**. [RS-bare]
8. **Revers 2026** (arXiv:2602.05614) Lem 2.2: bare-sum remainder
   ≤ cos(π/8)(2π)^{1/4} t^{−1/4}+0.127 t^{−3/4} ≈ 1.463 t^{−1/4}+0.127 t^{−3/4},
   t≥200. [RS-bare]
9. **Gabcke 1979** (DOI 10.53846/goediss-5113), quoted verbatim via Kuznetsov
   (arXiv:2312.03261): with the C₀ term retained, **|R| < 0.127 t^{−3/4}, t≥200**;
   with C₀+C₁, |R| ≤ 0.053 t^{−5/4}. Thesis PDF itself UNVERIFIED (403-blocked).
   [RS-C0]
10. **Platt–Trudgian 2021** (arXiv:2004.09765) Thm 1, verbatim: RH verified by
    **interval arithmetic up to height 3 000 175 332 800 ≈ 3·10¹²** (first
    12 363 153 437 138 zeros). Gourdon 2004 (2.44·10¹² / "10¹³ zeros") is
    unpublished, rounding control unclear ⇒ **not interval-certified**. Nothing
    rigorously higher through the Feb-2026 searches. [verified-height]

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
   (ε₀\* = 1/512 → 10^17.0; 1/128 → 10^14.8; 1/32 → 10^12.6). Against the
   RIGOROUS verified boundary 3·10¹² = 10^12.48 (§6(iii); NOT Gourdon's
   uncertified 10¹³), closing the M14-tier gap needs **ε₀\* ≈ 1/32, a
   factor ~16** in c_deck/C′ (revised up from doc 69 §4's factor 8, which
   read the unusable Tier-G row against the optimistic height). C′ ≤ 32
   and c_deck ≈ 1/16 were deliberately generous (doc 69 §3). So the no-gap
   statement ("verified below, designed tower above") needs exactly TWO
   finite deliverables, neither open-problem-shaped:
   - **(EFF-M14):** an effective 14th-moment (or any order in 10–16)
     bound E(log|ζ(½+it)|)^{2k} ≤ (2k−1)!!(½ log log T)^k(1+η), η ≤ 1,
     explicit T-threshold — Selberg's method with tracked constants
     [confirmed NOT in print, §6(i)];
   - **(TIGHT-C):** a factor ~16 in c_deck/C′ — placement bookkeeping.

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

## 6. Verdict of the mining pass — three corrections the literature forces

The mining did not confirm the first-pass §4 picture; it tightened it on
three counts. Recording all three with the prominence of the wins (the
banned move is to bury the correction).

**(i) (EFF-M14) is genuinely NOT in print — the task stands, unreduced.**
The strongest even-moment technology found is Tsang 1986's
∫(S(t+h)−S(t))^{2k} formula (item 3) — for the ARGUMENT S(t)=Im, with an
absolute-but-unnumerized constant, and for the increment not the value.
No fully numeric bound on ∫(log|ζ(½+it)|)^{2k} exists for any k≥1 (agent 1's
closing line). So (EFF-M14) does not reduce to a citation; it is a real
effectivization, in the exact shape §4 named. The novelty gate passes on
the narrow ground that the numeric constant is the new content — the method
(Selberg/Tsang moments) is classical.

**(ii) Tier G is not merely "self-defeating asymptotically" — its error is
O(1)-grade AT the onset, and its constant is unnumerized.** The uniform-in-y
Selberg CLT (item 1, Selberg 1992 / Tsang) is exactly
meas{log|ζ| ≤ y√(½loglogT)} = Φ(y)T + O(T·(logloglogT)²/√(loglogT)). At the
Tier-G onset T ~ 10^15 (loglogT ≈ 3.5, logloglogT ≈ 1.25) the error SHAPE
is (1.25)²/√3.5 ≈ 0.84 — O(1)-grade, ~400× the main term Φ(−z₀) ≈ 1/512 we
need to bound — and its constant C (items 1,2) is not numeric anywhere in
print. **Tier G cannot deliver a 1/512 tail at any finite height, for two
independent reasons.** This upgrades §4 reading 1 from a suspicion to a
literature fact: the finite-height design has NO Gaussian option; the moment
tier is forced, not merely preferred.

**(iii) The verified-range meeting is farther than doc 69 §4 claimed — the
rigorous boundary is 3·10¹² (10^12.48), not 10^13.** Platt–Trudgian 2021
(item 10) is the highest INTERVAL-ARITHMETIC-certified height; Gourdon's
10^13 is unpublished and not rounding-controlled, so it cannot anchor a "no
gap" statement. Recomputing the sensitivity against 10^12.48 with the now-
NUMERIC R–S floor (items 7–9; see (iv)):

| ε₀\* | Tier-G onset (illusory) | Tier-M14 onset | M14 gap to 3·10¹² |
|---|---|---|---|
| 1/512 | 10^15.2 | 10^17.0 | +4.5 |
| 1/128 | 10^12.8 | 10^14.8 | +2.3 |
| 1/64 | 10^11.6 | 10^13.7 | +1.2 |
| 1/32 | 10^10.3 | 10^12.6 | +0.1 |

So closing the gap on the (correct) finite-height M14 tier needs
**ε₀\* ≈ 1/32 — a factor ~16 in c_deck/C′, not the factor 8 of doc 69 §4.**
The honest no-gap statement: (EFF-M14) **and** a 16× constants improvement.
Both finite, neither open-problem-shaped, but the earlier "10^13, no gap"
coincidence was an artifact of (a) the optimistic Gourdon height and
(b) reading the Tier-G row, which is unusable at finite heights. **Doc 69 §4
is corrected accordingly.**

**(iv) One clean win: the R–S floor constant is now numeric, and it is an
even softer spectator than assumed.** Doc 70 §6's [CHECK Gabcke] resolves:
|ζ(½+it) − g_N(½+it)| ≤ 1.463 t^{−1/4} + 0.127 t^{−3/4} for t ≥ 200 (bare
main sum, Hiary–Patel–Yang / Revers, items 7–8), sharpening to
|R| < 0.127 t^{−3/4} with the C₀ correction (Gabcke, item 9). At the M14
optimum the ratio λ₀/floor is **≈ 65** (recomputed with the numeric
constant — larger than the earlier crude 30 because the t^{−1/4} decay wins
at these heights). The R–S error is confirmed a spectator with two orders of
headroom; doc 70 §1's "O(t^{−1/4})" now carries an explicit constant.

**Net.** The spine is unchanged and still arithmetic; the numbers moved:
finite-height design is moment-forced (no Gaussian escape), the meeting
target is 3·10¹² not 10¹³, and it needs (EFF-M14) plus 16× in the placement
constants. The R–S input is fully pinned. Task #16's residue is now exactly
those two finite deliverables, with (EFF-M14) the analytic one.
