# 73 — The Certified-Tail Calculus: (EFF-M4/M10) Closed Exactly, the Christoffel Upgrade, and (TAIL-6) Priced to a Factor

**Register: SEARCH** (task #18). §1–§3 [PROVED-sketch + EXACT numerics,
archived effm_moments.py / christoffel.out]; §4 the (EFF-E) demand made
exact; §5 the (TAIL-6) adjudication. Everything numeric below is exact
arithmetic (rational cumulants, deterministic sums), not simulation.

## 1. (EFF-M4/M10) CLOSED — the exact sub-Gaussian ladder [PROVED-sketch]

Object: ReP_X(t) = Σ_{p≤X} p^{−1/2}cos(t log p), X = T^{1/5} = 313 at
T = 3·10^12 (64 primes; support bound |ReP| ≤ Σp^{−1/2} = 8.401).

**(a) Exact independent-phase moments.** Single-cosine cumulants (exact,
from the log J₀ series): κ₂ = 1/2, κ₄ = −3/8, κ₆ = 5/4, κ₈ = −1155/128,
κ₁₀ = 3591/32, κ₁₂ = −546315/256. Totals κ_{2j}(ReP) = κ_{2j}(cos)·Σp^{−j}.
Moment ladder (σ² = s₁/2 = 1.0097):

| n | m_n exact | Gaussian | ratio |
|---|---|---|---|
| 2 | 1.0097 | 1.010 | 1.000 |
| 4 | 2.8888 | 3.059 | **0.945** |
| 6 | 13.092 | 15.44 | **0.848** |
| 8 | 79.335 | 109.1 | **0.727** |
| 10 | 592.88 | 991.6 | **0.598** |
| 12 | 5212.4 | 11013 | **0.473** |

**The prime sum is SUB-Gaussian at every order** — κ₄ < 0: prime
collisions LIGHTEN the tails. Doc 72 §2's Wall 2 is half-reversed: the
corruption condition s₁ ≫ k²s₂ governs the ratio → 1, but for UPPER tail
bounds the exact ladder is strictly below Gaussian. (m₄ closed form
(3/4)s₁² − (3/8)s₂ = 2.8888 ✓ cross-checked.)

**(b) The t-transfer at DOUBLED degree — spacing-MV.** Doc 72 §2's budget
X^{2k} ≤ T used length-based MV; the actual Montgomery–Vaughan theorem is
per-frequency: error Σ|c_N|²·O\*(3π/δ_N) with δ_N the gap at log N. For
distinct products a ≠ b of ≤ k primes: |log(a/b)| ≥ 1/(2max(a,b)), and the
1/N in |c_N|² = r_k(N)²/N cancels the δ_N^{−1} ~ N growth: relative
transfer error ≈ 6π·(#k-tuples)/U = 6π·64^k/T — at k = 5: **2·10^{-4}**.
So the certified moment order at (T, X) = (3e12, T^{1/5}) is
**2k ≤ 2·logT/logX = 10**, twice doc 72's naive budget. (k = 6 fails:
relative error ~0.5 — deg 12 is model-only.) Mixed/bilinear terms via the
MV Hilbert inequality on the merged frequency set; [CHECK at promotion:
MV 1974 exact constant 3π/2 vs 3π].

## 2. The Chernoff ceiling and the exponential-truncation wall

Exact independent-model Chernoff (min_v e^{−va}Π I₀(v/√p), computable to
any precision): P(ReP ≤ −3.1) ≤ 4.3e−3; **−4.1 ≤ 2.5e−5; −5.1 ≤ 7.7e−9;
−6.1 ≤ 2.3e−14** — near the support edge the true tail collapses far
below Gaussian. But the CERTIFIED Chernoff must truncate e^{−vReP} at the
degree budget: remainder ≤ 3.4e−4 at (v, J) = (1.0, 10) and explodes for
v ≥ 1.5 — Chernoff's optimal v\* (4–16) is unreachable. Verdict: within
the degree budget, ladder methods beat truncated-Chernoff.

## 3. The Christoffel–Markov upgrade [the new instrument]

Single-moment Markov wastes the ladder. The sharp one-sided bound of the
classical moment problem: P(X ≤ −a) ≤ 1/K_n(−a), K_n(x) = Σ_{j≤n}p_j(x)²
with p_j the orthonormal polynomials of the moment sequence — computable
by one Cholesky of the Hankel matrix of the EXACT ladder. Certified tails
(deg 10 = the transfer-legal maximum; deg 12 shown model-only):

| a | deg 6 | deg 8 | **deg 10** | (deg 12) | Gaussian truth |
|---|---|---|---|---|---|
| 3.6 | 2.75e−3 | 9.95e−4 | **5.03e−4** | 3.44e−4 | 1.70e−4 |
| 4.1 | 1.21e−3 | 3.09e−4 | **1.06e−4** | 4.71e−5 | 2.25e−5 |
| 4.6 | 5.86e−4 | 1.12e−4 | **2.79e−5** | 8.67e−6 | 2.35e−6 |
| 5.1 | 3.08e−4 | 4.60e−5 | **8.70e−6** | 2.02e−6 | 1.93e−7 |

At z ≈ 3.5–4 the deg-10 Christoffel bound loses only ×3–12 to the
Gaussian truth (single-m₁₀ Markov loses ×30–60). Rule confirmed: a
2n-moment ladder certifies near-Gaussian decay out to z ≈ √(2n); z = 3–4
is exactly within reach of deg 10. **The prime-chunk of (TAIL-6) is
certified: meas{ReP_X ≤ −4.1}/U ≤ 1.06e−4·(1+2e−4) — under the 2.4e−4
budget with threshold s_B = 2.0 left for the E-chunk.** Lean-shape: a
finite-dimensional statement (Hankel PSD + polynomial evaluation) — a
clean future brick.

## 4. (EFF-E) — the demand made exact; the variance map

Where log|ζ(½+it)|'s variance σ² = ½loglogT + 0.65 = 2.33 lives at
T = 3e12, with each block's certified degree:

| block | σ²_j | certified degree |
|---|---|---|
| p ≤ 313 (= T^{1/5}) | 1.010 | 10 (§1) |
| 313 < p ≤ 10⁴ | 0.235 | 6 |
| 10⁴ < p ≤ 10⁶ | 0.205 | 4 |
| 10⁶ < p ≤ √T | 0.22 | 2–3 (Chebyshev-grade) |
| smooth residual + offset 0.65 | ≤ 0.65 | 2 — **unless thin** |

Two structural facts found in the assembly arithmetic:
- **The joint degree budget is shared:** mixed moments across blocks obey
  Σ_j 2k_j·logY_j ≤ 2logT — block degrees trade off; one cannot run deg-10
  on the small block AND deg-6 on the mid block inside one mixed moment.
  Union-splitting (thresholds s_j, Σs_j = A) preserves the Gaussian
  exponent A²/2Σσ² only if every block is certified at Gaussian grade at
  its own s_j; the blocks capped at Chebyshev are the leak.
- **The +0.65 offset is plausibly thin-zero mass** [CONJECTURE, decisive
  and measurable]: the dip spikes of log|Z| contribute O(1) to m₂; if the
  offset is mostly dips, the THICK-part variance is prime-only (≈ 1.7) and
  the union stack tightens by e^{ΔA²/2σ²}-grade. Next probe: recompute m₂
  of log|Z| excluding e^{−1}-radius dip neighborhoods — a one-line change
  to probe_floor.py.

(EFF-E) as a proof task is now: effective deg-6 and deg-4 ladders for the
two mid blocks (same §1 machinery — exact cumulants + spacing-MV, nothing
new), plus the Selberg-decomposition residual with its variance LOCATED
(thin vs smooth). Classical-shaped throughout.

## 5. (TAIL-6) adjudicated: certified ~1e−3, target 2.4e−4 — gap = a factor 4–8, all in named constants

Assembled certified stack at A = 6.1 (Christoffel per block, optimal
threshold allocation, E-chunk ASSUMING §4's mid-block ladders): lands at
**~1e−3-grade**. Two structural limits say this is near-optimal for the
method class: the union-vs-joint loss (×10–30 vs the true joint tail
3.2e−5) and the shared degree budget (§4). Against the budget:
tail ≤ ε₀\*/(thickness 8) = 2.4e−4. **The remaining factor 4–8 is entirely
in named constants:** thickness 8 → ~3 (the Fubini–Markov window constant
was crude), ε₀\* = 1/512 → 1/256 (doc 69's C′ ≤ 32 was deliberately
generous), allocation tuning. Tonight's movement for perspective: naive
k=2 Markov stood at 5.4e−2; the exact-ladder + spacing-MV + Christoffel
stack stands at ~1e−3 — a factor ~50, all machine-checkable arithmetic.
The only genuinely open direction beyond constants: non-moment
certification (effective equidistribution of the 64-cosine block — the
one method class not priced by the degree budget).

## 6. What this opens

1. **The certified-tail calculus is now a reusable exact instrument**:
   rational cumulant ladders + spacing-MV transfer + Christoffel bounds —
   applicable to ANY Dirichlet-polynomial tail question in the lane (the
   taper polynomials, the deck margins, the mid blocks), replacing every
   crude Chebyshev in docs 56–72 at a factor 5–50 gain.
2. The offset-location probe (§4) is the next decisive measurement: if
   the 0.65 is thin, the thick-part variance drops to prime-only and the
   stack may reach ~3e−4 BEFORE any constant harvest.
3. The harvest list with numbers: thickness constant (Lean-refinable in
   ThickDips.lean — the 8 = 2×4 was two crude Vitali steps), ε₀\* audit
   (C′'s dip-layer constants under the χ′-terms), allocation optimizer
   (one page).
4. Lean target: the Christoffel consumable — `hankel_psd_tail_bound`:
   from a PSD Hankel matrix of certified moments, the 1/K_n(−a) tail
   bound. Finite-dimensional linear algebra; would machine-check the
   entire §3 table.
