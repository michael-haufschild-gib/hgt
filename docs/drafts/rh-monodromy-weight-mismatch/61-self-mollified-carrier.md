# 61 — The Self-Mollified Carrier: E–K Design Meets Route B

**Register: SEARCH** (follow-on to doc 55 §8's chirality discovery + E–K lead;
composes it with doc 56–58's Route B and doc 57's budget tiers). One mechanism
conjecture, one design principle, one calibration correction, pre-registered
probe P-SM. Session: mollified-dip.

## 1. The observation doc 55 §8 hands to Route B [REDUCTION]

A monotone-decreasing log-scale carrier with frozen-term share
ς² := W(0)²/K_W(½) bounded below is **self-mollified**:

> F_W(½+it)/W(0) = 1 + G_W(t),  E|G_W|² = 1/ς² − 1 = O(1).

This is exactly the normal form of doc 56's P = 1 + G — with NO mollifier:
no Möbius weights, no BV taper, no zeros-of-M pollution, no length inflation
(the object stays length N). Consequences, immediate:

- The dip lemma, the counting bridge, and the kernel consumption apply
  VERBATIM: `MollifiedDip.lean` (`dip_measure_lower`,
  `separated_dips_count_le`, `sliverCount_le_of_kernel`) was written for an
  arbitrary continuous field — it consumes the designed carrier unchanged.
- The kernel becomes **(SM-bdd)**: meas{t : |1 + G_W| ≤ r} ≤ C_W·r²·U — same
  class as (K-bdd), same ergodic×transfer split (doc 58 §4), but now the
  counted zeros are the CARRIER's own sliver zeros: the bound feeds
  (CR-density)-for-the-tower directly.

## 2. The chirality mechanism [CONJECTURE, mechanistic, testable]

The GAF-blind chirality of doc 55 §8.4 is the **mean-share gradient**: the
frozen term contributes a constant mean m = W(0) while the fluctuation
variance K_W(σ) − W(0)² DECREASES in σ (all moving terms carry n^{−2σ}).
So the signal-to-noise m²/(K_W(σ) − m²) grows rightward, and the
GAF-with-mean intensity ρ(σ) = (1/4π)Δ[log K + h(|m|²/K)] carries an
e^{−m²/K}-type suppression that is CHIRAL — strong on the right, absent on
the left. Predictions (pre-registered, §5): suppression monotone in ς;
chirality → 0 as ς → 0; ramp's LEFT-chirality is the mirror case (the
effective frozen term sits at the far edge, dominant leftward).

## 3. Calibration of doc 55 §8.5 — what E–K design can and cannot sidestep

Attack-as-false on "sidesteps the small-ball frontier entirely": the
triangle-inequality (elementary Eneström–Kakeya) zero-free region
W(0) > Σ_{n≥2} W(y_n) n^{−σ} begins only where the L¹ tail drops below the
frozen term — σ ≈ 1, far right of the sliver. **At sliver scale the statement
remains kernel-class.** What the design genuinely buys, in doc 57's currency:

1. **Layer removal:** no mollifier — (SM-bdd) is about the carrier itself.
2. **Constant collapse:** the density of G_W at the target point −1 carries
   the e^{−m²/(K−m²)}-grade factor: the (SM-bdd) CONSTANT is designed small
   (measured ×8–13 at ς ≈ 0.73, N = 40). Doc 57 Tier 2 needs only an explicit
   (c₀, ε₀) below the deck margin — a small designed constant is exactly the
   right shape; ε(c) → 0 is not required.
3. **Smoothed-AFE bonus:** a damped-edge exact-FE completion
   Z_W = Σ w_n n^{−s} + χ(s)·Σ w_n n^{−(1−s)} is line-real and exact-FE by
   construction, and smoothed AFEs carry SMALLER error terms E_W(T) — the
   self-domination clause (doc 43) gets easier at the same time.

## 4. The tower-compatibility question (doc 55 §8.5(ii)), with a proposed cut

Log-scale weights W(log n/log N) rescale every coefficient at every level —
the one-term-per-epoch cascade recursion (docs 44–54) breaks. Multiplicative-
scale weights w(n/N) preserve the recursion but do NOT suppress (doc 55 §8.2:
μ → Uniform, Var pinned at 1/12). Proposed middle cut [CONJECTURE]:
**dyadic-block-static weights** — fix W per block N ∈ [N₀, N₀^{1+δ}] at
y = log n/log N₀; within a block the cascade adds terms one per epoch with
entry amplitude W(y_entry) ≈ W(1) ≈ 0: entries are DAMPED at birth, which is
precisely where births live (the truncation edge). Block boundaries pay a
reweighting transport (parity coherence between consecutive carriers at the
same height — the doc 43 §3 RS-tower logic, at |ΔZ| = O(edge mass) grade).
If the block transport closes, the weighted tower inherits the whole walk
tier and the birth layer is design-suppressed.

## 5. Pre-registered probe P-SM (mean-share sweep; runpod; NOT run at write time)

Carriers W²_α(y) ∝ (1−y)^α, α ∈ {0, 1, 2, 4} (α = 0 sharp; α = 1 iramp-class),
N = 40, T = 2π(N+¼)², U = 60, CCW winding, both sides of the line at
c ∈ {1, 2}. Registered:

- **P-SM1 (prior 0.8):** right-sliver counts strictly decreasing in α.
- **P-SM2 (prior 0.55):** right-count suppression vs sharp within a factor 3
  of exp(−m²/(K−m²)) evaluated at ½ (the mean-share law, crude form).
- **P-SM3 (prior 0.7):** two-sided totals track Var_μ = the §8.1 law
  (Var(μ_α) computable in closed form).
- **FALSIFIER:** right-counts non-monotone in α, or suppression uncorrelated
  with ς — kills §2's mechanism; the chirality would then sit in phase
  structure, not mean-share, and §3(2)'s constant-collapse claim retracts.

## 6. What this opens

1. (SM-bdd) at designed ς joins doc 58's kernel program with a working margin:
   the needed bound has a small right-hand side by design — attack the
   ergodic half (K-bdd-∞) FIRST at large mean-share, where the co-area
   argument has the frozen term as a fixed anchor (the two-phase submersion
   never degenerates against a dominant mean — the induction may TERMINATE
   at depth 1 for ς close to 1).
2. The variational problem of doc 55 §8.3(2), restated with the right
   objective: maximize provable right-sliver suppression (m²/K and its
   σ-gradient) subject to exact-FE completion + block-transport fidelity —
   the design space is the block-static weights of §4.
3. If P-SM confirms §2, the chirality becomes an INSTRUMENT: the deterministic
   mean-share is a dial the GAF cannot see — measuring the deviation of ζ-side
   window statistics from GAF-with-mean predictions probes exactly the
   Steinhaus-vs-Gaussian gap that Route A needs (doc 55 §6.4) — the two routes
   converge on the same experiment from opposite sides.

## 7. P-SM adjudication [MEASURED — meanshare_probe.py, N = 40, U = 240, CCW winding, 0 bad contours]

| α | share ς² | R(c=1) | R(c=2) | L(c=1) | L(c=2) |
|---|---|---|---|---|---|
| 0 | 0.234 | 44 | 50 | 56 | 67 |
| 1 | 0.410 | 8 | 8 | 37 | 77 |
| 2 | 0.542 | **0** | **0** | 11 | 47 |
| 4 | 0.720 | **0** | **0** | 0 | 5 |

- **P-SM1 PASS, decisively:** right-sliver counts 50 → 8 → 0 → 0, strictly
  monotone in α — and the right strip is **exactly empty from mean-share
  ≈ 0.54** over 240 units, while the left side still carries 47 zeros at the
  same α. The chirality is total, not statistical, above a threshold
  ς* ∈ (0.41, 0.54] at N = 40.
- **P-SM2 FAILS AS REGISTERED — in the strong direction:** measured
  suppression (0.17, 0.01, 0.01) beats the crude one-point law
  e^{−m²/(K−m²)} (0.68, 0.42, 0.10) by 4–50×. The mechanism's direction is
  confirmed; the pointwise density factor is the wrong quantitative form —
  the intensity is governed by the σ-GRADIENT of the tilted profile
  (doc 55 §8.5(iii)'s finite-N GAF-with-mean), which is much stronger.
- **P-SM3 PASS for α ≤ 2** (two-sided totals/Var_μ: 1404, 1530, 1253 —
  within ±20%), **breaks at α = 4** (5 vs ~29): at large mean-share the
  carrier exits the GAF regime entirely — the near-line neighborhood empties
  on BOTH sides (mean dominance approaching, well before the σ ≈ 1 triangle
  bound).

**What the emptiness hands the proof program.** At ς² = 0.542 the rest-field
rms is still 0.92·m — pointwise mean-dominance FAILS on the line (the left
side shows the near-hits happen) — yet the right sliver is empty: the zeros
form where the variance is larger, i.e. left. The provability handle for this
is the Abel-mixture structure: A_n = W(y_n) positive decreasing gives
F_W = Σ_n (A_n − A_{n+1})·Z_n, a POSITIVE MIXTURE of the sharp partial sums
Z_n — an Eneström–Kakeya-type representation native to Turán's partial-sum
program. Typed target:

> **(EK-sliver) [OPEN, new]:** for positive decreasing log-scale weights with
> ς² ≥ ς*², the weighted matched sum F_W has NO zeros in
> 0 < σ − ½ ≤ c/log N, γ ∈ [T, T+U] — creation_rate K = 0 for the designed
> tower, `midCentral_empty` grade, no kernel needed.

Design tension for the variational step: α = 4 kills both sides but likely
AFE fidelity too; the working window is ς² ≈ 0.5–0.6 — right-empty while the
completion stays domination-grade. That constant ς* is now the single most
valuable number in the lane: measure its N-dependence next (if ς*(N) is
bounded away from 1, Route C closes creation with a fixed design).
