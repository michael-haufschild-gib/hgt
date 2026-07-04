# 42 — The Swap Has a Drift Engine: S″ Regime Map, and the Tip ≡ Lemma R

**Register: SEARCH → promotion draft** (tasks #145/#138/#142). Certification:
`computations/mwm` P-R14 (pre-registered, PASS). Supersedes the regime map of
doc 36 §7 / doc 37 §4; merges #145 into #139.

## 1. Audit finding: Theorem S′'s endpoint regime was VACUOUS on actual carriers

Regime 2 of doc 37 §4 requires M ≥ 56/δ. On a one-sided c/j window
(δ = c/(i+1), M = d−i−1 ≤ i by (F1)) this forces 56(i+1)/c ≤ i, i.e. **c > 56**.
For every model carrier c ≤ 56 the band is empty — the endpoint band had no
theorem coverage at all. (Doc 36 §7's earlier M ≥ 86/√δ was satisfiable; the
doc 37 renumbering — increment weakened from the phantom 0.417/δ to the honest
ΔG/(2W̄) — silently emptied it. Third audit catch of this arc.)

## 2. Lemma E″ — the drift-retained swap [PROVED HERE]

Add to the (F)-class:

- **(F8) lower drop regularity:** δ_j − δ_{j+1} ≥ c₈·δ_j² on the window
  (c/j fields: c₈ ≥ 1/(2c)).

**Lemma E″.** Assume (F2)–(F4), (F8), δ ≤ 1, C₀δ ≤ 1/2, s ∈ (0, δ/2). Then

> W_{i+1}(s) − W_i(s) ≥ c₈/(4δ) − 16/(M²δ²), hence ≥ 0 whenever
> **M ≥ 8/√(c₈·δ)**.

*Proof.* Lemma E′ (doc 36 §7): every ledger term of the swap is ≥ 0 except the
removed far-ahead R ≤ 16/(M²δ²). Retain ONE positive term, the k = 1 behind
drift: ¼[csch²((δ_{i+1}−s)/2) − csch²((δ_i−s)/2)] = ¼·(δ_i − δ_{i+1})·φ(ζ/2)
for some ζ ∈ (δ_{i+1}−s, δ_i−s) (MVT; d/dx[csch²(x/2)] = −φ(x/2)). Since
ζ ≤ δ_i ≤ (1+C₀δ)δ ≤ 1.5δ and φ is decreasing: φ(ζ/2) ≥ φ(0.75δ) ≥
(0.75δ)⁻³ − (0.75δ)⁻¹ ≥ 1.03/δ³ (δ ≤ 1). With (F8): drift ≥ c₈δ²·1.03/(4δ³)
≥ c₈/(4δ). ∎

Certification (P-R14): on c = 2 model fields the bound holds at every tested
(d, i, s) — and the TRUE swap is ≈ 3.3/δ (all drifts contribute; the measured
swap is positive even at M = 59 and M = 99, far outside the provable band).
Available sharpening, not needed now: retaining the full drift sum gives
swap ≥ κ/δ − 16/(M²δ²) with κ ≈ 3 (the ledger-integral of doc 40 §1 one
derivative up), band M ≳ 2.3/√δ.

## 3. Theorem S″ — one band instead of three regimes

**Theorem S″.** Assume (F1)–(F5), (F8), δ ≤ 1, C₀δ ≤ 1/4, and the march input
ΔG(s_i) ≥ 1 (Theorem B⁗ for i ≥ 200 on the C₀ ≤ 1/2 class; per-index value γᵢ
below). Then for every outer index with

> **M ≥ 8/√(c₈·δ)**   (non-vacuous: needs only (1−θ)d ≳ 8√(2c)·√i, i.e.
> all but the last ~O(√(cd)) indices; satisfiable for d ≥ 70)

the energy is strictly monotone: ΔS_i > 0.

*Proof.* ΔS = [W_{i+1}(s_{i+1}) − W_{i+1}(s_i)] + swap. The swap ≥ 0 by
Lemma E″ (its band contains Lemma D's M ≥ 2/√δ since c₈ ≤ 16). The first
bracket = ∫(−dW/ds) over the march step ≥ increment × response > 0: in the
endpoint band via Lemma D (M ≥ 2/√δ ✓), in the deep band via the pole response
(doc 36 §7, band-free). No swap-vs-response balance is needed anywhere —
E″ decouples them. ∎

The three-regime map with its two vacuous/fragile constants is replaced by the
single √δ-scale band. What survives regime-wise is only the response dichotomy
(deep/endpoint), which is band-free once the swap is nonnegative.

## 4. The residual tip IS Lemma R: #145 merges into #139

The uncovered indices are M < 8/√(c₈δ) — on c/j fields the last ~8√(2i) indices,
where the ahead field is m = M poles inside a span Mδ ≤ 8√(2cδ) → 0: a single
SHRINKING CLUSTER. This is precisely doc 34's cluster regime: doc 28 (L3) is its
m = O(1) case (trail saturation: s_near ≈ 2/(2d−M), W ~ 1/s² explodes upward —
"no balance needed where there is no competition"), and doc 25's tracking
clearance covers m ≤ 3. The (E-band) closure task is therefore NOT a new
analytic problem: it is **Lemma R (#139) at cluster size m ~ √d**, plus the
saturation endgame. One object, one task; #145 closes as merged. The consumer
side keeps its per-carrier check (margin-transition index inside the S″ band —
doc 36 §5(iii)), now with a 25×-smaller excluded set.

## 5. Chain status after this document (the push ledger)

(S-mono)/(AMP-mono) now stands as: **B⁗ (march, all C₀ ≤ 1/2) + S″ (energy
monotone, all but ~√d tip indices) + tip-cluster = Lemma R(m ~ √d) [#139] +
per-carrier (F1)–(F8) checks.** When #139's cluster bookkeeping lands (Lean
substrate already banked by the parallel stack), (AMP-mono)(iii) closes, and
with it (LEG)/#142 and #138; (SPUR-R) #135 then rests on doc 23's done bricks +
(CPI). The load-bearing wall beyond all of it is unchanged and now fully
exposed: the ARITHMETIC core — (DISC-fin)-unconditional, re-cut by #146 as: the
exact-FE truncation's off-line parity is even on dominated windows, provable
from the AFE/weld identity of the finite object itself (not from ζ). That is
where the next push lands: the weld identity as a proof engine, with doc 38's
(HANK-fin) minors as the instrument and the #146 coherence gradient as the
measured mechanism.
