# 39 — The Reversal Is an Edge Integral: C₀² Was the Wrong Axis

**Register: SEARCH** (task #147; supersedes the ARCHITECTURE of doc 37 Lemma H —
its statements stay true, its parametrization is replaced). Certification:
`computations/mwm/reversal_truth.py` (pre-registered; identity validated against
the machine-checked `ledger_regroup` to 4·10⁻²⁷ — the first run's sign slip was
caught by exactly that check).

## 1. What the certification measured

True reversal Σ_k (loss_k − gain_k)⁺ of the corrected ledger on c/j model fields
(δ_j = c/(j+1), C₀ ≈ 1/c), grid c ∈ {2,…,8}, d ≤ 2500, i/d ∈ [0.5, 0.85],
s/δ ∈ [0.10, 0.49]:

- **P-R1/P-R2 PASS**: max reversal at c = 2 (the actual-carrier constant C₀ ≈ ½)
  is **0.21–0.23**, against the march cushion 2. Doc 37's bound at C₀ = ½ (50) is
  off the truth by ~250×; even the best honest termwise refold (O(C₀), §2) is off
  by ~10×. The bulk march is true with margin ≥ 1.76 at every C₀ ≤ ½.
- **P-R3 FAIL — the load-bearing surprise**: the reversal does NOT scale with C₀
  (log–log slope −0.7 at fixed i/d). The C₀² axis of doc 37 Lemma H measures the
  wrong variable.
- **P-R5 PASS**: at the (F1) edge i = ⌈(d−1)/2⌉ the reversal SATURATES in d:
  0.181 / 0.211 / 0.224 / 0.230 at d = 150 / 400 / 1000 / 2500 (limit ≈ 0.235).
- **P-R6 PASS**: sharp monotone decay in θ = i/d: 0.21, 0.16, 0.10, 0.047, 0.018,
  0.002 at θ = 0.50, 0.52, 0.55, 0.60, 0.66, 0.75 (d = 400, c = 2). Max always at
  the small-s end (deep band), where the k*-protection of Lemma G vanishes.

## 2. Why termwise C₀²-folding was doomed — and unnecessary

Any termwise bound multiplies the (F4) half-gap position floor by the maximal-drop
mismatch. But those two worst cases consume the SAME budget: the ahead drops sum
to at most δ/2 (F4), so positions can halve only after the drop budget is spent.
Stacking them multiplicatively is what inflates 0.23 to 50. (Checked before
writing: doc 37's per-term constant 43/(kδ)³ is the legitimate (F4) floor
(16/3)/(kδ/2)³, NOT a variable bug — the fat is architectural, not arithmetic.)

## 3. The true mechanism [ANALYSIS + measured]

In the continuum frame ξ = l/i of a c/j field, behind positions are
u(ξ) ≈ −c·log(1−ξ) − s (log-INFINITE: the behind field stretches without bound)
while ahead positions are v(ξ) ≈ c·log(1+ξ) + s (log-COMPACT: ≤ c·log 2 ≈ 1.4 at
the edge). Matched pairs therefore split:

- **Near range**: per-pair loss < gain — governed by the elementary profile
  inequality (1+ξ)log(1+ξ) ≥ (1−ξ)|log(1−ξ)| (ξ ∈ (0,1)), which makes the loss
  weight-argument larger and the loss increment smaller.
- **Far range**: the gain weight w(u(ξ)) dies exponentially while the loss weight
  w(v(ξ)) stays bounded — far pairs are pure loss. The reversal is the AHEAD-TAIL
  WEIGHT INTEGRAL
  > rev ≈ (1/i)·∫ e^{−y/c} w(y) dy over the matched-onset tail, w = ½csch²(y/2),
  an edge quantity: saturating in d, decaying in θ = i/d, concentrated at small s
  — exactly the measured profile. C₀ never enters as the control variable.

## 4. The re-cut (Lemma H‡ architecture) [OPEN — two elementary lemmas]

> **Lemma H‡ (shape):** on (F)-fields with log-convex c/j-type profile,
> Σ_k (loss_k − gain_k)⁺ ≤ B(θ), with B(1/2) ≤ 1/4 and B decaying in θ.

Provable route, split at the far-pair onset:
1. **(REV-near)**: per-pair domination loss_k ≤ gain_k on the near range, from the
   profile inequality above + (F5). Elementary (Taylor/convexity), model-class.
2. **(REV-far)**: the far losses bounded by the ahead-tail integral
   Σ_{l far} d_{i+l}·w(v_l) ≤ (1/i)·∫ e^{−y/c}w(y)dy + near-cutoff term — an
   explicit one-dimensional estimate, no pairing at all.

With H‡: **Theorem B⁗ [target]: ΔG(s_i) ≥ 2 − B(θ) ≥ 7/4 for ALL C₀ ≤ 1/2** on
the model class — the bulk march holds for the ACTUAL carriers on theorem legs;
doc 37's (M″) threshold C₀ ≤ 1/10 and its "per-index evaluation below c = 10"
delegation are superseded. The per-carrier protocol's march clause shrinks to:
verify (F)-hypotheses + the two H‡ lemma inputs on the window (B(θ) is universal).

## 5. What this opens

1. Prove (REV-near) and (REV-far) — two contained elementary estimates; then
   Theorem B⁗ replaces B″ and the (S-mono) arc is theorem-complete in the bulk at
   actual-carrier constants (residuals: (E-band) #145 tip, Lemma R #139
   multiplicity).
2. The saturation limit B(1/2) ≈ 0.235 is a computable universal constant of the
   c/j class (the edge integral in closed form — likely elementary in
   exponential-integral terms). Worth one closed-form pass.
3. The same edge-integral lens should re-price the (E-band): the tip is where the
   ahead field is SHORT — the same ahead-tail integral with few terms — suggesting
   (L3)'s extension and H‡'s far bound are one object (#145 route 3).
4. Lean: the H‡ split is finite-sum + one 1-D integral bound — formalizable with
   the LedgerConvex algebra already banked (queue after paper proof).
