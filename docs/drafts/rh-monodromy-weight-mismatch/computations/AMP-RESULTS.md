# (AMP) margin landscape and crossing structure — results (task #135, doc 24)

Scripts: `computations/mwm/amp_margin_landscape.py`, `amp_crossing_probe.py` (pod).
At every critical point c of A_d = J^d_g: margin(c) := q_d(c)/(c⁴·ℰ(c)),
ℰ(c) = Σ_k (c−α_k)^{−2} (exact: −A″/A at extrema), q_d(c) = |τ|² − 2adc + d(d−1)c².
Models: (1) g = cos√x at 0, τ = 10+4i (q_d pos.-definite iff d > 7.25);
(2) recentered-60 carrier, τ = 8i (a = 0, no dip).

## Run 1 — margin landscape (pre-registered PO: zero failures)
**PO REFUTED — load-bearing.** Failures grow ~0.4·d (16 of 39 extrema at d = 40),
margin_min → ≈ 0.28, all failures at the FAR extrema (c ~ 14d). Sign transfer as
"copy everywhere" is false: at the far end the curvature term wins permanently.

## The flip discovery (analysis forced by PO's refutation)
Strict failure FORCES the sign: J(c) = q_d(c)A(c) + c⁴A″(c) with c⁴|A″| > q|A| has
sign(J(c)) = sign(A″(c)) = −sign(A(c)) — still alternating along consecutive
flipped extrema. Sign changes are lost only at COPY↔FLIP transitions:

> **Counting lemma (corrected): Z_c(J^d_{Pg}) ≤ 2 + T**, T = number of crossings of
> margin = 1 along the ordered critical points. T = 1 + evenness ⟹ Z_c ≤ 2.

(This also corrects doc 23 §3's provisional bound "≤ 2·#failures".)

## Run 2 — crossing structure (pre-registered PQ: T = 1; PR: outer monotone decrease)
**PQ PASS / PR PASS:** T = 1 for ALL d ≥ 10 (model 1) and ALL d ≥ 4 (model 2);
T_neg = 0; outer-half monotone violations = 0 in every case. Sole exception:
model 1, d = 8: T = 2 with the extra crossing in the dip region c ≈ a/(d−1) — the
q_d-definiteness threshold (d > 7.25) barely cleared; resolves by d = 10, matching
run 1's measured visibility threshold (doc 20).

## Verdict
The margin sequence is empirically unimodal-through-1: huge in the tracking regime
(1/d² curvature decay), monotone decreasing through ONE crossing into a permanent
far flip block. (SPUR-R) closes modulo one named kernel:

> **(AMP-mono)**: the margin sequence crosses 1 exactly once for d ≥ d₁(a,b,g)
> (sufficient: outer monotone decrease + dip clearance, both measured at zero
> violations).

Application note: one-sided-far carriers (model 2's shape) give T = 1; the u-plane
slit carrier of Ξ₁ recentered at u₀ = −T² has the SAME shape (zeros bounded on the
right by 0⁻, infinite on the left) — the t-plane recentered carrier is two-sided-far
(T = 2 risk ⟹ Z_c ≤ 4); the theorem-grade reader should live on the u-plane carrier.
