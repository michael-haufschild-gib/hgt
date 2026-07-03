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

## Run 3 — P-B: Hermite cluster model at multiple zeros (doc 25 Thm B)
Script: `computations/mwm/amp_cluster_hermite.py` (pod). g_m = (1−z/9)^m·cos√z, τ = 2+3i,
|x₀−τ|² = 58, σ = x₀/√d. Pre-registered: P-B1 (m=2) half-gap·√d/x₀ → 1; P-B2 (m=2)
margin·2x₀²/(58d) → 1; P-B3 (m=4) margin·4x₀²/(58d) → 1 at ALL THREE cluster critical
points (Lemma W: W_m ≡ m at every Hermite equilibrium). **ALL PASS**, rate O(d^{−1/2}):

| d | P-B1 | P-B2 | P-B3 (u=−√3, 0, +√3) |
|---|------|------|----------------------|
| 10² | 1.0023251 | 0.95576994 | 0.96139534, 0.96250024, 1.0009283 |
| 10³ | 1.0002269 | 0.99542442 | 0.99175939, 0.99611342, 1.0047541 |
| 10⁴ | 1.0000226 | 0.99954085 | 0.9977673, 0.99960991, 1.0018871 |
| 10⁵ | 1.0000023 | 0.99995407 | 0.99933119, 0.99996098, 1.0006343 |

Verdict: the m-fold zero splits at the SINGLE scale σ into the He_m configuration; cluster
margins → |x*−τ|²d/(m·x*²). Certifies doc 25 Thm B (m ≤ 3 proved outright; m = 4 is the
proof-shaped Lemma R regime — this run is its four-decade certificate).

## Run 4 — P-C/P-D/P-E/P-F: the reversal identity and the log-gap race (doc 26)
Script: `computations/mwm/amp_reversal_probe.py` (pod). Models: cos√x/τ=10+4i and
(1−x/9)cos√x/τ=2+3i; d = 16, 24, 40.
- **P-C PASS**: c⁴ℰ(c) = ℰ̂(1/c) − d·c² exact at every critical point (rel. err
  ≤ 1e−63; cross-check ℰ = −A″/A included).
- **P-D PASS**: (V″+b²V)·V sign ≡ margin verdict at EVERY critical point; exactly
  1 copy→flip transition in every run.
- **P-E REFUTED (load-bearing)**: outer-half log-gap monotonicity FALSE — violations
  2/3/6 at d = 16/24/40 (≈ 0.15d) while the crossing stays single: gap monotonicity is
  not the mechanism.
- **P-F**: crossing at i*/(d−1) ≈ 0.59 with d·δ@i* ≈ 3.5–4.3 (equilibrium at ≈ 27% of
  its gap); far-margin → 0.3044/0.2915/0.2795 (model 1) — an O(1) race, saturating
  below 1, never → 0.

## Run 5 — P-H: majorization march of the pole weights (doc 26)
Script: `computations/mwm/amp_majorization_probe.py` (pod). ξ_k = y/(y−β_k) at each
reversed equilibrium; sum rule Σξ_k = d verified to ≤ 2.6e−42 everywhere.
- **Full majorization REFUTED**: sorted-vector partial-sum domination fails on
  3/5/9 of 7/11/19 outer pairs (both models).
- **Top-1 PASS**: dominant weight ξ_max strictly increasing along outer equilibria —
  ZERO violations, both models, all d.
- **S-monotone PASS**: S = Σξ² strictly increasing along outer equilibria — ZERO
  violations, both models, all d.
Verdict: the outer crossing is a monotone LOCALIZATION transition driven by the
dominant pole weight under the conserved budget Σξ = d; kernel re-cut as (S-mono)
(doc 26 §5).

## Run 6 — P-I/P-J/P-K: the drift hierarchy between consecutive equilibria (doc 27)
Script: `computations/mwm/amp_drift_hierarchy_probe.py` (pod). Same two models,
d = 16, 24, 40. Cross-check |S − (d + p₂)|/S ≤ 1e−46 everywhere.
- **P-I PASS (0 violations)**: on every outer inter-critical interval, the smooth-path
  integrand Φ̃′ = −(2/c)Σw_k(η_k + p̃₁) has exactly the dip-then-rise shape (single
  − → + sign change), and Φ̃(c_{i+1}) − Φ̃(c_i) > 0 on every interval — (S-mono)
  re-derived along the pole-removed smooth path.
- **P-J PASS (0 violations)**: outer absolute gaps Δ_i strictly increasing.
- **P-K PASS (0 violations)**: θ_i < 1/2 at every outer critical point; θ at the last
  critical point = 0.1895/0.1634/0.1363 (model 1, d = 16/24/40) — the drift deepens
  monotonically with d and with i.
Verdict: (S-mono) reduces to (LEG) — net-positivity of the leg integrals — with the
length asymmetry PROVED (θ < 1/2 midpoint-push lemma + gap growth) and the endpoint
signs PROVED; in log-time the system is translated hyperbolic-Calogero kernels
(w = 1/(4sinh²((t−t_k)/2)), equilibria at Σcoth((t−t_k)/2) = −d, S = ¾d + ¼Σcoth²).
