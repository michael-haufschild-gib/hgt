
## 2026-07-04 (cycle 3) — #147: the reversal is an edge/deficit quantity, NOT C₀²
Certification `computations/mwm/reversal_truth.py` (pre-registered, identity
validated against ledger_regroup to 4e−27; first-run sign slip caught by P-R4):
TRUE reversal at c = 2 (C₀ ≈ 1/2) is ≤ 0.23 vs cushion 2 — doc 37's 200C₀² off by
~250×. P-R3 FAIL (load-bearing): no C₀ scaling — reversal is an (F1)-edge
phenomenon: saturates in d (0.181→0.230, d=150→2500), decays sharply in i/d
(0.21→0.002 over θ=0.50→0.75), max at small s. Doc 39-reversal-edge.md banked:
budget-coupling kills termwise C₀² folding; continuum mechanism = log-compact
ahead field vs log-infinite behind field; §6 same-session correction — near/far
split refuted (per-pair credit/debit = 3/4 uniformly at s→0; the quarter-deficit
sums to the measured 0.21), replaced by single explicit bound Lemma H‡′ via chain
(†). Remaining for Theorem B⁗ (ΔG ≥ 7/4 for ALL C₀ ≤ 1/2, model class): continuum
evaluation of the H‡′ integral with Riemann remainder + the [CONJECTURE] exact-3/4
closed form. #143 (Lean stack) delegated to codex agent by Michael this cycle.

## 2026-07-04 (cycle 4) — #147 closed-form pass: Theorem B⁗ on paper (doc 40)
Exact continuum reversal derived: R(θ,c,s) = ∫ cξ[w(v)/(1+ξ) − w(u)/(1−ξ)]⁺dξ,
sup at s = 0 (discrete-level s-monotonicity, one-line proof). c = 2 collapses
algebraically: integrand 8ξ²/(4−ξ²)² > 0 (every pair net-loss in the limit),
antiderivative 4ξ/(4−ξ²) − log((2+ξ)/(2−ξ)) verified by differentiation;
R(1/2,2,0) = 4/3 − log 3 = 0.2347210447. Certifications (pre-registered): P-R9
quad = closed to 1.7e−19 (after repairing tanh–sinh endpoint cancellation — the
integrand is a difference of ~1/ξ terms; first quad at dps 30 was 1e−3 off);
P-R8 sup_{c≥2} R(1/2,c,0) = 0.247355 at c = 2.5 < 1/4 (interior max, matches
discrete c = 3 > c = 2 observation); P-R7 discrete d = 10⁴ = 0.234071, O(1/i)
remainder K ≈ 3.3, sequence converges to closed form from below. 3/4 conjecture
REFUTED-and-explained (uniform-bound artifact; exact near-ratio → 1). Theorem B⁗:
reversal ≤ B*(θ) + K/i, B*(1/2) < 1/4 ⟹ ΔG ≥ 7/4 − K/i for ALL C₀ ≤ 1/2 —
supersedes B″'s C₀ ≤ 1/10 and the c < 10 delegation. Remaining for 1→2 grade:
(B⁗-a) c-sup calculus lemma, (B⁗-b) remainder constant K write-out. Tip bonus:
R → 0 quadratically as θ → 1 — tip doubly protected; re-price #145 with it.

## 2026-07-04 (cycle 5) — (B⁗-a) PROVED, (B⁗-b) written out (doc 41)
(B⁗-a): Lemma P [PROVED, fully elementary] — (m,r)-frame with the constraint
collapsing to cosh m = e^r; positivity criterion (POS_c):
tanh(cr/2)coth(cm/2) ≥ tanh(m/2); c = 2 case ⟺ cosh m ≥ 1 (one line);
c-monotonicity via y/sinh(cy) decreasing ⟹ integrand ≥ 0 for ALL c ≥ 2 (no ⁺
clipping; class boundary is c > 1). Sup Lemma via the unified single-signed form
c∫2sinh²(z/2)csch²(cz/2) − c∫(1−e^{−z})½csch²(cz/2): independent c = 2
partial-fraction re-derivation of 4/3 − log 3 (6e−27); tail R ≤ 8.16/c² (c ≥ 3);
Lipschitz L₀ ≤ 1.6; certified grid 1601 pts: max 0.2473801 at c* = 2.5275, guard
0.24938 < 1/4 — P-R10 PASS. B*(θ) ≤ B*(1/2) < 1/4 for all θ ≥ 1/2.
(B⁗-b): (K1) Taylor, (K2) per-pair, (E1) ≤ (8.5/(ci))(1.5 + log(2.9i/c)) all
[PROVED]; (K3) digamma-frame Euler–Maclaurin: boundary ≤ (4/9)/i (supΨ = 8/9 at
corner (2,1), P-R12), curvature ≤ 0.24/i² (∫|Ψ″| = 80/27 at c = 2 exactly —
Ψ₂ convex — P-R13), frame gap C_ψ/i (common/asymmetric split route written,
C_ψ ≤ 6 named — the ONE remaining constant; empirical total 3.3/i). THEOREM B⁗
FINAL: ΔG ≥ 7/4 − err(i) on the whole c ≥ 2 class, ΔG ≥ 1 for i ≥ 200.
Next: C_ψ page; Lemma P → Lean brick; (m,r)-frame re-cut of Lemma D/E′ bands.
