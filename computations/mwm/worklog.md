
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

## 2026-07-04 (cycle 10) — birth mechanism FILMED; the program's halves converge
birth_homotopy.py (P-B1/B2/B3 all PASS): marginal-term homotopy λ·35^{−s} on
the two N = 35 survivors + p-central control. Pairs absent at λ = 0, born in a
filmed on-line collision (gap .295→.101 then count −2, η grows .037→.097);
control at p ≈ .45: the SAME term REPELS (gap .359→.440 monotone). Mechanism =
stationary phase: the marginal term's Z-perturbation 2λ|γ|N^{−1/2}cos(θ_γ −
t log N) is stationary exactly at t = 2πN² — attraction coherent near
resonance, averaged repulsion off it. (MID-central) now has a provable shape:
oscillatory-integral sign profile + selectivity (gap stiffness vs N^{−1/2}
push = doc-12 small-ball with a mechanism anchor). CONVERGENCE: pair birth =
local disc sign flip under one-parameter perturbation = the SPUR arc's native
tracking object (doc 25 clearance, doc 38 minors, B⁗/S″ march) — the arithmetic
wall's final form is a disc-stability statement in the analytic arc's own
format; arithmetic enters only via the explicit phase/amplitude of the marginal
term. Doc 45 banked. Next: σ(p) attraction-boundary run; stationary-phase
write-out; #149 full text.

## 2026-07-04 (cycle 11) — σ(p) refutes pointwise attraction; (HOLD) model fits to 5%
sigma_profile.py P-S1 FAIL (registered fail-branch): uniform p-grids (N=22,35;
19×3 windows) show NO systematic push-sign profile — push sign configurational
(first-order theory right); doc 45 §2's coherent-attraction explanation
superseded; the film's survivor attraction was selection. Replacement: the
HOLDING model — pairs are term-held (λ* ≈ 0.7, load-bearing) and persist only
while the marginal term's beat phase Δφ = 2πp² ≤ Δφ* ≈ 0.2 rad: all 8 survivors
have Δφ ≤ 0.21 (max possible 1.6); predicted p* = 0.18 vs observed 0.19. No
other term can hold (all ≥ 10 rad off their own resonance at p-central).
(MID-central) proof shape = (HOLD-lemma) [oscillatory bookkeeping on the
explicit pair equation, single-term share isolated] + (GEN-valley) [doc-12
small-ball; measured census: ZERO generic-type mid-band pairs in [200,12000]].
Doc 46 banked. Next: τ-share statistic at survivors; (HOLD-lemma) write-out;
T ~ 2–3·10⁴ census decade cross-check.

## 2026-07-04 (cycle 12) — the reach law: 8/8, min margin 1.10
tau_share.py P-T1 PASS (stronger than registered): reach = |P_N(ρ)|/|Φ′(ρ)| ≥ η
at ALL 8 survivors (ratios 1.10–2.11; transcription Φ_{N−1}(ρ) = −P_N(ρ) to
1e−37). (REACH) conjecture banked: mid-band pairs only within the marginal
term's reach ⟹ subsumes (GEN-valley) if proved. Structural identity: |Φ′(ρ)| =
2η|H(ρ)| exactly (two-zero factorization) ⟹ (REACH) ⟺ |P_N(ρ)| ≥ 2η²|H(ρ)| —
the SAME η²|H| object as (MOAT-shallow); and |P_N| off-line has near-zeros at
rate η·(beat phase) — the amplitude and phase windows are ONE object. Census
decade [20000,30000) running on pod (P-H1/P-H2 registered).

## 2026-07-04 (cycle 12 addendum) — (BVAL): the wall's irreducible form
Exact-identity chain: pair ⟺ B(ρ) = −P_N(ρ), B = Φ_{N−1}; |P_N| on line =
2|γ|N^{−1/2}|cos φ|; ⟹ mid-band pair REQUIRES an N^{−1/2}-deep off-line valley
of the ONE-TERM-UNDER-RESOLVED background at p-central heights. (BVAL) named as
the irreducible statement; film's λ = 0 frames are its first instance checks
(background clean at both survivors). p-mechanism derived at sketch grade:
resonance = frozen-maximum window of |cos φ| ⟹ shallowest-possible valley
requirement ⟹ pairs easiest there; off-resonance the joint (depth ∧ phase)
requirement is deeper on average. G–M connection exact: (BVAL) = one
quantitative step of their under-resolution rigidity (their 100% theorem is the
extreme case). Census decade P-H1/P-H2 pending.
