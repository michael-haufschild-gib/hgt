# Pre-registration — (K-bdd) engine probes P4/P5/P6 (doc 58 §5 executed)

Written BEFORE the run (2026-07-05, session seed 1111089585816317988). These bind.

Setup: P = F_N·M_y, BV taper (mollified_dip_cert.py convention: λ_d = μ(d) for
d ≤ y₁ = √y, μ(d)·log(y/d)/log(y/y₁) for y₁ < d < y, 0 at y), y = √N,
matched window T = 2π(N+1/4)², U = 2000 (P4) / 1000 (P5). Conditioned
coefficient of a prime p ∈ (y, N]: A_p(t) = Σ_{k : c_{pk}≠0} c_{pk}(pk)^{−1/2}k^{−it},
rms_p² = Σ_k c_{pk}²/(pk). (At θ = 1/2, p ∈ (y,N] divides no contributing m
twice: p²|m ⟹ m/d ≥ p² > N for every p-free d — so A_p is exactly the
X_p-linear coefficient.) Random model: X completely multiplicative Steinhaus.

- **P4a (doc 58's registration; prior 0.55).** D_max(t) := max_{p∈(y,N]}
  |A_p(t)|/rms_p. For ε ∈ [0.15, 0.8] and N ∈ {100, 400, 1000}:
  P_t(D_max < ε) ≤ 2·ε⁴. FALSIFIER: fitted log-log slope < 3.
- **P4b (the induction engine; prior 0.6).** D₂(t) := second-largest of
  |A_p(t)|/rms_p. Same range: P_t(D₂ < ε) ≤ 2·ε². FALSIFIER: slope < 1.5 ⟹
  the two-phase co-area engine leaks; the write-out must route around
  (k-phase or direction-diversity argument).
- **P5 (doc 58's registration; prior 0.5).** ψ = 1_{|·|≤r}, r = 0.3, N = 400.
  Pair ratio g(τ) := ⟨ψ(P(t))ψ(P(t+τ))⟩_t/⟨ψ⟩², model g_m(τ) from Steinhaus
  draws at the same lags. Register: |g_true(τ)/g_model(τ) − 1| ≤ 0.10 for
  τ ∈ {1,2,5,10,20,50,100}. FALSIFIER: systematic deviation > 0.25 on a τ-band
  ⟹ (TRANSFER)/(SPEC-decay) suspect at the functional level.
- **P6 (new; prior 0.75).** Q(r) := meas{|P| ≤ r}/U. Register:
  |Q_true(r)/Q_model(r) − 1| ≤ 0.15 for r ∈ {0.1, 0.2, 0.3, 0.5},
  N ∈ {100, 400, 1000}. Tests the one-point window↔model transfer directly.

Adjudication: P4b PASS ⟹ the co-area induction's degeneracy pricing is sound —
write out (K-bdd-∞) at full force. P4a/P4b FAIL ⟹ the failure exponent is the
finding; retype the degeneracy event. P5+P6 PASS ⟹ (TRANSFER) is TRUE-shaped at
fixed functionals; the open half is mechanism only. P6 FAIL ⟹ the window is NOT
model-like at fixed scale — (K-bdd) itself becomes suspect despite doc 56 §9 P2.

## PREREG-3 (2026-07-05, before the gamma-profile run; binds)

- **P-F6 (the floor's fuel; prior 0.45).** Deterministic profile
  E|γ_p|² = Σ_{k≥2}(c^{(p)}_k)²/k for BV at N ∈ {1000, 4000, 40000}: there
  exists a dyadic p-sub-range of (y, N^{0.9}] with Mertens mass ≥ 0.05 and
  mass-weighted mean variance ε₀ ≤ 0.35, stable in N. FALSIFIER: weighted
  variance ≥ 0.8 on EVERY dyadic sub-range at the largest N — then the
  near-deterministic-range mechanism has no fuel in the BV design; escalate
  to (DESIGN-ε₀) or open the refutation branch.
- Secondary (recorded, not load-bearing): sharp-μ profile for comparison;
  design variants y₁ ∈ {y^{0.25}, y^{0.75}} to bracket the taper dial.

## PREREG-4 (2026-07-05, before the V-drift scan; binds — DECISIVE for the route)

- **P-F6 ADJUDICATION (recorded before PREREG-4's run): FALSIFIER FIRED.**
  BV min-range variance 1.705 at N = 4·10⁴ (every range ≥ 0.8); profile GROWS
  with N at every α (≈ 1.9×Δloglog). No fuel for the near-deterministic-range
  floor in the λ-on-[1,y] family.
- **P-F7 (V-drift; prior split 0.5/0.5 — DECIDES the route's premise).**
  Deterministic V(N) = Σ_{m≥2} b_m²/m for BV (y₁ = √y) at
  N ∈ {1000, 3000, 10⁴, 3·10⁴, 10⁵}, plus split V = V_inner (m ≤ N) +
  V_boundary (m ∈ (N, Ny]). Fit V(N) against (i) saturation a − b/log N and
  (ii) growth a + b·loglog N.
  Branch A (saturation fits better, boundary share stable): doc 56 §3's
  premise survives; the kernel grind continues (full-range w-slope next).
  Branch B (loglog fits better with slope b ≥ 0.3, driven by V_boundary):
  **doc 56's fixed-variance premise is FALSE as typed** — the boundary band
  is loglog-critical, κ²(N) → ∞, and the Route B refutation branch opens:
  write the no-go (no λ supported on [1, y] cancels the per-prime boundary
  fields) and move the card to 5-failed unless a redesign (support past y,
  different completion) evades it.

## PREREG-5 (2026-07-05, before the smooth-cutoff scan; binds)

- **P-F7 ADJUDICATION (recorded): BRANCH B FIRED.** V = −1.58 + 2.27·loglogN
  (rms 0.042 vs 0.073 saturation), boundary share 0.53 → 0.59; retrodicts
  doc 56 §9's V_BV(400) = 2.48 exactly. Doc 56 §3's V = O(1) is FALSE as
  typed. Route B enters escape-pricing.
- **P-F8 (escape E2 — smooth inner cutoff; prior 0.6).** Same V-scan with
  F̃ = Σ φ(n/N)n^{−s}, φ = 1 on [0,½], cos²-ramp on [½,1]:
  b̃_m = Σ_{d|m,d≤y} λ_d φ(m/(dN)). Register: V_smooth(N) fits saturation
  better than loglog on N ∈ {1000..10⁵}, with total V_smooth ≤ 3 at 10⁵.
  PASS ⟹ the criticality is the SHARP EDGE's, not the mollification's —
  Route B refutes as typed but re-types on a smoothed/designed carrier
  (verdict = re-cut, not tombstone). FAIL ⟹ the criticality is intrinsic to
  the matched-length product class — verdict hardens.
