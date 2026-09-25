# Numerical pre-certification: C₅ gate, theta Bezoutian ladder, TP order of Φ, Li tower

- **Date:** 2026-08-28
- **Status:** computation record (mpmath, 128-core pod). No Lean content. All positivity findings are
  *numerical evidence*, not proof; all *negativity* findings (TP₅ break) are verified far above the
  precision floor and are reliable as counterexample locations.
- **Serena memory:** `research/numerical_precert_c5_bezoutian_tp_li_2026_08_28`
- **Related cards:** `theta-center-mixed-odd-four-point-cusp` (C₅ / rank-four gate),
  frontier map `rh-current-frontier-map.md` (CLG/TTF, W2C, LI sections).

## Fidelity contract

Every computed object was transcribed **literally from the Lean working tree** (2026-08-28):

| Object | Lean source |
|---|---|
| `thetaCuspSeed t = 2π(2πt⁴−3t²)e^{−πt²}`, `thetaCuspSourceTerm x n = e^{x/2}·seed(n·eˣ)`, `Φ = thetaCuspFullSource = Σ_{n≥1} term` | `RHTower/ThetaCuspFinitePrimeSource.lean` |
| `L = thetaCuspLogSource = log Φ` | `RHTower/ThetaCuspKernelLogConcavity.lean` |
| reflected action `q(u,t)=2L(u)−L(u+t)−L(u−t)`, jets `q₁ = L'(u−t)−L'(u+t)`, `q₂ = −L''(u+t)−L''(u−t)` | `RHTower/ThetaCuspGlobalReflectedRiccati.lean` |
| `P = Φ(u+t)Φ(u−t)`, `A = P(u,0)−P(u,t)`, `D = P·q₁`, `J = P(q₂−q₁²)` | `HedenmalmCenterMixedCorrelationAngle`, `ThetaCuspCenterMixedPtolemyTransport`, `ThetaCuspReflectedSourceOddStationary(+Curvature)` |
| `C₅ = 24A²−9tAD+t²(5AJ−4D²)`, ratio, defect `y=(2A−tD)/A` | `RHTower/ThetaCuspReflectedSourceFifthRootCurvature.lean` |
| `xi s = ½s(s−1)π^{−s/2}Γ(s/2)ζ(s)` (= `s(s−1)/2·Λ₀+½`), `xiCent W = xi(½+W)` | `RHTower/RiemannTower.lean`, `XiShiftLoewnerCriticalGenerator.lean` |
| Bezoutian `B(w,y) = (ξc'(w)ξc(y)+ξc(w)ξc'(y))/(w+y)`; RH ⟺ `[B(w_j, conj w_k)]` PSD, nodes `Re w > ½` | `RHTower/XiBezoutianPointedIncidence.lean`, `ThetaTailFirstMomentDoubleLaplace.lean` |
| Li tower `λ_d` and shifted moments at `y=¼` | `RHTower/LiPairedPrimeArchShiftedMomentLanding.lean`, `XiShiftedReciprocalHankelTailCriterion.lean` |

Smoke checks passed: `∫Φ = ξ(½)` to 1e−19 (matches `thetaBilateralLaplace_eq_xiCent` normalization);
termwise derivatives vs numerical differentiation to 1e−40; evenness exact; both exact C₅ identities
(`C₅ = P²·action`, `C₅ = A²·(y(10+y)−5ty')`) at 1e−39 relative at every grid point; `λ₁` matches
Keiper's value after the analytic tail correction. **Pitfall recorded:** the literal Φ-series has
catastrophic cancellation for `x ≪ 0` (would need ~10⁷ digits at `x=−8`); evaluate at `|x|` via the
Lean evenness theorem `thetaCuspFullSource_neg` with parity signs.

## Result 1 — C₅(u,t) ≥ 0 (rank-four gate): PASSES; tight only at coalescence

- 58,083 points, `u ∈ [0,6]` (evenness spot-verified), `t ∈ (10⁻³, 8]` geometric, dps 40: **0 violations**.
  `y ∈ [0,2]` at every point (corpus claim confirmed).
- Dimensionless margin `C₅/A² ≈ 24` generically. Its infimum 0 is approached **only** along `t→0`,
  at exact rate `coeff(u)·t⁴` with `coeff(0) ≈ 633` (the u-minimum) rising to `≈ 7.7e12` at `u=6`.
  No interior near-zero manifold. The mid-scale failure of the 2026-08-28 no-go profiles does **not**
  occur for the literal theta source.
- Criticality ratio (with `r=e^q−1`, `a=tq₁`, `b=t²q₂`):
  `G = (9ra+5ra²+4a²)/(24r²+5rb)`, so `C₅ ≥ 0 ⟺ G ≤ 1`.
  - `G → 1` **identically** as `t→0`: numerator and denominator are both `34q²+O(q³)` — the
    quadratic-jet contributions cancel exactly. This is the structural reason all local/jet-based
    mechanisms fail (cf. the two no-go modules of the same date).
  - `G ≤ 0.909` for `t ≥ 0.25` on the grid (max at `u=0`, `t≈0.253`).
  - **`G(u,·)` monotone decreasing in `t`** on 115-point scans at `u ∈ {0, ½, 1, 2, 4}` — no violations.
    Monotone `G` with boundary limit 1 would *prove* `C₅ ≥ 0` outright; see `∂ₜG` attack note.
- Cusp expansion cross-check (hand-derived, matches grid): with `q = κt²+λt⁴+μt⁶+…`,
  `κ=−L''(u)`, `λ=−L⁗(u)/12`, `μ=−L⁽⁶⁾(u)/360`, the `t²`- and `t⁶`-coefficients of
  `T = 24r²−9ar+5rb−4a²−5a²r` vanish identically and
  `T|_{t⁸} = 40κμ − 16λ² − 24κ²λ + (8/3)κ⁴`.

## Result 2 — Bezoutian PSD ladder ranks 2–20: no genuine violation

- 3,920 random node systems (regimes: moderate / clustered / edge-hugging `Re→½⁺` / tall `Im∈(150,350)`)
  plus 8 adversarial descents (250 steps each): **0 PSD violations**.
- Every adversarial "negative" sat exactly at the dps-80 conditioning floor; all 8 endpoints re-verified
  **strictly PD at dps 300** (raw relative margins 1e−130…1e−190 are conditioning; correlation-normalized
  min eigenvalues 0.99 → ≈0.008 from rank 2 to 20 — positive throughout).
- Calibration for future agents: margin-vs-rank decay here is inherent analytic-kernel spectral decay
  plus node clustering. It is **not** a GORZ-style red flag. The only meaningful red flag is a sign flip
  that survives precision escalation; none exists.
- Detection sensitivity: rank-2 nodes straddling `γ₁` (`Im = γ₁ ± 0.1`) keep correlation margin
  `≈ 1.3e−3` stable as `Re → ½+10⁻⁴`.

## Result 3 — TP order of the translation kernel Φ(x−y): breaks exactly at 5

- TP₂ 120k minors ✓ (consistent with the Lean log-concavity `thetaCuspLogConcavityNumerator_neg_all`),
  TP₃ 100k ✓, TP₄ 100k ✓ — zero violations.
- **TP₅ fails**: 4/40k violations at widths ≤ 6, re-verified at dps 150 (normalized minors ≈ −1e−12 …
  −2e−11), at ordinary near-diagonal configurations (all five nodes inside width-1 windows, e.g. around
  `x≈2.8–3.2` and around `x≈0`). TP₆ 94/40k, TP₇ 117/40k, TP₈ 38/40k — all resolved.
  Exact violating node lists: `tp2_summary.json`.
- A priori, a finite break is forced: Φ cannot be PF∞ (Schoenberg would make its bilateral Laplace
  transform the reciprocal of a zero-free LP function, but the transform is `xiCent` — entire *with*
  zeros). The numerics locate the break **exactly at order 5**.
- Strategic consequence: the free total-positivity budget of the literal theta kernel ends at order 4 —
  the same order as the CLG/TTF rank-four wall. Rank-≤4 structures (C₅) lie in the generically-provable
  zone; order-≥5 packets cannot be closed by translation-kernel total positivity and need the
  reflected/completed (RH-strength) mechanism. **Do not invest in TP_m mechanisms for m ≥ 5.**

## Result 4 — Li tower health

- `λ_d > 0` for all `d ≤ 300` (4,000 zeros, dps 30, RvM tail estimate reported separately and
  subtracted for the robust check). Minimum ratio to the RH asymptotic `(d/2)(log d − log 2π − 1 + γ)`:
  **0.953** at `d ≈ 270`, trending upward.
- Shifted tower `m_k = Σ_q 2u_q^{k+1}`, `u_q = 1/(γ²+¼) ∈ (0, ≈5.0e−3]`: Hankel `H₀=(m_{j+k})` and the
  `[0,4]`-side `H₁=(4m_{j+k}−m_{j+k+1})` are **PD through size 12 at dps 150** (relative margins 1e−17
  at N=4 down to 1e−74 at N=12 — pure atom-clustering decay).
  **Pitfall:** at dps 30 the sizes ≥ 8 show spurious negative signs; always escalate precision before
  reading Hankel signs of this tower.

## Files

`theta_common.py` (all implementations), `run_c5.py` / `c5_grid.jsonl.gz` / `c5_summary.json`,
`run_bez.py` / `bez_draws.jsonl.gz` / `bez_summary.json` / `verify_adv.py`,
`run_tp.py` + `run_tp2.py` / `tp_summary.json` + `tp2_summary.json` / `validate_tp.py`,
`run_li.py` / `li_lambdas.jsonl.gz` / `li_summary.json` / `li_hankel_hi.py` / `li_hankel_hi.json`,
`g_mono.py` (G-monotonicity scans), `detect_zero.py` (γ₁ sensitivity), `smoke.py`, analysis scripts,
raw logs. Reproduction: any host with mpmath ≥ 1.3; each runner is standalone
(`python3 run_X.py` next to `theta_common.py`).
