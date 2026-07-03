# DISC synthetic node tests — results (task #132)

Scripts: `computations/mwm/disc_spur_test.py`, `computations/mwm/disc_recenter_test.py`.
Model carrier g(x) = cos(√x) (LP-type, zeros x_k = ((2k+1)π/2)² ≈ 2.47, 22.2, 61.7,
121.0, …); witness = one simple non-real pair via a real quadratic factor; control =
real quadratic factor at the same scale. Jensen sections J^{d,n}(X) = Σ C(d,j)γ(n+j)Xʲ,
exact rational coefficients, mpmath rootfinding (dps 60–80). Non-real roots counted in
conjugate pairs; disc > 0 ⟺ even pair count (squarefree).

## Run 1 — global sections, pair at x ≈ 10.8 (zero-index ~1)
Pre-registered P1 (control all hyperbolic): **PASS** — 0 pairs on all d ∈ {4..40}, n ∈ {0..24}.
Pre-registered P2 (no spurious pairs): **PASS** — witness counts ∈ {0,1} everywhere.
P3 (visibility band): pair visible ONLY at n = 0, d ≥ 10; invisible at d ≤ 8 and all n ≥ 1.

## Run 2 — global sections, pairs at x ≈ 60.5 (index ~2) and x ≈ 120.4 (index ~3)
Pre-registered P4 (band tracks index): **FAIL — load-bearing.** Both deeper pairs are
invisible at ALL (d,n), d ≤ 40, n ≤ 24. Scale analysis: C(d,j)/dʲ ≈ e^(−j²/2d)/j!, so
a structure at global coordinate x needs series terms j ~ (terms of the carrier at x)
with j²≲d — visibility cost d ≳ c·x. The shift index n does NOT re-center the view
(consistent with Pólya–Wiman forgetting: derivatives eventually absorb non-real pairs).
For ζ this would mean section degree ~ T² per window — the global Jensen frame pays
quadratic-in-height resolution.

## Run 3 — recentered sections at x₀ = 60 (pair at h = ±8i; control real pair ±8)
G(h) = (h² + 64)·cos(√(60+h)) vs G₀(h) = (h² − 64)·cos(√(60+h)); exact rational
recentering b_m = Σ_k (−1)^k C(k,m) 60^(k−m)/(2k)!.
Pre-registered P5 (visibility at small d): **PASS — stronger than predicted**: count = 1
at EVERY d ∈ {4..40} for n ∈ {0,1}; 0 for n ≥ 2.
Pre-registered P6 (control all zero): **PASS** — 0 pairs everywhere.

## Verdict
1. **No spurious pairs in any run** — section pair-count never exceeded the true local
   pair count (the (SPUR) mechanism holds cleanly in the model).
2. **Recentering IS localization; shift-n is not.** A degree-4 recentered section with
   n ≤ 1 reads the local square class exactly; witness/control discrimination is
   perfect at identical scales.
3. Dictionary for ζ (doc 20): recenter the u-plane carrier at u₀ = −T² (on the slit) —
   coefficients are Ξ₁-jets at the window center = Hardy-Z jet data at height T; the
   disc sign of low-degree jet sections is the candidate finite reader of N(W) mod 2.

## Run 4 — the REAL objects (pod): D–H foil vs ζ control (`computations/mwm/dh_disc_foil.py`)
Recentered t-plane jet sections at t₀ = 85.6993484853776 (the certified D–H off-line
zero's height; banked 18-digit seed reconfirmed, |root−seed| = 2.8e-17; carrier
reality |Im|/|Φ| < 1e-49).
Pre-registered PC (D–H count = 1 for d ∈ {4,6,8}, n ∈ {0,1}): **FAIL as registered,
PASS at n = 0**: counts are 1 at (4,0),(6,0),(8,0) and 0 at n = 1 — the n-band is
narrower on the real object (pair distance 0.3085 vs spacing ~1) than in the
synthetic model. Neither true falsifier occurred (no blind reader, no spurious pairs).
Pre-registered PD (ζ control all 0): **PASS** — 0 at all six (d,n).

**Verdict: the degree-4, n = 0 recentered jet section is a measured finite detector
of the square class on the real objects — disc < 0 at the D–H off-line zero,
disc > 0 for ζ at the identical window.** The w₁-detector question (Arc B) has its
first concretely measured candidate instrument.

## Run 5 — the truncation carrier (pod): first fully finite window-relation instance (#136)
Scripts: `computations/mwm/truncation_boxcount.py`, `/root/trunc_reader_run.py` (pod).
Box-count (winding, σ ∈ [0.53,1.35], Δt = 5, T ∈ [200,1030]): **5 off-line zero
boxes** of the exact-FE truncations g_N — pre-registered PL′ **PASS**. First zero
refined: **ρ_g = 0.60941068066067 + 221.0788841113159·i** of g₅ (|g| = 1.5e−49).
Reader on g₅'s completed carrier (PA2 reality 7e−49) at t₀ = Im ρ_g:
**non-real pairs = 1 at d = 4, 6, 8** (pre-registered PM′ PASS) — disc < 0 reads the
truncation's own local square class. Direct right-half count in the window: 1. This
is the first measured window-relation instance on a FINITE arithmetic object.
Consistency triangle (pre-registered PN, forced by the banked deck transport + RH
verified at T ≈ 221): domination q = max|ζ−g₅|/|g₅| on that window boundary MUST be
≥ 1 — measured **q = 4.72 (r = 0.20), q = 1.17 (r = 0.35)**: domination fails
exactly where parity is odd. The theorem's contrapositive observed in the data.

## Run 6 — P-U: u-plane reader on the #136 instance (theorem-track carrier; task #140)
Script: `computations/mwm/uplane_reader_136.py` (pod). Completion Φ(s) = π^{−s/2}Γ(s/2)g₅(s)
(Φ(1−s) = Φ(s) exact ⟹ descends to H(u), real on u < 0); recenter at u₀ = −t₀²,
h(v) = Φ(1/2 + i√(t₀²−v)); jets by 256-node Cauchy trapezoid at r = 8, dps 120.
- **P-U0 PASS**: refined zero ρ = 0.60941068066066512213 + 221.07888411131592586i,
  |Φ(ρ)| = 1.9e−196; pair at v = 0.011970697 ± 48.376782i (one-sided-far: nearest
  on-line zeros at |v| ~ 4e2).
- **P-U1/P-U2 PASS**: truncation carrier reads 1 non-real pair, disc < 0, at d = 4, 6, 8
  (coeff-Im-noise ≤ 3.5e−107) — u-plane reading ≡ t-plane reading (run 5).
- **P-U3 PASS**: ζ control (ξ jets at the SAME u₀): 0 pairs, disc > 0, at d = 4, 6, 8.
Verdict: the first fully finite window-relation instance now lives on the u-plane
one-sided-far carrier — the shape with PROVED tracking clearance (doc 25) and T = 1
counting (doc 24 §3). The reader's verdict is unchanged by the carrier transposition;
what remains between this instance and a theorem-grade reading is (AMP-mono)(iii) alone.
