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

## Run 7 — Euler-suppression discrimination (pod): what the arithmetic input really is (#146)
Script: `computations/mwm/euler_suppression_boxcount.py` (all pre-registrations in
the docstring and appended blocks BEFORE each run; raw outputs `es146.out`,
`es146_q.out`, `es146_x.out`; session seed 1920367149821033252, all seeds CSPRNG).
Design: exact-FE carriers Φ_a(s) = π^(−s/2)Γ(s/2)A_N(s) + reflection, A_N(s) =
Σ_{n≤N} a_n n^(−s) — FE and line-reality hold for EVERY real coefficient stream;
only the stream varies. Box sweeps σ ∈ [0.53,1.35], Δt = 5, N = ⌊√(T/2π)⌋:
band1 T ∈ [200,1030) (N = 5–12), band2 T ∈ [5000,5830) (N = 28–30, primary).
Classes: E (a_n = 1), M (random completely multiplicative ±1, 8 seeds), R (iid ±1,
8 seeds), Q (iid ±1 with a_{n²} = +1 forced — matches M's mean vector exactly,
kills dependence; 8 seeds), X-coh/X-incoh (the character stream χ₋₄ in its OWN
completion frame vs in ζ's frame — identical multiplicativity, coherence toggled).

Counts (total right-half off-line winding per sweep):

| class | band1 | band2 |
|---|---|---|
| E (ζ-truncation) | 5 | 4 |
| X-coh (χ₋₄, own frame) | 2 | 2 |
| X-incoh (χ₋₄, ζ frame) | 24 | 54 |
| M mean (8 seeds) | 43.8 [48,5,52,48,54,54,43,46] | 91.0 [95,77,92,91,94,97,92,90] |
| R mean (8 seeds) | 78.9 [69,74,80,82,95,76,89,66] | 138.0 [122,148,121,135,138,153,140,147] |
| Q mean (8 seeds) | 71.3 [77,67,67,66,72,76,88,57] | 150.8 [146,174,140,139,147,158,155,147] |

Pre-registered outcomes:
- **P-A PASS** (E band1 = 5, first hit (220,5,1) — exact run-5 replication through
  the symmetric Φ form).
- **P-B PASS** (R band2 = 138 ≫ 15: FE alone leaves a large off-line population).
- **P-C FAIL as registered, effect real**: M/R band2 ratio 0.66 (registered ≤ 0.5),
  dose-response REVERSED (band1 ratio 0.55). Every M below every R (~10σ):
  multiplicative dependence suppresses, but modestly and not gradedly.
- **P-F PASS (dependence-dominant)**: Q ≈ R (150.8 vs 138.0 ≥ registered 114.5) —
  the M-vs-R gap is carried by multiplicative DEPENDENCE, not the square-mean bias.
- **P-G PASS** (X-coh band2 = 2 ≤ 12) and **P-H PASS** (X-incoh band2 = 54 ≥ 30):
  the SAME character stream moves 2 → 54 when only the frame is toggled.
- **P-D PASS** (reader exactness on the new classes): refined off-line zeros of M
  and R carriers read pair count = 1, disc < 0, at d = 4,6,8 AND d = 10,12,16
  (jet Im-noise ≤ 1e−122). No blind reader, no spurious pairs — the falsifiers
  did not fire on any carrier class.
- **P-E PASS** (#146(a)): exact-ξ reader at both banked windows (t₀ = 85.699…,
  221.078…): 0 pairs, disc > 0, at d ∈ {10,12,16}, n ∈ {0,1} — (SPUR) stable to
  degree 16.
Structural half (settled by reasoning, not run): the Révész/BDR foil (Euler, no
FE) admits NO real carrier — the instrument requires the FE for line-reality
(doc 19 §5); its pincer role stays with doc 14 §6.

**Sharpest single datum**: M seed 894929634 has f(p) = +1 for all p ≤ 12, so in
band1 it IS the ζ-truncation — it scores exactly 5; in band2 it differs from E at
THREE primes (13, 19, 29) and scores 77. Three sign flips: 4 → 77.

**Verdict (the #146 discrimination).** The off-line-zero rate of exact-FE carriers
is governed by stream↔frame COHERENCE — whether the reflected coefficient stream
completes to an actual analytic L-object in that frame (the AFE identity) — with
multiplicativity a secondary, non-graded suppression. Measured gradient:
weld-coherent 2–5 ≪ character-in-wrong-frame 54 < random-multiplicative 91 <
structureless 138–151. This RE-CUTS #130's arithmetic clause: the bridge input
"Euler structure in the coefficients" is insufficient as stated; what (DISC-fin)
must consume is the WELD — the exact AFE/completion identity in which Euler
product and FE cohere. Doc 14 §6's qualitative pincer now has a quantitative
gradient on the lane's own instrument. Opens: (i) restate (DISC-fin) with the AFE
identity as the named input; (ii) the coherence dial is continuous — a pencil
between frames (e.g. interpolate the conductor) would measure the moat shape the
R5-series saw in the u-pencil, now for the window reader; (iii) doc 38's minor
chain as the margin statistic along that dial.
