# 52 — The Creation Rate: Births Are Tangencies, Priced by the Naked Partial Sum

**Register: SEARCH** (task #154; doc 49 §3(4), the fourth typed input of
(MID-central)). The reader identity below is verified from the Roy–You full
text (arXiv:2411.08364, their eq. (19), read directly); the derivative
computation is done here and sign-chased twice.

## 1. The weld reader on the line [verified restatement]

On σ = 1/2 (real coefficients), with F = F_N the naked partial sum and
χ the frame:

> ζ_N(½+it) = |F| e^{iφ} (1 + e^{iA(t)}),  A(t) := −2θ_RS(t) − 2φ(t),
> φ = arg F(½+it),

so on-line zeros of ζ_N are exactly {|F| = 0} ∪ {A ≡ π mod 2π}. This is the
weld identity in crossing form: the frame turns at rate −2θ_RS′, the stream
unwinds at −2φ′.

## 2. Births are tangencies [derivation]

An off-line pair creation (doc 48's reverse dichotomy εq(0) ≥ v₀²) is, in the
A-reading, a TANGENTIAL level crossing: A touches an odd-π level with A′ = 0
and lifts off — two on-line crossings merge and detach as a conjugate pair.
Transversal crossings (A′ ≠ 0 at level) are simple on-line zeros and create
nothing. Hence

> #births in [T, T+U] ≤ #{t : A(t) ≡ π (2π), |A′(t)| ≤ ε} + O(1) boundary.

## 3. The derivative identity and the price of a tangency [derivation]

s = ½ + it gives φ′(t) = Re(F′/F)(½+it), so

> A′(t) = −2θ_RS′(t) − 2·Re(F_N′/F_N)(½+it),  θ_RS′(t) ≈ log N at matched.

Two facts about Re(F_N′/F_N) on the line:
1. **Typical value −½·log N**: Re(F′/F) = ∂_σ log|F|, and the mean of
   log|F_N(σ+it)| has σ-derivative −⟨log n⟩_{n^{−2σ}} ≈ −½log N at σ = ½
   (weights n^{−1}).
2. **Poisson decomposition**: partial fractions over the zeros of the entire
   function F_N give Re(F′/F)(½+it) = Σ_ρ (½−β_ρ)/((½−β_ρ)² + (t−γ_ρ)²) + smooth;
   zeros RIGHT of the line contribute negative kernels of peak height
   −1/(β_ρ − ½).

Tangency needs Re(F′/F) = −θ_RS′ ≈ −log N — a deficit of ½·log N below
typical — which requires a zero of the NAKED partial sum within ≈ 2/log N
to the RIGHT of the critical line, at height within O(1/log N) of t.

> **Creation is priced by the right-of-line near-line zeros of F_N — no
> functional equation, no frame, a pure Dirichlet-polynomial question.**

## 4. The typed open lemma

> **(CR-density) [OPEN, classical-shaped]:** for the partial sum
> F_N(s) = Σ_{n≤N} n^{−s} in the matched range,
> #{ρ : F_N(ρ) = 0, 0 < β_ρ − ½ ≤ c/log N, γ_ρ ∈ [T, T+U]}
> ≤ ε(c)·U·log N, with ε(c) → 0 as c → 0.

Routes with known technology: second-moment Littlewood on F_N (the second
moment on the line is Σ_{n≤N} n^{−1} ~ log N — classical), Jensen discs at
scale 1/log N, or the σ-distribution literature for partial-sum zeros
(arXiv:0807.0019, arXiv:1507.01340 — to be mined for the near-line profile;
the spread of β about ½ at scale 1/log N is exactly what ε(c) measures).
Note the contrast with doc 50 §7: for the SYMMETRIZED family the moment
method dies at matched length; (CR-density) concerns the UNsymmetrized sum,
where no frame term blocks it.

## 5. Depth grading and the census anchor [measured]

Mid-band births need depth η ≥ ~0.09: beyond the tangency, the second-order
data (A″ and the |F|-valley) must conspire — the depth-graded count carries
an additional small-ball factor. Census calibration: 19 mid-band events in
24,000 units at log N ≈ 4.1, i.e. rate 8·10⁻⁴/unit against frame density
θ_RS′/π ≈ 1.3/unit — a suppression of ~1/1600 of which ~1/25 is the
(HOLD-phase) window measure and ~1/65 the depth small-ball. Functional form
open; anchor recorded.

## 6. Assembly of (MID-central) after docs 50–52

survivors ≤ [births: (CR-density) + depth small-ball]
          × [localization: SweepCascade.survivingBirths_length_le…, discharged
             by (DRIFT-dip) + collective_push_le outside (HOLD-phase)]
with the (HOLD-phase) window (doc 51 §5) the sole surviving habitat, exactly
as measured. Machine-checked today: the dichotomy, the collapse, the master
push bound, the localization combinatorics. Open, in force order:
(HOLD-phase) κ [single-term self-interaction], (DRIFT-dip) [bookkeeping],
(CR-density) [classical-shaped], (DEEP-FATE) [one sanctioned computation].

## 7. What this opens

1. (CR-density) via the second moment: ∫|F_N(½+it)|²dt is elementary — a
   Jensen-disc argument at radius c/log N may already close it; try on paper
   before any literature mining.
2. The left/right asymmetry is testable: archived odd events should pair
   with a right-of-line F_N zero at distance ~2/log N — a future census
   field (store the paired F_N zero σ).
3. The same tangency reading applied at the (HOLD-phase) edge should produce
   the κ tolerance: A″ at a tangency is the pair's initial curvature — the
   quadrature/hold ratio of doc 51 §5 in second-order form.

## 8. Same-session audit: bare Jensen does NOT close (CR-density)

Attempted §7(1) immediately. Shift-averaged Jensen discs at radius c/log N +
first-moment Littlewood (mean of log|F_N| on nearby vertical lines differs by
O(c) since ∂_σ mean-log ≈ −½log N) give count ≤ U·log N·O(1) — the TRIVIAL
density, no ε(c) smallness. First-moment information is structurally
insufficient: ε(c) is exactly the statement that the β-distribution of
partial-sum zeros has NO ATOM at the line at scale c/log N — a continuity-of-
profile fact. Routes that can carry it: second/fourth moments of log|F_N|
(variance ⟹ anti-concentration), or the σ-profile in the partial-sum zeros
literature (arXiv:0807.0019, 1507.01340). (CR-density) stands as typed, with
the no-go recorded so nobody re-walks bare Jensen.

## 9. Creation reader across p: intensity is p-FLAT; the envelope is depth, not count [MEASURED — 2026-07-04]

Ran the §1–§3 reader across p ∈ [0, ½] to test whether birth INTENSITY carries the
`B(p) = |cos(π/8 − 2πp²)|` envelope (the weld hope: survival + creation both ∝ B²).
Certification: `computations/mwm/creation_rate_envelope.py` (pre-registered C1–C4)
+ `creation_rate_envelope.out` (pod, numpy). Deficit function
`h(t) = θ_RS′(t) + Re(F_N′/F_N)(½+it)`, mean `+½log N`; births = downward
excursions of `h` to 0. Aggregated over N = 40…120, 4000 p-points each, 25 d-bins.

**Result — the "births ∝ B²" conjecture is REFUTED at the reader level.** The
first-order birth-proxy intensity (density of low-h / near-tangency events) is
FLAT in p: intensity ratio `[d<0.125]:[d>0.375] = 0.99` (census births 3.0);
mean-h, low tail q05, and near-tangency density all p-independent; R² of both
`H_B = cos²(π/8−2πp²)` and `H_frz = cos²(2πp²)` ≈ 0.01 (i.e. no fit — the data are
flat). The on-line zeros of ζ_N (the `min h` spikes) are uniform in p, confirming
the reader is sound; there is simply no first-order p-structure.

**Why flat, and where the envelope actually is.** The marginal-term resonance is
ONE term out of N — a `1/√N`-diluted modulation on the full-sum `h`, below the
bulk's O(1) on-line-zero fluctuations. The census sees the p-structure because
off-line pairs are MARGINAL-SELECTED (they exist only by the resonance); `h` is
not marginal-selected, so it averages the resonance away. The census
birth-clustering therefore lives NOT in the tangency DENSITY (p-flat) but in the
depth-graded LIFT-OFF — whether the tangency detaches deep enough to be mid-band
(doc 52 §5's depth small-ball, `η ≥ 0.09`). This is consistent with `B(p)` being a
birth-DEPTH cap (doc 51 §8(4)), not an intensity.

**The weld, corrected — the π/8 is SURVIVAL-only.** The fork (peak at p=0 vs p=¼)
resolves from the census directly: births peak at p≈0 (42/106 within 0.125 of
p≡0), and the frozen-max marginal line modulus `|cos 2πp²|` (doc 46 §6) peaks at
p=0 — while `B(p)` peaks at p=¼. So the creation-depth envelope is the FROZEN-MAX
modulus (phase offset **0**), NOT `B` (offset **π/8**). Creation and survival share
the SLIP variable `2πp²` but not the offset: the `π/8` is the RS-remainder /
metaplectic constant of the survival stationary VALUE (docs 50 §5, 51 §10), absent
from the creation modulus. The census birth-peak at p=0 is the fingerprint that
creation carries NO π/8.

**What this opens.** The right instrument for the depth envelope is the off-line
pair-depth census (doc 52 §7(2)): store per-event `(p, birth-depth)` and test
whether the birth DEPTH (not count) follows `|cos 2πp²|` (frozen-max, predicted)
vs `B(p)`. That is the weld test — 2D depth-graded, not the 1D reader. Next:
regenerate a small depth-graded off-line census over p ∈ [0,½] at one matched N and
fit the birth-depth p-profile; if it tracks `|cos 2πp²|`, the two census facts are
(survival: frozen dip, low edge, with π/8 in the dip phase) × (creation: frozen-max
depth, half-emptiness, no π/8) — welded at the shared slip `2πp²`, the π/8 living
only on the survival ledger.
