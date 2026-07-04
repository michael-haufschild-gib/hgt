# 64 — The Transfer Lemma: Model Pass-Count → Deterministic, at Second-Moment Cost

**Register: SEARCH**; §§1–3 are the write-out (proved-grade pieces marked),
§4 the typed residual input, §5 the theorem-shape, §6 pre-registers the
triple-log census (the falsifiable signature). Companion: doc 63 (model),
doc 62 (obstruction), `SecondMoment.lean` (the dpoly supply).

## 1. What must transfer, exactly

Doc 63 §4's K rests on ONE stochastic estimate: the near-origin pass count of
the Cesàro path over dyadic log-time blocks. Everything else in the chain
(hull exclusion, EMA recursion, sample decorrelation, exceptional-set
counting) is either proved (doc 62 §1) or Finset algebra (the Lean pass, this
cycle). The transfer must convert, for the TRUE walk at a right-sliver point:

> P_t(∃ pass of Z̄ at depth ≤ a in block [θ, 2θ]) from the model's c/log θ
> to ANY summable-enough deterministic bound,

where P_t is window measure, Z̄_k = Σ_{m≤k}(k−m+1)/k·m^{−s₀} — note the
coefficients are the FEJÉR/Riesz (R,1) triangle: the Cesàro field is itself a
Dirichlet polynomial with explicit triangular weights. Every first- and
second-order functional below is therefore `SecondMoment.dpoly` material.

## 2. The MV supply [proved-grade — pair correlations, exact]

- **Covariance of the Cesàro field:** E_t[Z̄_j·conj Z̄_k] = Σ_m w_m(j)w_m(k)
  m^{−1−2δ} + O(N/U) with w_m(k) = (k−m+1)⁺/k — exact by Montgomery–Vaughan
  (lengths ≤ N ≪ U). Diagonal: E|Z̄_k|² = θ_k(1 + o(1)) with θ_k = log k·λ(c).
- **The deviation field D_k = Z_k − Z̄_k:** again a dpoly (weights
  (m−1)/k-triangular complement); E|D_k|² = O(1) exactly — the discrete OU
  stationarity of doc 63 §2, now unconditional.
- **Fourth moments:** available by MV for blocks k ≤ N^{1−δ′} (squared length
  k² ≪ U); the TOP block (k ~ N, k² ≍ U) is marginal — handled separately in
  §5 by the pair-correlation-only weak bound (one block contributes one unit
  to the pass budget at worst; the sum is over ≍ log log N blocks).

## 3. Occupation-to-pass conversion [proved-grade mechanics]

A pass at depth ≤ a during a block forces occupation: the discrete path moves
per step by |Z̄_{k+1} − Z̄_k| = |Z_{k+1} − Z̄_k|/(k+1) (the exact EMA recursion
— Lean, this cycle), so crossing the ball B(0, 2a) takes ≥ a/v_j steps-in-θ,
where v_j = max block speed. Doob/4th-moment maximal control (available in
sub-top blocks by §2) gives v_j ≤ C√(log θ_j) off a summably-small event.
Hence, per block,

> P(pass at depth ≤ a) ≤ E[occupation time in B(0, 2a)] · v_j / a
> = (v_j/a)·∫_block P(|Z̄(θ)| ≤ 2a) dθ.

The pass bound is thereby reduced to POINTWISE anti-concentration of the
Fejér-weighted polynomial at absolute scale a — the single residual input:

## 4. The residual input, typed

> **(TRI-bdd) [OPEN]:** for the triangular/Fejér Dirichlet polynomial Z̄_k at
> right-sliver points, P_t(|Z̄_k| ≤ a) ≤ C·a²/log k for a ∈ [1, √(log k)].

Same anti-concentration class as (K-bdd)/(SM-bdd), with two differences that
cut opposite ways, both recorded: (i) HARDER — the Esseen λ-range needed
grows like √(log k) (relative scale down to θ^{−1/2}), not O(1); (ii) EASIER —
the object is the (R,1)/Fejér mean, the smoothest classical summation kernel,
with nonnegative triangular weights (positivity structure the sharp sum
lacks; the classical Riesz-mean literature is the natural mine — method
research, sanctioned). Fallback grading: (TRI-bdd) with any exponent
κ ∈ (0, 2] (P ≤ Ca^κ/log^{κ/2}k) still closes §5 with the budget inflated by
(log log N)^{1−κ/2}-grade — the m-dial absorbs every κ > 0.

## 5. The theorem-shape this buys [conditional; the deterministic K]

**(Transfer Lemma).** Assume (TRI-bdd) at exponent κ = 2. Then for the true
matched walk: E_t[#O(1)-depth passes over all blocks] ≤ C·(log log N)^{3/2}
(the extra √(log log N) against the model's triple-log is the price of the
maximal inequality in §3 — moments only, no Markov property consumed), and

> **K₁(N) ≤ q₀·C·(log log N)^{3/2}·(exceptional-conversion) per U·log N
> samples; K_m(N) ≤ q₀^{m−1}·K₁(N).**

Consumer check (doc 57 Tier 2): fixed ε₀ is met at m = 2 for every N with
log log N ≤ (ε₀/q₀C)^{2/3}-range and by m = 3 beyond — the m-dial dominates
every polylog-log; the designed tower picks its monotonicity order once,
uniformly. All chain links except (TRI-bdd) are second-moment or Finset
grade; nothing exponential-class remains in Route C.

## 6. Pre-registered: the triple-log census (P-TL; the falsifiable signature)

Hull tests need no winding — cumsums only — so large N is cheap. Registered
BEFORE the run: N ∈ {40, 400, 4000, 40000}, 1200 samples/side/N, m ∈ {1, 2},
right and left slivers (σ = ½ ± u/log N, u ∈ (0.1, 2)).

- **P-TL1 (prior 0.7):** the RIGHT m = 1 fail rate stays ≤ 3% at every N and
  does not double across the 1000× range of N — flat-to-triple-log, the
  model's most distinctive claim (any competing mechanism — mean-share decay,
  variance growth, GAF symmetry — predicts a visible rise).
- **P-TL2 (prior 0.65):** the LEFT m = 1 fail rate RISES measurably with N
  and fits a₀ + a₁·log log N better than a constant (the left pass count is
  ≍ log L: the same mechanism's measurable shadow — doc 63 §3; current small-
  sample hint: 9, 12, 12, 24 fails/60 over N = 40…400).
- **P-TL3 (prior 0.8):** RIGHT m = 2 fails ≤ 1 event per 1200 at every N.
- **FALSIFIER:** a right m = 1 fail rate rising ∝ log log N or faster kills
  the triple-log law and demotes doc 63 §3 to heuristic; a left rate that
  stays flat kills the pass-count mechanism itself.

## 7. Census adjudication: THE FALSIFIER FIRED — and handed back two better laws

Run (triplelog_census.py, archived; 1200 samples/side/N, N up to 4·10⁴):

| N | log log N | R m1 /1200 | R m2 /1200 | L m1 rate | m2/m1 ratio |
|---|---|---|---|---|---|
| 40 | 1.31 | 1 | 0 | 0.143 | — |
| 400 | 1.79 | 10 | 3 | 0.238 | 0.30 |
| 4000 | 2.12 | 39 | 14 | 0.318 | 0.36 |
| 40000 | 2.36 | 73 | 25 | 0.368 | 0.34 |

- **P-TL1 FAIL — the falsifier fired.** The right m = 1 rate rises ×73 across
  the range — far faster than triple-log. Doc 63 §3's pass-count law is
  DEMOTED to a small-L heuristic; the near-pass/capacitance count is not the
  operative asymptotic mechanism at full weight support.
- **P-TL2 PASS, decisively:** left rates fit a₀ + a₁·log log N with
  interior residuals < 0.01 (slope 0.21) — the log-time-linear shadow law
  confirmed on the side where it was predicted.
- **P-TL3 FAIL as registered** (3, 14, 25 events), BUT the m-dial law is
  CONFIRMED in corrected form: **the m2/m1 ratio is constant ≈ 1/3** at every
  N — each Cesàro level buys a fixed factor q₀ ≈ 0.34, exactly the
  multiplicative dial doc 63 §3 claimed, without the absolute-level claim.
- **The corrected right-side law [measured, mechanism identified]:**
  ln δ₁ is LINEAR in 1/log log N (consecutive slope estimates −11.3, −16.1,
  −12.5) — the Gaussian-tail signature of ANGLE DIFFUSION: the trajectory's
  direction diffuses ~O(1) per e-fold of log-time (fitted diffusivity
  D ≈ 0.19/e-fold), and spread ≥ π is the Gaussian range-tail
  P ≈ exp(−π²/(4D·log log N)). Consequence: δ₁ → O(1) as N → ∞ — the GLOBAL
  hull obstruction over full weight support [1, N] degrades asymptotically,
  because the trajectory is given unboundedly many e-folds to spread.

**The design fix the mechanism forces (and doc 61 §4 already wanted).** The
hull condition involves ONLY k ∈ supp(ΔA). A plateau-then-taper carrier
(A ≡ A₀ on [1, N′], monotone taper on [N′, N] with log(N/N′) = O(1)) puts the
whole mixture on {S_{N′}} ∪ (a BOUNDED log-length arc): the spread of a
bounded arc is N-UNIFORM, and the m-dial's measured 1/3-per-level applies on
top. This is the same object the tower-compatibility cut demanded
(block-static weights, doc 61 §4) and the same shape as the classical
smoothed-AFE edge — three independent pressures now select one design.

> **(HULL-taper) [registered for the next probe, prior 0.7]:** plateau+taper
> carriers with log(N/N′) ≤ 1 have N-UNIFORM right-side hull-fail rates
> (no rise from N = 400 to 4·10⁴), at a level ≤ the α = 2 full-support rate
> at N = 400, with the m-dial ratio ≈ 1/3 preserved.

Register note: everything machine-checked this cycle (`CesaroHull.lean`:
`abel_pos_mixture`, `pos_mixture_ne_zero`, `carrier_ne_zero_of_psum_halfplane`,
`carrier_ne_zero_of_cesaro_halfplane`, `cesaroPsum_step/speed` — umbrella 8627
jobs, lint green, axiom-clean) is support-agnostic: the Lean layer consumes
whatever support the design chooses. Only the analytic pass-count/spread
input moves; the corrected target is the bounded-arc confinement bound —
strictly easier than the global statement the census just killed.
