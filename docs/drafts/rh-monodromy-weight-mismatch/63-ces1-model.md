# 63 — (CES-1) in the Random Model: the EMA/OU Representation, the Winding Budget, and the First Explicit K

**Register: SEARCH**; §2 is [PROVED HERE (model calculus)], §3 the priced
winding budget with one attack-as-false verdict on the session conjecture,
§4 the explicit-K shape, §6 pre-registered. Model = complex Brownian
caricature of the Steinhaus matched walk; the deterministic transfer is §5
(pair-correlation grade — this is the route that does NOT hit doc 58's
degree-2 wall).

## 1. The model and the clock

Right-sliver point s₀ = ½ + c/log N + it. Walk steps m^{−½−c/logN}·ξ_m,
ξ_m unimodular quasi-random. Log-clock τ(n) = Σ_{2≤m≤n} m^{−1−2c/log N}:
τ(N) = L·λ(c), L := log N, λ(c) = (1−e^{−2c})/(2c) ∈ (0,1] — the sliver
compresses the clock by a bounded factor only (the statement lives inside the
critical window; absorb λ into L). Model: Z(τ) = 1 + B(τ), B complex BM,
τ ∈ [0, L], Z(0) = Z_1 = 1 — the frozen start is the walk's anchor.

## 2. The Cesàro mean is a unit-bandwidth EMA; its deviation is OU [PROVED HERE (model)]

With θ = log k, the Cesàro mean Z̄_k = (1/k)Σ_{n≤k}Z_n becomes
Z̄(θ) = e^{−θ}∫_0^θ e^u Z(u) du (+e^{−θ}-edge), i.e. the exponential moving
average at unit bandwidth in log-time. Exactly:

> **(ODE)** dZ̄/dθ = Z(θ) − Z̄(θ). The deviation D := Z − Z̄ satisfies
> dD = −D dθ + dB — an **Ornstein–Uhlenbeck process**, E|D|² = O(1)
> stationary.

Consequences (the smoothing gain, quantified):
- Z̄ is C¹ with speed |Z̄′| = |D| = O(1): one averaging converts the walk
  into a smooth path whose angular motion is priced by |D|/|Z̄|.
- E|Z̄(θ) − 1|² = θ − O(1): the EMA tracks the walk's diffusive scale √θ.
- Angular-variation density: E[|d arg Z̄/dθ|] ≤ E[|D|/|Z̄|] ≲ θ^{−1/2}
  (Hölder with E|D|³ = O(1), E|Z̄|^{−3/2} ≲ θ^{−3/4}).

## 3. The winding budget: the conjecture corrected, the finite invariant found

**Attack-as-false verdict on the session conjecture** ("finite expected
variation of the winding functional"): FALSE as stated — the expected total
variation of arg Z̄ over [1, L] is ∫^L θ^{−1/2}dθ ≍ √L → ∞. The averaging
does not make the total winding finite; it makes it INTEGRABLE-density
(θ^{−1/2} vs the raw walk's roughness), which is not yet a count.

**The finite invariant lives one renormalization deeper.** A (CES-1)
violation (angular spread ≥ π of the path points) requires the smooth path
Z̄ to pass CLOSE to the origin relative to its own scale: a C¹ path at scale
√θ sweeps large angle-as-seen-from-0 only during passes at depth ≪ √θ (a
side-swipe at relative depth ρ sweeps ≤ π − Ω(ρ); exceeding π needs a deep
pass plus curvature). Price the passes by dyadic capacitance: for 2D
diffusive motion at scale √θ, P(hit ball(0, O(1)) during block [θ, 2θ]) ≈
c/log θ, so

> **E[#O(1)-depth passes over [1, L]] ≈ Σ_{j ≤ log₂ L} c/j ≍ log log L
> = log log log N.**

The near-pass count is the finite invariant: bounded by an absolute constant
times **triple-log of N** — ≤ 2 for every N below astronomical ranges, and
the exceptional density inherits it:

> **(model law)** δ₁(N) := density of right-sliver points violating (CES-1)
> ≈ q₀·(a₀ + a₁·log log log N), q₀ = P(pass converts to a wrap) = O(1).

Calibration against the measured data (cesaro_diag, doc 62 §5): right-side
fail fractions 0/60, 0/60, 0/60, 2/60 at N = 40…400 — consistent with
q₀·a-constants of a few percent and the triple-log invisible in any feasible
range. The model also explains the LEFT asymmetry: leftward the walk scale
grows with the steps (late steps dominate), the path re-approaches the origin
at every scale, and passes are ≍ log L — double-log-many, hence the measured
left erosion (51→36/60).

**The m-dial [the design consequence].** Each further Cesàro level (weights
of monotonicity order m, doc 62 §2.5) applies another unit-bandwidth EMA:
speed drops to the OU of the previous deviation, near-pass conversion
requires m-fold-deep approaches, and the model density picks up another
small factor: δ_m ≈ δ₁·q₀^{m−1}-grade. Since the growth in N is triple-log,
**m = 2 already pins the exceptional density below any fixed ε₀ for every N
that will ever be computed, and the m-dial beats the triple-log for all N**:
the designed tower should use order-2 (convex) weight profiles at least.

## 4. The first explicit K (model-grade, consumer-shaped)

Sliver samples decorrelate at t-spacing ≍ 1/log N (the walk's phases move by
O(1) across it), so a height window of length U carries ≈ U·log N independent
samples, and hull-violation is NECESSARY for a zero (doc 62 §1 — proved, not
model). Therefore, for a monotone-order-m designed carrier:

> **K_m(N) ≤ δ_m(N)·U·log N,  δ_1(N) = q₀(a₀ + a₁·log log log N),
> δ_2(N) ≤ q₀·δ_1(N).**

with measured calibration q₀a₀ ≈ 0.03 at m = 1 (and the m = 1 exceptional
points carried exactly the measured zeros — doc 62 §5). This is the first
K with an explicit N-dependence in the lane; it feeds
`midCentral_survivors_le` as-is, and doc 57's Tier-2 budget (a fixed ε₀)
is met by m = 2 for all sub-astronomical N and by the m-dial in general.

## 5. Why the deterministic transfer is NOT walled [the structural gift]

Every quantity in §§2–4 is a functional of {Z̄_k} — LINEAR in the monomials
m^{−it}. Its second-order data (E|Z̄|², E|D|², cross-correlations, the
capacitance functionals via Dynkin-type identities on quadratic test
functions) is exactly `SecondMoment.dpoly` territory: Montgomery–Vaughan
pair correlations compute them in matched windows with relative error
N^{θ−1}-grade. The degree-2 wall (doc 58 §2) blocked EXPONENTIAL functionals
of the field; the Cesàro obstruction consumes only quadratic ones. The
transfer lemma to type: a Kolmogorov–Rogozin/second-moment version of the
pass-count bound — near-pass probabilities from L² data alone (Paley–Zygmund
on |Z̄|² per dyadic block: E|Z̄|² ≈ θ and E|Z̄|⁴ ≲ θ² give
P(|Z̄| ≤ ρ√θ) ≤ 1 − (1−ρ²)²·(E|Z̄|²)²/E|Z̄|⁴ — a one-sided block bound with
NO Gaussianity), then block-chaining. All MV-computable for the true walk.

## 6. Pre-registered (P-CES; cheap; to run immediately after this doc banks)

- **P-CES2 (prior 0.75):** the doubly-averaged (m = 2) hull test passes
  ≥ 59/60 on the right at ALL N ∈ {40,100,200,400}, and its left-side pass
  rate exceeds m = 1's (each averaging suppresses both, right faster).
- **P-CES1b (prior 0.6):** the m = 1 right-side failures, where they occur,
  each contain a near-origin pass of the Cesàro path at relative depth
  ≤ 0.2 (the mechanism, observed directly).
- **FALSIFIER:** m = 2 right-failures ≥ m = 1's anywhere ⟹ the EMA-cascade
  picture is wrong; halt and re-derive §3's m-dial.

## 7. What this opens

1. The transfer lemma of §5 (block Paley–Zygmund + chaining) is the single
   remaining analytic step between the model law and a THEOREM-grade
   K_m(N) — and it is second-moment technology, the lane's most banked kind.
2. Lean: §2's finite analog (discrete EMA recursion Z̄_{k+1} − Z̄_k =
   (Z_{k+1} − Z̄_k)/(k+1), telescoping speed bounds) is Finset algebra —
   formalizable now alongside doc 62 §1's hull exclusion; wire both into
   `MollifiedDip` → `midCentral_survivors_le` so the whole Route C chain is
   machine-checked up to the pass-count input.
3. The triple-log law is a falsifiable signature no other mechanism predicts:
   if a large-N census ever sees the m = 1 exceptional density RISE along
   log log log N, the model is confirmed in its most distinctive claim.

## 8. Adjudication of §6 [MEASURED — ces2_probe.py, archived, same day]

- **P-CES2 PASS on both clauses:** right-side m = 2 hull test 60/60 at every
  N ∈ {40, 100, 200, 400} (m = 1 also 60/60 in this fresh sample — the m = 1
  fail rate is ≤ ~1%, consistent with the earlier 2/60 draw); left-side
  m = 2 (59, 56, 57, 56)/60 exceeds m = 1 (52, 46, 52, 47)/60 at every N —
  each averaging suppresses spread on both sides, right faster. The
  EMA-cascade/m-dial picture of §3 stands; the falsifier did not fire.
- **P-CES1b VACUOUS this round:** zero m = 1 failures in 240 fresh
  right-sliver samples — the near-pass mechanism clause remains untested at
  sample sizes feasible here (it needs the rare-event set; queue it with the
  next large census, not a dedicated run).
- Net for §4's K: at m = 2 the measured right-side exceptional density is
  0/240 pooled across all N — the model's δ₂ ≤ q₀·δ₁ is if anything
  conservative; the designed order-2 carrier's K is consistent with ZERO at
  every tested scale, with §5's transfer lemma the remaining step from
  model-grade to theorem-grade.
