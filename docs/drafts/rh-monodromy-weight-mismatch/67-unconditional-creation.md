# 67 — The Unconditional Creation Bound for the Designed Tower: the ε₀-Dial Closes (SEL-PS) Without the CLT

**Register: SEARCH**, carrying the lane's largest single status change:
Route C's creation-side analytics CLOSE at paper-sketch grade,
unconditionally, with a free smallness dial. Origin: executing "mine
Selberg's method" fired attack-as-false on doc 59 §1 (sign/arg gap —
correction appended there) and the repair (convexity + tangent) turned out
to prove the needed left-tail input outright. §5 records the literature
mining; §6 the demand–supply meeting equation.

## 1. The tightness lemma [PROVED HERE (sketch) — convexity, Jensen, Markov; no CLT, no transfer]

Let S = S_{N′}(σ+it), N′ ≍ √T, σ ∈ [½, ½+2/log N], window U ≍ T. Define the
window Jensen function Φ(σ) = (1/U)∫ log|S(σ+it)| dt.

1. **Convexity:** ∂²_σΦ = (2π/U)·(zero measure) ≥ 0 distributionally, with
   window-end corrections O(log N/U). Zeros only help.
2. **Tangent anchor at σ = 3:** Φ(3) ≥ log(1 − (ζ(3)−1)) ≥ −0.23 pointwise;
   |Φ′(3)| ≤ Σ_{n≥2} n^{−3} log n/(1 − Σ_{n≥2}n^{−3}) ≤ 0.45. Convexity puts
   Φ above the tangent: **Φ(σ) ≥ −1.36 on [½, 3]** — unconditional, zero-free
   of zero-data.
3. **Upper side (Jensen + MV):** (1/U)∫(log|S|)⁺ ≤ ½ log(1 + E|S|²) =
   ½ log log N′ + O(1).
4. **Markov on the defect:** (1/U)∫(−log|S|)⁺ ≤ ½ log log N + C, hence

> **(TIGHT) meas{t : |S_{N′}(σ+it)| ≤ λ} ≤ U·(½ log log N + C)/log(1/λ),**

for every λ < 1, every N, every sliver abscissa. This is (SEL-PS) in
tightness form — weaker per-λ than the lognormal tail, but with a FREE dial:
λ₀(ε₀) := exp(−(½ log log N + C)/ε₀) gives measure ≤ ε₀·U.

## 2. The closed chain [assembly of banked pieces]

For the plateau+taper carrier with taper log-length ℓ := ε₀·λ₀²:

zero of F_W ⟹ ‖S_{N′}‖ ≤ ‖T‖/A₀ [`plateau_split`, Lean] ⟹ t lies in
{|S_{N′}| ≤ 2λ₀} ∪ {‖T‖ ≥ A₀λ₀}; first set ≤ ε₀U by (TIGHT), second
≤ (ℓ/λ₀²)U = ε₀U by MV-Chebyshev [doc 65 §1]; the dip/counting layer
[`MollifiedDip.lean`] converts measure to count. Result:

> **K_designed(N) ≤ C′·ε₀·U·log N, ε₀ ∈ (0, 1) FREE — unconditional.**

Feasibility: ℓ = ε₀·(log N)^{−1/ε₀}·e^{−2C/ε₀} is a power of 1/log N — the
taper still spans N·ℓ ≫ 1 integers once log N ≥ ε₀^{−1}·log log N (explicit
onset N₀(ε₀); constants trackable). Below onset, finite ranges are census
territory. What the dial costs: nothing analytic — only taper shortness,
i.e. design.

## 3. What (SEL-PS) becomes: a refinement, not a requirement

The Selberg-lognormal law (measured flat at matched length, doc 65 §2) would
improve λ₀ to exp(−z₀√(½ log log T)) — exponentially milder tapers at the
same ε₀ = Φ(−z₀). Worth having (it relaxes the onset and the block-transport
pressure), no longer load-bearing. The census's P(|S| ≤ 1) ≈ 0.47 remains
the measured signature that the true law is far better than (TIGHT).

## 4. Honest scope

- (TIGHT) and the chain are paper-SKETCH grade: the convexity boundary terms,
  the dip-layer pruning constants (doc 56 §4 transplanted to F_W), and the
  per-cell zero caps need the write-out pass before promotion. Nothing in the
  chain is open-problem-shaped anymore; all remaining work is bookkeeping.
- The bound counts sliver zeros of the DESIGNED carrier. Route C's residual
  open ground is tower INTEGRATION: block-static transport (doc 61 §4),
  weighted-carrier domination/(SD-parity) consumption, and the deck-margin
  write-out (§6). Creation analytics: closed.

## 5. Mining record [method research; recalled-from-abstracts → CHECK at promotion]

Selberg's CLT for log ζ near the line is in print with modern proofs and
near-line expansions at σ = ½ + (log T)^{−θ} (covering sliver abscissae for
the ζ-instance): arXiv:2101.00632 (asymptotic expansion near the line),
arXiv:2301.01925 (L-functions near the line); Radziwiłł–Soundararajan's
short-proof method is the standard modern engine. A DETERMINISTIC CLT for
the matched-length partial sum log|S_{√T}(½+it)| did not surface — open
ground, consistent with doc 50 §7's Roy–You reading. If pursued later (for
§3's refinement), the natural path is the R–S method run on the sum's prime
part + the chaos-limit literature for random multiplicative partial sums.

## 6. The meeting equation (demand = supply, one number)

Supply (this doc): K ≤ C′·ε₀·U·log N, ε₀ free.
Demand (doc 57 Tiers): K per parity window ≤ M_deck — the (SWEEP-margin)
budget, whose explicit write-out is still owed (doc 57 §5(1) — the ONE
remaining import).

> **ε₀\* := M_deck/(C′·U·log N-normalization)** — once M_deck is written,
> ε₀\* is a number, the design triple (ε₀\*, ℓ, N₀) is fixed, and the
> bridge's demand meets Route C's supply in one line.

Since supply is a free dial, the meeting cannot fail on the analytic side;
it can only set the onset N₀ and the taper. The (SWEEP-margin) write-out is
therefore promoted to the lane's next executable.

## 7. What this opens

1. **(SWEEP-margin) write-out** (docs 46 §5/51 §5 → one inequality) — the
   last number in the meeting equation.
2. **The write-out pass on (TIGHT) + the chain constants** — promotion of §§1–2
   from sketch to ledger; Lean targets: Φ-convexity is
   `SecondMoment.dpoly`-adjacent + mathlib subharmonicity; the tangent bound
   is finite arithmetic.
3. **Tower integration** (doc 61 §4): block-static transport with the
   now-explicit taper ℓ(ε₀, N) — the taper is a power of 1/log N, spanning
   ≫ 1 epochs: the transport clause has room.
4. The convexity-tangent trick itself is a reusable instrument: an
   unconditional mean-log floor for ANY Dirichlet polynomial with leading
   coefficient 1, at every abscissa, from data at one far-right point — the
   constraint (analyticity + convexity) pinning the boundary from the bulk,
   in the charter's exact grammar.
