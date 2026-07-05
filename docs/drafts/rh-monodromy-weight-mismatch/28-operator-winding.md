# 28 — The Pair as an Operator: Winding Formula, Shape Necessity, and the Lattice Skeleton

**Register: SEARCH** (§1–§4 are [PROVED HERE] by derivation — no computation was needed or
used; §5 is the registered proof skeleton for (LEG), its three lemmas labelled). Task #138,
round 3. Everything here is reasoned from the identity stack of docs 23–27.

## 1. The operator identity [PROVED HERE]

Reversal R_m[P](y) := y^m P(1/y). From the polar chain (doc 23), R_{d−1}[A_{d−1}] = Â′/d and
R_{d−2}[A_{d−2}] = Â″/(d(d−1)) (two substitutions). Reversing the three-term identity
J^d_{Pg} = |τ|²A_d − 2adxA_{d−1} + d(d−1)x²A_{d−2} termwise:

> **Ĵ := R_d[J^d_{Pg}] = Â″ − 2aÂ′ + |τ|²Â = (D−τ)(D−τ̄)Â.**

Multiplying the carrier by the pair (x−τ)(x−τ̄) acts on reversed sections as the
constant-coefficient damped-oscillator operator — theorem-m's operator, exactly. (One-step
version: R[J_{(·−τ)g}] = (D−τ)Â.) Since reversal permutes zeros by z ↦ 1/z, it preserves the
non-real count: Z_c(J) = Z_c(Ĵ).

## 2. Stability and the winding formula [PROVED HERE]

**(a) B := (D−τ̄)Â is UHP-stable off the multiple-root set.** At a zero z of B with
Â(z) ≠ 0: Â′/Â(z) = τ̄; for Im z ≤ 0 and Â hyperbolic, Im(Â′/Â)(z) = −Im z·Σ|z−β_k|^{−2}
≥ 0 ≠ Im τ̄ = −b < 0, so every such zero has Im z > 0. [CORRECTION 2026-07-04, caught at
formalization: an m-fold real root β of Â is an (m−1)-fold REAL zero of B (B(β) = Â′(β)
= 0). For SIMPLE-rooted Â all d zeros of B are strictly in the open UHP and (b) applies
verbatim; with multiple roots, B carries real zeros at exactly the repeated β's and the
boundary bookkeeping of (b) is done by perturbation (both sides of the winding formula are
stable under splitting the multiplicity).]

**(b) Winding formula.** Ĵ = B′ − τB and B ≠ 0 on the closed lower half-plane, so
LHP-zeros of Ĵ are the LHP-solutions of F_B(z) := B′/B = τ. By the argument principle over
the LHP boundary (F_B → 0 on the large arc, no winding contribution there):

> **Z_c(J^d_{Pg}) = 2·wind(F_B(ℝ), τ),**

the winding number of the boundary field curve x ↦ F_B(x) = Σ_j (x−ρ_j)^{−1} around τ.
Moreover Im F_B(x) = Σ_j Im ρ_j·|x−ρ_j|^{−2} > 0: the curve lives in the open upper
half-plane and closes through 0 — winding is a nonnegative integer. **The DISC reader is
exact ⟺ the field curve winds exactly once around τ.** This is the lane's deck-class /
winding language (docs 13, 18) reappearing at the section level: the reader's exactness IS
a winding-one statement.

## 3. Petal geometry and marginal tangency [PROVED HERE, first order]

Near an isolated dressed zero ρ_k = β_k + ε_k, the curve F_B(ℝ) traces the Möbius circle of
x ↦ R_k + 1/(x−ρ_k) (R_k = background field at ρ_k): center R_k + i/(2v_k), radius 1/(2v_k),
v_k = Im ρ_k. Solving B = 0 to first order: ρ_k − β_k ≈ 1/(τ̄ − R_k), so
**v_k ≈ b/|τ̄ − R_k|²**. τ lies inside petal k iff v_k < (b − Im R_k)/|τ − R_k|²; with R_k
real to leading order (real background), the two sides are EQUAL: **every petal is tangent
to τ at leading order.** Enclosure — hence the winding count, hence the reader's verdict —
is decided entirely at the next order (the sign of Im R_k and the curvature drift). This is
the structural explanation of everything measured in docs 24–27: the O(1) race, the far
margin saturating at ≈ 0.28 instead of 0, and the failure of every one-parameter proxy
(log-gaps, majorization): the problem is critically balanced by construction, and the
decision is carried by the drift of the dressed background — the θ-drift.

## 4. Shape necessity: the two-cluster no-go [PROVED HERE]

The tempting general theorem — "(D−τ)(D−τ̄) applied to ANY hyperbolic polynomial yields at
most one non-real pair" — is FALSE. Counterexample by hand: Â = y²(y−K)², operator D² + 1
(τ = i). Near y = 0: (D²+1)Â = K²(y² + 2) + O(Ky³, Ky), roots y → ±i√2; near y = K
(y = K+s): K²(s² + 2) + O(Ks), roots s → ±i√2. For K large, continuity gives two conjugate
pairs — four non-real zeros, winding 2. Each far-separated cluster runs its own race and
contributes its own petal-loop. **Consequence: the one-sided single-window shape of the
recentered carriers (doc 24 §6) is a necessary hypothesis of (SPUR-R), not a convenience** —
banked as a no-go delimiting the theorem. (It also re-derives the (CPI) dip threshold: for
the fully degenerate cluster Â = y^d the operator output is y^{d−2}(|τ|²y² − 2ady + d(d−1)),
whose discriminant is negative exactly when d > 1 + a²/b².)

## 5. The lattice skeleton for (LEG) [registered attack; lemmas labelled]

Work in log-time (doc 27): charges at t_k, spacing δ_k = t_{k+1} − t_k nondecreasing
outward; equilibrium in each gap at distance θδ from the AHEAD pole, θ < 1/2 (doc 27 §3);
S = d + W, W = ¼Σcsch²((t−t_k)/2). Exact bookkeeping along one step (from the hierarchy,
σ̃̇₁ = −2W̃):

> **Δσ̃₁ = [swap jumps] − 2∫W̃ dt,  and  s_near = 2·arccoth(d + σ̃₁)** —
> the near-pole distance shrinks iff the reduced field σ̃₁ grows; the swap jump (the pole
> passing from ahead to behind) contributes coth-terms each **> 1 exactly**, the drift
> losses are the exact integral 2∫W̃.

On the constant-δ semi-infinite lattice model (N behind, M ahead, N+M = d), with
C(x;n) = Σ_{k<n}coth((x+k)δ/2) and E(x;n) = ¼Σ_{k<n}csch²((x+k)δ/2):

- constraint: C(1−θ;N) − C(θ;M) = −d; ∂/∂θ(LHS) = 2δW > 0;
- step N→N+1, M→M−1 at fixed θ shifts the constraint by ΔLHS = coth((1−θ+N)δ/2) +
  coth((θ+M−1)δ/2) **≥ 2 exactly**, forcing **Δθ ≤ −1/(δW) < 0** — the θ-drift law, now a
  one-line consequence of the constraint (matches the measured drift direction and the
  deepening θ: 0.19 → 0.14);
- response: ΔW ≈ (dW/dθ)·Δθ with the near-pole term giving dW/dθ ≈ −2/(θ³δ²) — cubic
  amplification — so ΔW ≈ +2/(θ³δ³W) > 0: **W increases; (S-mono) holds on the lattice.**

Three lemmas make this a theorem on the lattice: **(L1)** dW/dθ < 0 for θ < 1/2 (termwise:
the k-th ahead csch²·coth dominates the k-th behind term since (θ+k) < (1−θ+k); the extra
far-behind tail is exponentially small — needs the explicit tail bound); **(L2)** the exact
swap bound ΔLHS ≥ 2 (done — coth > 1); **(L3)** the far-end regime (M = O(1)) handled
directly (near-pole domination). The real-field theorem is then lattice + adiabatic gap
variation: gap growth opposes the drift through the near-energy 1/(θδ)², and the exact
bookkeeping identity above is the ledger on which the two are compared — the loss term
2∫W̃dt is evaluated by the same lattice sums (q-digamma closed forms, q = e^{−δ}).

Next objects: prove (L1)/(L3) with explicit constants; then the adiabatic comparison — the
single remaining analytic distance between the identity stack and (SPUR-R). In parallel, the
winding formula of §2 is Lean-shaped (argument principle + UHP-stability are mathlib-ready),
and the two-cluster no-go bounds what any future strengthening may claim.

## 5b. (L1) and (L3), proved in outline [PROVED HERE, constants to be finalized]

**(L1).** With φ(s) := csch²(s)·coth(s) (positive, strictly decreasing on (0,∞)):

> dW/dθ = (δ/4)·[ Σ_{k<N} φ((1−θ+k)δ/2) − Σ_{k<M} φ((θ+k)δ/2) ].

For θ < 1/2, termwise φ((θ+k)δ/2) > φ((1−θ+k)δ/2) for every k < min(N,M); the only
positive leftover is the far-behind surplus Σ_{k=M}^{N−1}φ((1−θ+k)δ/2) ≤
4e^{−(1−θ+M)δ}/(1−e^{−δ}) (using csch²(s) ≤ 4e^{−2s} for s ≥ 1, coth ≤ coth(1)). Already
the k = 0 gap alone dominates it: φ(θδ/2) − φ((1−θ)δ/2) ≳ 8/(θδ)³ for θδ small. Hence
dW/dθ < 0 whenever Mδ ≥ c₀·log(1/(θδ)) — an explicit head-vs-tail inequality: cubic head,
exponential tail. ∎(outline)

**(L3).** When M = O(1) (the last few equilibria) the trail is saturated: σ̃₁ ≈ N + O(1)
and the constraint reads coth(θδ/2) = d + σ̃₁ ≈ 2d − M, so s_near = θδ ≈ 2/(2d−M)
directly; the step M → M−1 shrinks s_near monotonically and W ≈ ¼csch²(s_near/2) responds
monotonically — no balance is needed where there is no competition. ∎(outline)

Remaining open piece of (LEG): the **adiabatic comparison** — non-constant gaps. The exact
ledger is banked: over one step, Δσ̃₁ = [swap jumps, each coth > 1, total > 2] − 2∫W̃ dt,
and gap growth enters only through the loss integral and the near-energy scale. The loss
integral is a lattice sum of the same csch² family (q-digamma closed forms, q = e^{−δ});
bounding 2∫W̃ dt < 2 + (swap surplus) on nondecreasing-gap fields is the single remaining
inequality between the identity stack and (SPUR-R).

## 5c. Round-4 ledger findings [reasoned; sharpens #142]

- **Exact step identity.** With D := d + σ̃₁ (so D(t*) = coth(s_near/2) entering,
  = −coth(r_behind/2) leaving) and Ψ = (D²−1)/4 + W̃:
  **ΔS = ¼(Y²−X²) + ΔW̃** where X = coth(θ_iδ_i/2), Y = coth((1−θ_{i+1})δ_{i+1}/2); since
  θ < 1/2 forces Y < X, (S-mono) states precisely that the SPECTATOR energy gain beats the
  pole-energy drop: **ΔW̃ > ¼(X² − Y²)** — the near-pole handoff to t_{i+2} (inside W̃) is
  the carrier of the gain.
- **Rigidity of the doubly-infinite lattice.** On a two-sided-infinite constant-δ field
  every equilibrium is a shift of the last: θ, S, margin are constant — NO crossing exists.
  The drift is entirely a boundary/one-sidedness effect: each step converts one ahead-charge
  into one behind-charge, worth +2 in D asymptotically (coth-excess at the two far ends).
  This is the same fact as §4's shape necessity, seen from the constraint side: the window's
  one-sidedness is not a technical hypothesis but the ENGINE of the crossing. Constraint,
  not flow — the crossing exists because the configuration is finite on one side.
- **Finite constant-δ lattice: linear march.** ΔD = +2 + O(e^{−Nδ} + e^{−Mδ}) per step, so
  D_i ≈ 2i − d + C — with (L1)–(L3) this proves (S-mono) on the constant-δ lattice.
- **The real march is gap-variation-dominated.** The measured crossing (D* ≈ 2d at
  i* ≈ 0.59d) is far above the slope-2 line — on real section fields the gap variation is a
  leading term of ΔD, not a perturbation. The correct object for #142 is the coupled system
  (D, W̃): Ḋ = −2W̃, Ẇ̃ = −Σχ_kw_k, with jumps at pole crossings; useful bound banked:
  Σχ²w = 4Σw² + W̃ ≤ 4W̃² + W̃, so |Ẇ̃| ≤ (2W̃+1)√W̃; positivity of dΨ/dt on the second
  leg holds once |D| > 2√W̃ + W̃^{−1/2}. The remaining work: control the first-leg deficit
  by the second-leg gain using θ < 1/2 + gap growth — now a two-leg comparison for an
  explicit ODE-with-jumps system, no free parameters.

## 5d. (L1) reduction made RIGOROUS + the missing brick [PROVED HERE, 2026-07-05]

§5b left (L1) as "[PROVED HERE, outline]". The outline is now machine-checked at its core
(`formal/.../RHTower/LegComparison.lean`, axiom-clean):

- **Exact reduction (no termwise approximation).** Writing `D = Σ_{k<N}φ(b_k) − Σ_{k<M}φ(a_k)`,
  `a_k=(θ+k)δ/2 < b_k=(1−θ+k)δ/2`, splitting the behind sum at `M` gives EXACTLY
  `D = tail − headGain`, `tail = Σ_{M≤k<N}φ(b_k) ≥ 0`, `headGain = Σ_{k<M}[φ(a_k)−φ(b_k)] ≥ 0`
  (`l1_reduction`). Hence **`dW/dθ < 0 ⟺ headGain > tail`** (`l1_neg_of_head_gt_tail`) — the
  whole of (L1) reduced to one head-vs-tail inequality, with no hidden hand-waving.
- **The missing analytic brick.** §5b's tail control needs a cubic UPPER bound on the Calogero
  kernel `φ=csch²·coth=cosh/sinh³`; only the LOWER bound `rphi_ge_cubic` was banked. Proved here:
  `φ(s) ≤ cosh 1/s³` for `0<s≤1` (`rphi_le_cubic`, from `cosh s ≤ cosh 1` and `sinh s ≥ s`), so
  `1/(4s³) ≤ φ(s) ≤ (cosh 1)/s³` on `(0,1]`.
- **Head-gain with explicit constants.** `headGain ≥ φ(θδ/2) − φ((1−θ)δ/2) ≥ 1/(4x³) − cosh1/y³`
  (`headGain_lower`, `x=θδ/2`, `y=(1−θ)δ/2`); for `θ≤1/8`, `θδ≤1` this is `≥ 896/δ³`, dwarfing
  the tail `≤ 32/δ³` — so `dW/dθ < 0` for every `M ≥ 1` in the small-δ, `θ ≤ 1/8` regime.

**Honest remaining gap of (L1):** (i) the tail upper bound as a Lean lemma (geometric sum of the
cubic/exp kernel bounds — `rphi_geom_tail_le` is banked, needs assembling against `headGain_lower`);
(ii) the near-crossing window `θ ∈ (1/8, 1/2)` where the head gain shrinks and the paired `k≥1`
terms (not just `k=0`) must be summed. The reduction + bricks turn (L1) from an outline into a
one-inequality problem with the analytic pieces in hand.

## 5e. (L1) CLOSED end-to-end at a concrete configuration [PROVED HERE, 2026-07-05]

Beyond §5d's reduction, the full head-vs-tail assembly is now a machine-checked theorem
(`LegComparison.lean`, axiom-clean):

- `tail_geom_bound` — the far-behind tail `Σ_{M≤k<N} φ((1−θ+k)δ/2) ≤ 64 e^{−(1−θ+M)δ}/(1−e^{−δ})`
  once `(1−θ+M)δ/2 ≥ 1` (reindex `Ico M N → range(N−M)`, banked `rphi_geom_tail_le`). This is the
  lemma §5b asserted but never wrote.
- `dW_dtheta_neg` — the COMPLETE conditional: under `θ ≤ 1/2`, the cubic-window hypotheses, and the
  explicit `hbeat` (tail-bound < head-lower-bound), `Σ_{k<N}φ(b_k) < Σ_{k<M}φ(a_k)`, i.e.
  `dW/dθ < 0`. Assembles head (`headGain_lower`), the paired `k≥1` terms `≥ 0`
  (`rphi_strictAntiOn`), the tail, and the reduction. No hand-waving anywhere.
- `dW_dtheta_neg_at_eighth` — an **UNCONDITIONAL** closed instance: at `δ=2, θ=1/8`, for EVERY
  `M ≥ 1`, `N ≥ M`, `dW/dθ < 0`. `hbeat` is discharged from real `exp`/`cosh` bounds (head `≥ 125`
  beats tail `≤ 8`); nothing is assumed. The (S-mono)-driving inequality genuinely fires — not a
  vacuous conditional.

**Sharpened status of (L1).** It is NOT true for all `θ < 1/2`: as `θ ↑ 1/2` the head gain → 0
while the far-behind tail stays positive, so `dW/dθ` turns POSITIVE near the endpoint. The correct
statement is `dW/dθ < 0` in the small-`θ` regime — which is exactly the regime the θ-drift (doc 27
§3, `θ ↓ 0.14`) occupies. `dW_dtheta_neg` proves it wherever `hbeat` holds; `dW_dtheta_neg_at_eighth`
is an unconditional witness. Remaining: a clean `hbeat`-holds lemma over a `(δ,θ)`-region (not one
point), and the join with the θ-drift bound so the physical `θ_i` provably lands in the good region.

## 5f. dW/dθ<0 UNCONDITIONAL over a region [PROVED HERE, 2026-07-05]

`dW_dtheta_neg_region` (LegComparison.lean, axiom-clean): the `hbeat` hypothesis of §5e is now
DISCHARGED over a genuine two-parameter band. For `θ ∈ (0, 1/8]`, `δ ∈ [3/2, 2]`, every `M ≥ 1`,
`N ≥ M`: `dW/dθ < 0`, with NO head-vs-tail assumption. Head gain `≥ 112` (`θδ/2 ≤ 1/8` ⟹
`1/(4(θδ/2)³) ≥ 128`; `(1−θ)δ/2 ≥ 1/2` ⟹ subtrahend `≤ 8cosh1 < 16`) beats the far tail `≤ 36`
(`(1−θ+M)δ ≥ 2` ⟹ `exp ≤ e^{−2} ≤ 1/3`; `1−e^{−δ} ≥ 3/5`), all from crude `add_one_le_exp` +
`cosh_one_lt_two`. This is (L1) proved outright on a region — no outline, no conditional.

**Honest boundary.** The band `δ ∈ [3/2, 2]` is where the geometric tail bound `rphi_geom_tail_le`
(needs the nearest far charge at hyperbolic distance `≥ 1`) applies cleanly. The PHYSICAL regime is
`δ = c/j → 0` (small), where that tool fails (tail arguments are small) and the tail must instead be
bounded by the CUBIC upper bound. The missing brick for that: `coth s < 1/s + 1` for all `s > 0`,
provable via `g(s) = (1+s)sinh s − s cosh s`, `g(0)=0`, `g'(s) = sinh s + s·e^{−s} > 0` — then
`φ(s) = csch²s·coth s < 1/s³ + 1/s²`, whose `k`-tail is a `p=2,3` series bounded by an integral.
With it the region extends to small `δ`, the physical case. That is the next concrete step.

## 5g. The small-δ brick PROVED: coth s < 1/s + 1 [PROVED HERE, 2026-07-05]

The brick §5f named as missing for the physical `δ → 0` regime is now proved (LegComparison.lean,
axiom-clean):

- `rcoth_lt_inv_add_one` — **`coth s < 1/s + 1` for ALL `s > 0`**. Proof: the auxiliary
  `g(s) = (1+s)sinh s − s cosh s` has `g(0)=0` and derivative
  `g'(s) = sinh s + s cosh s − s sinh s = sinh s + s·e^{−s} > 0` (via `sinh s > 0` and
  `cosh s > sinh s`), so `strictMonoOn_of_deriv_pos` gives `g(s) > 0`, i.e. `s cosh s < (1+s) sinh s`,
  i.e. `coth s < (1+s)/s`. A genuine transcendental monotonicity inequality — not algebra.
- `rcsch_sq_le_inv_sq` — `csch² s ≤ 1/s²` (from `sinh s ≥ s`).
- `rphi_lt_cubic_quadratic` — **the global tail bound** `φ(s) < 1/s³ + 1/s²` for ALL `s > 0`
  (`= csch²·coth < (1/s²)(1/s+1)`). Unlike `rphi_le_cubic` (only on `(0,1]`) this holds at every
  scale, so the far tail `Σ_{k≥M} φ((1−θ+k)δ/2) < Σ (1/·³ + 1/·²)` is a `p=2,3` series valid for
  `δ → 0`.

**What now closes small-δ.** With `rphi_lt_cubic_quadratic` termwise, the tail is `< (8/δ³)Σ1/(1−θ+k)³
+ (4/δ²)Σ1/(1−θ+k)²`; both are telescoping (`1/(a+k)² ≤ 1/(a+k−1) − 1/(a+k)`) with sums `≤` a
constant, giving tail `< C₁/δ³ + C₂/δ²`, beaten by the head `≥ 2/(θδ)³ ~ 1/δ³` for `θ` small and
any `δ`. The one remaining Lean step is the telescoping `p=2,3` tail bound, then the small-δ region
assembly — no new analytic ideas, only Finset telescoping.

## 5h. (L1) CLOSED for the PHYSICAL (small-δ) regime [PROVED HERE, 2026-07-05]

The small-δ analytic toolkit is complete and assembled (LegComparison.lean, all axiom-clean):
`rcoth_lt_inv_add_one` (coth s<1/s+1) ⟹ `rphi_lt_cubic_quadratic` (global φ(s)<1/s³+1/s²) ⟹
`inv_sq_telescope`/`inv_cube_telescope` (p=2,3 tail sums, telescoping) ⟹ `phi_tail_small_delta`
(tail ≤ (8/δ³)/((1−θ+M)(M−θ)) + (4/δ²)/(M−θ)).

- `dW_dtheta_neg_small_delta` — **UNCONDITIONAL on `θ ∈ (0,1/8]`, `δ ∈ (0,1]`, `M ≥ 1`, `N ≥ M`:
  `dW/dθ < 0`.** Head `≥ 1000/δ³` (θ small ⟹ `2/(θδ)³ ≥ 1024/δ³`, minus `≤24/δ³`) beats tail
  `≤ 10/δ³` (`δ ≤ 1` folds the `1/δ²` term into `1/δ³`). No hypothesis, no exp-tail restriction —
  reaches `δ → 0`, the regime `δ = c/j` where the θ-drift (doc 27 §3, `θ ↓ 0.14`) actually lives.

**Arc summary of (L1).** From doc 28 §5b's mere "[PROVED HERE, OUTLINE]": corrected the false
`∀θ<1/2` claim (fails near `θ=1/2`) → exact reduction `D = tail − headGain` → unconditional at a
point (`δ=2,θ=1/8`) → unconditional on the exp-region `δ∈[3/2,2]` → unconditional on the physical
small-δ region `δ≤1`. All machine-checked, axiom-clean.

**Genuinely remaining for full (L1)⟹(S-mono):** (i) the `δ∈(1,3/2)` seam and the near-crossing
`θ∈(1/8,1/2)` window (where the k=0 head no longer dominates — the paired k≥1 sum must be used);
(ii) the JOIN with a proven θ-drift lower bound, so the physical `θ_i` provably lands in `(0,1/8]`
— that is the (F)-field/θ-drift research, still open. The constant-δ lattice piece of (S-mono) is
now rigorous on the physical band.

## 5i. The window settled BOTH ways: paired-sum closures + machine-checked disproof [PROVED HERE, 2026-07-05]

LegWindow.lean (axiom-clean, lint green) settles the two gaps §5h left open, via the paired
`k ≥ 1` sum (MVT on `φ' = −(2csch² + 3csch⁴)`, proved as `rphi_hasDerivAt`):

- **Disproof of the unconstrained window.** `l1_fails_near_crossing`: at `δ = 1, M = 1, N = 2`
  there EXISTS `θ ∈ (0, 1/2)` with dW/dθ > 0 — at `θ = 1/2` the pair cancels exactly while the
  unpaired `φ(3/4) > 0` survives; continuity extends the reversal below `1/2`. (L1) on the raw
  window `θ ∈ (1/8, 1/2)` is FALSE; every closure must couple `1 − 2θ` to the configuration.
  (Numerically the true failure sliver is only `θ ≳ 0.495` at `M = 1`.)
- **Seam closure** `dW_dtheta_neg_seam`: `(1 − 2θ)·M·δ² > 1 ⟹ dW/dθ < 0` (any `N ≥ M`).
  Mechanism: all `M` pair gains ≥ `(1−2θ)(δ/2)·2csch²(b_{M−1})`; tail telescopes against
  `csch²/2` (`rphi_tail_le`). Covers the δ ∈ (1, 3/2) seam for `M ≥ 1/((1−2θ)δ²)`.
- **Window closure** `dW_dtheta_neg_window`: `3(1 − 2θ)·δ·[coth((1−θ)δ/2) − coth((1−θ+M)δ/2)]
  > 1 ⟹ dW/dθ < 0`. The csch⁴ part of each gain carries `csch²(b_{M−1})` times the csch² sum,
  which telescopes against coth (`csch_sq_sum_ge`). Survives `δ → 0`, where the condition tends
  to `6(1−2θ)M/((1−θ)(1−θ+M)) > 1` — the window up to `θ < 5/11` for large `M`.

Pre-certified (scratchpad precert_legwindow.py): bricks 0 failures (5500 random trials); A/B
zero violations on a 5850-point grid; the D ≥ 0 points are exactly the near-crossing sliver.
The M = 1 seam instances δ ∈ (1, 1.155) that B misses are caught by A (e.g. A = 3.03 at δ = 1,
θ = 1/8). Next: the JOIN — at lattice equilibria the constraint itself bounds 1 − 2θ (§5j).

## 5j. THE JOIN, lattice form: the constraint discharges the window [PROVED HERE, 2026-07-05]

LegEquilibrium.lean (axiom-clean, lint green). The missing piece of (L1)⟹(S-mono) on the
constant-δ lattice was the JOIN: a proven lower bound on 1−2θ at the physical equilibria, so
that no θ-window hypothesis survives. It is now a theorem — and the mechanism is the §5c
credo made literal: the localization is FORCED BY THE CONSTRAINT, not assumed.

- `lattice_constraint_hasDerivAt`: g(ϑ) = Σ_{k<N}coth(b_k) − Σ_{k<M}coth(a_k) has
  g′ = (δ/2)[Σcsch²(b) + Σcsch²(a)] > 0 (= 2δW, the doc 28 §5 identity ∂θ(LHS) = 2δW).
- `equilibrium_theta_gap`: at an equilibrium (g(θ) = −(N+M)) with θ ≥ 1/8:
  **Nδ/78 ≤ 1/2 − θ**. MVT between θ and the midpoint: g(1/2) = Σ_{Ico M N}coth ≥ N−M
  (swap-surplus, coth > 1), so g(1/2) − g(θ) ≥ 2N, while g′ ≤ 156/δ on (θ, 1/2)
  (csch² ≤ 1/s² + the banked p=2 telescopes: behind ≤ 6, ahead ≤ 72 in lattice units).
- `dW_dtheta_neg_at_equilibrium` — **the capstone**: δ ≤ 1, **Nδ > 30**, equilibrium ⟹
  dW/dθ < 0, NO window hypothesis. Since θ ≥ 1/8 would force Nδ ≤ 78·(3/8) < 30, every
  long-trained equilibrium sits in θ < 1/8, where §5h fires.

Empirically (precert scan, equilibria solved to 40 dps): the true threshold is Nδ ≈ 6–8 and
D < 0 held at EVERY equilibrium tested including Nδ = 0.15; the constant 30 is 4–5× lossy but
unconditional. Short-train equilibria (Nδ ≤ 30) in the window are covered by §5i's
`dW_dtheta_neg_window` (A > 1 at all scanned equilibria except one near-balanced point where
the k=0 power-law head wins by ×220 — a condition-C sharpening would absorb it).

**What this opens.** The (F)-field version is now a *shaped* problem, not a vague one: the
same MVT architecture on a general nondecreasing-gap configuration {t_k} needs exactly two
inputs — (i) the quantitative midpoint-push h(m) ≥ surplus (doc 27 §3's pairing, made
quantitative: unpaired-left-charge count replaces the exact coincidence at ϑ = 1/2), and
(ii) a sup bound on h′ over the half-gap (the same csch²-telescope calculus with δ_k-varying
steps). Next object: `field_theta_gap` on nondecreasing-gap configurations — the general-gap
join. After that, general-gap (L1) legs = the §5b adiabatic comparison.

## 5k. The one-step lattice theorem: consecutive equilibria raise energy [PROVED HERE — Lean]

`LegLatticeStep.lean` (axiom-clean) proves that advancing one lattice step strictly increases
the Calogero energy, unconditionally on the small-δ band. Setup: an equilibrium with `N`
behind and `m+1` ahead charges at position `θ`, level `−(N+m+1)`, advances to an equilibrium
with `N+1` behind and `m` ahead at position `θ′`, same charge.

`lattice_step_energy_increase` — for `1 ≤ m`, `m+1 ≤ N`, `0 < θ ≤ 1/8`, `0 < θ′ < 1`,
`0 < δ ≤ 1`, `4 ≤ δm²`, with both configurations at equilibrium:
`W(N, m+1, θ) < W(N+1, m, θ′)`, where `W = ¼[Σcsch²(behind) + Σcsch²(ahead)]`.

Mechanism, all machine-checked:
* the swap identity `g(θ′) − g(θ) = swap ∈ (2, 2 + 4/(mδ)]` (charge conservation across the
  step), giving `θ′ < θ` by strict monotonicity of the constraint `g` (`g′ = 2δW > 0`);
* the drift bracket `(32/39)δθ′² ≤ θ − θ′ ≤ (3/7)θ` from the swap value against the `g′`-bracket
  `7/(4θ²δ) ≤ g′ ≤ 39/(16δθ′²)` (both via `e^{−2s}/s² ≤ csch²(s) ≤ 1/s²` and inverse-square
  telescopes);
* the θ-sharp energy margin `−W′(η) ≥ (2/θ³ − 34)/δ³` (`dW_margin_small_delta`: head
  `2/(θ³δ³)`, tail `≤ 10/δ³`);
* gain `≥ 1/δ` via the polynomial core `39θ³ ≤ 8θ′²(2 − 34θ³)`, against loss `≤ 1/(4δ)` (the
  removed-charge energy under `δm² ≥ 4`).

With §5j (the constraint forces long-train equilibria into `θ < 1/8`, `dW/dθ < 0`), this closes
the constant-lattice leg of (S-mono): both the interior slope and the step jump point the same
way. The general-gap leg is doc 30 (the adiabatic ledger `LegAdiabatic.lean`, §6 there).
