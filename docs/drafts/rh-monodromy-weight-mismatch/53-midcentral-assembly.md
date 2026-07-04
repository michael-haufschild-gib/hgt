# 53 — (MID-central) Assembled: Four Lemmas, Machine-Checked Skeleton, One Computation

**Register: LEDGER for the Lean content; SEARCH for §4** (tasks #156–#160).
Lean: `RHTower/DriftDip.lean`, `HoldPhase.lean`, `CreationRate.lean`,
`MidCentral.lean` — umbrella 8618 jobs, lint green, all capstones axiom-clean
[propext, Classical.choice, Quot.sound], zero sorries.

## 1. What is now PROVED in Lean (the four lemmas' cores)

**(DRIFT-dip) — fully proved** (`drift_dip`, `drift_dip_excursion`): a
cumulative angle walk with per-step increments in [θmin, θmax] ⊂ (0, π/3]
reaches, within 2π + θmax of angle progress, a block on which cos ≤ −1/2 for
every offset j with j·θmax ≤ π/3; with amplitude floor a the walk takes a
negative excursion of size (L+1)·a/2. Only step bounds are consumed — the
certified drift formula (doc 50 §4) supplies them blockwise, so the lemma is
drift-robust exactly as doc 51 §4 demanded. Supporting bricks:
`angle_growth`, `angle_span`, `exists_first_passage`,
`cos_le_neg_half_on_window`.

**(HOLD-phase) — proved bricks** (`pair_hasDerivAt`, `pair_deriv_norm`,
`hold_kill_criterion`, `coherent_sum_lower`): the two-zero factorization
derivative identity Z′(iη) = 2iη·g(iη) (the exact reach denominator of doc
46 §5); the kill-margin algebra A·c ≤ −d ⟺ (A/d)·(−c) ≥ 1 (= cos(slip)·R ≥ 1
of doc 51 §9(b)); the coherent accumulation lower bound (≥ half mass within
π/3 total spread — the |H|-growth engine).

**(CR-density) — proved bridges** (`finset_chebyshev`, `far_kernel_lower`,
`pricing_pigeonhole`): the variance→anti-concentration counting bridge
(#{|f| ≥ λ} ≤ Σf²/λ²); the far-kernel bound (a Poisson kernel at planar
distance ≥ c is ≥ −1/c); the tangency-pricing pigeonhole (kernel sum below
−(B + n/c) forces a c-close zero).

**Assembly — proved** (`MidCentralInput`, `midCentral_survivors_le`,
`midCentral_empty`, `midCentral_survivors_in_window`,
`killedFrom_of_prefix_nonpos`, `birthKilled_of_prefix_dip`): over the
cascade bookkeeping of `SweepCascade`, positive-depth births with (i) a
prefix-dip for every out-of-window birth and (ii) an in-window creation bound
K have at most K survivors, all localized to the slip window — (MID-central)
in counting form, machine-checked end to end.

## 2. Where the remaining analytic content sits — exactly two hypothesis fields

- `dip_kills`: out-of-window births have a killing prefix-dip. Supplied on
  paper by `drift_dip_excursion` + the amplitude floor; the floor's
  availability against the configurational |H| is the open (HOLD-phase)
  kernel (doc 51 §9(b)).
- `creation_rate`: in-window births ≤ K. Supplied by the (CR-density) chain
  once the partial-fraction decomposition + variance of log|F_N| are proven
  (doc 52 §4, §8 no-go recorded).

Nothing else is open in the skeleton: every reduction between these fields
and the survivor count is a theorem.

## 3. (DEEP-FATE) — the sanctioned computation, adjudicated

`computations/mwm/deep_fate_tracker.py` (pre-registered), 11 census events
tracked through k = birth … N+10 with the exact census carrier:

- **P-DF2 PASS**: off-line runs below matched level ≤ 3·N^{1/3} entries.
- **P-DF3 PASS for the resonant survivors**: 6/8 mid-band pairs exist for
  exactly ONE entry epoch (on-line at N−1, pair at N, reabsorbed at N+1) —
  census survivors are ephemeral resonance objects, as the hold story says.
- **P-DF1 FAIL, informatively**: the window-edge event (d = 0.182, N = 28)
  DEEPENS past matched level to η = 0.425 ≈ N^{−1/4} — doc 48 §3's feared
  branch is real — then saturates and is reabsorbed within ~10 ≈ 3.3·N^{1/3}
  entries. Same shape for shallow events entering over-resolution (k > N).
  The deepen branch lives ONLY in the over-resolved regime, outside the
  bridge's matched object; it saturates at the predicted scale and dies on
  the (DRIFT-dip) clock. No accumulation, no persistence, anywhere.

Consequence for the assembly: no fifth input is needed; the measured
absorption clock (≈ 3·N^{1/3}) is the constant the paper-side (DRIFT-dip)
bookkeeping should reproduce.

## 4. What this opens

1. The (HOLD-phase) kernel is now ONE inequality: an amplitude floor for the
   walk against |H| in the window — attack via `coherent_sum_lower` applied
   to the background blocks (the anti-phase→coherent transition across the
   window is where |H| stiffens; doc 51 §9(b)).
2. (CR-density)'s Lean-side is ready to consume a partial-fraction
   decomposition of Re(F_N′/F_N): formalizing THAT (finite Blaschke/Hadamard
   for Dirichlet polynomials) is a self-contained next module.
3. The over-resolved deepen-saturate-die arc (P-DF1's fail) is new
   phenomenology: η_max ≈ k^{−1/4} at saturation suggests the valley depth
   of the over-resolved carrier is itself the (BVAL) object — a second,
   independent window into the background rigidity question of doc 46 §6.
4. Feed `midCentral_survivors_in_window` back through the deck relation: the
   (SWEEP-margin) boundary term is now formally the in-window population —
   the bridge's remaining arithmetic is K-counting in a 0.19-wide window.

## 5. Cycle-18 update: the walk tier is COMPLETE (RotationDip + PerturbedDip)

New Lean, all proved, axiom-clean (umbrella 8620 jobs, lint green):
- `sum_cos_closed_form` — the walk's prefix sums are the circle chord
  r·cos γ − r·cos(γ + Mθ), exactly (geometric sums, no estimates).
- `exists_orbit_cos_ge` + `rotation_dip` — the first-wrap dip: a misaligned
  start (cos γ ≤ 1 − δ) dips below −r(δ − (1 − cos(θ/2))) within one wrap.
  Kill-power fades exactly at anti-phase (θ ≈ π) — marginal dominance, as the
  physics demands.
- `perturbed_rotation_dip` + `birthKilled_of_perturbed_rotation` — phase
  errors ≤ e₀ (the certified cubic drift) and envelope decay [a_min, a_max]
  absorbed as explicit budgets; `dip_kills` discharged for REAL pushes.
- `polar_ratio_explicit` — the polar data in closed form: γ = β − θ/2 + π/2,
  r = 1/(2 sin(θ/2)); the alignment window is now an explicit condition on
  (β, θ) alone. Plus `one_sub_exp_eq`, `abs_cos_sub_cos_le`,
  `log_ratio_bounds` (the step-angle input 1/j ≤ log(j/(j−1)) ≤ 1/(j−1)).

**Nothing below the carrier boundary remains unproven.** The complete
remaining distance to (MID-central) fully-proven is three named tiers:
- (T1) birth-phase supply: β at birth = the stationary value πn₀ − 2πd² + π/8
  (certified numerically; Lean needs the RS-theta/Stirling expansion) — this
  converts "out of slip window" into the misalignment hypothesis of
  `birthKilled_of_perturbed_rotation`.
- (T2) carrier-per-entry reading: each tower entry updates a pair's depth by
  one real push of the stated cosine form (doc 48's dichotomy globalized —
  zero-continuation/IFT grade).
- (T3) (CR-density) — the in-window creation bound: OPEN mathematics (doc 52
  §4, §8), not merely unformalized.

## 6. Cycle-19 update: (T2) general machinery COMPLETE; (T1) reframed

- `DepthUpdate.lean` BANKED: the walk update η² ← η² + εq₀ is the LITERAL
  zero motion (zeros of v² + D exactly ±i√D / ±√(−D)); center-over-cofactor
  d = Z(0)/h(0).
- `PairPeel.lean` BANKED: double application of the banked `exists_peel`
  gives the global factored form Z = (v² + η²)·h with h analytic and
  zero-free on all of U, from "two simple zeros, no others" — plus the exact
  depth reading η² = Z(0)/h(0) (`pair_peel_depth`). Umbrella 8622 jobs, lint
  green, axiom-clean. **Tier (T2) is now complete at the general level**; the
  residue is per-instance (doc 48 §2's checkable Rouché count) plus the
  analytic supply of order-1 data.
- **(T1) reframed after the Stirling audit** (user prompt: "don't we have
  that stirling already?"): mathlib has only real asymptotic Stirling and a
  64-line Complex.digamma stub (definition, recursion, meromorphy) — BUT the
  assembly consumes only derivative-level data (θ′, θ″); the absolute π/8
  rides abstractly. (T1) = digamma partial fractions from
  `Complex.GammaSeq_tendsto_Gamma` + vertical-line bounds via the banked
  `log_ratio_bounds` — a contained module, not a Binet build.
- Open ledger for full (MID-central): (T1) contained-module grade; (T2)
  per-instance + order-1 supply; (T3) (CR-density) — open mathematics.
