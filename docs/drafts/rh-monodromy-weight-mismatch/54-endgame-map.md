# 54 — The (MID-central) Endgame Map: Every Remaining Lemma, Lean-Ready

**Register: LEDGER for §1 (what is banked); SEARCH for §§2–4** (tasks
#130/#163). Purpose: the exact residual between the banked stack (docs 50–53,
umbrella 8623 jobs) and (MID-central) fully proven — each remaining lemma
with its Lean-facing statement, so execution parallelizes.

## 1. Banked (axiom-clean, lint green — no sorries anywhere)

Assembly: `MidCentralInput → midCentral_survivors_le/_empty/_in_window`.
Walk tier (complete): CascadeGeometric (collapse, resonance denominator,
Abel master bound), DriftDip, RotationDip (exact chord + first-wrap dip),
PerturbedDip (drift/envelope budgets + `birthKilled_of_perturbed_rotation` +
`polar_ratio_explicit`: γ = β − θ/2 + π/2, r = 1/(2sin(θ/2))), SweepDichotomy,
SweepCascade, GaussLattice, log_ratio_bounds.
(T2) general: DepthUpdate (exact update/absorption, center-over-cofactor),
PairPeel (global factored form from `exists_peel` twice, `pair_peel_depth`).
(T1) bricks: DigammaBounds (iterated recursion, vertical summand,
digamma reflection).

## 2. Tier (T1) — frame-derivative supply. Two lemmas.

**(T1-a) vertical_sum_log_bounds [elementary, anchor-free]:**
for σ ≥ ½, t ≥ 1, N : ℕ:
`|∑ n ∈ range N, (σ+n)/((σ+n)² + t²) − ½·log(((σ+N)²+t²)/(σ²+t²))| ≤ 4/t`.
Proof shape: FTC on f(x) = ½log(x²+t²) (as ReversalClosedForm) + per-interval
second-derivative error |f″| ≤ 1/(x²+t²), summing to ≤ π/t + 1/t². Consumes
only banked technology.

**(T1-b) trigamma_series or digamma_vertical_anchor [the one analytic
input]:** either
`HasSum (fun n : ℕ => ((z+n)⁻¹)^2) (deriv digamma z)` (trigamma series —
NO anchor constant; θ″-grade suffices for the slip law since the −γ
normalization cancels in all consumed quantities), or the integral route
`Re z > 0 → digamma z = (∫ t in Ioi 0, Real.log t · t^(z−1) · e^{−t})/Γ z`
via `Complex.Gamma_eq_integral` + differentiation under the integral.
The trigamma variant is smaller: differentiate `digamma_apply_add_nat`
(both sides differentiable: Γ analytic away from poles) and supply
`Tendsto (deriv digamma) (comap re atTop) 0` — the sole asymptotic fact.

## 3. Tier (T2) — per-instance carrier supply. Two lemmas.

**(T2-a) carrier order-1 data:** for the census-window instances, the pair
zeros are simple: `analyticOrderAt Φ ρ = 1`. Certified numerically per event
(|Φ′(ρ)| = 2η|H| > 0 measured); Lean route: interval-arithmetic evaluation
of Φ′ at the certified box (the #136/#140 truncation-window technology —
already banked for windows; needs the derivative variant).

**(T2-b) the Rouché count:** exactly two zeros in D_w — doc 48 §2's
per-instance hypothesis. Lean route: winding-number evaluation on ∂D_w by
interval arithmetic (the census `winding` pipeline formalized on ONE
certified instance suffices for the theorem-track instance; the general
statement stays hypothesis-typed as in `pair_peel`).

## 4. Tier (T3) — (CR-density). The open core.

`#{ρ : F_N(ρ) = 0, 0 < β−½ ≤ c/log N, γ ∈ [T,T+U]} ≤ ε(c)·U·log N, ε(c)→0.`
Bare Jensen no-go recorded (doc 52 §8). Live routes: variance of log|F_N|
(anti-concentration via the banked `finset_chebyshev`), or the β-profile
continuity from the partial-sums literature (arXiv:0807.0019, 1507.01340 —
unmined). THIS is the one place new mathematics is required; everything else
in this document is execution.

## 5. Dependency graph (what unlocks what)

(T1-a) + (T1-b) → misalignment supply for `birthKilled_of_perturbed_rotation`
→ `dip_kills` field discharged for the actual carrier outside the window.
(T2-a) + (T2-b) → `pair_peel_depth` applies per instance → pushes ARE the
walk data (depth reading exact).
(T3) → `creation_rate` field → `midCentral_survivors_le` with explicit K
→ (MID-central) proven; feeding the deck relation (doc 53 §4(4)) turns the
window population into the (SWEEP-margin) boundary term of the bridge.

## 6. Cycle-23 reduction: (T1) is OFF the critical path; the honest terminus

Re-audit finding, machine-checked: the θ_RS / digamma content does NOT gate
`dip_kills`. The tower's RELATIVE phases φ_{N−m} − φ_N are θ_RS-free (the RS
theta term is m-independent, cancels in the difference), so the walk step
angles come from the banked Gamma-free `log_ratio_bounds` and the slip 2πd²
is elementary in √(t/2π). `DipKillsWiring.lean` banks this:

- `CarrierBirthData` — the concrete per-birth hypothesis bundle matching
  `birthKilled_of_perturbed_rotation`.
- `dipKills_of_carrierData`, `midCentralInput_of_carrierData`,
  `midCentral_survivors_le_of_carrierData` — MID-central survivors ≤ K from
  carrier data + creation bound, NO digamma anchor in the chain.

**The honest terminus of the formalization.** After this cycle, MID-central
is reduced — machine-checked, axiom-clean, umbrella 8624 jobs — to exactly:

  (R2) per-instance carrier certificates inside `CarrierBirthData`: the order-1
       simple-zero data (`depth_pos`) and the push-form realization
       (`push_form`, doc 48 §2's Rouché count). Numerically certified per
       event; formalizable via the #136/#140 interval-arithmetic window
       technology for the theorem-track instance, hypothesis-typed for the
       universal statement. NOT open — execution.

  (R3) `creation_rate` = the (CR-density) bound: `#{F_N=0 near line}` ≤
       ε(c)·U·log N. This is GENUINELY OPEN MATHEMATICS (doc 52 §4, §8
       no-go). No formalization closes it; it needs a theorem.

The (T1) digamma layer (recursion, reflection, summand, error mass, vertical
log comparison) is fully banked and reusable, but is now known to feed the
CONTEXT (frame density, resonance scale), not the `dip_kills` critical path.

**Consequence for the goal "MID-central fully proven in Lean":** the assembly,
walk tier, (T2) general machinery, (T1) digamma layer, and the concrete
reduction are ALL machine-checked. The single irreducible obstruction is (R3),
(CR-density) — an open problem in the analytic theory of zeros of Dirichlet
polynomials in the AFE-matched regime (the regime Gonek–Montgomery leave open
in print, doc 50 §7). MID-central cannot be "fully proven" — in Lean or on
paper — until (CR-density) is proven as mathematics. Everything formalizable
without solving an open problem is now formalized.
