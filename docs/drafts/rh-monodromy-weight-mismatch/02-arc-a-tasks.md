# Arc A — granular task breakdown (Lean language bank)

Goal: finish Arc A of `01-research-plan.md` — the generic Kummer-obstruction lemma set and the
RH ⟺ tower / RH_{2^k} ladder equivalences against mathlib's ζ. Pure execution (gate-exempt),
zero sorries, axiom-clean.

## Design decisions (made 2026-07-03, before any Lean)

**D1 — Convex Ω, not general simply connected.** All Arc A theorems are stated for convex open
Ω (the half-plane {Re s > 1/2} is convex). This dodges two known gaps: general
simply-connected exhaustion machinery, and the verified-absent mathlib lemma
`IsPreconnected (open ∖ finite)` (checked earlier this session — NOT in mathlib; do not
re-derive). Exhaustion pieces Ω ∩ ball(2, R) are convex (intersection of convex), bounded,
and each contains finitely many zeros (zeros of a non-trivially-zero entire function have no
finite accumulation point). Generic simply-connected versions are optional later strengthening.

**D2 — Uniqueness via identity theorem, not connectivity of Ω∖Z.** Two analytic n-th roots of
the same f on connected Ω that agree at ONE point s₀ with f(s₀) ≠ 0 are equal: on a small
disc around s₀, g₁/g₂ is continuous into the discrete μ_n ⟹ constant = 1 on the disc ⟹
`AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq` (identity theorem, in mathlib) finishes.
Never needs Ω∖Z connected.

**D3 — Base-point normalization at s = 2.** ξ(2) ≠ 0 (from `riemannZeta_ne_zero_of_one_lt_re`,
Γ-nonvanishing, factor ≠ 0). Fix a root value w₀ with w₀^n = ξ(2); on every exhaustion piece
take THE root with g(2) = w₀; D2 makes the family agree on overlaps; glue.

**D4 — ξ via the entire completed zeta.** Pole algebra (done once, on paper):
Λ(s) = Λ₀(s) − 1/s − 1/(1−s) ⟹ s(s−1)/2·Λ(s) = s(s−1)/2·Λ₀(s) + 1/2. So define

    xi s := s * (s − 1) / 2 * completedRiemannZeta₀ s + 1 / 2

entire by construction, with xi(0) = xi(1) = 1/2 (matches the classical ξ(0) = ξ(1) = 1/2 —
built-in sanity check), xi = s(s−1)/2·Λ away from {0,1}, FE from Λ₀(1−s) = Λ₀(s).
All names below marked (P) must be probed in /tmp before use; the Λ/Λ₀ relation's exact
mathlib name and sign convention is probe item #1.

**D5 — Order divisibility in ℕ∞.** State divisibility against the analytic order API
((P) `analyticOrderAt` vs `AnalyticAt.order`); zeros of interest have finite order (xi ≢ 0 on
connected Ω since xi(2) ≠ 0), so divisibility statements can be phrased on the ℕ-valued order
after a finiteness lemma.

## Tasks

### A0 — probes + prior-art sweep (blocks everything)
- /tmp probe file 1 (APIs): order-of-vanishing (`analyticOrderAt`, `analyticOrderAt_pow`?,
  `AnalyticAt.order_eq_nat_iff`?), removable singularity (`Complex.analyticAt_of_...` — find
  the real name), `Complex.Gamma_ne_zero`, identity theorem
  (`AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq`?), cpow nonvanishing.
- /tmp probe file 2 (zeta layer): `differentiable_completedRiemannZeta₀`?,
  `completedRiemannZeta₀_one_sub`?, the Λ/Λ₀ relation name + sign, the Λ↔ζ product formula
  name, `#print RiemannHypothesis` (record exact def incl. trivial-zero guard clauses),
  conjugation lemma for ζ or Λ ((P) `riemannZeta_conj`?).
- Repo sweep: `scripts/formal_tools.py research` for: zero-order factorization, analytic root,
  peeling, `IsSimplyConnected` definition + `Convex → IsSimplyConnected` bridge (the banked
  `exists_analyticOnNhd_pow_eq` takes `IsSimplyConnected`; find how U0KummerBranch/
  AnalyticRoot discharge it — reuse, don't re-prove).
- Exit: worklog table of verified names; revised statements for A1/A2 if APIs differ.

### A1a — `KummerObstruction.lean`: easy direction + uniqueness
- `analyticOrderAt_pow_smul`-type lemma if missing: ord(g^n) = n·ord(g).
- `root_orders_dvd` : g analytic on Ω, g^n = f on Ω ⟹ ∀ρ∈Ω, n ∣ ord_ρ f.
- `pow_root_unique` (D2): connected Ω, g₁^n = g₂^n = f, g₁ s₀ = g₂ s₀, f s₀ ≠ 0 ⟹ g₁ = g₂ on Ω.
- Exit: compiles standalone; no sorries.

### A1b — global peeling lemma
- `exists_peel` : f analytic on open Ω, ρ ∈ Ω, ord_ρ f = m (finite) ⟹ ∃ h analytic on Ω,
  (∀ s ∈ Ω, f s = (s−ρ)^m * h s) ∧ h ρ ≠ 0 ∧ (∀ s ∈ Ω∖{ρ}, h s = f s / (s−ρ)^m).
  Construction: define h by the division formula off ρ and the local-factorization value at ρ;
  analyticity off ρ trivial, at ρ via `AnalyticAt.order_eq_nat_iff` local factor + eventual
  equality. Orders: ord_σ h = ord_σ f for σ ≠ ρ, ord_ρ h = 0.
- Exit: lemma + order bookkeeping lemmas.

### A1c — finite-Z root + exhaustion glue (the main A1 theorem)
- `exists_root_of_finite` : convex bounded Ω, Z(f) ∩ Ω finite, all orders divisible by n ⟹
  root exists: induct with A1b peeling to f = ∏(·−ρᵢ)^{n·qᵢ} · u, u nonvanishing; root :=
  ∏(·−ρᵢ)^{qᵢ} · (banked `exists_analyticOnNhd_pow_eq` root of u); include the
  normalized-at-2 variant (D3).
- `exists_root_iff_orders_dvd` (capstone): Ω = {1/2 < re s} (or any convex open with a marked
  point), f analytic non-trivially-zero: (∃ g analytic, g^n = f on Ω) ↔ (∀ ρ ∈ Ω, n ∣ ord_ρ f).
  Exhaustion Ω_R := Ω ∩ ball(2,R), R ∈ ℕ; finiteness of Z ∩ Ω_R from no-finite-accumulation;
  glue by D2/D3 (roots agree on Ω_R ∩ Ω_{R'} = Ω_{min}); define g by g s := g_R s for any R
  with s ∈ Ω_R, well-definedness from gluing.
- Risk note: the exhaustion glue is the only genuinely fiddly Lean here (a ℕ-indexed family
  with compatibility); if it stalls, fall back to stating the capstone for f with locally
  finite zero set given as data + a separate instantiation lemma for entire f.
- Exit: capstone compiles; this is the load-bearing Arc A theorem.

### A1d — generic coherent tower
- `CoherentTower` def: χ : ℕ → (ℂ → ℂ), χ 0 = f, ∀k (χ(k+1))² = χ k, all analytic on Ω.
- `tower_iff_nonvanishing` : convex Ω, f analytic non-trivially-zero:
  (∃ coherent tower) ↔ ∀ s ∈ Ω, f s ≠ 0.
  ⟸: port the `u0_coherent_kummer_tower` one-log construction (U0/U0KummerBranch.lean:224)
  generically. ⟹: (χ k)^{2^k} = f by induction, so A1a gives 2^k ∣ ord ∀k ⟹ ord = 0 or ⊤;
  ⊤ excluded by non-trivially-zero (identity theorem).
- Exit: both directions, no sorries.

### A2a — ξ layer
- `xi` def per D4; `differentiable_xi` (entire); `xi_one_sub : xi (1−s) = xi s`;
  `xi_conj : xi (conj s) = conj (xi s)` (needs (P) conjugation lemma for Λ₀ — if absent in
  mathlib, derive from ζ's conj lemma away from ℝ-issues, or restrict A2 statements to not
  need conj and drop this — it is only needed for the B3 equivariance later; decide at probe).
- `xi_one : xi 1 = 1/2`, `xi_zero : xi 0 = 1/2`, `xi_two_ne_zero : xi 2 ≠ 0`,
  `xi_eq_completed : s ≠ 0 → s ≠ 1 → xi s = s(s−1)/2 * completedRiemannZeta s`.
- Exit: layer compiles.

### A2b — zero correspondence
- `xi_eq_zero_iff_zeta` : 1/2 < re s → s ≠ 1 → (xi s = 0 ↔ riemannZeta s = 0)
  (factor s(s−1)/2 ≠ 0; Γ(s/2) ≠ 0 since re(s/2) > 1/4; π^{−s/2} ≠ 0).
- `xi_ne_zero_of_one_le_re` : 1 ≤ re s → xi s ≠ 0. For re s > 1 from
  `riemannZeta_ne_zero_of_one_lt_re`; for re s = 1 need zeta's edge nonvanishing —
  (P) probe `riemannZeta_ne_zero_of_re_eq_one` / `riemannZeta_ne_zero` variants; mathlib has
  the PNT-adjacent edge result (recalled — verify). If absent: drop this lemma and weaken
  downstream statements to re s > 1 (the ladder/tower theorems never need the edge line —
  zeros in Ω automatically have re < 1 only via this lemma; without it, state ladder over
  {1/2 < re s} minus nothing and let divisibility at hypothetical re-1 zeros ride along
  harmlessly). Decision at probe time; do not let this lemma block the arc.
- Exit: correspondence lemmas compile.

### A2c — ladder
- `RHLadder (k : ℕ) : Prop := ∀ ρ, 1/2 < ρ.re → xi ρ = 0 → 2^k ∣ (ord_ρ xi)`.
- `rhLadder_iff_root : RHLadder k ↔ ∃ g, AnalyticOnNhd ℂ g Ω ∧ ∀ s ∈ Ω, g s ^ 2^k = xi s`
  (A1c capstone at n = 2^k; non-trivially-zero from xi_two_ne_zero).
- Exit: compiles.

### A2d — RH equivalences
- `rh_iff_no_zeros_right` : RiemannHypothesis ↔ ∀ s, 1/2 < s.re → xi s ≠ 0.
  →: unfold mathlib RH (per A0 probe); ζ-zeros in Ω are nontrivial (trivial zeros have
  re < 0); apply correspondence. ←: a nontrivial zero with re < 1/2 reflects by
  `xi_one_sub` to a zero with re > 1/2 (FE reflection); re = 1/2 is what remains.
  Careful: mathlib's RH statement form decides the exact bookkeeping — write AFTER A0.
- `rh_iff_tower : RiemannHypothesis ↔ ∃ coherent tower of xi on Ω` (via A1d).
- `rh_iff_forall_ladder : RiemannHypothesis ↔ ∀ k, RHLadder k`
  (←: 2^k ∣ ord ∀k ⟹ ord = 0 or ⊤; ⊤ excluded; →: vacuous).
- Exit: the three named theorems compile.

### A2e — gate + bookkeeping
- `scripts/formal_tools.py lint --check-generated`; /tmp `#print axioms` on the three A2d
  theorems + A1c capstone (expect [propext, Classical.choice, Quot.sound]); regenerate index;
  add files to umbrella imports (new top-level `RHTower.lean` umbrella or into
  MainTheorems.lean — top-level, NOT under Bottcher/U0, layering rule); move card
  `rh-tower-obstruction-language.md` through its gates; worklog tick; library-backlog ticket
  for door index if warranted.

Dependency order: A0 → A1a → A1b → A1c → A1d → A2a → A2b → A2c → A2d → A2e, with A1d and
A2a/A2b parallelizable after A1c.
