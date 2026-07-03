# RH tower/obstruction language: ξ-Kummer tower, RH_{2^k} ladder, root equivalence

- **ID:** rh-tower-lang
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** ../../rh-monodromy-weight-mismatch/00-approach.md §3 (Arc A of 01-research-plan.md)
- **Statement:** For Ω = {Re s > 1/2} and ξ(s) = s(s−1)/2·Λ₀(s) + 1/2 (entire, = ½s(s−1)Λ(s)
  off {0,1}): (i) generic root⟺divisibility (analytic n-th root on a convex open set with
  locally finite zero set ↔ n divides every vanishing order); (ii) mathlib's
  `RiemannHypothesis` ↔ coherent ℤ₂-Kummer tower of ξ on Ω; (iii) ladder
  RHLadder k := "2^k ∣ ord at every ξ-zero in Ω" satisfies RHLadder k ↔ ∃ analytic 2^k-th
  root of ξ on Ω, and RH ↔ ∀k RHLadder k.

## Goal
Banks the branch-native language for the MWM lane (docs/drafts/rh-monodromy-weight-mismatch):
RH stated as a branching/tower obstruction, graded by multiplicity divisibility. Level 1
("no odd-multiplicity — in particular no simple — off-line zeros") is the lane's first open
target; this card is the certified scaffolding. Non-circular: elementary complex analysis
over mathlib's `completedRiemannZeta₀`; no RH-strength input anywhere.

## Gates
- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [x] 1 → 2  fully-proven: complete proof (carried directly in Lean; pure execution)
- [x] 2 → 3  formalized: `formal/GaloisForLFunctions/RHTower/` (KummerObstruction, Peeling,
      RootExistence, CoherentTower, RiemannTower + umbrella `RHTower.lean`, imported by
      MainTheorems). Capstones: `RHTower.exists_root_iff_orders_dvd`,
      `RHTower.coherentTower_iff_nonvanishing`, `RHTower.rhLadder_iff_root`,
      `RHTower.rh_iff_xi_ne_zero_right`, `RHTower.rh_iff_tower`,
      `RHTower.rh_iff_forall_ladder`. Build green; `#print axioms` =
      [propext, Classical.choice, Quot.sound] on all six (2026-07-03); formal lint passed.
- [ ] 3 → 4  publication-ready: standalone paper (theorem + proof + Lean certificate + Door-2)

## Approach
Reused banked machinery (`exists_analyticOnNhd_pow_eq` U0/U0KummerBranch.lean:100, coherent-
tower pattern :224) + new generic layer: derivative-free root rigidity via geom_sum₂_mul +
identity theorem; global peeling by division + removable singularity; finite-zero induction +
convex exhaustion Ω∩ball(2,R+1) glued by rigidity at the marked point s=2; ξ-layer mirrored
from rh-formal-atlas RvMXiEntire (same toolchain v4.30.0, cited in header, not imported);
zero correspondence via ζ = Λ/Gammaℝ + Gammaℝ_ne_zero_of_re_pos; edge line free via
riemannZeta_ne_zero_of_one_le_re; local finiteness via codiscreteWithin + compact-finite.
New reusable helper: `natCast_dvd_natCast_of_enat` (ℕ∞ dvd descent — absent from mathlib).

## Log
- 2026-07-03 — created in 0-backlog (MWM lane opening)
- 2026-07-03 — formalized same day: 5 modules + umbrella, all capstones axiom-clean, lint
  green; moved 0-backlog → 3-formalized. Lesson recorded in worklog: pipeline exit-code
  masking (`| tail`) hid failures — gate builds now use pipefail.
- 2026-07-03 (late) — B3 extension banked: `RHTower/Reflection.lean` (xi_conj; generic
  analyticOrderAt equivariance under conjugation and s ↦ 1−s; pairings xi_orderAt_conj,
  xi_orderAt_one_sub). All five axiom-clean [propext, Classical.choice, Quot.sound];
  umbrella + MainTheorems green; lint green (index regenerated).
- 2026-07-03 (night) — DirichletRigidity.lean added: `no_polynomial_surgery` (finite-divisor
  rigidity of the Dirichlet-series class; droves-dichotomy fragment), axiom-clean
  [propext, Classical.choice, Quot.sound], umbrella + MainTheorems + lint green.

2026-07-03 — extended: `RHTower/LogIndependence.lean` — the principal wall's arithmetic
carrier, both sides (lane doc 10-blind-cone.md §5): `log_third_shifts_dependent` (explicit
ℚ-dependence of Hurwitz-shift logs at q=3, witness 2·8=4²), `log_shifts_independent`
(transcendental shifts multiplicatively free — transcendence→polynomial-identity→eval at −n₀),
`log_prime_shifts_independent` (prime-supported shifts free at rational denominator, via
padicValRat helpers padicValRat_prod/padicValRat_zpow). All axiom-clean
[propext, Classical.choice, Quot.sound]; umbrella imports updated; lint gate green.

2026-07-03 — extended: `RHTower/PerturbationZero.lean` — `exists_zero_of_sphere_domination`,
the Rouché-free zero-planting lemma (max-modulus on g/(g+h); mathlib has no Rouché): sphere
domination 3‖g‖ ≤ ‖h‖ + h(s₀)=0 + g(s₀)≠0 ⟹ g+h vanishes in the ball. Existence engine of
the Weyl counterexample (lane doc 11 §2). Axiom-clean; build 9012 jobs; lint green.
