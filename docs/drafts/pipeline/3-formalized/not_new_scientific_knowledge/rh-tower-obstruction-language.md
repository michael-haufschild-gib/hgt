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

2026-07-03 — extended: `RHTower/DeckCocycle.lean` — A3 revived (task #113, q62 deck pattern):
the box invariant as deck class, NO argument principle. `pow_root_ratio` (roots differ by a
constant root of unity, anchored derivative-free via pow_root_unique), `deckClass` def,
`deckClass_pow_eq_one` (values in μ_n), `deckClass_root_indep` (choice-independence),
`deckClass_sq` (dyadic coherence w_k = w_{k+1}²), `deckClass_eq_one_iff_exists_root`
(triviality ⟺ global root on U₁ ∪ U₂ — the ladder link, with the two-chart annulus glue).
All axiom-clean [propext, Classical.choice, Quot.sound]; RHTower target builds green (8562
jobs). NOTE: full-tree gate temporarily blocked by the parallel agent's in-flight
Bottcher/HarmonicMaxPrinciple.lean — not this lane's file; re-run the full gate after their
session lands. Remaining A3 chunk: the monomial dictionary (w_k of (z−a)^m·h =
dyadicRoot(k)^m via exists_peel + explicit slit-plane cpow branches — still no Rouché).

2026-07-03 — extended: `RHTower/DeckMonomial.lean` — A3 chunk 2, the monomial dictionary:
`deckClass_monomial` — the deck class of the explicit slit-chart branches of the n-th root
of (z−a)^m at basepoints a ± i equals exp(2πi·m/n) (the enclosed order mod n as a root of
unity; the q62 dyadic multiplier at n = 2^k). Supporting: `monoRoot₁/₂` branch defs (clog on
slitPlane + sign-correcting constant), `monoRoot₁/₂_pow` (root property), `_analyticOnNhd`,
`deckClass_mul_global` (global factors cancel). All axiom-clean; RHTower green 8563 jobs.
NO argument principle anywhere. Remaining A3 chunk 3 (assembly): slit-chart star-convexity
⟹ preconnectedness + deckClass_root_indep + exists_peel ⟹ ANY local roots of a peeled
single-zero function carry class exp(2πi·m/2^k) — w_k literally counts the enclosed order.

2026-07-03 — A3 COMPLETE: `RHTower/DeckAssembly.lean` — the capstone
`deckClass_single_zero`: for f = (z−a)^m·h on a ball (h analytic nonvanishing), ANY local
n-th roots on the two slit charts have deck class exp(2πi·m/n) at a ± (R/2)i — **the coarse
box invariant w_n counts the enclosed order mod n, machine-checked with NO argument
principle**. Supporting layer: chart geometry (isOpen/star-convex slit charts via
linear_combination-corrected affine algebra, translated half-plane overlaps,
chart_inter_eq), generalized dictionary deckClass_monomial' at a ± εi (log_ofReal_mul),
h-root from Arc A root existence with vacuous zero set. All axiom-clean
[propext, Classical.choice, Quot.sound]; RHTower green 8564 jobs. Files of the A3 arc:
DeckCocycle.lean (class + gluing iff + coherence), DeckMonomial.lean (branches +
dictionary), DeckAssembly.lean (geometry + capstone).

2026-07-04 — extended: `RHTower/DeckMultiZero.lean` — multi-zero ADDITIVITY of the cocycle:
`deckClass_multi_zero` — for f = ∏(z−ρᵢ)^{mᵢ}·h on ball a R with all ρᵢ ∈ closedBall a r₀
and h nonvanishing, ANY local n-th roots on the slit ANNULUS charts carry deck class
exp(2πi·(Σmᵢ)/n): w_n counts the TOTAL enclosed order. Mechanism: off-center factorization
z−ρ = (z−a)·u(z) with u(annulus) ⊆ B(1,1) ⊆ slitPlane ⟹ correction roots are GLOBAL and
cancel (deckClass_mul_global); per-zero monomial classes multiply (deckClass_mul/prod);
annulus-chart preconnectedness via polar parametrization (continuous image of a convex
rectangle — isPreconnected_chartRA/LA). Supporting: corrRoot + corr_mem_slitPlane +
shifted_factor + deckClass_congr. All axiom-clean; RHTower green 8565 jobs. NO argument
principle. Next: wiring to the ξ layer (per-box invariant of completedRiemannZeta).

2026-07-04 — ξ-LAYER WIRED: `RHTower/XiDeck.lean` — the deck calculus instantiated on the
actual completed zeta. `xi_orderAt_ne_top`; `xi_peel_ball` (exists_peel + continuity
shrink: ξ = (z−ρ₀)^m·h, h nonvanishing on a ball); `xi_deckClass` (ANY local n-th roots of
ξ on the slit charts at any ρ₀ have class exp(2πi·m/n), m = vanishing order — for ALL
sufficiently small radii); `exp_two_pi_mul_div_eq_one_iff` (class trivial ⟺ n ∣ m);
**`xi_deckClass_eq_one_iff_ladder_dvd`** — at n = 2^k, triviality of the deck class IS the
divisibility clause of RHLadder k. Chain now closed end to end:
RiemannHypothesis ⟺ ∀k RHLadder k (rh_iff_forall_ladder, Arc A) ⟺ per-zero clauses that
are EXACTLY deck-class triviality (XiDeck) — the MWM lane's w_k obstruction cocycle is a
fully machine-checked reformulation of RH on exact monodromy data, with no argument
principle anywhere in the entire chain. All axiom-clean; RHTower green 8566 jobs.

- 2026-07-03 `formal/GaloisForLFunctions/RHTower/DeckHomotopy.lean` — **charge conservation** (M1 arc, task #117): the deck class is a deformation invariant, with no argument principle. `deckClass_step` (dominated perturbation ‖f−g‖<‖g‖ on the charts transports roots of g to roots of f via the global correction root exp((1/n)·log(f/g)) — the ratio lands in B(1,1) ⊆ slitPlane — and `deckClass_mul_global` pins the class), `deckClass_perturb` (any-roots form, via `deckClass_root_indep`), `deckClass_chain` (finite chains of consecutive dominations transport roots end to end), `deckClass_deformation_invariant` (capstone: the charge of F N read from ANY roots equals the charge of F 0 — enclosed multiplicity mod n cannot change while no zero touches the charts). Helper surface: `mem_slitPlane_of_norm_sub_one_lt`, `ratioRoot`/`_pow`/`_ne_zero`/`_analyticAt`, `basepointP/M_mem_charts`. Axiom-clean [propext, Classical.choice, Quot.sound]; `lake build GaloisForLFunctions.RHTower` green (8567 jobs); index + lint gate passed. Consumed by the M1 conservation program (15-conservation-program.md, forthcoming).

- 2026-07-03 `formal/GaloisForLFunctions/RHTower/FarFieldAnchor.lean` — **far-field anchor** (M1 arc, task #118): the computable endpoint conservation drains to. `deckClass_of_nonvanishing` (zero-free ball ⟹ trivial class for ANY local roots; the m = 0 instance of `deckClass_single_zero`), `xi_ne_zero_of_one_lt_re` (via the banked ξ/ζ zero correspondence + mathlib's `riemannZeta_ne_zero_of_one_lt_re`), `ball_re_gt_one`, and the capstone `xi_deckClass_far_field`: any local n-th roots of ξ on the charts of a ball strictly right of Re s = 1 have deck class 1 — far boxes of the actual completed zeta carry zero charge at every rung. Axiom-clean [propext, Classical.choice, Quot.sound]; RHTower green (8568 jobs); index + lint gate passed.

- 2026-07-03 `formal/GaloisForLFunctions/RHTower/ReflectionParity.lean` — **the first constraint-forces-parity theorem** (Arc B base, task #114; planned FEDescent construction REPLACED by a direct reflection-cancellation argument — no descent, no power-series surgery). `analyticOrderAt_even_of_reflection` (f analytic, f(2c−s) = f(s), finite order at the fixed point c ⟹ order EVEN; proof: peel f = (s−c)^m·h, reflect, cancel the monomial off the puncture, evaluate h(c) = (−1)^m·h(c) ≠ 0 by tendsto uniqueness along 𝓝[≠]), `xi_central_order_even` (via banked xi_one_sub), `xi_central_ladder_two` (the k = 1 rung clause at s = 1/2 in ℕ∞), `xi_deckClass_central_sq_trivial` (w₁ trivial at the FE fixed point: any local square roots of ξ have deck class 1 — consumes xi_deckClass_eq_one_iff_ladder_dvd at k = 1). Mechanism named: parity is seen at the RAMIFIED/FIXED locus of a constraint symmetry; D–H shows FE alone cannot force it off-line ⟹ Arc B hunts correspondences whose fixed locus reaches off-line points. Generic theorem applies to every FE-symmetric pencil member (family-wide central anchor for M4). Axiom-clean [propext, Classical.choice, Quot.sound]; RHTower green (8569 jobs); index + lint gate passed.

- 2026-07-03 `formal/GaloisForLFunctions/RHTower/UPlaneDescent.lean` — **the u-plane descent** (Arc B, task #121; consumes the q62 lane's `Bottcher.SchwarzReflection` — first cross-lane import, mathlib-only dependencies). `uSqrt` (principal root, with `uSqrt_sq`, `norm_uSqrt_of_ne_zero` = √‖w‖, `uSqrt_re_pos` on the slit plane, analyticity); `xiDescent w = ξ(1/2 + √w)` patched at 0; continuity EVERYWHERE incl. across the slit (one-sided log limits `continuousWithinAt_log_of_re_neg_of_im_zero` / `tendsto_log_nhdsWithin_im_neg_of_re_neg_of_im_zero` + evenness `xi_half_sub` bridging the reflected branch value −uSqrt); **`xiDescent_differentiable` — ENTIRE via the Painlevé engine** (`differentiableOn_of_off_horizontal_line` at the real line); **`xi_eq_xiDescent`** — the global descent identity with no branch bookkeeping (evenness absorbs the root sign); `sq_mem_slitPlane_of_re_pos`; capstone **`rh_iff_xiDescent_ne_zero_slitPlane` : RH ⟺ the descended entire function has no zeros on the slit plane** — the critical line IS the slit, the FE involution is quotiented away, the deck calculus's local slit-chart geometry becomes the global domain. All axiom-clean [propext, Classical.choice, Quot.sound]; RHTower green (8571 jobs); index + lint gate passed. Lean lessons: `le_or_lt` absent (by_cases), `push_neg` deprecated (use not_or/not_lt rewrites), HO-unification on AnalyticAt.comp needs explicit `(f := ...)`.

- 2026-07-03 `formal/GaloisForLFunctions/RHTower/LedgerJump.lean` — **the ledger jump** (M1 arc, task #124; completes identity (L) of 15-conservation-program.md). `deckClass_jump`: if f' = (z−ρ')^{m'}·f on the ball (the enclosed configuration gains ONE zero of multiplicity m', ‖ρ'−a‖ ≤ r₀), then any local n-th roots of f' and f on the annulus charts have deck classes differing by exactly exp(2πi·m'/n). Proof = two evaluations of `deckClass_multi_zero` (extended configuration indexed by Option ι, new zero at none; Finset.prod_insert/prod_map + Embedding.coeFn_mk/Option.elim simp) and the ratio of the explicit classes — no new analysis, no argument principle. With `deckClass_deformation_invariant` (no-flux case) the conservation ledger (L) — charge difference ≡ boundary multiplicity flux mod n — is now theorem-grade for piecewise-generic deformations. Axiom-clean [propext, Classical.choice, Quot.sound]; RHTower green (8572 jobs); index + lint gate passed.

- 2026-07-03 `formal/GaloisForLFunctions/RHTower/SeamCocycle.lean` — **the seam cocycle** (OC2 of 15-conservation-program.md, task #122; u-plane carrier). `deckClass_basepoint_indep` (the deck class of chart roots is identical at every basepoint pair in overlapU × overlapD where f ≠ 0 — via pow_root_ratio constancy on the two banks); `seam_jump` — **the seam ledger**: around an on-seam zero f = (z−a)^m·h, the left seam class of any bank roots equals exp(2πi·m/n) × the right seam class, σ_L = e(m/n)·σ_R, where σ_R/σ_L are the gluing ratios of the bank roots GU/GD against the chartR/chartL roots (which are analytic ACROSS the right/left seam segments respectively). The identity is VALUE-LEVEL — only the four root values enter; constancy interpretation via pow_root_ratio. `xiDescent_orderAt_ne_top` (witness xiDescent(9/4) = ξ(2) ≠ 0), `xiDescent_peel_ball`, and the instance `xiDescent_seam_jump`: on the actual descended completed zeta, crossing an on-slit point (= on-line ξ-zero) multiplies the seam class by exp(2πi·ord/n). Reading: the whole-plane tower obstruction of ξ = off-line deck classes (RH content) + the unconditional seam ledger of on-line multiplicities. Axiom-clean [propext, Classical.choice, Quot.sound]; RHTower green (8573 jobs); index + lint gate passed. Lean lesson: `GL` is reserved mathlib notation (general linear group) — invalid as a binder name.

- 2026-07-03 `formal/GaloisForLFunctions/RHTower/ModulusHolography.lean` — **modulus-only holography** (M6, task #123). `circleAverage_log_norm_single_zero` (single-zero Jensen: A(r) = m·log r + log‖h(a)‖, via mathlib's zero-free `AnalyticOnNhd.circleAverage_log_norm_of_ne_zero` — the JensenFormula/ValueDistribution development landed in mathlib and supplies the harmonic mean value); capstone `deckClass_eq_exp_circleAverage_slope`: **the deck class of ANY local n-th roots = exp(2πi·α/n) with α the two-circle slope of the circle-average of log‖f‖** — boundary modulus on two circles determines the interior charge, no phases, no root choices, no argument principle (the charter's bulk-from-boundary clause as a theorem); instance `xi_deckClass_eq_circleAverage_slope`: |ξ| on two circles determines the box charge of the completed zeta — the formal version of what the R-series winding engines measured. Axiom-clean [propext, Classical.choice, Quot.sound]; RHTower green (8574 jobs); index + lint gate passed. Lean lessons: Real.log_pow is (x, n); ContinuousAt.comp/AnalyticAt.comp need explicit (f := ...) whenever the point is an application.

- 2026-07-03 `formal/GaloisForLFunctions/RHTower/MirrorPencil.lean` — **the mirror identity + incidence map** (M8, task #127; doc 16 §3, R9-verified to 30 digits before formalization). Abstract layer over any FE-paired functions (Λ₁(1−s) = ε·Λ₂(s), Λ₂(1−s) = ε'·Λ₁(s)): `pencil_mirror` (reflection s ↦ 1−s = parameter involution (c,d) ↦ (dε', cε)), `pencil_fe_unit` (ε·ε' = 1 from any nonvanishing point), `pencil_mirror_zero_iff` (zero-set involution), `pencil_conj_symm`/`pencil_conj_zero` (reality of d = c̄ members under the conjugate-dual relation), **`incidence`** (r(s) = −Λ₂(s)/Λ₁(s)) + `pencil_eq_zero_iff_incidence` (member through any point = exact algebra; the family's zero dynamics = level-set geometry of one meromorphic function). Dirichlet layer: `dirichletXi χ = N^{s/2}·completedLFunction χ` renormalizes mathlib's completed L to a CONSTANT root number — `dirichletXi_one_sub` (via Loeffler's `IsPrimitive.completedLFunction_one_sub`; exponent algebra (1−s)/2 + (s−1/2) = s/2) — and `dirichlet_pencil_mirror` instantiates the mirror on actual Dirichlet pencils (the R3/R5 measured family). Axiom-clean [propext, Classical.choice, Quot.sound]; RHTower green (8575 jobs); index + lint gate passed.

- 2026-07-03 `formal/GaloisForLFunctions/RHTower/CountingSubstitute.lean` — **the Rouché substitute + the pinning lemma** (M9, task #128). `exists_annulus_roots` (the deckClass_multi_zero root construction, exposed: peeled functions have analytic n-th roots on both slit annulus charts); `nat_eq_of_exp_eq` (equal classes at level n force equal counts below n); **`enclosed_count_eq_of_close`** — Hurwitz-type stability with NO argument principle: a dominated perturbation ‖f−g‖ < ‖g‖ on the annulus charts preserves the EXACT enclosed multiplicity count; the large-n trick needs no a priori bound (compare classes at n = N_f + N_g + 1 — a residue below the modulus determines the number); **`pinned_zero_on_line`** — doc 16 §1 formal: a single simple on-line reference zero + a dominated perturbation carrying the FE∧reality symmetry f(1−s̄) = conj f(s) forces every perturbed zero in the hole ONTO the critical line (the reflection of a zero is a zero, and count 1 leaves no room for a pair). First-compile clean. Axiom-clean [propext, Classical.choice, Quot.sound]; RHTower green (8576 jobs); index + lint gate passed. NOTE: this closes the lane's share of the SHARED MATHLIB GAP (no Rouché/Hurwitz) for dominated-perturbation counting — the deck calculus is now a self-contained counting theory.

- 2026-07-04 `formal/GaloisForLFunctions/RHTower/WindowRelation.lean` — **the window relation, counting core** (W1, task #129; doc 18). `lineReflect` (z ↦ 1−z̄, involution, re-formula); **`window_identity`** — the bookkeeping identity (ID): for any reflection-closed configuration with invariant multiplicities, D = L + 2N (filter partition by re-trichotomy + sum_nbij' along the reflection); `window_modEq_iff` (D ≡ L mod 2^{k+1} ⟺ 2^k ∣ N); **`xi_window_relation_of_ladder`** — RHLadder k forces the window relation for EVERY reflection-closed zero configuration of ξ (closure/invariance from the banked xi_orderAt_conj + xi_orderAt_one_sub; divisibility descent via natCast_dvd_natCast_of_enat); **`pair_window_relation_iff`** — the shrunk-window reading: on the two-point configuration {ρ₀, 1−ρ̄₀} the relation IS the rung 2^k ∣ mult, per zero. Axiom-clean [propext, Classical.choice, Quot.sound]; RHTower green (8577 jobs); index + lint gate passed. Follow-up (W1b): dictionary wiring (D = deck class at 2^{k+1}, L = seam-ledger product) + the k=1 sign(Ξ) base case.
- 2026-07-03 (#130 attack, W2a): `RHTower/SquareLadder.lean` — the window relation's GLOBAL extreme.
  `rhLadder_iff_root_slitPlane` (RH_{2^k} ⟺ analytic 2^k-th root of xiDescent on slitPlane),
  `rhLadder_one_iff_sqrt` ((WR_1)'s target = "xiDescent is a square on the slit plane"),
  `rh_iff_forall_root_slitPlane`. Pure transport along u = (s−1/2)² (center_sq_mem_slitPlane /
  half_add_uSqrt_mem_rightHalf); no new analytic machinery. 8578 jobs, axiom-clean
  [propext, Classical.choice, Quot.sound], formal lint passed. Theory: doc 19-square-class.md.
- 2026-07-03 (#137, W2g): `RHTower/GermExtension.lean` — the arithmetic-germ packaging.
  `farHalf` layer (open/convex/2∈/⊆rightHalf), `exists_farHalf_root` (the level-k germ is
  the Euler side's free gift: ξ ≠ 0 on Re s > 1 ⟹ root exists via exists_root_iff_orders_dvd
  with vacuous divisibility), `rhLadder_iff_germ_extends` (RH_{2^k} ⟺ every level-k root germ
  on Re s > 1 extends analytically to Re s > 1/2, extension agreeing with the germ; uniqueness
  up to μ_{2^k} via pow_root_unique, normalization ω = h(2)/g₁(2)). Doc 21 §3's continuation
  form banked. 8579 jobs, first-compile clean, axiom-clean [propext, Classical.choice,
  Quot.sound], formal lint passed.

2026-07-05 — extended (codex batch, reviewed + verified this date): the modulus-holography
branch now reaches the GLOBAL ladder/RH surface. `ModulusHolography.lean`:
`xi_circleAverage_slope_eq_order` (the two-circle slope of the circle-average of log‖ξ‖ IS
the local vanishing order), `xi_circleAverage_slope_exp_eq_one_iff_ladder_dvd` (slope
root-of-unity at level 2^k ⟺ local ladder divisibility), `rhLadder_iff_circleAverage_slope_exp_eq_one`
and `rh_iff_forall_circleAverage_slope_exp_eq_one` — **RH ⟺ at every right-half ξ zero, for
every k, the two-circle modulus slope has trivial 2^k exponential**: a machine-checked
equivalent of RH stated in |ξ| alone (no phases, no root choices, no argument principle).
Central instances: `xi_central_circleAverage_slope_exp_eq_one` (FE fixed-point parity makes
level 2 trivial at s = 1/2), `xi_central_circleAverage_slope_eq_even_integer` (central slope
= exact even integer). Weld of formulations: `germ_extends_iff_circleAverage_slope_exp_eq_one`
and `root_slitPlane_iff_circleAverage_slope_exp_eq_one` — germ continuation, slit-plane root,
and boundary-modulus criterion are now formally the SAME gate per rung. Zero-surgery reach:
`not_riemannHypothesis_of_sphere_domination_right` / `_center_margin` (planted zero with the
checkable margin 1/2 + r < Re s₀ ⟹ ¬RH) and
`exists_circleAverage_slope_obstruction_of_sphere_domination_center_margin` (planting forces
an explicit failed modulus-slope criterion at some rung). Chain composition in
`AnnealWindowRelation.lean`: `anneal_window_parity_transport_of_domination` (domination proves
the deck-side congruence at EVERY rung) and `xi_rung_of_finite_side_of_domination`
(domination + seam congruence at 2^(k+1) + finite-side rung ⟹ ξ rung). EM supply composed in
`EMCarrier.lean`: `anneal_deck_transport_of_emCarrier_close`, `anneal_seam_L_transport_of_emCarrier_close`
(EM remainder + finite closeness replace the abstract (AFE)/domination premises). Interface
work: `pinned_zero_re_eq_half` (CountingSubstitute, geometric re = 1/2 form),
`CarrierBirthData` shrunk (DipKillsWiring; polar + nonresonance now proved internally via
`birthKilled_of_perturbed_rotation_explicit_polar`), count endpoints
`pricing_close_zero` / `sliverCount_le_of_average_kernel` / `thickSliverCount_le_of_average_floor_kernel`.
All 23 new/changed endpoints verified axiom-clean [propext, Classical.choice, Quot.sound];
RHTower green (8638 jobs); formal lint passed.

2026-07-05 — extended (task #27, the seam grind): `SeamCongruence.lean` — the hL seam
congruence exhausted. **The blindness identity**: `seam_iff_rung` (pure [propext]) and
`anneal_seam_iff_rung_of_domination` — under the window identities D = L + 2N and
D-transport, the seam congruence hL at 2^(k+1) is EQUIVALENT to the rung congruence at
2^k; tower limit `seam_tower_iff_offline_eq` / `_zero`: all levels simultaneously ⟺
exact off-line matching N₁ = N₂ (⟺ window RH when the finite side is all on-line). The
seam datum IS the rung in on-line coordinates — machine-checked in both directions; its
value is the 2D→1D coordinate change. **The sign instrument** (Turing's counting core,
no argument principle): `exists_interleaved_zeros` (IVT engine),
`window_online_of_sign_data` (squeeze s ≤ L ≤ D ≤ s ⟹ L = D, N = 0),
`xi_online_of_sign_data` (every window zero on the line),
`window_simple_of_sign_data` / `xi_simple_online_of_sign_data` (every window zero
SIMPLE), `hL_exact_of_sign_data` (hL as equality, all levels at once), and the two
consumable endpoints `xi_window_online_of_domination_sign_certificate` and
`xi_window_online_of_em_sign_certificate` (the EM weld: domination supplied from the
doc 78 Euler–Maclaurin finite data — window RH from purely finite certifiable
inequalities). Umbrella 8640 jobs green; lint passed; all 14 endpoints axiom-clean
[propext, Classical.choice, Quot.sound].
