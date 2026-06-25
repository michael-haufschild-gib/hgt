# Böttcher tower — Lean formalization of q62 (status)

Goal: build, from Mathlib up, a machine-checked proof of
`q62-bottcher-independence-n2-all-parameters` (Nguyen Q6.2, quadratic nonexceptional).
The q62 card statement is NOT to be altered; the Lean tower must reach exactly it.

Toolchain: `leanprover/lean4:v4.30.0`, Mathlib pinned. Iterate with
`lake env lean GaloisForLFunctions/Bottcher/<File>.lean` (and `lake build <module>` for oleans).
Discipline: ZERO sorries (verified by grep on every checkpoint). Finite-energy /
analytic side-conditions ride as explicit hypotheses, never as sorries.

## Banked (compiling, sorry-free)

### Tier 1 — `MonodromyObstruction.lean` (COMPLETE)
The one-coordinate monodromy obstruction engine (`unbounded-one-coordinate-monodromy-obstruction.md`):
- `eq_zero_of_card_roots_gt_natDegree` — poly with > natDegree distinct roots is 0.
- `rotate_injOn` — the m rotates `ζ^k·f` of a nonzero f under an order-m multiplier are distinct.
- `eq_zero_of_high_monodromy` — degree-<m poly killed by all m rotates is 0 (the finite-degree contradiction).
  (Transcendence-kills-coefficients is a Mathlib primitive, pulled in at assembly.)

### Tier 2a/2c — `LogPotential.lean`
Logarithmic potential theory (absent from Mathlib), built from the integral layer:
- defs: `logKernel` (= -log‖x-y‖), `logPotential` Uᵘ, `logEnergy` I(μ), `logEnergyPair` J(μ,ν).
- `logKernel_symm`, `logEnergyPair_self`.
- potential algebra: `logPotential_smul`, `logPotential_add`.
- mutual-energy bilinearity: `logEnergyPair_smul_left/right`, `logEnergyPair_add_left/right`.
- `logEnergy_smul` — I(c·μ)=c²·I(μ).
- `logEnergy_convexCombo` — I(a·μ+b·ν)=a²I(μ)+ab·J(μν)+ba·J(νμ)+b²I(ν)  [the card's I(μ_t) algebra].

### Tier 2b — `Capacity.lean`
- defs: `IsProbOn`, `robinConstant` V(K)=inf energy, `logCapacity`=exp(-V), `IsEquilibrium`, `greenFunction` g=V-Uᵘ.
- `logCapacity_lt_of_robinConstant_lt`.

### Tier 2c — `EnergyVariation.lean`
- `logEnergy_perturbation_identity` — I(μ_t)=V_A−2t(1−t)G+t²(Iν−V_A)  [card Step 1 displayed formula].
- `exists_energy_lt_of_green_pos` — G>0 ⟹ ∃ small t>0 with I(μ_t)<V_A  [the strict-gain step].

### Tier 2d — `CapacitySeparation.lean`
- `capacity_separation_core` — equal capacity + a positive-Green-integral perturbation on K2 ⟹ False
  (the card's Step-1 contradiction; Frostman/equilibrium-existence analytics ride as hypotheses).

### Tier 1→4 bridge — `AlgIndep.lean`
- `iterate_monodromy`, `eval_comm_of_coeff_fixed` — helpers.
- `eq_zero_of_monodromy` — a monodromy automorphism σ fixing transcendental G, fixing the
  order-m multiplier ζ, scaling F↦ζF, kills any Y-degree-<m relation P(F,G)=0  [bivariate obstruction].
- `algIndep_of_unbounded_monodromy` — UNBOUNDED monodromy ⟹ NO nonzero relation (full algebraic
  independence). This is the complete §2 (disconnected-case) logic, parameterised on the deep input
  `mono` that the exact-Prüfer theorem supplies.

### Tier 3a — `Period.lean` (period formula COMPLETE)
- `period_point_inside` / `period_point_outside` — Cauchy-kernel dichotomy (`2πi` inside, `0` outside).
- `period_integral_eq` — `∫_K (∮(z-ζ)⁻¹dz) dμ = 2πi·μ(ball)` (no mass on the circle).
- `period_fubini_swap` — `∮_γ ∫_K = ∫_K ∮_γ` (joint integrability hyp: loop separated from `supp μ`).
- `period_eq` — **the period formula** `∮_γ dlogφ_c = 2πi·(enclosed mass)`.

### Tier 3 link — `MonodromyMultiplier.lean`
- `multiplier_orderOf_of_mass` — enclosed mass `2⁻ⁿ` ⟹ multiplier `exp(∮_γ dlogφ_c)` has order `2ⁿ`.
  Chains `period_eq` → `orderOf_dyadicRoot`. The order+multiplier content of `mono` is now verified;
  the remaining `mono` piece is the germ-field deck-transformation (multiplier AS a field automorphism)
  and Brolin (`enclosed mass = 2⁻ⁿ` for a depth-`n` cylinder).

### TOP — `Q62.lean`
- `NoRelation K F G` — algebraic independence as "no nonzero `P∈K[W][Y]` with `P(F,G)=0`" (= Nguyen's "alg. indep. over ℂ(z)").
- `q62_disconnected` — **disconnected/disconnected case PROVEN** from `algIndep_of_unbounded_monodromy` (verified machinery + the monodromy input).
- `q62_independence` — **top q62 theorem COMPILES**: card's Mandelbrot case-split; disconnected discharged outright, connected/mixed via the E–vS rigidity obstruction `hRigid`. Conditional on the two named deep inputs (`hDisc` monodromy, `hRigid` rigidity); nonexceptional conditions `c∉{0,-2}`, `c₁≠c₂` carried in the statement.

## Status of the q62 cases (logical architecture)
- **Disconnected/disconnected: logic COMPLETE** (`algIndep_of_unbounded_monodromy`), modulo two
  named analytic inputs: (i) the `mono` hypothesis = exact-Prüfer monodromy (T3); (ii) capacity
  separation `K_c1 ≠ K_c2` (`capacity_separation_core`, done modulo Frostman hyps).
- Connected/connected and mixed: pending (need the E–vS rigidity tower).

### Concrete dynamics layer — `Dynamics.lean`
- `quadratic c` (`z↦z²+c`), `filledJulia c` (`K_c`), `mandelbrot` (`M`), `Disconnected c` (`c∉M` = the `Disc` of `q62_independence`).
- escape: `quadratic_norm_ge/lt`, `quadratic_orbit_growth` (geometric), `not_mem_filledJulia`.
- **`K_c` compact**: `filledJulia_subset_closedBall`, `isBounded_filledJulia`, `filledJulia_forward`,
  `filledJulia_eq_iInter`, `isClosed_filledJulia`, `isCompact_filledJulia`.
- `disconnected_iff_zero_not_mem`, `disconnected_of_norm_gt` (disconnected params exist for `‖c‖>2`).
  `K_c` is now a genuine compactum — the carrier for the equilibrium measure / capacity theory (item 2).

### Green's function layer — `GreenFunction.lean` (analytic core of the Böttcher coordinate)
- `abs_log_le_two_abs_sub_one`, `log_quadratic_approx` (one-step estimate `|log‖f_c w‖−2log‖w‖| ≤ 2‖c‖/‖w‖²`).
- `greenApprox` (`g_n = 2⁻ⁿlog‖orbitₙ‖`), `greenApprox_step_bound`, `escape_regime_stable`, `greenApprox_step_geom_bound`.
- **`greenApprox_converges`** — `G_c = lim g_n` exists on the escape set (Cauchy via summable geometric differences).
- `greenApproxPlus_tendsto_zero_of_mem` — **`G_c = 0` on `K_c`** (squeeze on the bounded orbit).
- `greenApprox_quadratic` — `g_n(f_c z)=2·g_{n+1}(z)` (seed of `φ_c(z²+c)=φ_c(z)²`).
- `greenLimit` (`G_c`), `greenApprox_tendsto`, **`greenLimit_quadratic`** (`G_c(f_c z)=2·G_c(z)`, the Böttcher functional equation).
- `greenLimit_eq_tsum`, `greenLimit_lower_bound`, `greenLimit_pos` (`G_c>0` for `‖z‖>3`), `greenLimit_pos_escape` (`‖z‖>2`).
- `greenLimit_iterate` (`G_c(f^[N]z)=2ᴺG_c(z)`), `exists_orbit_gt`, `greenLimit_eq_pullback`,
  **`greenLimit_pos_basin`** (`G_c>0` EXACTLY on `Ω_c`; `=0` on `K_c` — the defining sign property).
- **`greenLimit_abs_sub_log`** (`|G_c(z)−log‖z‖| ≤ 2‖c‖/‖z‖²` ⟹ Robin constant `0` ⟹ `cap(K_c)=1`).
- `bottcherModulus` (`|φ_c|=exp G_c`), `one_lt_bottcherModulus` (`|φ_c|>1` on `Ω_c`),
  `bottcherModulus_quadratic` (`|φ_c(z²+c)|=|φ_c(z)|²`).
The Green's function of a quadratic Julia set + the Böttcher MODULUS are now formalized from scratch (not in Mathlib).
All genuinely PROVEN analysis (not assumed). `#print axioms` on every result = `[propext, Classical.choice, Quot.sound]` only.
### Complex Böttcher coordinate — `ComplexLogBound.lean` + `BottcherCoord.lean`
- `norm_clog_one_add_le` — `‖log(1+w)‖ ≤ 2‖w‖` (mean-value inequality on `closedBall 1 ½`).
- `bottcherLogTerm` + `norm_bottcherLogTerm_le` + `bottcherLogTerm_summable` — the ℂ log-series converges (escape set).
- `bottcherLog` (`= log z + ∑ₖ termₖ`), **`bottcherCoord`** (`φ_c = exp(bottcherLog)`).
- `bottcherLogTerm_re` (`Re(termₖ)=g_{k+1}-g_k`), **`bottcherLog_re`** (`Re(log φ_c)=G_c`),
  `norm_bottcherCoord` (`‖φ_c‖=exp G_c`), `one_lt_norm_bottcherCoord` (`φ_c: escape→{|w|>1}`).
- `bottcherLogTerm_quadratic` + `bottcherLog_sum_quadratic` (functional-equation seed, branch-free).
- **Analyticity**: `analyticAt_quadratic_iterate` (orbit), `one_add_mem_slitPlane`, `analyticAt_bottcherLogTerm`,
  `differentiableOn_bottcherLogSum` (Weierstrass M-test on `escapeOpen`), `differentiableOn_bottcherLog`,
  **`analyticOnNhd_bottcherCoord`** — `φ_c` is PROVEN ANALYTIC on the slit neighborhood `escapeOpen ∩ slitPlane`.
- `hasSum_deriv_bottcherLogSum`, **`deriv_bottcherLog`** (`d log φ_c = z⁻¹ + ∑ₖ deriv termₖ`).
- **`harmonicAt_greenLimit`** (`G_c` harmonic, via `Re` of analytic `log φ_c`).
`G_c` now has ALL FOUR Green's-function defining properties: **harmonic** (`harmonicAt_greenLimit`),
**`=0` on `K_c`** (`greenFunctionDyn_eq_zero_iff`), **`>0` on `Ω_c`** (`greenLimit_pos_basin`),
**`~log‖z‖` at `∞`** (`greenLimit_abs_sub_log`) — exactly the input to Brolin's uniqueness argument.
NEXT for `hDisc`: the equilibrium-measure / Brolin theorem (`G_c = potential of μ_c`, `μ_c` balanced, cylinder
mass 2⁻ⁿ) → `∮_γ dlogφ_c = 2πi/2ⁿ` (proven `period_eq`) → germ-field automorphism → `DyadicMonodromyTower`.

## VERIFIED so far (sorry-free, from Mathlib up): 14 modules, 128 results
Top theorem `q62_independence` COMPILES (conditional on `hDisc`, `hRigid`); disconnected case PROVEN
(`q62_disconnected`, `q62_disconnected_tower`); the entire algebraic / potential-theoretic / contour
skeleton + the period formula are complete and machine-checked.

## Remaining for UNCONDITIONAL q62 (each a real analytic/dynamical build, none in Mathlib)
These discharge the two named hypotheses of `q62_independence`:

Disconnected (`hDisc`):
1. Böttcher coordinate `φ_c` + Green-potential rep `dlogφ_c = ∫(z-ζ)⁻¹dμ_c` (connect to `period_eq`).
2. `K_c = supp μ_c`, `cap(K_c)=1` — connect `Dynamics` to Tier-2 capacity (discharges `capacity_separation_core` Frostman hyps).
3. Brolin: `μ_c` balanced ⟹ depth-`n` cylinder mass `2⁻ⁿ` (feeds `multiplier_orderOf_of_mass`).
4. Full-shift coding of disconnected `K_c` (symbolic dynamics).
5. Germ-field deck transformation: build `DyadicMonodromyTower` from analytic continuation around cylinders.
6. Transcendence of `φ_c` (Becker–Bergweiler).

Connected (`hRigid`):
7. Eremenko–van Strien smooth-piece Julia rigidity (arXiv:0810.2260) + algebraic-IFT continuation contradiction.

Final:
8. Instantiate everything into `q62_independence`, removing `hDisc`/`hRigid` → unconditional theorem.

Priority path: items 1–6 (disconnected, needs no E–vS). Each is a compiling increment; the period
formula (T3a) and the obstruction engines are already in hand, so the remaining weight is building the
Böttcher/Julia/Brolin/germ-field analytic infrastructure that Mathlib does not have.

## Progress log — 2026-06-24 (continued, brick-by-brick toward discharging hDisc)

New verified bricks in `BottcherCoord.lean` (full `lake build GaloisForLFunctions.Bottcher` exit 0; zero sorries/axioms; zero ring-noise):

- `norm_bottcherCoord_eq_exp_green` — `‖φ_c(z)‖ = exp(G_c(z))` on the escape set. Bridges
  max-modulus (analytic `φ_c`) to the maximum principle (real `G_c`).
- `greenLimit_eqOn_of_isMaxOn` — **maximum principle for `G_c`**: an interior max of `G_c`
  on a preconnected open `U ⊆ escapeOpen∩slitPlane` forces `G_c` constant. Via
  `Complex.eqOn_of_isPreconnected_of_isMaxOn_norm` on `φ_c`. Uniqueness engine (Brolin A2).
- `bottcherCoord_quadratic` — **functional equation** `φ_c(z²+c) = φ_c(z)²` (exact; the
  `log(z²)−2log z ∈ 2πiℤ` branch ambiguity is annihilated by `exp`). The conjugacy
  `φ_c ∘ f_c = (·)² ∘ φ_c` of the dynamics to `w ↦ w²`.
- `norm_iterate_ge` — orbit stays in the escape regime (`‖z‖ ≤ ‖f_c^[n] z‖`).
- `bottcherCoord_iterate` — **iterated functional equation** `φ_c(f_c^[n] z) = φ_c(z)^(2ⁿ)`.
  Where the dyadic `2ⁿ` of the monodromy is born.

### Precise remaining gap to discharge `hDisc` (exact-Prüfer monodromy tower)
`multiplier_orderOf_of_mass` already gives: cylinder mass `2⁻ⁿ` ⟹ multiplier order `2ⁿ`.
Two from-scratch sub-towers remain (Mathlib lacks both):
- **GAP A (Brolin / balanced measure):** define `μ_c` (Riesz measure of `G_c` — Mathlib has
  NO Riesz/subharmonic/Laplacian-as-measure), prove `G_c` = potential of `μ_c` (uses the new
  max principle), `f_*μ_c = μ_c` balanced (from `greenLimit_quadratic`), hence depth-`n`
  cylinder mass `= 2⁻ⁿ`.
- **GAP B (germ-field monodromy):** realize continuation around the depth-`n` cylinder loop as
  a field automorphism `σ_n ∈ M ≃ₐ[K] M` with `σ_n φ_{c₁} = ζ_{2^{n+1}} φ_{c₁}`, `σ_n φ_{c₂}
  = φ_{c₂}`. The conjugacy/iterate bricks above are its algebraic backbone; needs Mathlib-absent
  analytic-continuation-along-paths infrastructure.
Then `DyadicMonodromyTower` assembles ⟹ `hDisc` discharged ⟹ `q62_independence` unconditional
on the disconnected/disconnected case. `hRigid` (E–vS) remains for connected/mixed.

### GAP B route is Mathlib-supported (found 2026-06-24) — `npow` covering
`Complex.isQuotientCoveringMap_npow (n) [NeZero n] : IsQuotientCoveringMap (·^n) (powMonoidHom n).ker`
and `isCoveringMap_npow` give: `w ↦ w^{2ⁿ}` on `ℂˣ` is a covering whose **deck group is exactly
`(powMonoidHom (2ⁿ)).ker` = the `2ⁿ`-th roots of unity, acting by multiplication** — i.e. `μ_{2ⁿ}`,
the dyadic monodromy multiplier group, already formalized. Homotopy/path lifting
(`Topology.Homotopy.Lifting`) supplies analytic-continuation-along-paths.
Concrete monodromy construction:
1. `bottcherCoord_iterate` conjugates `f_c^[n]` to `w ↦ w^{2ⁿ}` (proven).
2. Deck transformation `w ↦ ζ·w` (ζ ∈ μ_{2ⁿ}, from the npow covering kernel) pulls back through
   `φ_c` to a branch-change of `φ_c`, FIXING `z` (hence fixing `K = ℂ(z)`) and sending
   `φ_{c₁} ↦ ζ·φ_{c₁}`.
3. That branch-change is the field automorphism `σ_n ∈ M ≃ₐ[K] M` of `DyadicMonodromyTower`.
No deck-group-as-automorphisms is pre-built in Mathlib's covering API — that piece is the next
sub-tower, but the covering + kernel + lifting it rests on are all present.

### New file `Bottcher/MonodromyCovering.lean` (2026-06-24, build green, zero axioms)
First import of Mathlib's covering theory into the tower. Verified:
- `dyadicDeck n := (powMonoidHom n).ker` — the `n`-th roots of unity in `ℂˣ` (deck group).
- `dyadicDeck_pow`, `deck_mul_npow` — kernel elements are `n`-th roots of unity; left-mult is a
  deck transformation (preserves `w ↦ wⁿ`).
- `npow_eq_iff_mem_dyadicOrbit` — **monodromy torsor**: `w₁ⁿ = w₂ⁿ ↔ w₁ ∈ orbit(μ_n) w₂`
  (= `isQuotientCoveringMap_npow.apply_eq_iff_mem_orbit`). Fibre = one `μ_n`-orbit.
- `eq_dyadicRoot_mul_of_npow_eq` — two values with equal `2ⁿ`-th powers differ by a `2ⁿ`-th root
  of unity. Pins the monodromy multiplier set to `μ_{2ⁿ}`.
NEXT brick (#52→σ_n): set up the function/germ field `M ⊇ K=ℂ(z)` and realize the deck multiplier
`w ↦ ζ·w` as `σ_n ∈ M ≃ₐ[K] M` with `σ_n φ_{c₁} = ζ φ_{c₁}`, `σ_n φ_{c₂}=φ_{c₂}` — assembling
`DyadicMonodromyTower`. Parallel: GAP-A (#53) balanced measure ⟹ cylinder mass `2⁻ⁿ`.

### `MonodromyCovering.lean` +2 faithful value-level bricks (2026-06-24, build green)
- `bottcherCoord_pow_preimage` — a `f_c^[n]`-preimage `w` of `z` gives `φ_c(w)^(2ⁿ) = φ_c(z)`:
  the dynamics supplies the *actual* `2ⁿ`-th roots of `φ_{c₁}` (radical tower NOT formally adjoined
  — avoids the toy that assumes independence). `bottcherCoord_iterate` read backwards.
- `bottcherCoord_preimage_dyadic` — two preimages' Böttcher values differ by a `2ⁿ`-th root of
  unity. The monodromy multiplier at the value level.

### Next brick = germ-field sub-tower (the irreducible analytic core of `hDisc`)
Need: field `M` of multivalued-analytic / germ functions on `Ω_c`, `K=ℂ(z) ↪ M` (RatFunc ℂ),
`F=φ_{c₁}, G=φ_{c₂} ∈ M`, and `σ_n ∈ M ≃ₐ[K] M` = monodromy round the depth-`n` cylinder loop,
PROVEN `σ_n G=G`, `σ_n F=ζ_n F`. Realized as precomposition with a deck transformation of the
Böttcher covering (deck map is a homeomorphism, so precomposition is automatically a `K`-algebra
automorphism — no separate "continuation-as-automorphism" needed). Mathlib gives covering
(`isQuotientCoveringMap_npow`), lifting (`Topology.Homotopy.Lifting`), Kummer-Galois
(`autAdjoinRootXPowSubC`). The basin covering space + deck-precomposition automorphism is the
build. NOTE: a purely abstract `K(G)(F)` rational-function model is a TOY (assumes independence) —
`M` must be the actual germ field with the actual `φ_c`.

### `BottcherCoord.lean` +2, new `Winding.lean` +1 (2026-06-24, build green 2768 jobs, zero axioms)
- `bottcherCoord_eq_mul_exp` — branch-free `φ_c = z·exp(∑ₖ termₖ)` (`z≠0`).
- `differentiableOn_bottcherCoord` — `φ_c` analytic on ALL of `escapeOpen` (off the slit too), so
  circles `C(0,R)` lie in the domain.
- `circleIntegral_dlog_bottcher` — **base period** `∮_{C(0,R)} d log φ_c = 2πi` (total mass = 1,
  `cap K_c = 1`, winding 1). `n=0` rung of the dyadic period tower. Proof: `z⁻¹`-pole gives `2πi`,
  series part is a single-valued derivative ⟹ loop integral `0` (FTC).

### STRATEGIC: dyadic periods `2πi/2ⁿ` come from the FUNCTIONAL EQUATION, not Brolin's measure
`d log φ_c(f z)·f'(z) = 2·d log φ_c(z)` (log-derivative of `φ_c∘f=φ_c²`). So pulling a loop back
through `f` HALVES its period: `∮_{γ̃} d log φ_c = ½ ∮_{f∘γ̃} d log φ_c`. The `n`-fold pullback of
the base loop (period `2πi`) has period `2πi/2ⁿ` = the order-`2ⁿ` monodromy multiplier exponent.
⟹ GAP-A (equilibrium measure / cylinder mass `2⁻ⁿ`) is NOT needed for the period VALUES — the
period halving is pure functional-equation + contour change-of-variables. The remaining subtlety:
the `n`-fold pullback loop is non-closing (that non-closure IS the monodromy), so the deeper rungs
still need the continuation/path framework, but the multiplier value `2πi/2ⁿ` is now elementary.
NEXT: formalize the period-halving (change of variables ∮_{f∘γ̃} g = 2∮_{γ̃} g for g = d log φ_c).

### `Winding.lean` +3 self-similarity bricks (2026-06-24, build green 2768, zero axioms)
- `logDeriv_bottcherCoord_self_similar` — `logDeriv φ_c (z) = z · logDeriv φ_c (f_c z)`. The
  functional equation `φ_c∘f=φ_c²` differentiated (via Mathlib `logDeriv_comp`/`logDeriv_mul`):
  the pointwise/multiplicative form of "pullback through f halves the period".
- `escapeOpen_iterate` — escape set is forward-invariant.
- `logDeriv_bottcherCoord_iterate` — `logDeriv φ_c(z) = (∏_{k<n} f^[k]z)·logDeriv φ_c(f^[n]z)`.
  Product expansion of `d log φ_c` = Cauchy transform of equilibrium measure, in product (not
  measure) form. Exhibits the `2⁻ⁿ`-generating structure with NO measure theory.
These make the dyadic period self-similarity fully explicit and verified at the pointwise level.
NEXT: lift pointwise self-similarity to the contour/period statement (∮ around the n-fold pullback
loop = 2πi/2ⁿ), then to the germ-field automorphism σ_n (deck precomposition) → DyadicMonodromyTower.

### `Winding.lean` +1 contour-lift (2026-06-24, build green 2768, zero axioms)
- `pathInt_comp_quadratic` — **period-doubling** `∮_{f_c∘γ} ω = 2∮_γ ω` for `ω = d log φ_c`,
  done as a parametrized `intervalIntegral` (NO measure theory, NO general contour object — Mathlib
  has none). The integral form of `f_c*ω = 2ω`. Since `ω` is single-valued on the whole basin
  (branches of `φ_c` differ by constants, killed by `d log`), the `n`-fold loop pullback of the base
  loop (period `2πi`) has period `2πi/2ⁿ` — the order-`2ⁿ` monodromy multiplier exponent.

### Period side of `hDisc` is now elementary & faithful (no Brolin measure)
Banked end-to-end for the ACTUAL `φ_c`: base period `2πi` (`circleIntegral_dlog_bottcher`) +
self-similarity `f*ω=2ω` (`logDeriv_bottcherCoord_self_similar`, pointwise + iterate) + contour-lift
period-doubling (`pathInt_comp_quadratic`) ⟹ the multiplier value `exp(2πi/2ⁿ)`, order `2ⁿ`
(already abstract in `orderOf_dyadicRoot`/`multiplier_orderOf_of_mass`).

### THE remaining blocker for `hDisc` (explicit): σ_n as a germ-field automorphism
`DyadicMonodromyTower` needs `σ_n ∈ M ≃ₐ[K] M` (not just the multiplier value/order). This requires
the field `M` of multivalued-analytic functions on `Ω_c` with `σ_n` = analytic continuation around
the depth-`n` loop = deck transformation. CANNOT be a toy abstract `K(G)(F)` (assumes independence).
Mathlib lacks the germ-field-with-monodromy; has étale space (`Topology.Sheaves.EtaleSpace`), path
lifting (`Topology.Homotopy.Lifting`), covering (`isQuotientCoveringMap_npow`) to build on. This is
the next sub-tower. `hRigid` (E–vS) remains for connected/mixed.

### `Winding.lean` +1 n-fold period (2026-06-24, build green 2768, zero axioms)
- `pathInt_iterate_comp` — `∮_{f_c^[n]∘γ} ω = 2ⁿ ∮_γ ω`. ⟹ an `n`-fold loop pullback has period
  `2πi/2ⁿ` = order-`2ⁿ` monodromy multiplier exponent, for the ACTUAL `φ_c`, zero measure theory.
PERIOD/MULTIPLIER THEORY FOR `φ_c` IS COMPLETE: base `2πi` + self-sim `f*ω=2ω` + contour-lift
period-doubling + n-fold scaling. The multiplier value `exp(2πi/2ⁿ)` & order `2ⁿ` are pinned.

### The TWO remaining sub-towers for unconditional q62 (each Mathlib-absent, major):
1. **σ_n as germ-field automorphism (`hDisc`).** Needs `M` = field of analytic functions on the
   universal cover of `Ω_c` (or germ field) with `σ_n` = continuation/deck around the depth-`n`
   loop. Mathlib has étale space (`EtaleSpace`, `isCoveringMap_base`) + path lifting but NO
   analytic-continuation-as-field-automorphism and NO meromorphic-germ FIELD. Building it (sheaf of
   analytic fns → étale space → field on stalks → lift-as-automorphism → action on φ_c, well-defined
   via monodromy theorem) is a research-scale formalization. The period side above PINS what σ_n
   must do (scale by exp(2πi/2ⁿ)); only the automorphism realization remains.
2. **Eremenko–van Strien rigidity (`hRigid`).** Separate hard 2009 theorem (arXiv:0810.2260), not
   in Mathlib; needed for the connected/mixed cases.
Both are genuine multi-week/team-scale formalizations; the entire analytic FOUNDATION beneath them
(~27 theorems) is built and zero-axiom.

### New `DeckAutomorphism.lean` — algebraic core of σ_n (2026-06-24, build green 2812, zero axioms)
- `polyScaleHom`/`polyScaleEquiv` — `W ↦ ζ·W` as an honest ℂ-algebra automorphism of the fibre
  coordinate ring `ℂ[W]` (`polyScaleEquiv_X : σ(W) = ζ·W` — the scaling `σ_n F = ζ_n F`).
- `polyScaleHom_comp` — `σ_ζ∘σ_η = σ_{ζη}` (the `μ`-action homomorphism).
- `polyScaleHom_injective_param` — `ζ ↦ σ_ζ` faithful ⟹ `orderOf σ_ζ = orderOf ζ` (deck group
  `μ_{2ⁿ}` embeds; supplies the order-`2ⁿ` requirement).
So the scaling + composition + order of `σ_n` are now realized by a genuine field-coordinate
automorphism. REMAINING for `σ_n` on the FULL field: (a) lift `ℂ[W]`-equiv to the field `ℂ(W)` via
`IsFractionRing` functoriality (next brick), (b) embed actual `φ_c` germs into a cover field `M ⊇
ℂ(z)` extending `ℂ(W)` with `W = φ_{c₁}` — the genuine analytic input. Period side + algebraic core
of σ_n are DONE; the analytic cover-field embedding is the remaining piece of `hDisc`.

### `DeckAutomorphism.lean` +field lift (2026-06-24, build green 2812, zero axioms)
- `deckRatEquiv` — the deck automorphism on the fibre FIELD `ℂ(W)` (lift of `polyScaleEquiv` via
  `IsLocalization.algEquivOfAlgEquiv`). A genuine ℂ-algebra field automorphism.
- `deckRatEquiv_smul_gen` — `σ(W) = ζ·W` on the field generator. The `σ_n F = ζ_n F` clause.

### KEY STRUCTURAL FINDING (recorded in DeckAutomorphism.lean): the abstract route is CIRCULAR
A `DyadicMonodromyTower` for the actual coordinates needs `σ_n` on `M ⊇ ℂ(z)` with `φ_{c₁}` scaled
and `φ_{c₂}` FIXED & transcendental. Any `σ_n`-fixed element of `ℂ(z)(φ_{c₁})` lies in `ℂ(z)=K`, so
a fixed transcendental `φ_{c₂}` forces `φ_{c₂}∉ℂ(z)(φ_{c₁})` — the independence itself. ⟹ the
well-definedness of `σ_n` (fixing `φ_{c₂}`) CANNOT come from an abstract algebraic `M`; it must come
from ANALYTIC CONTINUATION on the actual germ/cover field, where the action on `φ_{c₂}` (trivial
monodromy of the other basin's loop) is an analytic FACT. This pins ALL remaining `hDisc` work to
the analytic-continuation layer — no algebraic shortcut exists. The period side + the algebraic
SHAPE of `σ_n` are fully built; the analytic continuation (field of multivalued fns on `Ω_c` + σ as
continuation, well-defined by the monodromy theorem) is the irreducible remaining core.

### MATERIAL FINDING + new `MonodromyContinuation.lean` (2026-06-24, build green 2943, zero axioms)
Mathlib ALREADY HAS the covering monodromy theorem: `IsCoveringMap.monodromy` is a
homotopy-invariant fibre bijection (`monodromy_bijective`, `monodromy_trans_apply` functoriality,
`monodromyFunctor`). This removes the hardest hand-built piece (homotopy invariance / monodromy
theorem) from the continuation layer — the layer is far more tractable than first assessed.
Banked:
- `isCoveringMap_dyadic` — the covering `w↦w^{2ᵏ}` of `ℂ∖{0}` (= `isCoveringMap_npow` at `2ᵏ`).
- `dyadic_monodromy_bijective` — its monodromy is a fibre bijection (the topological continuation
  operator `σ`, well-defined by Mathlib's monodromy theorem).
- `dyadic_monodromy_trans` — functoriality `π₁ → Sym(fibre)` (image = deck group).

### Updated concrete path to `σ_n` (each step now a defined Mathlib-supported brick):
1. topological monodromy of the dyadic covering ✓ (here)
2. it's a deck element `ζ ∈ μ_{2ᵏ}` of order `2ᵏ` — generator loop of `π₁(ℂ∖{0})=ℤ`, order from
   the winding/period theory (built) — NEXT brick
3. induced field automorphism = `deckRatEquiv ζ` ✓ (built)
4. pull back along `φ_{c₁}` to the basin, fixing `φ_{c₂}` (analytic fact: loop null-homotopic in the
   other basin) — the remaining genuinely-analytic input
`hRigid` (E–vS) still pending for connected/mixed.

### `MonodromyContinuation.lean` +`dyadic_generator_lift` — step 2 DONE (2026-06-24, build clean, zero ax)
- `dyadic_generator_lift` — explicit `2ᵏ`-th-root lift `Γ(t)=exp(2πi t/2ᵏ)` of the generator loop:
  `Γ(t)^{2ᵏ}=exp(2πi t)` (lifts) ∧ `Γ(1)=exp(2πi/2ᵏ)·Γ(0)` (primitive `2ᵏ`-root multiplier) ∧
  order `2ᵏ`. The dyadic monodromy multiplier as covering monodromy, matching the period value.
σ_n path: steps 1 (topological monodromy) ✓, 2 (generator multiplier, order 2ᵏ) ✓, 3 (deckRatEquiv
field automorphism) ✓. REMAINING: step 4 = pull the dyadic covering back along `φ_{c₁}` to the
actual disconnected basin `Ω_{c₁}` (its branched covering minus precritical orbit), carry `φ_{c₂}`/`z`
as functions, prove `σ_n` fixes `φ_{c₂}` (loop null-homotopic in the other basin). Step 4 needs the
disconnected-basin covering structure (Cantor Julia set) — the major remaining analytic build.
`hRigid` (E–vS rigidity) remains for connected/mixed.

### New `BasinBranching.lean` — step 4 opened (2026-06-24, build green 2944, zero axioms)
- `disconnected_critical_escapes` — `Disconnected c ⟹ ∃ N, f_c^[N] 0 ∈ escapeOpen c`. The critical
  point escapes; its value sits at a positive Green level — the source of `φ_c`'s branching.
- `disconnected_green_critical_pos` — `Disconnected c ⟹ G_c(0) > 0`. The branch locus is the level
  set `{G_c = G_c(0)}` and its `f_c`-preimages (the depth-`n` cylinders).
σ_n skeleton (steps 1–3: covering monodromy, generator multiplier order 2ⁿ, deckRatEquiv field
automorphism) DONE. Step 4 dynamical foundation started. Full step 4 = branched covering
`Ω_{c₁}∖(precritical orbit)` + `φ_{c₁}` single-valued on it + `φ_{c₂}`/`z` carried + `σ_n` fixes
`φ_{c₂}` — the major remaining analytic build (disconnected/Cantor covering). `hRigid` (E–vS) pending.

### `BasinBranching.lean` +4 — cylinder level structure (2026-06-24, build green 2944, zero axioms)
- `greenApprox_tendsto_basin` — `g_n→G_c` on the whole basin (via pullback to escape regime).
- `greenLimit_quadratic_basin` — `G_c(f_c z)=2 G_c(z)` on all of `Ω_c` (levels double under `f_c`).
- `not_mem_filledJulia_iterate` — basin forward-invariant.
- `greenLimit_iterate_basin` — `G_c(f_c^[n] z)=2ⁿ G_c(z)`: depth-`n` cylinder `{G_c(0)/2ⁿ<G_c<
  G_c(0)/2ⁿ⁻¹}` maps `2ⁿ`-to-1 onto the critical collar `{G_c(0)<G_c<2 G_c(0)}` — the dyadic
  covering of step 4, matching the skeleton's `w↦w^{2ⁿ}` covering.
Step 4 progress: critical escape + critical level + cylinder doubling + the 2ⁿ-to-1 collar map
are now in the tree. REMAINING for step 4: realize `f_c^[n]: cylinder → collar` as an honest
covering map (branch points = precritical orbit removed), lift `φ_{c₁}`, carry `φ_{c₂}`/`z`, apply
the verified continuation skeleton ⟹ `σ_n`, assemble `DyadicMonodromyTower`. `hRigid` (E–vS) pending.

### `BasinBranching.lean` +2 — collar map local-triviality (2026-06-24, build green 2944, zero ax)
- `hasStrictDerivAt_quadratic` — `f_c'(z) = 2z`.
- `quadratic_map_nhds` — `f_c` is a local homeomorphism off the critical point (`map f_c (𝓝 z) =
  𝓝(f_c z)` for `z≠0`). With the cylinder structure (`greenLimit_iterate_basin`, `2ⁿ`-to-1), this
  gives: `f_c^[n]: cylinder → collar` is `2ⁿ`-to-1 AND a local homeomorphism off the precritical
  orbit — an honest covering there, the analytic realization of the skeleton's `w↦w^{2ⁿ}` cover.
Step 4 status: cylinder doubling ✓, `2ⁿ`-to-1 collar map ✓, local-homeo off critical point ✓.
REMAINING: assemble these into `IsCoveringMap (f_c^[n]) (collar ∖ critical-values)`, lift `φ_{c₁}`
single-valued, carry `φ_{c₂}`/`z`, `σ_n` fixes `φ_{c₂}` ⟹ `DyadicMonodromyTower`. `hRigid` pending.

### `BasinBranching.lean` +polynomial degree (2026-06-24, build green 2944, zero axioms)
- `quadraticPoly`/`quadraticPolyIterate` — `f_c` and `f_c^[n]` as polynomials.
- `quadraticPolyIterate_natDegree` — `deg(f_c^[n]) = 2ⁿ`: the `2ⁿ`-fold covering degree (each value
  attained `2ⁿ` times; off the `2ⁿ−1` critical values the `2ⁿ` preimages are distinct).
- `quadraticPolyIterate_eval` — polynomial agrees with the iterated map.
Step 4 covering ingredients now ALL machine-checked: cylinder doubling ✓, `2ⁿ`-to-1 fibre (degree)
✓, local-homeo off critical point ✓, fibre count `2ⁿ` ✓. REMAINING: assemble even-covering
(trivialization) on the punctured collar → `IsCoveringMap (f_c^[n])`, lift `φ_{c₁}`, carry `φ_{c₂}`/`z`,
`σ_n` fixes `φ_{c₂}` → `DyadicMonodromyTower`. No Mathlib "proper-local-homeo ⟹ covering" shortcut;
the trivialization is hand-built. `hRigid` (E–vS) pending.

### New `FigureEight.lean` module — disconnected-basin / winding bricks (2026-06-25, build green, zero axioms)
Disjoint from the ∞-side uniformization work; this is the disconnected-only topology, the genuine
remaining analytic crux of `hDisc`. Four verified bricks (each `#print axioms` = `[propext,
Classical.choice, Quot.sound]`):
- `pathInt_dlog_lift_closed_eq_zero` (in `CoverConstruction.lean`) — **the `φ_{c₂}`-fixed half**: a
  closed loop inside the single-valued domain `D_m={f^[m]z∈escape∩slit}` of the lift `φ̃c` has
  `∮_γ d log φ̃c = 0` (FTC for closed loops). The asymmetry vs the `c₁`-loop: same loop, period
  `2πi/2ⁿ` for `φ_{c₁}` (crosses fundamental domains) but `0` for `φ_{c₂}` (null-homotopic in the
  other basin). This is "`σ_n` fixes `φ_{c₂}`" on the genuine (analytic-continuation) route — NOT the
  circular self-map route (`hliftF` of `q62_independence_disconnected_of_lifts` forces `g=id` because
  it must fix `ℂ(z)`; that reduction is a dead-end confirmed here).
- `winding_value_of_iterate_loop` — **the winding value**: a depth-`n` lifted loop (`f^[n]∘γ` has
  iterate-period `2πi`) has `∮_γ d log φ_{c₁} = 2πi/2ⁿ`. Pure consequence of `pathInt_iterate_comp`.
  Reduces the winding lemma to ONE existence statement (`hbase` = the lifted base loop).
- `fderiv_greenLimit_critical` (L4a) — **the branch point**: for `Disconnected c`, `fderiv ℝ G_c 0 =
  0`. The escaping critical point `0` is a critical point of `G_c` (basin scaling `G_c=½G_c∘f_c` +
  `f_c'(0)=0`). Uses the just-added `harmonicOnNhd_greenLimit_basin`.
- `exists_holomorphic_completion_critical` (L4c) — **the holomorphic saddle model**: near `0`,
  `G_c = Re F` for `F` analytic with `deriv F 0 = 0` (harmonic-conjugate `exists_analyticOnNhd_ball_re_eq`
  + L4a via Cauchy–Riemann). So `F − F(0) = ½F''(0)z² + O(z³)`: the non-degenerate saddle whose level
  set `{G_c=G_c(0)}` is the figure-eight, below which the basin splits into 2 Cantor lobes.

GENUINE REMAINING CRUX (everything else built or reduced): the **lifted winding loop** `hbase` —
construct a closed `γ` around ONE lobe with `f^[n]∘γ` = base circle (period `2πi`), `γ` shrinking into a
disk in `Ω_{c₂}`. Needs: (L4c→) non-degeneracy `F''(0)≠0` ⟹ figure-eight splits sublevel into 2
components ⟹ a loop around one lobe; + cylinders-shrink-to-points. Then: winding value + L1 ⟹ `σ_n`
(`φ_{c₁}↦ζφ_{c₁}`, `φ_{c₂}` fixed) ⟹ `φ_{c₁}∘f^[n]` not a square in `meroField` (`not_square_of_period_ftc`)
⟹ Kummer irreducibility (`kummer_*` in `Q62Assembly`) ⟹ `NoRelation` ⟹ `hDisc` unconditional.

### `FigureEight.lean` +2 (2026-06-25, build green, zero axioms) — non-degeneracy scaffold
- `critical_orbit_ne_zero` (L4d) — `Disconnected c ⟹ f_c^[k] 0 ≠ 0` (k≥1): `0` is aperiodic (periodic ⟹
  bounded orbit ⟹ `0∈K_c`). So `c=f_c(0)` is not precritical.
- `fderiv_greenLimit_eq_zero_iff_quadratic` (L4e) — for `z₀∈Ω_c`, `z₀≠0`: `∇G_c(z₀)=0 ↔ ∇G_c(f_c z₀)=0`
  (chain rule; `f_c'(z₀)=2z₀` invertible). Critical points propagate forward off `0`.
NEXT (escape base case): `∇G_c ≠ 0` on `escapeOpen` (via harmonic conjugate `F` with `F'=logDeriv φ_c ≠ 0`).
Then: L4e backward from escape + L4d ⟹ `c` regular (`∇G_c(c)≠0`) ⟹ saddle non-degenerate (`F''(0)≠0`,
L4c) ⟹ `{G_c=G_c(0)}` figure-eight ⟹ sublevel splits into 2 lobes ⟹ loop around one lobe (`hbase`) ⟹
[winding value + L1] `σ_n` ⟹ not-a-square ⟹ Kummer irreducible ⟹ `hDisc` unconditional.

### `FigureEight.lean` +1 (2026-06-25) — escape base case, step 1 of 5
- `logDeriv_bottcherCoord_escape` — `d log φ_c = z⁻¹ + S'(z)` on ALL of `escapeOpen` (slit-free, via
  `φ_c = z·exp S`). The object the Cauchy estimate bounds.
REMAINING escape base case: (2) `‖S'(z)‖ ≤ 16‖c‖/‖z‖³` via Cauchy estimate
`Complex.norm_deriv_le_of_forall_mem_sphere_norm_le` on a ball of radius `‖z‖/2` (value bound
`‖S‖ ≤ 2‖c‖/‖z‖²` = `norm_bottcherLog_sub_log_le`); (3) `‖z‖²>16‖c‖ ⟹ ‖z⁻¹‖>‖S'‖ ⟹ logDeriv φ_c ≠ 0`;
(4) propagate to all `escapeOpen` via `logDeriv_bottcherCoord_iterate_eq_zero_iff`; (5) `logDeriv ≠ 0
⟹ ∇G_c ≠ 0` (CR, as in L4c). Then backward L4e from escape + L4d ⟹ `c` regular ⟹ non-degenerate saddle.

### `FigureEight.lean` — ESCAPE BASE CASE COMPLETE + `c` regular (2026-06-25, build green, zero axioms)
The whole `∇G_c ≠ 0` base case is now machine-checked (5 steps), plus the critical value is regular:
- `logDeriv_bottcherCoord_escape` — `d log φ_c = z⁻¹ + S'` slit-free on `escapeOpen`.
- `norm_deriv_bottcherLogSum_le` — Cauchy estimate `‖S'(z)‖ ≤ 16‖c‖/‖z‖³`.
- `logDeriv_bottcherCoord_ne_zero_far` — `d log φ_c ≠ 0` for `‖z‖²>16‖c‖` (pole dominates).
- `logDeriv_bottcherCoord_ne_zero_escape` — `d log φ_c ≠ 0` on ALL `escapeOpen` (orbit escapes + zero-set invariance).
- `deriv_eq_zero_of_fderiv_re_eq_zero` (CR helper) + `fderiv_greenLimit_ne_zero_escape` — `∇G_c ≠ 0`
  on `escapeOpen` (harmonic conjugate `F`, `deriv F = logDeriv φ_c` by identity theorem on `B∩slit`).
- `fderiv_greenLimit_ne_zero_critical_value` — `∇G_c(c) ≠ 0`: propagate L4e forward from `c` to escape,
  each `f^[j]c = f^[j+1]0 ≠ 0` (L4d). ⟹ saddle at `0` is NON-DEGENERATE (`F''(0)=F'(c)≠0`).
NEXT: `F''(0) ≠ 0` formally (relate the L4c conjugate's 2nd derivative to `∇G_c(c)` via the functional
equation) ⟹ `{G_c<G_c(0)}` near `0` splits into 2 components ⟹ loop around one lobe (`hbase`) ⟹
[winding-value + L1] `σ_n` ⟹ not-a-square ⟹ Kummer ⟹ `hDisc`. Connected case (`hRigid`): E–vS, separate.

### `FigureEight.lean` — NON-DEGENERATE SADDLE COMPLETE (2026-06-25, build green, zero axioms)
- `deriv2_completion_critical_ne_zero` (L4l) — `F''(0) ≠ 0` for any holomorphic completion `F` of `G_c`
  near `0`. Via a second conjugate `F_c` near `c`: `Re(F − ½F_c∘f_c) ≡ 0` ⟹ `deriv F(z) = z·F_c'(z²+c)`
  ⟹ `F''(0) = F_c'(c) ≠ 0` (L4k). The saddle at `0` is order-2: `{G_c = G_c(0)}` a genuine figure-eight.
The local analytic model of the disconnected critical point is now FULLY characterized:
`F` analytic near `0`, `Re F = G_c`, `F'(0)=0`, `F''(0)≠0`.
NEXT: `{Re(F−F(0)) < 0}` near `0` has exactly 2 components (the local normal form `w=√(½F''(0))·z`
sends `F−F(0) ↦ w²`, sublevel `{Re w² < 0}` = two opposite sectors) ⟹ the two Cantor lobes ⟹ loop
around one lobe ⟹ basin period `2πi/2ⁿ` ⟹ not-a-square ⟹ Kummer ⟹ `hDisc`. Connected case: E–vS.

### `FigureEight.lean` — LOCAL NORMAL FORM `w↦w²` COMPLETE (2026-06-25, build green, zero axioms)
- `exists_analyticAt_sq_eq` — nonvanishing analytic `g` has a local analytic `√g` (via `s·exp(½log(g/g₀))`).
- `exists_factor_order_two` — `F z−F 0 = z²·G z`, `G 0 = ½F''(0) ≠ 0` (Taylor `exists_eventuallyEq_sum_add_pow_mul` to order 3).
- `exists_sq_normal_form` — `∃ h` biholo (`h 0=0`, `deriv h 0≠0`) with `F z−F 0 = h(z)²` near `0`.
The disconnected critical point is the standard saddle: `{G_c=G_c(0)}=h⁻¹{Re w²=0}` (figure-eight),
`{G_c<G_c(0)}=h⁻¹{Re w²<0}` (two lobes). Local model in Lean: COMPLETE.
NEXT (the genuinely Mathlib-absent topology): turn `{Re w²<0}` = two sectors into "the sublevel set near
`0` has ≥2 connected components" (via `h` homeomorphism), pick a loop around one lobe, then the
multivalued basin monodromy `2πi/2ⁿ` → not-a-square → Kummer → `hDisc`. Connected case: E–vS.

## LiftPeriod.lean — fractional dyadic period from a lift (2026-06-25)

`FigureEightCapstone.lean` (figure-eight + two-lobe split at the real `G_c`) and `LiftPeriod.lean`
land the analytic core of the dyadic monodromy multiplier, all axiom-clean
(`[propext, Classical.choice, Quot.sound]`), wired into the `Bottcher.lean` aggregator:

- `circleIntegral_logDeriv_bottcher` — `∮_{C(0,R)} logDeriv φ_c = 2πi` for the genuine `logDeriv φ_c`
  (base period / winding 1), via `logDeriv_bottcherCoord_escape` + `circleIntegral_dlog_bottcher`.
- `fractional_period_of_lift` — if `γ` lifts the base circle through `f_c^[n]`
  (`f_c^[n]∘γ = C(0,R)` with velocity match) then `∮_γ d log φ_c = 2πi/2ⁿ`. The order-`2ⁿ`
  multiplier exponent for the actual `φ_c`, NO equilibrium measure (functional-equation route via
  `pathInt_iterate_comp`).
- `hasDerivAt_quadratic_iterate` — `HasDerivAt (f_c^[n]) (∏_{k<n} 2·f_c^[k] x) x` (iterate chain rule).
- `hvel_of_diff_lift` — the velocity-match hypothesis of `fractional_period_of_lift` is automatic
  from a *differentiable* lift (chain rule + deriv uniqueness).

NET: the winding crux (#73) is reduced to one isolated statement — **a differentiable lift of the
base circle through `f_c^[n]` exists** (a path whose `f_c^[n]`-image traces `C(0,R)` once; its
endpoints differ by the deck map, giving the primitive-`2ⁿ`-root multiplier). The period VALUE
`2πi/2ⁿ` is now proven outright. Next: construct that lift (single-branch continuation of the circle
through the `2ⁿ`-fold cover; the figure-eight two-lobe split provides the separated component the
loop encircles), then feed `not_square_of_period_ftc` → Kummer `inputs` tuple → discharge `hDisc`.

## LiftConstruction.lean — the two geometric gates for path-lifting the circle (2026-06-25)

The lift `γ` for `LiftPeriod.fractional_period_of_lift` is to be built by lifting `C(0,R)` through
the EXISTING covering `isCoveringMapOn_quadratic_iterate` / `isCoveringMap_quadratic_iterate_restrict`
(CoverConstruction.lean) — NOT via a global Böttcher inverse (so #75/#76 univalence is bypassed).
The two missing geometric inputs are now proven, axiom-clean, wired into `Bottcher.lean`:

- `exists_sphere_subset_noncritical` — for `R` large, `C(0,R) ⊆ (criticalValues)ᶜ` (finite critical
  values are bounded), so the base loop lies in the covering base and is liftable.
- `exists_sphere_preimage_subset_escapeOpen` — for `R` large, every preimage of `C(0,R)` under
  `f_c^[n]` is in `escapeOpen c` (forward bound `escapeBound`, `‖z²+c‖≤‖z‖²+‖c‖` iterated), so the
  lift lands where `logDeriv φ_c` is the single-valued form `fractional_period_of_lift` integrates.
  Supporting: `escapeBound`, `escapeBound_succ/_nonneg`, `norm_iterate_le_escapeBound`.

Mathlib path-lifting API confirmed available:
  `IsCoveringMap.exists_path_lifts : IsCoveringMap p → ∀ (γ : C(I,X)) (e), γ 0 = p e → ∃ Γ : C(I,E), p∘Γ = γ ∧ Γ 0 = e`
  `IsCoveringMap.liftPath`, `IsCoveringMap.isLocalHomeomorph`, `IsCoveringMap.monodromy`.

NEXT BRICK (the remaining open input of #73): upgrade the topological lift to the analytic one that
`fractional_period_of_lift` needs —
  (1) feed `circleMap 0 R` (as `C(I,ℂ)` after reparametrizing `unitInterval ↔ [0,2π]`) and a base
      escapeOpen preimage `e` into `exists_path_lifts` on `isCoveringMap_quadratic_iterate_restrict`;
  (2) DIFFERENTIABILITY of the lift: it is locally `chart.symm ∘ circleMap` with `chart` an analytic
      `OpenPartialHomeomorph` (`exists_openPartialHomeomorph_of_hasStrictDerivAt`), so `HasDerivAt`
      follows; `hvel_of_diff_lift` then discharges the velocity hypothesis automatically;
  (3) endpoint = deck image: `Γ 1` and `Γ 0` lie in the same fibre (both over `circleMap`'s closed
      basepoint), differing by the order-`2ⁿ` deck rotation → the primitive-`2ⁿ`-root multiplier.
Then: `not_square_of_period_ftc` (period `2πi/2ⁿ ∉ 4πiℤ`) → Kummer `inputs` tuple → `hDisc`.

## LiftConstruction.lean — differentiability of the lift (the crux), 2026-06-25

Added (all axiom-clean, wired):
- `prod_two_mul_iterate_ne_zero_of_escapeOpen` — escape points are non-critical for `f_c^[n]`.
- `exists_analytic_local_section` — analytic local right-inverse `ψ` of `f_c^[n]` at a non-critical
  point (inverse function theorem, `HasStrictDerivAt.localInverse`/`.to_localInverse`).
- `hasDerivAt_lift_of_continuousAt` — **THE differentiability crux**: a *continuous* lift `Γ` through
  `f_c^[n]` (local biholo, `d ≠ 0`) with differentiable base path `g = f_c^[n]∘Γ` is itself
  differentiable, `Γ' = d⁻¹·g'`. Forces `Γ = ψ∘g` near each point and inherits the derivative.

This upgrades the topological lift to the differentiable one with NO global Böttcher inverse needed.

REMAINING ASSEMBLY (mechanical, the last hDisc-analytic brick): combine on `R` large (both gates):
  - `IsCoveringMap.exists_path_lifts` on `isCoveringMap_quadratic_iterate_restrict` with base path
    = `circleMap 0 R` (reparametrize `unitInterval ↔ [0,2π]`) and basepoint a chosen escapeOpen
    preimage → continuous `Γ : C(I, subtype)`, `f_c^[n]∘Γ = circle`, `Γ 0 = e₀`;
  - project to `γ : ℝ → ℂ`, in `escapeOpen` by `exists_sphere_preimage_subset_escapeOpen`;
  - `hasDerivAt_lift_of_continuousAt` per θ ⟹ differentiable; `hvel_of_diff_lift` ⟹ velocity match;
  - `fractional_period_of_lift` ⟹ `∮_γ d log φ_{c₁} = 2πi/2ⁿ`;
  - endpoint `γ(2π)` vs `γ(0)`: same fibre, deck-rotated ⟹ multiplier `exp(2πi/2ⁿ)` (primitive 2ⁿ root)
    via `exp_logDeriv_antiderivative` → non-squareness of `a=φ_{c₁}∘f^[k]` → Kummer `inputs`
    (`q62_disconnected_kummer`) → `hDisc`.
The self-map route (`hDisc_tuple_of_lifts`) is the confirmed DEAD-END (g must fix ℂ(z) ⟹ g=id);
the Kummer route above is the live one.

## LiftConstruction.lean — basepoint + surjectivity (2026-06-25, cont.)

Added (axiom-clean): `exists_iterate_eq` (f_c^[n] surjective, FTA on the degree-2ⁿ iterate poly) and
`exists_escapeOpen_preimage_basepoint` (an escapeOpen preimage of the loop basepoint (R:ℂ) — the
`Γ 0 = e₀` datum). LiftConstruction.lean now holds the COMPLETE brick set for the lift assembly:
gates (×2), local section, differentiability-crux, surjectivity, basepoint.

ENDPOINT FIX for the final glue: lift a slightly-LONGER arc `circleMap 0 R` over `[−ε, 2π+ε]`
(reparametrized to `unitInterval`) instead of exactly `[0,2π]`, so the differentiable lift `γ` is
analytic on an OPEN nbhd of `[0,2π]` — then `hasDerivAt_lift_of_continuousAt` applies at the endpoints
too and `hvel` holds on the closed `uIcc` that `fractional_period_of_lift` needs. Remaining glue:
`IsCoveringMap.exists_path_lifts` (subtype `(criticalValues)ᶜ`) + this reparam + projection.

## LiftExists.lean — WINDING CRUX CLOSED (2026-06-25)

`exists_continuous_circle_lift` + `exists_circle_lift_period` (both axiom-clean, wired):
- the continuous lift of `C(0,R)` through `f_c^[n]` exists, built via `IsCoveringMap.exists_path_lifts`
  on `isCoveringMap_quadratic_iterate_restrict` (subtype `(criticalValues)ᶜ` + `unitInterval↔arc`
  reparam over `(-1, 2π+1)`), `R` past both gates;
- `exists_circle_lift_period` : **∃ R γ γ', ∮_γ d log φ_c = 2πi/2ⁿ, UNCONDITIONALLY**. The continuous
  lift → `hasDerivAt_lift_of_continuousAt` (differentiable) → `hvel_of_diff_lift` (velocity) →
  `fractional_period_of_lift` (value). The realized fractional dyadic period — the analytic heart of
  the disconnected monodromy — is now a theorem with NO hypotheses.

REMAINING for hDisc (algebraic, no analytic gap left): feed the period `2πi/2ⁿ` into
`no_singlevalued_branch_of_dyadic_period` ⟹ no single-valued 2-root branch ⟹ non-squareness of
`a = φ_{c₁}∘f^[k]` in `meroField(Ext)` ⟹ `Irreducible (X^{2^k} - C a)` (Capelli,
`X_sq_sub_C_irreducible_of_not_square`) ⟹ the Kummer `inputs` tuple ⟹ `q62_disconnected_kummer`
⟹ `hDisc` ⟹ instantiate `q62_independence` (disconnected/disconnected).

## hDisc — the meroField/Kummer bridge: DESIGN (the remaining algebraic work, 2026-06-25)

Analytic side is DONE & axiom-clean (LiftExists): `exists_circle_lift_period` (period 2πi/2ⁿ),
`multiplier_eq_exp_of_period` (→ multiplier exp(2πi/2ⁿ)), `isPrimitiveRoot_dyadic_multiplier` (ζ),
`bottcherCoord_iterate_escape` (radical relation `F^{2ᵏ} = bottcherCoord∘f^[k]`).

The live close is `q62_disconnected_kummer` ⊳ `noRelation_of_kummer_inputs` (KummerDeck:151), needing per
`d` a tuple `(B, Field B, Algebra ℂ(z) B, i : B →ₐ V, a GB ζ : B, k)` with `d<2ᵏ`,
`IsPrimitiveRoot ζ (2ᵏ)`, `Irreducible(X^{2ᵏ}−C a)`, `F^{2ᵏ} = i a`, `i GB = G`. Status of each piece:
  - `k := d+1`, `d < 2ᵏ` — trivial.
  - `ζ` — `exp(2πi/2ᵏ)`, primitive via `isPrimitiveRoot_dyadic_multiplier` (DONE). Lives in ℂ ⊆ B.
  - `F^{2ᵏ} = i a` — radical relation `bottcherCoord_iterate_escape` (DONE), with `a` = germ of
    `bottcherCoord∘f^[k]` in B and `F = bottcherCoord` germ in V.
  - `i GB = G` — `G = φ_{c₂}` germ; `GB` its pullback. Mechanical (`restrictMeroHom`).
  - `Transcendental` — `transcendental_of_kummer_inputs` (KummerDeck:259).
  - **THE ONE GAP**: `Irreducible(X^{2ᵏ}−C a)` ⟸ `a` not a square in `B` (Capelli p=2,
    `X_sq_sub_C_irreducible_of_not_square`, `−1=i²` in ℂ). And `a` not a square in `B = meroField(Ext)`
    ⟺ the root `bottcherCoord∘f^[k-1] = F^{2^{k-1}}` is NOT in the base `B` (only on the cover `V`) ⟺
    it has nontrivial monodromy around the loop in `Ext` — which is EXACTLY the realized fractional
    period `2πi/2ⁿ` (`exists_circle_lift_period`, `multiplier_eq_exp_of_period`).

So the bridge = "fractional monodromy ⟹ root not in base ⟹ not a square". `B`/`i` = `meroField(Ext)`/
`restrictMeroHom`; constructing `Ext` (the base domain the loop lives in) + the "monodromy ⟹ not a
pullback" lemma is the remaining `meroField`-API formalization. Self-map route (`hDisc_tuple_of_lifts`)
stays the DEAD-END (g fixes ℂ(z) ⟹ g=id); Kummer is live.

### NON-CIRCULARITY (critical, 2026-06-25): non-squareness MUST be monodromy, not transcendence
Tempting shortcut: `a = F^{2ᵏ}` is transcendental over `K=ℂ(z)` (F hypertranscendental), so in the
rational function field `K(a)`, `a = t` is not a square. CLEAN — but WRONG here, because the Kummer
input `i GB = G = φ_{c₂}` forces `B ⊇ K(φ_{c₂})`, so the relevant base is `B = K(φ_{c₂}, a)`. Then
`a` not a square in `K(φ_{c₂})(t)` REQUIRES `t = φ_{c₁}^{2ᵏ}` transcendental over `K(φ_{c₂})` — i.e.
the very algebraic INDEPENDENCE of `φ_{c₁}, φ_{c₂}` we are proving. CIRCULAR.
⟹ The base `B = meroField(Ext)` must be built from the cover GEOMETRY (functions on the base domain
of the f^[k]-cover), NOT from `φ_{c₁}`; and `a` not a square in it must come from the root
`F^{2^{k-1}}` having nontrivial MONODROMY around the loop in `Ext` (`exists_circle_lift_period`'s
`2πi/2ⁿ`), keeping it out of the base. This is the non-circular close; the period work feeds it.
Remaining write: the cover base domain `Ext` + the "fractional-monodromy ⟹ not a restrictMeroHom
pullback ⟹ not a square" meroField lemma.

## hDisc — CONCRETE carrier resolving the g=id obstruction (2026-06-25)

The dead-end "deck σ over ℂ(z) ⟹ g=id" assumed σ is a self-map of ONE planar domain (where z fixes the
point ⟹ g=id). RESOLUTION: σ is the deck of the COVERING `E := f_c^[n]⁻¹(X) → X` (E, X ⊆ ℂ both planar,
`isCoveringMap_quadratic_iterate_restrict`). Carrier:
  - V = meroField(E), F = bottcherCoord germ on E (single-valued on E — descends to multivalued on X);
  - B = meroField(X), i = pullback by `f_c^[n]` (restrictMeroHom-style precomposition);
  - g : E → E = the covering deck self-map (monodromy of the base loop, permuting the 2ⁿ sheets,
    `f_c^[n]∘g = f_c^[n]`, g ≠ id — sheets share the same X-point);
  - σ = precompose-by-g `meroField` automorphism. σ fixes i(B) (pullbacks from X). KEY: σ fixes
    `i(ℂ(z)) = ℂ(f_c^[n])` — NOT the E-coordinate — so g≠id is consistent (no dead-end).
  - σ F = F∘g = ζ·F, ζ = exp(2πi/2ⁿ) the multiplier (`multiplier_eq_exp_of_period`, period from
    `exists_circle_lift_period`). `bottcherCoord(g z)/bottcherCoord(z)` = the monodromy ratio.
Then `fixed_not_sqrt_of_scaling σ … ` ⟹ `a = F^{2ᵏ}` not a square in B ⟹ `Irreducible(X^{2ᵏ}−C a)`
⟹ Kummer `inputs` ⟹ `q62_disconnected_kummer` ⟹ hDisc. PLANAR, non-circular, uses built pieces.

REMAINING WRITE (multi-brick, concrete): (1) the deck self-map `g` of E from the regular 2ⁿ-cover
(Mathlib `IsCoveringMap.monodromy` gives the fibre action; lift to a deck homeomorphism of the regular
cover); (2) `meroField(E)`/`meroField(X)` + pullback hom `i`; (3) `σ F = ζ F` from the multiplier;
(4) assemble the Kummer `inputs` tuple. Every analytic input is DONE & axiom-clean.

### SIMPLIFICATION (2026-06-25): base period suffices for non-squareness
`a = bottcherCoord|_X` not a square in `meroField(X)` needs only the BASE period `2πi`
(`circleIntegral_logDeriv_bottcher`, DONE), not the fractional one: `√a = exp(½ bottcherLog)` has
sign-monodromy `exp(½·2πi)=−1` around the loop in `X=(criticalValues)ᶜ` ⟹ no single-valued germ ⟹
not a square. And "a not a square" ⟹ "not a 2ʲ-power" ⟹ `Irreducible(X^{2ᵏ}−C a)` for ALL k (Capelli,
−1 a square). So ONE non-squareness fact (base-period sign monodromy of √bottcherCoord) closes every
`d` in the Kummer inputs. The fractional-period/lift machinery (axiom-clean) gives the deck multiplier
and is the natural route for the OTHER coordinate's transcendence, but non-squareness is cheaper.
REMAINING hDisc write = the meroField(X) germ lemma "sign-monodromy ⟹ no square-root germ ⟹ not a
square", then assemble Kummer inputs. Pure meroField-germ API work; all analytic facts are theorems.
