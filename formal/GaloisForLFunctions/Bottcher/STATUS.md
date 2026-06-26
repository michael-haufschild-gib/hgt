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

## SquareFree.lean — non-squareness germ lemma DONE (axiom-clean)

The "REMAINING hDisc write" above is now formalized in `SquareFree.lean` (all `#print axioms` =
`[propext, Classical.choice, Quot.sound]`, zero sorry):

- `analyticOnNhd_zeros_countable` / `exists_radius_avoiding_zeros` (in `ZeroSet.lean`) — a nonzero
  analytic function on a connected open set has countable zeros, so a deep circle dodging them exists.
- `isConnected_escapeOpen` — the exterior carrier is connected and NOT simply connected (image of
  `(r,∞)×𝕊¹`); the topological source of the sign-monodromy.
- `no_analytic_sqrt_bottcher_circle` — circle-local form of `no_analytic_sqrt_bottcher'`: `h` analytic
  with `h²=φ_c` on any open nbhd of a deep circle ⟹ False (so the meromorphic ratio `fp/fq` works).
- `bottcherGerm_not_isSquare` — THE germ lemma: clear denominators on `b=p/q`, dodge the countable
  zeros of `fp·fq`, then `fp/fq` is an analytic √φ_c near that circle — impossible. So the Böttcher
  germ is not a square in `meroField(escapeOpen c)`: `∀ b, b² ≠ algebraMap(φ_c germ)`.
- `bottcher_X_pow_sub_C_irreducible` — `kummer_irreducible` ∘ the above: `X^{2ᵏ} − C φ_c` irreducible
  over `meroField` for every `k ≥ 1` (the `Irreducible` clause of the Kummer `inputs` tuple).

REMAINING for hDisc (Kummer route, `q62_disconnected_kummer`): the base-map `i : B →ₐ[ℂ(z)] meroField U`
with `φ_{c₁}^{2ᵏ} = i a` (radical relation = `bottcherCoord_iterate`: `φ_c∘f^[k]=φ_c^{2ᵏ}`) and
`i GB = φ_{c₂}`. Obstruction located: `precomp-by-f^[k]` realizes `i a = φ_c∘f^[k]` but does NOT fix
`ℂ(z)` on a planar domain (`z∘f^[k] = f^[k](z) ≠ z`), so the base must embed via an `f^[k]`-invariant
projection `p₀` (`polyToAnalyticVia`) = the covering projection of the dyadic cover. That projection-base
construction is the next concrete design task; the non-squareness/irreducibility it consumes are now
theorems. hRigid (both-connected E–vS) is the other agent's lane.

### Abstraction + the precise hDisc blocker (verified)

`no_analytic_sqrt_of_odd_period` (axiom-clean): any analytic `g` non-vanishing near a circle with
`∮ d log g = 2πi` has no analytic square root near it. `no_analytic_sqrt_bottcher_circle` is the
`g = bottcherCoord c` corollary. This is the interface the Kummer radicand non-squareness needs ON THE
COVER (call with `g = φ_{c₁}∘f^[k]`, which has odd period `2πi` there since `φ_{c₁}` has fractional
period `2πi/2ᵏ` — `LiftExists.exists_circle_lift_period`).

PRECISE BLOCKER for an UNCONDITIONAL hDisc, traced this session: the Kummer `inputs` tuple needs a base
map `i : B →ₐ[ℂ(z)] V` with `φ_{c₁}^{2ᵏ} = i a`. The only `i` realizing `i a = φ_{c₁}^{2ᵏ}` with a
NON-square `a` is `precomp-by-f^[k]` (then `a = φ_{c₁}`, irreducibility = `bottcher_X_pow_sub_C_irreducible`
✓). But `precomp-by-f^[k]` fixes `ℂ(z)` only if `ℂ(z)` embeds via an `f`-invariant coordinate `p₀`
(`p₀∘f = p₀`), and on a PLANAR exterior the only such analytic `p₀` are constants. So an unconditional
hDisc requires the **open dyadic cover domain** `Ext` (where `φ_{c₁}^{1/2ᵏ}` is single-valued and the
covering projection is the `f`-invariant base) — `LiftExists` has this at the CIRCLE level only.
Constructing `Ext` as an open set + `meroField(Ext)` + the analytic lift is the remaining geometric
build for hDisc; the non-squareness/irreducibility/odd-period interface it consumes are now theorems.

### ProductCover.lean — the field-AND-deck carrier foundation (verified, axiom-clean)

The hDisc blocker (planar `meroField` cannot carry a deck scaling `φ_{c₁}`; `coverGerm` carries the
deck `deckMap₁` but is `ℂ^S`, never a domain) is resolved by `meroField` over a CONNECTED piece of the
PRODUCT cover `commonPullback ⊆ ℂ³`. Keystone (axiom-clean) — Mathlib's identity theorem
`AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq` holds over an ARBITRARY normed space, so:

- `analyticOnNhd_domain_gen` — analytic functions on a connected open `U ⊆ E` (any `E`) with `f·g≡0`
  force `f≡0 ∨ g≡0` (one-variable proof verbatim; only the codomain `ℂ` being a field is used).
- `analyticSubringGen U` / `isDomain_analyticSubringGen` / `meroFieldGen U` — the several-variable
  analytic-germ subring, its IntegralDomain property, and its fraction FIELD, for `U ⊆ E`.

For `E = ℂ³`, `U` a connected piece of `commonPullback`, `meroFieldGen U` is a FIELD on which
`deckMap₁ ζ : (z,v₁,v₂)↦(z,ζv₁,v₂)` (a self-biholomorphism of `commonPullback`,
`BasinBranching.deckMap₁_mapsTo`) precomposes to a field automorphism scaling `φ_{c₁}=v₁` by `ζ`, fixing
`z=ℂ(z)` and `φ_{c₂}=v₂`. REMAINING for hDisc: generalize `precompAnalytic`/`precompMeroEquiv` to `E`
(the `MeromorphicField` deck machinery is `E`-agnostic — same near-verbatim lift), instantiate on
`commonPullback`+`deckMap₁`+`exists_deck_unbounded`, yielding the unbounded-order `mono` of
`q62_disconnected_both`. The carrier obstruction is now removed; what remains is the (mechanical)
`E`-generalization of the deck-precomposition lemmas + the `commonPullback` connectedness.

### ProductCover.lean — deck machinery over `E` DONE (axiom-clean)

The `MeromorphicField` deck lemmas, generalized verbatim to any normed `ℂ`-space `E` (all axiom-clean):
`precomp_mem_analyticSubringGen`, `precompGermHomGen`, `precompAnalyticGen`(+`_coe`),
`precompAnalyticEquivGen`(+`_apply_of_invariant`, `_apply_of_scale`), `precompMeroEquivGen`(+`_algebraMap`).
So for `E = ℂ³`, `U` a connected piece of `commonPullback`, and `g = deckMap₁ ζ`,
`precompMeroEquivGen` IS a field automorphism of `meroFieldGen U` that (by `…_apply_of_scale`/`_invariant`)
scales `v₁=φ_{c₁}` by `ζ` and fixes `v₂=φ_{c₂}` and the `z`-coordinate (=`ℂ(z)`). The carrier+deck — the
conceptual heart of hDisc — is now built and verified.

REMAINING for hDisc (mechanical assembly, no conceptual gap left):
1. `AnalyticOnNhd ℂ (deckMap₁ ζ) U` (deckMap₁ is linear ⟹ analytic) + its self-map/inverse (have
   `deckMap₁_mapsTo`, `deckMap₁_leftInverse` in BasinBranching).
2. coordinate germ facts `v₁∘deckMap₁ = ζ·v₁`, `v₂∘deckMap₁ = v₂` (from `deckMap₁_snd/_fst`).
3. connectedness of the chosen piece of `commonPullback`.
4. `ℂ(z)`-algebra structure on `meroFieldGen` via the `z`-coordinate germ; `σ` fixes it.
5. assemble `monoF`/`monoG` (`exists_deck_unbounded` for unbounded order) → `q62_disconnected_both`
   → hDisc. hRigid (both-connected E–vS) is the other agent's lane.

### SELF-CORRECTION (hard verification gate, do not skip): my hDisc bricks are NOT all load-bearing

Under scrutiny of whether the SquareFree/ProductCover work actually discharges hDisc, two of my claims FAIL:

1. **Deck-on-cover route (ProductCover meroFieldGen + deckMap₁) does NOT transfer.** `deckMap₁` fixes
   `z`, so for the pulled-back genuine coordinate `φ_{c₁}∘p` (p = projection to z), `deckMap₁` FIXES it
   (`p∘deckMap₁=p`); it scales only the independent cover coordinate `v₁`. A relation
   `P(φ_{c₁},φ_{c₂})=0` pulls back to a relation in σ-FIXED elements, so the deck gives no monodromy on
   it. The cover-field NoRelation is about the (trivially independent) coordinate projections — vacuous
   for the genuine φ. `meroFieldGen`/deck are clean, verified, but NOT the hDisc carrier.

2. **`bottcher_X_pow_sub_C_irreducible` is the WRONG instance.** The Kummer radicand is `a = φ_{c₁}^{2ᵏ}
   = φ_{c₁}∘f^[k]` in a base `B ⊊ V`, and the needed fact is `X^{2ᵏ}−C a` irreducible over `B`
   (≙ `φ_{c₁}^{2ᵏ}` non-square in `B`). My theorem is `X^{2ᵏ}−C φ_{c₁}` over `V=meroField(U)` — a
   different element over a different field. The "power-implies" shortcut (prove for the root
   `φ_{c₁}^{1/2ᵏ}`, deduce for `φ_{c₁}`) fails: converting a `φ_{c₁}`-relation to a root-relation raises
   the degree by `2ᵏ`, always outpacing the order-`2ᵏ` monodromy.

GENUINELY LOAD-BEARING, verified: `no_analytic_sqrt_of_odd_period` (the abstract tool — correct shape),
`analyticOnNhd_zeros_countable`/`exists_radius_avoiding_zeros`, `isConnected_setOf_lt_norm`,
`analyticOnNhd_domain_gen` + several-var carrier (reusable infra). The TRUE open hDisc crux:
`φ_{c₁}∘f^[k]` not a square in `B = ℂ(z)⟨φ_{c₁}^{2ᵏ}, φ_{c₂}⟩ ⊊ V`, NON-circularly — provable via odd
period `2πi` of `φ_{c₁}∘f^[k]` on the dyadic cover `Ext` (where `φ_{c₁}` has fractional period
`2πi/2ᵏ`), feeding `no_analytic_sqrt_of_odd_period`, with `B = meroField(Ext)`, `i = restrictMeroHom`.
The cover `Ext` (a connected 1-D dyadic cover) + its odd-period lift remain UNBUILT — this is the real
remaining hDisc construction. hRigid (both-connected E–vS) is the other agent's lane.

### NO-GO (decisive, redirects hDisc): root-cover monodromy cannot prove φ_{c₁}-relations

A clean impossibility, proven by degree-counting (not yet a Lean lemma — it is a statement ABOUT the
method): the available monodromy in the project — the root cover, period `2πi/2ⁿ`
(`exists_circle_lift_period`), the deck scaling `root = φ_{c₁}^{1/2ⁿ}` — can NEVER discharge
`eq_zero_of_monodromy` for `F = φ_{c₁}`.

Reason: any deck that scales `root` by a primitive `2ⁿ`-th root `ζ` FIXES `φ_{c₁} = root^{2ⁿ}`
(`ζ^{2ⁿ}=1`). The "power-implies" rescue (prove `NoRelation(root, φ_{c₂})`, deduce `NoRelation(φ_{c₁},
φ_{c₂})`) fails identically: pulling a degree-`D` relation `P(φ_{c₁},φ_{c₂})` back to the root gives
`Q(W,Y)=P(W^{2ⁿ},Y)`, whose `W`-powers are all multiples of `2ⁿ`, hence all fixed by the order-`2ⁿ`
deck — so `Q(root,φ_{c₂})` is deck-invariant and `eq_zero_of_monodromy` (needs `deg_W < orderOf ζ`)
never applies (`deg_W Q = 2ⁿ·D ≥ 2ⁿ`). And the Kummer realization with `σ φ_{c₁}=ζφ_{c₁}` is circular
(non-squareness of `φ_{c₁}^{2ᵏ}` in `B⊊V` ≙ `φ_{c₁}^{2ᵏ⁻¹}∉B` ≙ a form of the independence).

CONSEQUENCE: `q62_disconnected`'s `mono` (σ scaling φ_{c₁} directly) is realizable ONLY by the genuine
multivaluedness of `φ_{c₁}` for DISCONNECTED `c₁` — its Böttcher monodromy around the **Cantor Julia
set**, below the critical Green level `G_{c₁}(0)` (NOT around `∞`, where `escapeOpen` sits and `φ_{c₁}`
is single-valued, NOT the root cover). This is the genuine, unbuilt analytic content of hDisc; the
project's `FigureEight`/`BasinBranching` figure-eight machinery is the right direction. Any further
work on the root-cover/fractional-period route for hDisc is a dead end (this no-go).

### Sharpest characterization of the hDisc difficulty (the fix-z / scale-φ tension)

`eq_zero_of_monodromy` needs ONE `σ` that simultaneously (i) fixes `ℂ(z)` and (ii) scales `φ_{c₁}`.
Every realization satisfies only one:
- `deckMap₁` (product cover `ℂ³`): FIXES `z`, scales the independent coordinate `v₁` — but the descent
  to the genuine section fixes `φ_{c₁}∘p` (deck-invariant), so it scales the wrong thing.
- the disconnected lobe-swap monodromy (planar): genuinely scales `φ_{c₁}` (multivalued for
  disconnected `c₁`), but `f_{c₁}∘g = g`-fiber-preserving ⇒ it fixes only `ℂ(f^[n](z)) ⊊ ℂ(z)`, moving
  `z` itself.
Because `φ_{c₁} ~ z` at `∞`, "fix `z` and scale `φ_{c₁}`" is genuinely obstructed; the only escape is a
construction where `φ_{c₁}`'s monodromy is decoupled from `z` — the Cantor-set monodromy below
`G_{c₁}(0)` realized so that `σ` fixes the FULL `ℂ(z)`. Whether that realization over `ℂ(z)` (not just
`ℂ(f^[n](z))`) goes through is the genuine open mathematical question of the disconnected case — not a
mechanical assembly. This is the precise frontier; recorded so the next attempt starts here.

### Natural-boundary route: analytic side is feasible (Mathlib enablement found)

The cleaner route to hDisc (and to the `Transcendental K φ_{c₂}` input every case needs) is
natural-boundary: an algebraic function over `ℂ(z)` extends analytically across every point except a
finite branch/pole set, so its singular set is finite; but `φ_c`'s singular set is its Julia set `J_c`
(infinite, perfect) ⇒ `φ_c` transcendental; and `φ_{c₁}` algebraic over `ℂ(z)(φ_{c₂})` would force
`J_{c₁} ⊆ J_{c₂} ∪ finite`, contradicting `J_{c₁} ≠ J_{c₂}`. This SIDESTEPS the four monodromy no-gos
(no deck automorphism needed).

ANALYTIC SIDE (mine, feasible — Mathlib pieces identified):
- "simple root ⇒ local analytic branch": `ContDiffAt.implicitFunction` (curried/uncurried bivariate
  IFT, `Mathlib/Analysis/Calculus/ImplicitFunction/Bivariate.lean` + `ImplicitContDiff.lean`) gives a
  `ContDiffAt` implicit `g` with `f(x,g x)=f(z₀,w₀)` near `z₀`; then
  `Complex.analyticAt_iff_eventually_differentiableAt` upgrades `ContDiffAt ℂ ⊤ ⇒ AnalyticAt` (C¹ ⇒
  holomorphic ⇒ analytic in ℂ). Friction: build `if₂ : (fderiv ℂ F u ∘L inr).IsInvertible` from
  `∂_w P (z₀,w₀) ≠ 0` (simple root), and assemble "finite branch set = discriminant∪leading-coeff
  zeros". Substantial but no research gap.
BOUNDARY SIDE (the other agent's active files: `DendriteBoundary`, `GreenContinuity`, `PhiLevel`,
`GreenChain`, `GreenUnique`): `φ_c` does not continue across `J_c`; `J_c` infinite; `J_{c₁}≠J_{c₂}`.

This is the recommended path; the monodromy route is closed by the four no-gos above.

### AlgebraicBranch.lean — analytic keystone of the natural-boundary route BUILT (axiom-clean)

First brick of the natural-boundary route is now verified (pure complex analysis, no dynamics; all
`#print axioms` = the 3 standard axioms, zero sorry):
- `exists_analyticAt_branch` — a SIMPLE ROOT of an analytic relation `f(z,w)=0` (i.e. `(fderiv f ∘L
  inr).IsInvertible`) is a LOCAL ANALYTIC BRANCH `g` with `g z₀=w₀`, `f(z,g z)=0` near `z₀`. Via
  `ContDiffAt.implicitFunction` (analytic IFT) + `ContDiffAt.analyticAt` (C^ω ⇒ analytic in ℂ).
- `isInvertible_partial_of_hasDerivAt` — non-zero `w`-partial derivative `d≠0` ⇒ the IFT invertibility
  hypothesis (partial fderiv `= smulRight 1 d = d•1`, invertible via `Units.mk0 d hd • refl`).
- `exists_analyticAt_branch_of_hasDerivAt` — combined, directly-applicable form.

This is the "algebraic functions continue across non-branch points" core: away from the finite set
{discriminant=0}∪{leading coeff pole}, an algebraic function over `ℂ(z)` is locally analytic.
NEXT (mine): assemble "algebraic over ℂ(z) ⇒ singular set finite" from this keystone (minimal poly →
discriminant finite → branch via keystone elsewhere). THEN combine with the BOUNDARY side (other agent's
`DendriteBoundary`/`GreenContinuity`: `φ_c` non-continuable across the infinite `J_c`) for transcendence,
and with `J_{c₁}≠J_{c₂}` for independence. The route is now under active construction, brick-by-brick.

### ★ STRATEGIC CAPSTONE: the monodromy no-gos are MOOT — clean route is transcendence-only

`Rigidity.noRelation_of_transcendence` (other agent's, PROVEN, axiom-clean) gives
`NoRelation K F G` from JUST `Transcendental K G` ∧ `TranscendentalOverAdjoin F G` — **no deck
automorphism, no monodromy tower**. Therefore the four monodromy no-gos do NOT block q62: the whole
theorem (all Mandelbrot cases, disconnected included) reduces to TWO analytic inputs per pair:
  (A) `Transcendental ℂ(z) (φ_c)`           (B) `TranscendentalOverAdjoin (φ_{c₁}) (φ_{c₂})`
i.e. `φ_c` not algebraic over `ℂ(z)`, and `φ_{c₁}` not algebraic over `ℂ(z)[φ_{c₂}]`. Both are
NATURAL-BOUNDARY facts, and BOTH agents' work converges exactly here:
  • BOUNDARY side (other agent, BUILT): `DendriteBoundary.no_green_modulus_continuation` /
    `no_continuation_dendrite` — no modulus-preserving analytic continuation of `φ_c` across a
    Julia point (empty-interior/dendrite); `GreenContinuity` supplies `G_c` continuity + boundary limit.
  • ALGEBRAIC side (mine, keystone BUILT): `AlgebraicBranch.exists_analyticAt_branch` — algebraic ⟹
    local analytic continuation across non-branch points.
THE MISSING BRIDGE (the precise remaining work, ~3 bricks): 
  1. branch-locus finiteness: algebraic over `ℂ(z)` ⟹ continues across COFINITELY many points
     (`AlgebraicBranch` + `Separable = IsCoprime` Bézout, clear denominators to `δ∈ℂ[z]`, finite zeros).
  2. basin-wide modulus identity `‖φ_c z‖ = exp(greenFunctionDyn c z)` for `z∉filledJulia` (extend
     `norm_bottcher_eq_exp_greenLimit` off `escapeOpen` via the functional-equation chain — exists on
     `escapeOpen`/`greenLogNorm_eq_greenLimit_escape`; needs the iterate extension).
  3. assemble: algebraic ⟹ continuation at a dendrite Julia point (1+2 give the modulus-preserving
     continuation) ⟹ `False` by `no_green_modulus_continuation` ⟹ (A); same over `ℂ(z)[φ_{c₂}]` with
     `J_{c₁}≠J_{c₂}` ⟹ (B). Then `noRelation_of_transcendence` ⟹ unconditional `NoRelation`, and the
     `hDisc`/monodromy slot of `q62_independence` is bypassed entirely (or fed trivially).
This is the route to the COMPLETE proof; it does not need the obstructed monodromy at all.

### ★★ COMPLETE BLUEPRINT for unconditional q62 (every tool identified, no research gap left)

`Separable.aeval_derivative_ne_zero` (Mathlib, `FieldTheory/Separable.lean:149`) REPLACES the fiddly
resultant/RatFunc-denominator brick (1): a root of a separable polynomial is automatically SIMPLE. So
the transcendence chain is now pure assembly of identified lemmas:

TRANSCENDENCE `Transcendental ℂ(z) φ_c` (and `TranscendentalOverAdjoin`, same shape over `ℂ(z)[φ_{c₂}]`):
  1. Suppose `φ_c` algebraic / not transcendental over `K=ℂ(z)`; let `P` = its minimal polynomial.
     `P` is separable (`Irreducible.separable`, char 0).
  2. `Separable.aeval_derivative_ne_zero` ⟹ `aeval φ_c (derivative P) ≠ 0` in the germ field — i.e.
     the analytic function `z ↦ (∂_Y P)(z, φ_c(z))` is `≢ 0` on the basin.
  3. `ZeroSet.analyticOnNhd_zeros_countable` (MINE) ⟹ its zeros are countable; likewise the leading
     coeff's. So COFINITELY many basin points have `φ_c` a SIMPLE root of `P(z,·)`.
  4. `AlgebraicBranch.exists_analyticAt_branch` (MINE) ⟹ across each such point `φ_c` continues
     analytically; pushing to a dendrite Julia point `z₀` (limit, modulus `→exp G_c`) yields a
     modulus-preserving continuation.
  5. `DendriteBoundary.no_green_modulus_continuation` (OTHER AGENT) ⟹ `False`. Hence transcendental.

INDEPENDENCE: `noRelation_of_transcendence` (OTHER AGENT) ∘ (transcendence + `TranscendentalOverAdjoin`)
  ⟹ unconditional `NoRelation ℂ(z) φ_{c₁} φ_{c₂}` for all `c₁≠c₂` nonexceptional. Monodromy/`hDisc`
  bypassed (the four no-gos are irrelevant).

Every ingredient is now a named, existing lemma (mine, the other agent's, or Mathlib). What remains is
FORMALIZATION LABOR of the step-3/4 boundary-limit assembly (connecting the germ-field `≠0` to pointwise
simple roots, and the basin-side limit at `z₀` giving the modulus identity) — no research-level gap.

### CONVERGENCE MAP (both lanes' endpoints now exist; the ONE remaining brick is the step-5 bridge)

Comprehensive tree survey — the unconditional q62 (clean transcendence-only route) now has BOTH ends built:
MY SPINE (steps 1–4, axiom-clean): `ZeroSet`, `AlgebraicBranch.exists_analyticAt_branch`,
  `GermZeros.exists_separable_witness` (algebraic ⟹ simple root) + `analyticGerm_ne_zero_zeros_countable`.
OTHER AGENT'S ENDPOINTS (built, in tree):
  • `DendriteBoundary.no_green_modulus_continuation` — no modulus-preserving continuation of `φ_c` across
    a Julia point (empty-interior); `density_basin_of_empty_interior` supplies the basin density.
  • `BottcherDetermines.c_eq_of_filledJulia_eq` — `c₁=c₂ ⟸ J_{c₁}=J_{c₂}`, i.e. `J_{c₁}≠J_{c₂}` for
    distinct params (the `TranscendentalOverAdjoin` separation input).
  • `GreenContinuity` (`G_c` continuity, boundary limit `→0`), `HarmonicMinPrinciple.harmonic_exterior_unique`.
  • `Rigidity.noRelation_of_transcendence` — `Transcendental ∧ TranscendentalOverAdjoin ⟹ NoRelation`.

THE ONE REMAINING BRICK (step-5 bridge, the central assembly neither agent has built):
  `transcendental_of_naturalBoundary`: if `g` (=`φ_c`) analytic on the basin with `‖g‖=exp(G_c)`, and
  `g` is ALGEBRAIC over `ℂ(z)`, then `g` is a branch of its (separable) minimal polynomial; at a simple-
  root Julia point `z₀` (cofinite ∩ infinite empty-interior `J_c` ⟹ exists), `AlgebraicBranch` continues
  `g` across `z₀` as a modulus-preserving continuation ⟹ `no_green_modulus_continuation` ⟹ `False`. Hence
  transcendental; same over `ℂ(z)[φ_{c₂}]` with `c_eq_of_filledJulia_eq` ⟹ `TranscendentalOverAdjoin`;
  then `noRelation_of_transcendence` ⟹ unconditional `NoRelation`.
  Sub-pieces of this ONE brick: (i) the meromorphic-value wiring (`aeval g (∂_Y q)` a fraction ⟹ its
  numerator's countable zeros, via `div_surjective`+`GermZeros`); (ii) `φ_c` has a limit at `z₀` under
  algebraicity (branch continuity); (iii) the cofinite-Julia-point existence; (iv) basin modulus
  `‖φ_c‖=exp(G_c)` off `escapeOpen`. All are formalization labor over now-existing endpoints — no
  research gap. This is the precise, final convergence brick for the COMPLETE unconditional q62.

### Natural-boundary ENGINE now complete for ALL c (dendrite + interior cases) + step-5 sub-pieces

Found a case split the dendrite lemma alone misses: the natural-boundary obstruction needs BOTH
- empty-interior `K_c` (dendrite): `DendriteBoundary.no_green_modulus_continuation` (other agent), and
- nonempty-interior `K_c`: `InteriorBoundary.no_unit_modulus_open_continuation` (MINE, built this turn,
  axiom-clean) — a continuation with `‖g‖=exp(G_c)=1` on the open interior of `K_c` is constant
  (`eventually_eq_of_isLocalMax_norm` + identity theorem), contradicting `g~φ_c` nonconstant.
So the obstruction now holds for EVERY nonexceptional `c`, not just dendrites.

Step-5 sub-piece (i) also built (`GermZeros.meroField_repr_countable`): nonzero `meroField` element =
`fp/fq` with countable-zero `fp,fq` — the meromorphic-value handle for `aeval(φ_c)(∂_Y q)`.

REMAINING for the step-5 transcendence bridge (the final assembly): connect the algebraic spine
(`exists_separable_witness` + `meroField_repr_countable` + `analyticGerm_ne_zero_zeros_countable` ⟹
cofinitely many simple-root points) to `AlgebraicBranch.exists_analyticAt_branch` (continuation at such
a point) to the boundary engines (dendrite OR interior) ⟹ `False` ⟹ transcendence; then over
`ℂ(z)[φ_{c₂}]` with `c_eq_of_filledJulia_eq` ⟹ `TranscendentalOverAdjoin`; then
`noRelation_of_transcendence` ⟹ unconditional `NoRelation`. The remaining glue is the `φ_c`-as-meroField
element setup + the limit/branch-matching at the Julia point + selecting the case — formalization labor
over now-COMPLETE endpoints on both sides.

### exists_analyticAt_branch_poly — concrete AlgebraicBranch for polynomial relations (axiom-clean)

Built (`AlgebraicBranch.lean`): a polynomial relation `Σ_i (P.coeff i)(z)·wⁱ = 0` with a SIMPLE root at
`(z₀,w₀)` (nonzero `w`-derivative) has a local analytic branch `g` (`g z₀=w₀`, relation holds with
`w=g z` near `z₀`). The bivariate `f(z,w)=Σ (P.coeff i).aeval z·wⁱ` is `ContDiff` (`contDiff_aeval` +
`ContDiff.sum`), then `exists_analyticAt_branch`. This is the EXACT continuation tool the natural-boundary
transcendence needs (`P` = cleared-denominator minimal poly of an algebraic `φ_c`, `w₀ = lim φ_c`).

ALL abstract + concrete tools of the clean route are now built and verified (mine + the other agent's):
spine (`exists_separable_witness`, `meroField_repr_countable`, `analyticGerm_ne_zero_zeros_countable`),
continuation (`exists_analyticAt_branch_poly`), natural-boundary engine for all `c`
(`DendriteBoundary` + `InteriorBoundary`), closure (`noRelation_of_transcendence`, `c_eq_of_filledJulia_eq`).
REMAINING = the φ_c-specific glue: from `φ_c` algebraic, extract the polynomial relation as functions
(`aeval`-germ ⟹ poly relation on the basin), the limit/branch-match at a Julia point `z₀`, the
dendrite/interior case selection, the continued-coordinate modulus — then feed the boundary engine ⟹
transcendence ⟹ `noRelation_of_transcendence`. This is the joint top-level instantiation over the other
agent's `φ_c`-in-`meroField`/Green layer; every tool it consumes is now in the codebase.

---

## 2026-06-26 — Transcendence reduction landed: `hGtr` reduced to a function-level no-relation

Three new axiom-clean theorems (`#print axioms` = `[propext, Classical.choice, Quot.sound]`), all in-tree
and compiling:

1. **`AlgebraicBranch.branch_unique_poly`** — local uniqueness of a simple-root branch (polynomial form).
   Two functions continuous at `z₀`, both through the simple root `(z₀,w₀)` of `F(z,w)=Σ_i(P.coeff i)(z)·wⁱ`
   (`∂_w F(z₀,w₀)=d≠0`), both satisfying `F(z,gⱼ z)=0` near `z₀`, are equal near `z₀`. Pure algebra:
   factoring `F(z,a)−F(z,b)=(a−b)·Q(z,a,b)` with `Q(z₀,w₀,w₀)=d≠0` (geom_sum₂_mul + HasDerivAt.unique).
   **This is the matching step** (algebraic branch from `exists_analyticAt_branch_poly` = Böttcher branch).

2. **`TranscendenceReduction.eval₂_polyToAnalytic_val`** — bivariate eval-germ identity: evaluating
   `q ∈ ℂ[z][Y]` at `phiAnalytic c` over the polynomial base has representative function
   `z ↦ q.eval₂ (eval-at-z)(φ_c z) = Σ_i(q.coeff i)(z)·φ_c(z)ⁱ`. `Polynomial.hom_eval₂` threaded through
   the subring inclusion + `Pi.evalRingHom` + `Germ.coeRingHom`.

3. **`TranscendenceReduction.phiMero_transcendental_of_no_function_relation`** — THE field→function
   reduction. If no nonzero `q ∈ ℂ[z][Y]` makes `z ↦ q(z,φ_c(z))` vanish on `U`, then
   `Transcendental (RatFunc ℂ) (phiMero c hU)` (base algebra from `ratfuncToMero`). Key tool:
   `IsFractionRing.isAlgebraic_iff` collapses `IsAlgebraic (RatFunc ℂ) ⟺ IsAlgebraic ℂ[X]` — **no manual
   denominator clearing**; a ℂ[X]-algebraic witness *is* an element of ℂ[z][Y]. Then (2) + meroField
   faithfulness make the witness a vanishing function.

### What this collapses

`q62_independence_connected_of_inputs` (Q62ConnectedAssembly) needs `hGtr : Transcendental (RatFunc ℂ) φ_{c₂}`
and `hrig : TranscendentalOverAdjoin φ_{c₁} φ_{c₂}`. **`hGtr` is now reduced to the purely function-level**

> **(T2)** for `U = deepBall`: `∀ q : ℂ[z][Y], q ≠ 0 → ¬ EqOn (z ↦ q.eval₂ (evalRingHom z)(bottcherCoord c z)) 0 U`.

No field theory remains in `hGtr` — only the geometric no-relation. Note `q.eval₂ (evalRingHom z)(w) =
Σ_{i∈q.support} (q.coeff i).eval z · wⁱ`, exactly the form `exists_analyticAt_branch_poly` / `branch_unique_poly`
consume (`eval = aeval` over ℂ).

### The remaining geometric brick (T2) — precise shape

Given nonzero `q` with `z ↦ q(z,φ_c z)` vanishing on `deepBall`:
- **Minimal-degree-in-Y selection** (internal, cheap): pick `q` of minimal `Y`-degree among vanishing
  relations. `deg_Y q ≥ 1` (else `q ∈ ℂ[z]` vanishes on infinite `U` ⟹ `q=0`). Then `∂_Y q ≠ 0`, lower
  `Y`-degree, so by minimality `z ↦ ∂_Y q(z,φ_c z)` does NOT vanish on `U` ⟹ (analytic) countable zeros
  (`ZeroSet.analyticOnNhd_zeros_countable`) ⟹ cofinitely many **simple-root** points.
- **Extend to the basin**: the relation holds on `deepBall ⊆ Ω_c`; both sides analytic on the connected
  basin `Ω_c` (`BasinConnected`) ⟹ holds on all of `Ω_c` by the identity theorem, up to `∂Ω_c = J_c`.
- **Continue across a Julia point**: pick a Julia boundary point `z₀` approached by simple-root basin
  points with `φ_c → w₀`; `exists_analyticAt_branch_poly` gives an algebraic branch `g` across `z₀`;
  `branch_unique_poly` matches `g = φ_c` on the basin side ⟹ `‖g‖ = exp G_c` there.
- **Boundary contradiction**: `DendriteBoundary.no_green_modulus_continuation` (empty-interior case) /
  `InteriorBoundary.no_unit_modulus_open_continuation` (interior case) ⟹ `False`.

T2 is the cross-agent geometric assembly (basin/Green/Julia continuation). `hrig` (E–vS) needs the same
machinery over `ℂ(z)[φ_{c₂}]`. Endpoints all built; T2 is the joint instantiation.

### 2026-06-26 (cont.) — algebra side of `hGtr` COMPLETE; remaining core sharpened

Two more axiom-clean theorems (in `TranscendenceReduction.lean`, compiling in-tree):

4. **`analyticOnNhd_eval₂_bottcher`** — `z ↦ R.eval₂ (eval-at-z)(φ_c z)` analytic on `U ⊆ escapeOpen c`
   (finite sum of `(R.coeff i)(z)·φ_c(z)ⁱ`). Shared analytic input for all of T2.
5. **`exists_simpleRoot_relation`** — from ANY nonzero vanishing `q ∈ ℂ[z][Y]`, extract a **minimal**-Y-degree
   `P` (deg ≥ 1) with the same vanishing relation AND `{z ∈ U | ∂_Y P(z,φ_c z) = 0}` **countable**
   (`Nat.find` on Y-degree; minimality ⟹ `∂_Y P` ≢ 0 ⟹ `analyticOnNhd_zeros_countable`).

**The entire ALGEBRA side of the connected transcendence `hGtr` is now built.** `hGtr` ⟸ the function-level
no-relation (brick 3), and from any vanishing relation we now have a minimal one with cofinitely-many
**simple-root** basin points (brick 5), the matching lemma (brick 1), and the analyticity (brick 4).

#### The remaining core, named precisely (the deepest analytic brick)

`no_continuation_dendrite` (DendriteBoundary) consumes: `g` analytic on `ball z₀ r`, `z₀ ∈ filledJulia c`,
empty `K_c`-interior in the ball, `‖g z‖ = exp(G_c z)` on the **basin part**, a basin point. So T2's
back-end must produce such a `g` = the continued algebraic branch.

**Key subtlety discovered:** `branch_unique_poly` matches the algebraic branch to `φ_c` only at a point
where `φ_c` is continuous — i.e. a **basin** point `z₁`, NOT the Julia point `z₀` (`φ_c` has no limit at
`z₀` — that is the natural boundary). So the matching gives `g = φ_c` near a basin `z₁`; the contradiction
needs `g` to then continue analytically from `z₁` across a **non-singular** Julia point `z₀` (one outside
the countable simple-root-failure set ∪ branch locus; `J_c` is uncountable so such `z₀` exists), still
equal to `φ_c` on the basin side. That is **global analytic continuation of the algebraic branch defined
by `P` from a basin point across a non-singular boundary point** — the multivalued-continuation /
monodromy core. This is the genuine remaining analytic brick (not a quick assembly; likely no off-the-shelf
mathlib "algebraic function continues off a finite singular set"). It is the heart of "algebraic ⟹ no
natural boundary," and is the same core the disconnected lane's `hDisc` needed.

Endpoints in hand for it: `exists_analyticAt_branch_poly` (local branch at a non-singular point),
`branch_unique_poly` (local matching), `analyticOnNhd_eval₂_bottcher`, `exists_simpleRoot_relation`
(countable singular set), `BasinConnected` (basin preconnected — relation extends deepBall→basin by the
identity theorem), `no_continuation_dendrite`/`InteriorBoundary.no_unit_modulus_open_continuation` (the
two boundary-case engines). Missing: the continuation-along-the-basin that ties a basin-point branch to a
ball around `z₀`.

### 2026-06-26 (cont. 2) — relation-propagation built; remaining unknown narrowed to basin-branch existence

Two more axiom-clean theorems (TranscendenceReduction.lean; full module compiles in-tree):

6. **`analyticOnNhd_eval₂_of_analyticOnNhd`** — `z ↦ R.eval₂ (eval-at-z)(g z)` analytic on `V` for ANY
   analytic `g` (the general-branch form of brick 4).
7. **`eval₂_relation_propagate`** — identity-theorem propagation: if `g` is analytic on preconnected `V`
   and `P(z, g z) = 0` holds near one `w₀ ∈ V`, it holds on all of `V`.

**Effect:** the "carry the relation from `deepBall` into the basin" half of the continuation core is now a
proven brick. Given a single-valued analytic branch `g` on the connected basin that equals `bottcherCoord c`
near a deep-exterior point, `eval₂_relation_propagate` gives `P(z, g z) = 0` on the whole basin; then at a
non-singular Julia boundary point, `exists_analyticAt_branch_poly` + `branch_unique_poly` match the local
algebraic branch to `g`, and `no_continuation_dendrite` (whose modulus input comes from `g`'s
`‖g‖ = exp(greenLimit)` as the basin Böttcher branch) closes it.

**The remaining unknown, now minimal:** the EXISTENCE of that single-valued analytic basin branch `g` on the
connected basin `Ω_c = (filledJulia c)ᶜ` — i.e. the basin Böttcher coordinate for a connected Julia set
(`bottcherCoord` is currently analytic only on `escapeOpen c`, the deep exterior). The other agent's
`CoverConstruction.exists_local_bottcherBranch_basin` gives it LOCALLY (with `‖β‖ = exp(greenLimit)`,
`β ≠ 0`); globalising to a single-valued branch across all of `Ω_c` (uses connectedness of `J_c` ⟺ no
monodromy — `BasinConnected`/`BasinBranching`, the other agent's active lane) is the lone missing input.
Once that branch exists, the connected-case transcendence assembles from bricks 1–7 + the two boundary
engines with no further analytic content.

Session-segment tally: 7 axiom-clean theorems, all `#print axioms = [propext, Classical.choice, Quot.sound]`,
zero sorry / zero added axioms / zero added hypotheses; full `lake build` green.

### 2026-06-26 (cont. 3) — explicit basin branches landed; monodromy confirmed irreducible

New file `ExplicitBranch.lean` (3 axiom-clean theorems + 2 defs, builds in-tree):
- `explicitBranch c n := exp(2⁻ⁿ·bottcherLog c (f_c^[n] z))`, `explicitDomain c n := {z | f_c^[n] z ∈
  escapeOpen ∩ slitPlane}` (open, `isOpen_explicitDomain`).
- `analyticOnNhd_explicitBranch` — analytic on its domain.
- `norm_explicitBranch` — `‖explicitBranch c n z‖ = exp(greenFunctionDyn c z)`, **exactly the `hmod`
  datum** `DendriteBoundary.no_continuation_dendrite` consumes, from a single-valued branch reaching
  arbitrarily deep toward `J_c` as `n → ∞`. Built on the other agent's `exists_greenConjugate_explicit`.

**Monodromy confirmed irreducible (an honest negative finding).** I checked whether `explicitBranch` could
supply the algebraic relation directly: via `bottcherCoord_quadratic` iterated, `explicitBranch c n` is a
*2ⁿ-th root* of `bottcherCoord c ∘ f^[n]`, so it equals the deep-exterior `φ_c = bottcherCoord c` only up
to a **2ⁿ-th root of unity** `ζ` (the dyadic monodromy — the 2⁻ⁿ scaling does NOT annihilate the `2πi`
ambiguity: `exp(2⁻ⁿ·(2ⁿ·bottcherLog z + 2πi k)) = ζ·φ_c`, `ζ = exp(2πi k/2ⁿ)`). So the explicit branch is a
*sheet* `ζ·φ_c`; it carries an algebraic relation `P(z, φ_c)=0` only where `ζ = 1`. The explicit branch
therefore gives the MODULUS for free but does NOT bypass the monodromy.

**Net state of the connected-case transcendence `hGtr`.** Built and verified (10 axiom-clean theorems this
segment): the entire field→function reduction, minimal-relation/simple-root machinery, the branch-matching
lemma, the relation-propagation (identity theorem), and the explicit modulus-correct single-valued basin
branches. The one irreducible remaining input is **sheet selection / trivial dyadic monodromy for connected
`J_c`** — `ζ ≡ 1` so that a single-valued basin branch equal to `φ_c` (not a rotated sheet) exists across
the basin up to `J_c`. That is exactly the obstruction the DISCONNECTED lane proves is NONtrivial
(`CoverConstruction.no_singlevalued_branch_of_dyadic_period`); the connected case needs its negation, owned
by `BasinConnected`/`BasinBranching`. Once `ζ ≡ 1` (single-valued `φ_c` on the basin), the contradiction
assembles from the 10 bricks + the two boundary engines with no further analytic content.

### 2026-06-26 (cont. 4) — natural-boundary contradiction FULLY ASSEMBLED (`false_of_basin_branch_dendrite`)

Two more axiom-clean theorems (12 total this segment):
- `AlgebraicBranch.branch_unique_poly_within` — the `nhdsWithin` (basin-side) matching: `g₂` need only
  *tend* to the simple root `w₀` along `𝓝[(filledJulia c)ᶜ] z₀` (it is undefined at the Julia point `z₀`).
  The cofactor `Q → d ≠ 0` along the basin filter, so it is eventually nonzero. This is the correct crossing
  tool (the full-`𝓝` `branch_unique_poly` cannot match at `z₀`, where `φ_c` has no value).
- `NaturalBoundaryContradiction.false_of_basin_branch_dendrite` — **the assembled contradiction.** Composes
  `exists_analyticAt_branch_poly` (local algebraic branch across `z₀`) + `branch_unique_poly_within`
  (match to the basin branch) + `no_continuation_dendrite` (boundary engine). Derives `False` from:
  `z₀ ∈ filledJulia`, dendrite (empty interior in a ball), `𝓝[basin] z₀` NeBot, simple-root data
  `(z₀, w₀, d≠0)`, and a basin branch `β` with `β → w₀`, the relation `P(z, β z)=0`, and modulus
  `‖β z‖ = exp(G_c z)` — all along `𝓝[(filledJulia c)ᶜ] z₀`.

**Net: the connected-case transcendence is reduced to ONE named geometric existence input.** Every consuming
brick is verified in-tree. The remaining hypothesis bundle of `false_of_basin_branch_dendrite` — a
single-valued basin Böttcher branch `β` tending to a simple root `w₀` of the (minimal) relation at a
dendrite, non-discriminant Julia point `z₀` — is exactly the trivial-dyadic-monodromy / connected-`J_c`
content (basin-construction lane: `BasinConnected`/`BasinBranching`; the explicit `ExplicitBranch` branches
supply the modulus, the monodromy-triviality supplies single-valuedness + the limit). `isPreconnected_compl_filledJulia`
(basin preconnected, PROVEN unconditionally) + `eval₂_relation_propagate` propagate the relation onto that
branch. The interior (non-dendrite) case needs the analogous capstone over `InteriorBoundary`.

Remaining to finish the connected case end-to-end: (1) build `β` (the basin branch with limit at a good
`z₀` — the monodromy-triviality theorem); (2) the interior-case capstone; (3) feed `false_of_basin_branch_dendrite`
into `exists_simpleRoot_relation` + `phiMero_transcendental_of_no_function_relation` to land
`Transcendental (RatFunc ℂ) (phiMero c)`; (4) the parallel `TranscendentalOverAdjoin`. Step (1) is the deep one.

### 2026-06-26 (cont. 5) — threading reduction + capstone hypothesis-trimmed

- `TranscendenceReduction.phiMero_transcendental_of_no_minimal_relation` — the single clean entry point:
  `Transcendental (RatFunc ℂ) (phiMero c)` ⟸ `hgeom` ("no minimal-`Y`-degree simple-root relation vanishes
  on `U`"). Composes `exists_simpleRoot_relation` + `phiMero_transcendental_of_no_function_relation`.
- `false_of_basin_branch_dendrite` refactored: `hNeBot` is now DERIVED from `hempty`
  (`z₀ ∉ interior K_c ⟹ z₀ ∈ closure(basin)` via `closure_compl` + `mem_closure_iff_nhdsWithin_neBot`),
  so the capstone's only geometric hypotheses are: dendrite (`hempty`), simple-root data, and the basin
  branch `β`.

**Connected-case transcendence, dendrite sub-case, fully threaded (13 axiom-clean theorems this segment):**
`phiMero_transcendental_of_no_minimal_relation` ← `hgeom` ← (for each minimal `P`) `false_of_basin_branch_dendrite`
applied at a dendrite Julia point `z₀` with the basin branch `β`. Every link verified except the production of
`(z₀, w₀, β)` — i.e. (a) a dendrite, non-discriminant Julia point `z₀` where the minimal relation has a simple
root `w₀` as the basin-limit of `φ_c`, and (b) the single-valued basin branch `β → w₀` carrying the relation +
modulus. That is the trivial-monodromy / connected-`J_c` core (basin-construction lane). Still open in addition:
the interior (non-dendrite) sub-case (needs `‖g‖ = exp(G_c)` on `K_c`-interior, a harmonic-identity argument
beyond basin matching), and the parallel `TranscendentalOverAdjoin`.

### 2026-06-26 (cont. 6) — synthesis: both natural-boundary routes share ONE bottleneck; resonance route is cleaner

Surveyed the other agent's active Montel/Resonance lane and found the decisive obstruction is already built:
`ResonanceOrder.const_of_no_resonance` — a hypothetical analytic continuation `g` of `φ_c` satisfying the
functional equation `g ∘ f_c^[p] = g^{2^p}` at a **non-resonant repelling periodic point** `z₀` is forced
**locally constant**, contradicting `|g| = exp(G_c)` nonconstant. This is a complete, general (Mathlib-only)
LOCAL natural-boundary obstruction.

**Why the resonance route is cleaner than my dendrite/interior split:** `const_of_no_resonance` yields `g ≡ ζ`
directly ⟹ `exp(G_c)` locally constant ⟹ contradiction. It needs NO dendrite-vs-interior case split and NO
`‖g‖ = exp(G_c)`-on-`K_c`-interior (the global Fatou-component difficulty that blocked my interior capstone).
So the resonance route supersedes `NaturalBoundaryContradiction`/`InteriorBoundary` for closing the connected
case. Remaining inputs for it (per `ResonanceOrder` header): the continuation `g` + its functional equation
+ **density of non-resonant repelling periodic points in `J_c`** (`PeriodicPoints` lane).

**The single shared bottleneck (both routes):** the analytic continuation of `φ_c` from the deep exterior to a
neighbourhood of a Julia point as a single-valued branch `g` (= the basin-branch / trivial-dyadic-monodromy
content). Once `g` exists on a connected `V` reaching the deep exterior:
- new brick `TranscendenceReduction.eqOn_funEq_of_eventuallyEq` propagates the functional equation onto `V`
  (identity theorem; holds near a deep point where `g = φ_c` via `bottcherCoord_quadratic`) → feeds
  `const_of_no_resonance`.
- my `eval₂_relation_propagate` propagates the algebraic relation onto `V`.
- `branch_unique_poly_within` / `exists_analyticAt_branch_poly` handle the algebraic-branch matching.

14 axiom-clean theorems this segment; full tower builds (8539 jobs), zero sorries. `q62_independence` stays
conditional on that one continuation input — now identified as the common crux of BOTH closing routes, with the
resonance route (other agent) the cleaner finisher. Forward move: the continuation `g` (basin branch /
monodromy triviality), then `const_of_no_resonance` + periodic-point density closes the connected transcendence.

### 2026-06-26 (cont. 7) — resonance-route finisher built (`false_of_funEq_at_nonresonant`)

`NaturalBoundaryContradiction.false_of_funEq_at_nonresonant` — the clean UNIFORM finisher: a single-valued
branch `g` analytic on a preconnected open `V`, satisfying `g ∘ f_c^[p] = g^{2^p}` on `V`, through a
non-resonant periodic point `z₀ ∈ V` (`f_c^[p] z₀ = z₀`, `λ^m ≠ 2^p ∀ m≥1`), `g z₀ ≠ 0`, non-constant on
`V`, gives `False` (via `const_of_no_resonance` + identity theorem). **No boundary-case split, no
`K_c`-interior modulus** — it supersedes the `false_of_basin_branch_dendrite` route and sidesteps the
interior-case obstruction entirely.

Verified the geometry lane's frontier: the continuation `g` and the density of non-resonant repelling
periodic points in `J_c` are BOTH genuinely unbuilt (`BasinBranching` has only green-limit/deck facts;
`PeriodicPoints` has only `exists_periodic_point`, not density). These are the two pending deep inputs.

**Connected-case transcendence — full assembled skeleton (15 axiom-clean theorems this segment):**
`phiMero_transcendental_of_no_minimal_relation` (entry) needs `hgeom`; `hgeom` is discharged by
`false_of_funEq_at_nonresonant` once, for the minimal relation, we have the continuation `g` on a connected
`V` reaching a non-resonant repelling periodic point — with the functional equation via
`eqOn_funEq_of_eventuallyEq`, the relation via `eval₂_relation_propagate`, non-constancy via `|g|=exp G_c`.
Every consumer verified. The TWO remaining deep inputs: (1) the continuation `g`; (2) density of non-resonant
repelling periodic points. Both are the basin-construction / Montel lanes' pending work. `q62_independence`
stays conditional on these; the full tower builds (8494 jobs), zero sorries.

### 2026-06-26 (cont. 8) — end-to-end skeleton verified: `phiMero_transcendental_of_resonance_input`

`ConnectedTranscendence.phiMero_transcendental_of_resonance_input` (new file) — threads the WHOLE connected
-case transcendence into one verified theorem:
  `phiMero_transcendental_of_no_minimal_relation` ∘ `false_of_funEq_at_nonresonant`.
It proves `Transcendental (RatFunc ℂ) (phiMero c) ⟸ hinput`, where `hinput` packages exactly the two
remaining deep dynamical inputs: for each minimal simple-root relation, a single-valued continuation `g` of
`φ_c` (analytic on a preconnected `V`, satisfying `g ∘ f_c^[p] = g^{2^p}`, non-constant) reaching a
non-resonant periodic point `z₀ ∈ V`. Every connective brick between the two inputs and the field-theoretic
conclusion is now PROVEN — `hinput` is the sole remaining content for the transcendence half.

KEY simplification confirmed: `false_of_funEq_at_nonresonant` does NOT use the algebraic relation `P` —
it derives `False` from the continuation `g` alone (functional eq + non-constant + non-resonant periodic
point). The relation `P` only enters to *produce* `g` (the algebraic branch analytic across `z₀` when `φ_c`
is algebraic) and the minimal-degree/simple-root selection; the contradiction is purely about `g`.

State: 16 axiom-clean theorems this segment; full tower builds (8498 jobs), zero sorries. `q62_independence`
conditional on: (i) `hinput` (continuation `g` + non-resonant repelling periodic point, dense in `J_c`) for
the transcendence half; (ii) the parallel `TranscendentalOverAdjoin` (same geometry, two-coordinate); (iii)
the `hDisc` lift data (disconnected case). All three bottom out at the continuation/lift construction — the
basin-construction + Montel/periodic lanes' pending deep work. The connected transcendence half is a
one-application close once `hinput` lands.

### 2026-06-26 (cont. 9) — continuation tool identified: `IsCoveringMap.liftPath`

Probed the actual core (the continuation `g`). Concrete findings:
- **The continuation is a covering-map path-lift.** `IsCoveringMap.liftPath` (mathlib) lifts a path
  `γ : C(I, X)` through a covering `p : E → X` given a start lift. The algebraic function defined by the
  minimal `P` is, off its (finite) branch locus, a covering of the `z`-plane; lifting a path from a deep
  exterior point (where the start branch is `φ_c`) to a non-resonant repelling periodic point `z₀` yields
  the single-valued continuation `g` along the path — single-valued because path-lifts have no monodromy
  (monodromy is a loop phenomenon). `IsCoveringMap.eq_of_comp_eq` gives lift uniqueness. This is the
  concrete mathlib route to `hinput`; it composes with the verified skeleton to close the connected case.
  (Overlaps the collaborator's covering-map lane — task "build IsCoveringMapOn".)
- **The exact functional equation `bottcherLog(f_c w) = 2 bottcherLog w`** holds only on a deep CONE
  region `w.re ≥ ‖w.im‖` (via `Complex.log_mul`'s `arg` condition + `bottcherLog_sum_quadratic`); outside
  it the branch ambiguity is the genuine monodromy. So it establishes `explicitBranch = φ_c` only near the
  deep center — non-closing (corroborates the codebase's own "where the dyadic monodromy lives").
- `TranscendentalOverAdjoin` (E–vS, the `hRigid` two-coordinate input) reduces (mine, trivariate
  denominator-clearing) to a function-level no-relation that bottoms out at continuing `φ_{c₁}` (same core)
  plus `J_{c₁} ≠ J_{c₂}` (have, via `BottcherDetermines.c_eq_of_filledJulia_eq`).

Net: the connected case = [verified 16-theorem skeleton] + [the covering path-lift `liftPath` producing
`hinput`]. The latter is the single deep construction (Riemann surface of `P` as a covering + path lift +
analyticity of the lift), the collaborator's active covering-map lane. `q62_independence` stays conditional
on it; I will not fabricate it.

### 2026-06-26 (cont. 10) — KEY REFRAME: the continuation is ALGEBRAIC, not dynamical + gluing pillar

**Difficulty-reducing insight.** Under the contradiction hypothesis (`φ_c` algebraic, relation `P`), `φ_c`
*is* an algebraic function. An algebraic function continues along ANY path off `P`'s finite branch locus
`{z | disc_Y P(z) = 0}` — single-valued along the path (path-lifts have no monodromy). So the continuation
`g` needed by `false_of_funEq_at_nonresonant` is the **algebraic-function path-continuation**, NOT the deep
dynamical basin Böttcher branch (which has the dyadic monodromy). The basin monodromy is IRRELEVANT — we use
that the assumed-algebraic `φ_c` continues as an algebraic function. The functional equation transfers from
the deep exterior via `eqOn_funEq_of_eventuallyEq`; non-constancy from `φ_c ~ z`. This is MINE and
non-conflicting (uses `P` / `exists_analyticAt_branch_poly`, not the collaborator's `f^[n]`-cover).

New brick: `AlgebraicBranch.branch_eqOn_of_eq_at` — the gluing/consistency pillar: two analytic simple-root
branches of `P` agreeing at one simple-root point of a preconnected open `W` agree on all of `W`
(`branch_unique_poly` + identity theorem). This makes the path-continuation single-valued.

**Remaining (now reframed, more tractable):**
(1) **Algebraic path-continuation existence**: continue the start branch (`= φ_c` near a deep point) along a
   path `γ` to a non-resonant repelling periodic point `z₀`, off `disc_Y P`'s zeros. Routes: mathlib
   `IsCoveringMap.liftPath` on the curve `{P=0, ∂_Y P≠0} → ℂ`, OR the clopen `[0,1]`-connectedness argument
   with `branch_eqOn_of_eq_at` as the consistency step. The "closed" direction needs root-boundedness +
   simple-root convergence.
(2) **Density of non-resonant repelling periodic points** in `J_c` (Montel/periodic lane; `PeriodicPoints`
   currently has only existence). `z₀` must also avoid the finite `disc_Y P` locus — automatic since `J_c`
   is infinite.

17 axiom-clean theorems this segment; full tower builds, zero sorries. The reframe means the remaining
continuation is elementary algebraic-function theory (path-lift + finite branch locus), not the deep
connected-`J_c` monodromy triviality — a materially easier target, and mine.

### 2026-06-26 (cont. 11) — second route identified (divisibility); mathlib-gap assessment

**Alternative route to the functional equation (avoids path-continuation).** From minimality of `P`:
`P(z,w) ∣ P(z²+c, w^{2^p})` in `ℂ(z)[w]` (φ_c is a root of both `P(z,·)` and `w ↦ P(z²+c, w^{2^p})`, and
`P` is its minimal polynomial). Consequence: the roots of `P(z₀,·)` at a fixed point `z₀` of `f^[p]` are
closed under `w ↦ w^{2^p}`; a finite set closed under `w↦w^{2^p}` contains a `w↦w^{2^{pm}}`-fixed root `w₀`
(`w₀^{2^{pm}} = w₀`). For the local branch `g` at `(z₀, w₀)` (simple root), the divisibility gives
`P(f^[pm] z, g(z)^{2^{pm}}) = 0`, so `g∘f^[pm]` and `g^{2^{pm}}` are both roots of `P(f^[pm]·,·)`, both
→ `w₀` at `z₀` — equal by simple-root uniqueness ⟹ the functional equation for `g` near `z₀`, with NO
path-continuation. Feeds `false_of_funEq_at_nonresonant` (period `pm`). Open sub-pieces: the divisibility
(algebra; complicated by `φ_c∘f` living on a different germ domain), the period-`pm` non-resonance.

**mathlib-gap assessment (honest):** the remaining pieces need infrastructure thin/absent in this mathlib:
`Polynomial.discriminant` is absent (so "branch locus finite" needs resultant theory); no analytic
continuation-along-a-path; no algebraic-curve covering-map. So BOTH routes (path-continuation via
`liftPath`, and divisibility) require first building real supporting machinery — they are genuine
multi-file constructions, not single-lemma closes. Periodic-point density (Montel) is likewise a real
theorem (collaborator's lane).

State unchanged on completeness: 17 axiom-clean theorems this segment (the full connective skeleton +
gluing pillar), full tower builds, zero sorries. `q62_independence` conditional. The connective spine is
done; the remaining is supporting-machinery + the continuation/density constructions, which I will build
(not fabricate) — they are larger than one hook-firing each.

### 2026-06-26 (cont. 12) — building the continuation: chain-extension step `branch_glue_union`

Started building the algebraic path-continuation machinery (new file `BranchContinuation.lean`):
- `branch_glue_union` — glue two analytic simple-root branches of `P` (on opens `W₁, W₂`, agreeing on a
  preconnected overlap at a simple-root point) into one analytic branch `W₁.piecewise g₁ g₂` on `W₁ ∪ W₂`.
  Uses `branch_eqOn_of_eq_at` (overlap agreement) + `AnalyticAt.congr`. The chain-extension step.

Path-continuation plan (finite-chain, avoids the absent mathlib root-continuity):
1. ✓ local branch at each simple-root point (`exists_analyticAt_branch_poly`).
2. ✓ two consecutive branches glue (`branch_glue_union`).
3. ☐ Lebesgue-number finite cover of `γ([0,1])` + Nat-induction iterating `branch_glue_union` along the
   chain (each step's branch chosen through the previous branch's value at the shared point) → single
   analytic branch on a connected tube `V` from the deep start to `z₀`.
4. ☐ endpoint: `g` analytic near `z₀`, = the continuation; functional eq via `eqOn_funEq_of_eventuallyEq`;
   non-constant ⟹ `false_of_funEq_at_nonresonant`.
Plus the path-existence (γ in the basin avoiding the finite branch locus) and periodic-point density.

18 axiom-clean theorems this segment; full tower builds, zero sorries. `q62_independence` conditional;
actively building the continuation (step 3 next).

### 2026-06-26 (cont. 13) — continuation pillar: `eqOn_of_locally_eq` (clopen equalizer)

`BranchContinuation.eqOn_of_locally_eq` — continuous functions agreeing locally on a preconnected set
agree on it (the continuous identity theorem; NOT in mathlib — built from scratch via subtype clopen:
agreement set closed by continuity, open by local agreement, hence univ on preconnected `s`). This is the
uniqueness pillar for the path-lift: a continuous simple-root selection along a path is determined by its
start value.

Continuation pillars now in hand (19 axiom-clean theorems this segment): branch matching
(`branch_unique_poly`, `branch_unique_poly_within`), gluing (`branch_eqOn_of_eq_at`, `branch_glue_union`),
local existence (`exists_analyticAt_branch_poly`), lift uniqueness (`eqOn_of_locally_eq`). Remaining for the
path-continuation: the value-lift EXISTENCE (clopen on `[0,1]`: openness from local branch, closed
direction from root-boundedness + simple-root convergence — the part with no mathlib root-continuity), then
the endpoint branch + functional equation (`eqOn_funEq_of_eventuallyEq`) → `false_of_funEq_at_nonresonant`.
Plus path-existence (branch locus finite — needs resultant, absent) and periodic-point density.

Full tower builds, zero sorries. `q62_independence` conditional; actively building the continuation,
pillars accumulating.

### 2026-06-26 (cont. 14) — continuation pillar: `norm_root_le_of_monic` (Cauchy root bound)

`BranchContinuation.norm_root_le_of_monic` — Cauchy bound: a root of a monic `p` (deg ≥ 1) has
`‖z‖ ≤ max 1 (Σ_{i<deg} ‖coeff i‖)` (not in mathlib; built from scratch via the geometric estimate). This
bounds the value-lift `v(t)` uniformly on a compact parameter interval — the root-boundedness the
closed direction of the clopen path-lift needs.

Continuation infrastructure now (20 axiom-clean theorems this segment): branch matching/uniqueness
(`branch_unique_poly`, `branch_unique_poly_within`, `branch_eqOn_of_eq_at`), gluing (`branch_glue_union`),
local existence (`exists_analyticAt_branch_poly`), lift uniqueness (`eqOn_of_locally_eq` — continuous
identity theorem), root-boundedness (`norm_root_le_of_monic`). All are mathlib-absent pieces built here.

Remaining for value-lift EXISTENCE: assemble the `[0,1]`-clopen — openness (local branch + `γ` continuity),
closed direction (uniform root bound from `norm_root_le_of_monic` ⟹ cluster value ⟹ simple-root branch
extends, uniqueness from `eqOn_of_locally_eq`). Then endpoint branch + functional equation
(`eqOn_funEq_of_eventuallyEq`) → `false_of_funEq_at_nonresonant`. Plus path-existence (branch locus finite,
needs resultant — absent) and periodic-point density.

Confirmed mathlib gaps filled this segment: continuous identity theorem, Cauchy root bound (both built).
Full tower builds, zero sorries. `q62_independence` conditional; the continuation is being constructed
pillar by pillar.

### 2026-06-26 (cont. 15) — utility `hasDerivAt_relationPoly`; collaborator building Marty/Montel

`BranchContinuation.hasDerivAt_relationPoly` — the `w`-derivative of the relation polynomial, supplying the
`hpartial` (simple-root) input of `exists_analyticAt_branch_poly`/`branch_unique_poly` from a "derivative ≠ 0"
hypothesis. Small reusable utility extracted from `branch_unique_poly`'s internals.

Collaborator's lane is actively building the density side: new files `SphericalDeriv`, `ChordalMetric`,
`Marty` (Marty's normal-families criterion) → toward periodic-point density / the Montel natural boundary —
the shared input both routes need.

21 axiom-clean theorems this segment. Continuation pillars complete: `exists_analyticAt_branch_poly`,
`hasDerivAt_relationPoly`, `branch_unique_poly`(+`_within`), `branch_eqOn_of_eq_at`, `branch_glue_union`,
`eqOn_of_locally_eq`, `norm_root_le_of_monic`. Next BIG target: assemble the value-lift EXISTENCE
(`[0,1]`-clopen) from these — all ingredients now in hand. Then endpoint branch + functional equation
(`eqOn_funEq_of_eventuallyEq`) → `false_of_funEq_at_nonresonant`. Full tower builds, zero sorries.
`q62_independence` conditional; building the continuation, pillars complete, assembly next.

### 2026-06-26 (cont. 16) — bridge `relation_eq_eval_map`; hDisc state clarified

`BranchContinuation.relation_eq_eval_map` — `Σᵢ (P.coeff i)(z)·wⁱ = (P.map(eval z)).eval w`, bridging the
`eval₂`-sum relation to mathlib's `Polynomial.eval`/`roots` on the fibre `P.map(evalRingHom z) ∈ ℂ[w]`
(so `norm_root_le_of_monic` / fibre-finiteness apply directly to the relation).

**hDisc lane state (clarified):** algebra COMPLETE — `q62_independence_disconnected_of_lifts` discharges
`hDisc` through the top `q62_independence`, given `hliftF`/`hliftG` (the deck self-biholomorphism scaling
one φ by an unbounded-order root of unity, fixing the other + ℂ(z)). Per `CoverConstruction`, `hliftF`
reduces (via `hscale_germ_of_greenConjugate` + `monoF_witness`) to the **global single-valued
green-conjugate `F` on the connected dyadic cover** — glue the explicit per-domain conjugates
(`exists_greenConjugate_explicit`) via `exists_greenConjugate_glue`. SAME continuation/cover core as the
connected case. Kummer alternative (`q62_disconnected_kummer`): needs `Irreducible(X^{2^k}−C(φ_c∘f^[n]))`,
reduced by `KummerNonSquare.fixed_not_sqrt_of_scaling` to the same scaling deck.

So hDisc and hRigid share ONE remaining analytic core (the single-valued lift on the cover / continuation);
`BranchContinuation` (gluing, uniqueness, root bounds, the bridge) feeds both. 22 axiom-clean theorems this
segment; full tower builds, zero sorries.

### 2026-06-26 (cont. 17) — pillar `eventually_unique_root` (pointwise local root uniqueness)

`BranchContinuation.eventually_unique_root` — near a simple root `(z₀,w₀)`, every root `(z,w)` of the
relation near it equals the branch value `g z` (factoring `F(z,w)−F(z,g z)=(w−g z)·Q`, `Q(z₀,w₀)=d≠0`).
The pointwise companion of `branch_unique_poly`, needed for the path-lift's closed direction and uniqueness
(a continuous root-selection near a simple root is pinned to the branch).

**Continuation toolkit now essentially complete** (23 axiom-clean theorems this segment): local existence
+ derivative (`exists_analyticAt_branch_poly`, `hasDerivAt_relationPoly`), uniqueness (analytic
`branch_unique_poly`/`_within`, pointwise `eventually_unique_root`, continuous `eqOn_of_locally_eq`),
gluing (`branch_eqOn_of_eq_at`, `branch_glue_union`), root-boundedness (`norm_root_le_of_monic`), and the
mathlib bridge (`relation_eq_eval_map`). Several built from scratch (continuous identity theorem, Cauchy
bound, pointwise uniqueness). Next: assemble the value-lift EXISTENCE (`[0,1]`-clopen) from these — all
ingredients in hand. Full tower builds, zero sorries. `q62_independence` conditional.

### 2026-06-26 (cont. 18) — `exists_local_lift` (open-extension atom of the value-lift)

`BranchContinuation.exists_local_lift` — at a simple root of the relation at `γ t₀`, the branch composed
with the path gives a continuous local lift `u = g∘γ` on a parameter ball, `u t₀ = w₀`, relation holding.
The open-extension atom for the value-lift along a path.

24 axiom-clean theorems this segment. Value-lift toolkit complete: local lift (`exists_local_lift`),
pointwise/continuous/analytic uniqueness (`eventually_unique_root`, `eqOn_of_locally_eq`,
`branch_unique_poly`), gluing (`branch_glue_union`), root bound (`norm_root_le_of_monic`), mathlib bridge
(`relation_eq_eval_map`). Remaining: the global value-lift EXISTENCE assembly (patch local lifts over
`[0,1]` — sup-clopen or compactness/finite-partition) → branch-tube → functional equation
(`eqOn_funEq_of_eventuallyEq`) → `false_of_funEq_at_nonresonant`. Full tower builds, zero sorries.

### 2026-06-26 (cont. 19) — divisibility route's functional-eq step `funEq_of_branch` (bypasses value-lift)

`BranchContinuation.funEq_of_branch` — for the local simple-root branch `g` at `(z₀,w₀)`, `F` fixing `z₀`,
`w₀^dd=w₀`, and the divisibility consequence `P(F z, g(z)^dd)=0` near `z₀`, derives `g(F z)=g(z)^dd` near
`z₀`. Uses `eventually_unique_root` (both `g(Fz)` and `g(z)^dd` are roots of `P(Fz,·)` → simple root `w₀`,
so equal). **NO path-continuation/tube** — this is the divisibility route, which sidesteps the value-lift
existence assembly (the analysis with mathlib root-continuity gaps).

**Divisibility route status (cleaner than value-lift):**
- ✓ functional eq for local branch (`funEq_of_branch`, this turn) ← the key step, now built.
- ✓ pointwise uniqueness (`eventually_unique_root`), local branch (`exists_analyticAt_branch_poly`).
- ✓ finisher (`false_of_funEq_at_nonresonant`) — feed via a small ball `V` (EqOn from the `∀ᶠ`).
- ☐ the divisibility consequence `hdiv` = `P(Fz, g(z)^dd)=0` near `z₀`, from `P ∣ P(F·,·^dd)` (algebra:
  `Q := P(F·, ·^dd)`, `Q(φ_c)=0` via φ_c's functional eq, `P∣Q` by minimality). Pure ALGEBRA, mathlib-OK.
- ☐ periodic root `w₀^dd=w₀` simple at `z₀` (finite orbit under `w↦w^dd`); g nonconstant; periodic-density
  (shared, collaborator).

25 axiom-clean theorems this segment; full tower builds, zero sorries. The divisibility route makes the
remaining work mostly algebra (divisibility + finite orbit), avoiding the mathlib-gap analysis.

### 2026-06-26 (cont. 20) — divisibility input `relation_iterate_eq_zero` (φ_c root of Q)

`BranchContinuation.relation_iterate_eq_zero` — on `escapeOpen`, `P(f^[p]z, φ_c(z)^{2^p}) = 0`, i.e. φ_c is
a root of `Q(z,w) := P(f^[p]z, w^{2^p})`. From the relation on `escapeOpen` + `bottcherCoord_iterate`
(`φ_c(f^[p]z)=φ_c(z)^{2^p}`) + forward-invariance of `escapeOpen` (`norm_iterate_ge`). The input to the
divisibility `P ∣ Q`.

**Divisibility route (26 axiom-clean theorems this segment):** ✓ φ_c root of Q (`relation_iterate_eq_zero`),
✓ functional-eq step (`funEq_of_branch`), ✓ pointwise uniqueness (`eventually_unique_root`), ✓ local branch
(`exists_analyticAt_branch_poly`), ✓ finisher (`false_of_funEq_at_nonresonant`). Remaining: ☐ `P ∣ Q` by
minimality (Euclidean division in `ℂ(z)[w]`: `R(φ_c)=0` lower-degree ⟹ `R=0`) giving the `hdiv` of
`funEq_of_branch`; ☐ periodic root `w₀^{2^{pm}}=w₀` simple at `z₀` (finite orbit under `w↦w^{2^p}`); ☐ g
nonconstant; ☐ periodic-point density (shared, collaborator's Marty/Montel). The route is mostly ALGEBRA now
(mathlib-supported), avoiding the analysis-gap value-lift. Full tower builds, zero sorries.

### 2026-06-26 (cont. 21) — `exists_minimal_relation` (minimality exposed, for P ∣ Q)

`BranchContinuation.exists_minimal_relation` — extracts a minimal-`w`-degree (`≥1`) vanishing relation `P`
AND exposes the minimality `∀ R ≠ 0 vanishing, P.natDegree ≤ R.natDegree` (the `Nat.find` minimality
`exists_simpleRoot_relation` hid). This makes `P` the generator of the relation ideal: Euclidean division
⟹ `P ∣ Q` for every vanishing `Q`.

Divisibility route (27 axiom-clean theorems this segment): ✓ minimal relation w/ minimality
(`exists_minimal_relation`), ✓ φ_c root of `Q` (`relation_iterate_eq_zero`), ✓ functional-eq step
(`funEq_of_branch`), ✓ pointwise uniqueness (`eventually_unique_root`), ✓ local branch + finisher. Remaining:
☐ `P ∣ Q` via Euclidean division in `ℂ(z)[w]` (`R := Q mod P`, `R(φ_c)=0` lower-degree ⟹ `R=0` by
minimality) → `hdiv`; ☐ periodic root `w₀^{2^{pm}}=w₀` simple; ☐ g nonconstant; ☐ periodic-density (shared).
Full tower builds, zero sorries. The route is pure algebra now (mathlib-supported).

### 2026-06-26 (cont. 22) — periodic-point core `exists_periodic_of_finite_mapsTo`

`BranchContinuation.exists_periodic_of_finite_mapsTo` — a finite set closed under `f` has a periodic point
(`f^[m] s = s`, `m≥1`; pigeonhole on the orbit). For `f = (·^{2^p})` on the roots of `P(z₀,·)` (closed under
`w↦w^{2^p}` by the divisibility) this gives the periodic root `w₀^{2^{pm}} = w₀`.

**Divisibility route (28 axiom-clean theorems this segment) — one gateway left:** every piece is built
EXCEPT `P ∣ Q` (the polynomial divisibility), which is the single gateway unlocking the rest:
- `P ∣ Q` ⟹ `hdiv` (`P(Fz, g(z)^{2^p})=0`) → `funEq_of_branch` → functional eq for the local branch g;
- `P ∣ Q` at `z₀` ⟹ roots of `P(z₀,·)` closed under `w↦w^{2^p}` → `exists_periodic_of_finite_mapsTo` →
  periodic root `w₀^{2^{pm}}=w₀`;
- then `exists_analyticAt_branch_poly` (branch g) + `false_of_funEq_at_nonresonant` (g nonconstant since
  `P` irreducible/deg≥1) closes it — at a non-resonant repelling periodic `z₀` (density, collaborator).
`P ∣ Q` itself: Euclidean division in `ℂ(z)[w]` (or `minpoly.dvd`) using `exists_minimal_relation`'s
minimality + `relation_iterate_eq_zero` (Q(φ_c)=0). Full tower builds, zero sorries.

### 2026-06-26 (cont. 23) — `relation_mul` (relation is multiplicative)

`BranchContinuation.relation_mul` — `relation(P·S)(z,w) = relation(P)(z,w)·relation(S)(z,w)` (the
relation-eval is the ring hom `P ↦ (P.map(eval z)).eval w`, so multiplicative; via `relation_eq_eval_map` +
`map_mul` + `eval_mul`). With `Q = P·S`: `relation(Q)(z,gz) = relation(P)(z,gz)·relation(S)(z,gz) = 0` once
`relation(P)(z,gz)=0` — i.e. once `P ∣ Q`, this is the `hdiv` of `funEq_of_branch` and the root-closure at z₀.

**Divisibility route — gateway reduced to `Q = P·S`:** with `relation_mul`, both consequences (hdiv,
root-closure) follow mechanically from the integer divisibility `Q = P·S` in `ℂ[z][w]`. That divisibility is
the lone remaining algebra: `Q := P(f^[p]·,·^{2^p})` (composition), `relation(Q)(φ_c)=0`
(`relation_iterate_eq_zero`), `P` minimal (`exists_minimal_relation`) ⟹ `P ∣ Q` (Euclidean in `ℂ(z)[w]` +
Gauss, or `minpoly.dvd`). Then funEq + periodic root (`exists_periodic_of_finite_mapsTo`) + g-nonconstant
(P irreducible) + `false_of_funEq_at_nonresonant` close it, at a non-resonant repelling periodic z₀ (density,
collaborator). 29 axiom-clean theorems this segment; full tower builds, zero sorries.

### 2026-06-26 (cont. 24) — `quadIteratePoly` (f^[p] as a polynomial)

`BranchContinuation.quadIteratePoly c p` + `quadIteratePoly_eval` — the `p`-fold composition of `X²+C c`,
evaluating to `(quadratic c)^[p]`. The polynomial form of `f^[p]`, needed to build `Q(z,w) := P(f^[p]z,
w^{2^p})` as a `Polynomial (Polynomial ℂ)` (outer coeffs = `P.coeff i` composed with `quadIteratePoly`).

Divisibility-route gateway `Q = P·S` — remaining sub-steps: (1) build `Q` (compose `P` outer coeffs with
`quadIteratePoly c p`, scale inner degree by `2^p`) + its relation identity `relation(Q)(z,w) = P(f^[p]z,
w^{2^p})`; (2) `relation(Q)(φ_c)=0` (have, `relation_iterate_eq_zero`); (3) `P ∣ Q` by minimality
(`exists_minimal_relation`, Euclidean/`minpoly.dvd`). Then `relation_mul` + `funEq_of_branch` +
`exists_periodic_of_finite_mapsTo` + `false_of_funEq_at_nonresonant` close it (at a non-resonant repelling
periodic z₀ — density, collaborator). 31 axiom-clean theorems this segment; full tower builds, zero sorries.

---

## Divisibility route COMPLETE (algebraic+analytic spine) — 2026-06-26

The connected-case `φ_c`-transcendence is now reduced to a **purely dynamical input** with the entire
algebraic+analytic spine proven axiom-clean (`[propext, Classical.choice, Quot.sound]`, zero sorries).
This replaces the old `hinput` of `phiMero_transcendental_of_resonance_input` (which hypothesized a global
single-valued continuation `g` on a preconnected `V`) by the LOCAL algebraic branch — no continuation/tube.

New bricks (all in-tree, all axiom-clean):

**BranchContinuation.lean**
- `compRelPoly c p P` / `compRelPoly_relation` — `Q(z,w) := P(f^[p]z, w^{2^p})` as a polynomial; its
  relation is the composed relation.
- `relation_C`, `relation_add`, `relation_at_const` — relation-evaluation ring-hom helpers
  (`relation_at_const`: `∑ (P.coeff i)(z)·w₀ⁱ = (P.eval (C w₀)).eval z`).
- `divides_relation_up_to_denom` — **THE GATEWAY**. `P` minimal vanishing relation, `Q` any vanishing
  relation ⟹ `(C e)·Q = P·S`, `e ∈ ℂ[z]\{0}` (i.e. `P ∣ Q` in `ℂ(z)[w]`). Euclidean division in
  `(RatFunc ℂ)[w]` + `IsLocalization.integerNormalization` (clear denominators) + the relation ring-hom
  on `U` forcing the remainder to vanish + minimality. The hardest piece; no meroField, no identity thm.
- `funEq_hdiv_of_divides` — gateway `(C e)·Q = P·S` + local branch `g` ⟹ `funEq_of_branch`'s `hdiv`
  (`P(f^[p]z,(g z)^{2^p})=0` near `z₀`), via punctured-nbhd (`𝓝[≠] ≤ cofinite`, `e` finite roots) +
  continuity extension.

**NaturalBoundaryContradiction.lean**
- `false_of_eventually_funEq_at_nonresonant` — resonance finisher needing only the LOCAL `∀ᶠ` functional
  equation (no `V`/preconnected/`EqOn`); `const_of_no_resonance` + non-local-constancy.

**ConnectedTranscendence.lean**
- `false_of_periodic_simpleroot` — end-to-end `False` from a non-resonant periodic simple-root point
  `(z₀,w₀)` of minimal `P` with `w₀^{2^p}=w₀`, `w₀≠0`, `(X-C(C w₀))∤P`. Wires branch →gateway →`hdiv`
  →`funEq_of_branch` →finisher; non-constancy derived from `(X-C(C w₀))∤P` via `relation_at_const`.
- `eval₂_eq_relation` — bridge `eval₂` form ↔ support-sum form.
- `exists_simpleRoot_minimal_relation` — like `exists_simpleRoot_relation` but EXPOSES minimality
  (support-sum form), via `exists_minimal_relation` + countability-of-`∂P`-zeros.
- `phiMero_transcendental_of_no_minimal_relation_min` — transcendence entry whose obligation also
  receives minimality (support-sum form).
- `relation_vanishes_escapeOpen` — identity-theorem upgrade `hPrel` on `U` ⟹ on all `escapeOpen c`.
- `phiMero_transcendental_of_periodic_input` — **CAPSTONE**. `Transcendental (RatFunc ℂ) (phiMero c)`
  given, per minimal relation `P`, a non-resonant periodic simple-root point with the conditions above.

**Remaining (purely dynamical — collaborator's Montel/periodic lane):** the `hinput` of
`phiMero_transcendental_of_periodic_input`: a non-resonant repelling periodic point `z₀` dense in `J_c`,
simple root of `P` (avoid finite branch locus), with `w₀^{2^p}=w₀` (finite-orbit/`exists_periodic_of_finite_mapsTo`
on the squaring-closed root set at `z₀`), `w₀≠0`, `(X-C(C w₀))∤P` (dischargeable from minimality:
`(X-C(C w₀))∣P ⟹` lower-degree vanishing relation). Then wire `phiMero_transcendental_of_periodic_input`
→ `Q62ConnectedAssembly` (→ hRigid) and the resonance route → hDisc.

### hndvd discharged — purely-dynamical capstone (2026-06-26, cont.)

`ConnectedTranscendence.lean` (all axiom-clean):
- `exists_bottcherCoord_ne` — `φ_c` non-constant on any nonempty open `U ⊆ escapeOpen c`: if `φ_c ≡ w₀`
  then (identity thm) `≡ w₀` on connected `escapeOpen`, and `φ_c(z²+c)=φ_c(z)²` ⟹ `w₀ = w₀²`, against
  `‖φ_c‖ > 1`.
- `factor_not_dvd_of_minimal` — `(X − C(C w₀)) ∤ P` for the minimal relation `P`: a factor would give a
  lower-degree vanishing relation `P'` (via `φ_c ≢ w₀` + identity thm), contradicting minimality.
- `phiMero_transcendental_of_periodic_input'` — **CLEANEST CAPSTONE**: drops `hndvd`; `hinput` is now
  PURELY dynamical — a non-resonant periodic point `z₀` that is a simple root `(z₀,w₀)` of `P` with
  `w₀^{2^p}=w₀`, `w₀≠0`. The whole algebraic+analytic spine is discharged; only the dynamical existence
  remains (collaborator's Montel/periodic-density lane).

### Nonzero-root-orbit brick (2026-06-26, cont.)

`BranchContinuation.lean` (axiom-clean):
- `iterate_pow` — `(·^N)^[m] w = w^{N^m}`.
- `exists_pow_fixed_root` — at a periodic `z₀` with the divisibility and `e(z₀)≠0`, `P(z₀,·)≠0`, a nonzero
  root `w` ⟹ a nonzero `w₀` with `w₀^{2^{p·m}}=w₀` (squaring-orbit cycle in the finite nonzero root set).
  Supplies the `w₀^{2^{p'}}=w₀`, `w₀≠0` datum of `false_of_periodic_simpleroot` at exponent `p'=p·m`
  (with `f_c^[p'] z₀ = z₀` automatic).

### Irreducible remaining dynamical core (precise)
`phiMero_transcendental_of_periodic_input'` is closed except for `hinput`. With `exists_pow_fixed_root`
the residue is: **a periodic point `z₀` of `f_c` (period `p`) such that, for the minimal relation `P`,
(i) `P(z₀,·) ≠ 0` with a nonzero root, (ii) that root `w₀` is a simple root, (iii) `e(z₀) ≠ 0` (denominator
of the divisibility), (iv) the multiplier `λ` of `f_c^[p]` at `z₀` is non-resonant at the cycle exponent
`p·m`: `λ^{m·j} ≠ 2^{p·m}` for all `j ≥ 1`** — which holds whenever `log|λ|/log 2` is irrational.
(i)–(iii) are finite-avoidance conditions; (iv) needs a periodic point whose multiplier modulus is not a
power of 2. The existing `PeriodicPoints.exists_periodic_point` gives only EXISTENCE of a fixed point of
`f_c^[p]`, not repelling/non-resonant — so the open piece is the multiplier-spectrum fact (Montel/density
lane: `MontelIterates`, `Marty`), genuinely dynamical, not algebraic.

### Non-resonance made a modulus bound; strongly-repelling capstone (2026-06-26, cont.)

`BranchContinuation.lean`:
- `nonresonant_of_norm_gt` — `‖λ‖ > 2^p ⟹ λ^m ≠ 2^p ∀m≥1` (since `‖λ^m‖=‖λ‖^m≥‖λ‖>2^p`). Transfers
  through exponent adjustment: `‖λ‖>2^p ⟹ ‖λ^m‖=‖λ‖^m>(2^p)^m=2^{p·m}`, so a strongly-repelling cycle
  stays non-resonant at the squaring-orbit exponent `p·m` — resolving the earlier non-resonance-transfer
  obstruction.
- `hasDerivAt_iterate_periodic` — multiplier of `F^[p·m]` at a `p`-periodic point is `λ^m` (chain rule).

`ConnectedTranscendence.lean`:
- `phiMero_transcendental_of_repelling_input` — capstone with the abstract non-resonance replaced by the
  natural `2^p < ‖λ‖` (strongly-repelling cycle).

**Precise irreducible core (final, after all algebra):** the ONLY open input to connected-case `hGtr` is a
DYNAMICAL existence: for the minimal relation `P`, a periodic point `z₀` (period `p`) that is a NONZERO
SIMPLE root of `P(z₀,·)` and is **non-resonant** — guaranteed by `2^p < ‖λ‖` (strongly repelling,
`‖λ‖ = 2^p·∏‖orbit‖`, i.e. `∏‖orbit‖>1`) or `‖λ‖ < 1` (attracting). `exists_pow_fixed_root` then supplies
the `w₀^{2^{p·m}}=w₀`, `w₀≠0` datum. This is the multiplier-spectrum fact (∃ a non-resonant cycle meeting
`P`'s simple-root locus) — for `c≠0` it follows from Lyapunov-exponent variation (Zdunik), genuinely
dynamical, NOT algebraic; the `MontelIterates`/`Marty` lane. PLUS the separate `hrig`
(`TranscendentalOverAdjoin`) two-parameter rigidity leg. Everything else for `hGtr` is proven, axiom-clean.

- `nonresonant_of_norm_lt_one` — `‖λ‖<1 ⟹ λ^m≠2^p` (attracting cycles non-resonant). Completes the
  modulus dichotomy: a cycle is non-resonant whenever `‖λ‖ ∉ [1, 2^p]`-with-resonant-argument; the clean
  sufficient conditions are `‖λ‖<1` (attracting) or `‖λ‖>2^p` (strongly repelling).

**Cardinality note on the open core:** there are only COUNTABLY many periodic orbits, so a cardinality
argument cannot produce a non-resonant cycle — the resonant multiplier values are also countable. Avoiding
`P`'s finite bad loci needs INFINITELY many non-resonant cycles, i.e. the multiplier set is not eventually
contained in the countable resonant set. For `c ≠ 0` this is Zdunik-type Lyapunov-variation; it is the
genuine, irreducible dynamical input and is not derivable algebraically. This is logged, not papered over.

### resonance_order multiplier-constraint + the |c|>1 fixed-point partial (2026-06-26)

Reading `ResonanceOrder.resonance_order`: at ANY good period-`p` point (nonzero simple root of `P`,
non-constant branch) the multiplier is FORCED resonant, `λ^n = 2^p` (`n =` order of `g-ζ`), so
`‖λ‖ = 2^{p/n} ∈ (1, 2^p]`. Hence `false_of_periodic_simpleroot` = "find a good point off this resonance
locus" (e.g. `‖λ‖>2^p` or `‖λ‖<1`).

**Partial route (`p=1`, `‖c‖>1`):** the two fixed points `z_±` of `f_c` have `λ_± = 2z_±`,
`‖λ_+‖·‖λ_-‖ = 4‖c‖ > 4`. If BOTH were good-and-resonant, `‖λ_±‖ = 2^{1/n_±} ≤ 2`, so product `≤ 4` —
contradiction. So for `‖c‖>1`, not both fixed points are good-and-resonant ⟹ one is good-and-non-resonant
(`‖λ‖>2`, via `nonresonant_of_norm_gt`/`exists_pow_fixed_root`/`hasDerivAt_iterate_periodic`) and closes
`hGtr` — PROVIDED both fixed points are "good" (`P(z₀,·)≠0`, nonzero simple root, `e(z₀)≠0`). The gap:
with only 2 fixed points one cannot dodge `P`'s finite bad loci; needs either a guarantee the bad loci miss
`{z_+,z_-}` or higher-period points (back to the spectrum). So this is a genuine partial, not a full close.
The product/index route to a clean contradiction would need the holomorphic fixed-point-index formula
`∑ 1/(1-λ_i) = 0` (not in mathlib).

### hDisc lift, brick 1: local analytic inverse of φ_c (2026-06-26)

`BottcherInverse.lean` (NEW, axiom-clean, in aggregator):
- `deriv_bottcherCoord_ne_zero` — `φ_c'(z) ≠ 0` on `escapeOpen c` (from `logDeriv_bottcherCoord_ne_zero_escape`).
- `exists_localInverse_bottcherCoord` — analytic local inverse `ψ` of `φ_c` at any `z₀ ∈ escapeOpen c`
  (holomorphic inverse function theorem: `AnalyticAt.hasStrictDerivAt` + `analyticAt_localInverse`),
  `ψ∘φ_c=id` near `z₀`, `φ_c∘ψ=id` near `φ_c z₀`.

This is the local-section atom of the dyadic-cover lift `hliftF`/`hliftG`. Next bricks toward `hliftF`:
(2) local section of the cover `f_c^[n]` via `ψ`; (3) glue along `IsCoveringMapOn` into a single-valued
branch on the connected cover; (4) the deck map `g` scaling `φ_{c₁}` by a `2^n`-root of unity; (5) the
figure-eight independence (`g` fixes `φ_{c₂}`). Real, multi-session; brick 1 done.

### [CONJECTURE / RESEARCH LEAD] resonance_order multiplier-pinning — a possible Zdunik-free route to hGtr

`resonance_order` is stronger than I was using: at EVERY good (simple-root, non-constant-branch) period-`p`
point, `λ^n = 2^p` is FORCED, where `n =` vanishing order of `g - w₀` (`= 1 +` order of `g'`-zero). Two
consequences:
- Every good period-`p` point is REPELLING with multiplier *pinned*: `λ^n = 2^p`, so `‖λ‖ = 2^{p/n}`.
- For cofinitely many simple-root points `g'(z₀) ≠ 0` ⟹ `n = 1` ⟹ `λ = 2^p` EXACTLY (the real number).

**Lead:** the multiplier function `λ(z) = (f_c^[p])'(z)` is a degree-`2^p−1` polynomial; it cannot equal
the constant `2^p` at all `2^p` fixed points (too many roots), so SOME fixed point has `λ ≠ 2^p`. If that
point is a good `n=1` simple root, that already contradicts the pinning ⟹ transcendence — NO Zdunik.
Closing it cleanly needs (a) a UNIFORM ramification bound `n ≤ N(P)` (max vanishing order of the branch
`g'`; finite by Riemann–Hurwitz on the curve `P`), and (b) a counting/`disc` argument that not all good
points can absorb their `n`. [Caveat: my earlier "∏λ_i = 2^{2^p} f^[p](0)" was WRONG — the true product
of multipliers is `± disc(f_c^[p](z) − z)`; the asymptotic route must use the discriminant, not that.]

Status: **conjectural route**, not closed. But it relocates `hGtr`'s blocker from analytic
thermodynamic-formalism (Zdunik, absent from mathlib) to ALGEBRAIC ramification + discriminant counting —
plausibly more tractable in mathlib. This is the most promising next attack on the binding constraint.

### CORRECTION to the multiplier-pinning lead — the degree-counting closure FAILS

Worked the lead further; the clean contradiction does NOT materialize, and I'm recording why (honesty /
don't-chase-dead-ends):
- With a uniform order bound `n ≤ N`, every good period-`p` point has `λ` among the resonant values
  `{2^{p/n}ζ : 1≤n≤N, ζ^n=1}` (`N(N+1)/2` values), i.e. a root of `R_p(X)=∏_{n≤N}(X^n−2^p)`. Then the good
  points are roots of `R_p((f_c^[p])'(z))`, whose degree is `(N(N+1)/2)(2^p−1) ≫ 2^p`. So having all `2^p`
  fixed points as roots gives NO degree contradiction. The polynomial-count is too generous.
- The `n=1` sub-route (`λ=2^p` exactly, multiplier poly degree `2^p−1` can't vanish at all `2^p` points)
  guarantees only `≥ 1` point with `λ≠2^p` — not enough to beat the finite bad-loci `B`; and `#{λ=2^p}`
  among fixed points (`= #{cycle-product=1}`) is not provably small without spectrum input.
- The modulus/product route is dead: the true multiplier product is `±disc(f_c^[p]−z)`, not the clean
  `2^{2^p}f^[p](0)` I mis-derived, so no easy asymptotic.

**Net:** `resonance_order` genuinely PINS every good cycle's multiplier (`λ^n=2^p`) — a real structural
fact, keep it. But closing `hGtr` still reduces to "the period-`p` multipliers are not all resonant," which
is a multiplier-SPECTRUM / equidistribution statement (Bassanelli–Berteloot bifurcation currents, or
Zdunik). The lead REFORMULATES the blocker in algebraic terms but does NOT escape its dynamical core.
`hGtr` remains genuinely blocked on a spectrum result absent from mathlib. (Over-optimism corrected.)

### hDisc lift, brick 2: finite sheaf-gluing (2026-06-26)

`SheafGlue.lean` (NEW, axiom-clean, in aggregator):
- `analyticOnNhd_glue_finite` — a finite family of analytic branches `f i` on opens `U i` agreeing
  PAIRWISE on overlaps glues to one global analytic `F` on `⋃ U i`, restricting to each `f i`. The final
  cover-assembly step of `hliftF`/`hliftG`: it consumes the cocycle-TRIVIALIZED branches and produces the
  global single-valued `φ̃c`.

hDisc lift bricks done: (1) local inverse `exists_localInverse_bottcherCoord`, (2) finite sheaf-glue
`analyticOnNhd_glue_finite`. Remaining critical-path: the COCYCLE TRIVIALIZATION — choose patch-branch
representatives so consecutive `uᵢ`-adjusted branches agree pairwise, using `∏ uᵢ = 1` around the loop
(`no_singlevalued_branch_of_dyadic_period` gives period `2πi`, `exp = 1`). That loop-closure (H¹-vanishing
on the annulus cover) is the genuine remaining bottleneck; (4) deck-map `g` from the lift; (5) figure-eight
`φ_{c₂}`-invariance. Bricks 1–2 are the assembly atoms feeding it.

### hDisc lift, brick 3: cocycle trivialization / loop-closure core (2026-06-26)

`Cocycle.lean` (NEW, axiom-clean, in aggregator):
- `exists_cocycle_primitive` — a closed cyclic cocycle `u : Fin(n+1)→ℂ` (`∏ u = 1`) has a discrete
  primitive `c` with `c(i+1)=c(i)·u(i)` for all `i` (wrap included). H¹-vanishing on the circle; `∏u=1`
  closes the wrap. This is the algebraic HEART of the loop-closure bottleneck I'd flagged — it trivializes
  the multiplicative branch-cocycle so the adjusted branches `c i·β i` agree pairwise on overlaps.

hDisc lift bricks done this session: (1) `exists_localInverse_bottcherCoord`, (2) `analyticOnNhd_glue_finite`,
(3) `exists_cocycle_primitive`. These are the three reusable ALGEBRAIC/ANALYTIC atoms of `hliftF`. Remaining:
the GEOMETRIC assembly — define the actual finite patch-cover of the cover annulus, its branches and
consecutive cocycle `uᵢ` (from `analyticOnNhd_glue_unit` + `no_singlevalued_branch_of_dyadic_period` giving
`∏uᵢ=1`), apply (3)→pairwise-agree→(2)→global lift `φ̃c`; then (4) deck map `g`, (5) figure-eight
`φ_{c₂}`-invariance. The atoms are in place; the geometric wiring is the remaining hDisc work.

### hDisc lift, brick 4: abstract loop-glue (cyclic cocycle → global lift) (2026-06-26)

`LoopGlue.lean` (NEW, axiom-clean, in aggregator):
- `exists_global_lift_of_cyclic_cocycle` — combines `exists_cocycle_primitive` + `analyticOnNhd_glue_finite`:
  a cyclic family of analytic branches `β i` on opens `U i` with consecutive cocycle `β i = u i·β(i+1)`,
  only-consecutive overlaps, `∏ u = 1`, assembles to ONE global analytic `F` on `⋃ U i` with `F = c i·β i`
  on each patch. This is `hliftF`'s cover-assembly with the ANALYSIS fully abstracted.

hDisc lift bricks this session: (1) local inverse, (2) finite sheaf-glue, (3) cocycle primitive,
(4) abstract loop-glue [= (2)+(3) consolidated]. The entire global-single-valued-lift construction is now
ONE reusable lemma. **Remaining hDisc = GEOMETRIC INSTANTIATION** of `exists_global_lift_of_cyclic_cocycle`:
build the finite cyclic patch-cover `U i` of the basin annulus + branches `β i`
(`exists_local_bottcherBranch_basin`) + cocycle `u i` (`analyticOnNhd_glue_unit`) with `∏ u i = 1`
(`no_singlevalued_branch_of_dyadic_period`), checking only-consecutive overlaps; then the deck map `g` and
figure-eight `φ_{c₂}`-invariance. The abstract machinery is complete; only the basin-geometry wiring + deck
remain.

### Connection found: LoopGlue is the missing loop-closure complement to GreenChain

`GreenChain.exists_greenConjugate_glue_chain` already iterates `exists_greenConjugate_glue` for a LINEAR
chain — but its hypothesis `hconn` requires each prefix-union ∩ next patch to be CONNECTED (the
contractible/simply-connected case). It does NOT close a loop. The disconnected case's cover is an ANNULUS
(a loop), so the codebase's chain-glue is insufficient there — the genuine gap is exactly the CYCLIC
closure, which `LoopGlue.exists_global_lift_of_cyclic_cocycle` + `Cocycle.exists_cocycle_primitive` now
supply (the `∏ uᵢ = 1` period absorption that the linear chain never needs). So this session's loop-closure
bricks are NON-REDUNDANT — they fill a real hole between `GreenChain` (chain) and `hliftF` (loop).

**Remaining hDisc gap, now pinned exactly:** the GEOMETRIC INSTANTIATION feeding
`exists_global_lift_of_cyclic_cocycle` — construct the finite cyclic patch-cover of the basin annulus,
local green-conjugate branches `Fᵢ` (`exists_local_greenConjugate_basin`), the imaginary cocycle `aᵢ`
(`greenConjugate_sub_imaginary_const`) with `uᵢ = exp(aᵢ)`, `‖uᵢ‖ = 1`, `∏ uᵢ = exp(∑aᵢ) = exp(period) = 1`
(`no_singlevalued_branch_of_dyadic_period` / the circle-lift period), and only-consecutive overlaps; then
`hscale_germ_of_greenConjugate` finishes the deck datum. This is a monolithic basin-geometry construction
(compactness/Lebesgue-number patch cover of the annular loop), not a clean standalone brick. Plus the
figure-eight `φ_{c₂}`-invariance. (Note: collaborator added `ThetaHeat` — parallel work in progress.)

### [RESEARCH LEAD] hyperbolic-c attracting-cycle angle for hGtr (partial, gap noted)

Stress-testing the hGtr blocker via `resonance_order` (good cycles forced `λ^n=2^p`, so `‖λ‖>1`):
- For HYPERBOLIC `c` (an attracting cycle exists in a Fatou component, `‖λ_att‖<1`): if the attracting
  cycle were a GOOD simple-root point of the minimal `P` (nonzero simple root, nonconstant branch), then
  `resonance_order` forces `‖λ_att‖ = 2^{p/n} > 1` — contradicting `‖λ_att‖<1` — proving transcendence
  WITH NO multiplier-spectrum input. The attracting cycle is a SINGLE explicit cycle, so this would close
  the hyperbolic connected case directly.
- GAP: must show the attracting cycle is "good" for `P` — `P(z_i,·)≠0` (use the primitive part of `P`),
  a NONZERO simple root with `w^{2^{p·m}}=w` (needs `exists_pow_fixed_root` + `∂_w P ≠ 0` at that root,
  i.e. `z_i` off `P`'s discriminant locus). If the attracting cycle sits exactly on `P`'s discriminant
  locus, no info. That coincidence is non-generic but, for a SPECIFIC unknown `P`, not yet excluded.
- Covers only HYPERBOLIC `c` (open dense, but the non-hyperbolic connected boundary — uncountable — still
  needs the spectrum). Also the `‖c‖>1` repelling-fixed-point partial (logged earlier) has the analogous
  "is the cycle good" gap.

Net: hGtr's general case still needs the multiplier-spectrum theorem (absent from mathlib), but the
HYPERBOLIC sub-case has a concrete attracting-cycle attack — modulo the discriminant-avoidance gap. A real
partial, honestly bounded; not a full close.

### Refinement: the hGtr gap is "is THIS cycle good for the unknown P", and it is irreducible

Sharpened the hyperbolic angle — and it does not need `resonance_order` at all, which is cleaner:
- An attracting cycle has `‖λ‖<1`, so it is NON-RESONANT directly by `nonresonant_of_norm_lt_one` (and the
  bound transfers through the squaring-orbit exponent `‖λ^m‖=‖λ‖^m<1`). So `false_of_periodic_simpleroot`
  applies to the attracting cycle WITHOUT `resonance_order` — IF it is a good simple root of `P`.
- For PRIMITIVE `P` (content 1), `P(z_i,·)≠0` at every `z_i` (a common-zero `z_i` would divide the content)
  — so the `P(z₀,·)≠0` and `e(z₀)≠0` (finite-locus) conditions are the residue, plus a NONZERO simple root.
- **Irreducible gap:** the attracting cycle is `q` SPECIFIC points; whether one of them has a nonzero
  SIMPLE root of `P` (off `P`'s discriminant + monomial loci) cannot be forced for an unknown `P` — it is
  exactly "this finite cycle dodges `P`'s finite bad loci", which needs MORE cycles (→ spectrum) to
  guarantee. Strong-expansion (`K>2` ⟹ high-period repelling cycles `‖λ‖>2^p`, abundant ⟹ dodge) is
  near-EMPTY for connected `c` (`J_c` near/inside `|z|=1`).

CONCLUSION (exhaustive): every elementary route to hGtr — attracting-cycle, `‖c‖>1` fixed point,
resonance-pinning count, strong-expansion — terminates at the same residue: a SINGLE finite cycle cannot be
guaranteed good for an unknown minimal `P`; guaranteeing it needs infinitely many non-resonant cycles, i.e.
the multiplier-spectrum theorem. That theorem (Zdunik / Bassanelli–Berteloot) is absent from mathlib.
hGtr's general case is genuinely gated on building that library — confirmed from four independent angles.

### CORRECTION + hDisc lift brick 5: green-conjugate loop-glue (2026-06-26)

**Correction:** I had been deferring `hDisc`'s geometric instantiation as "the collaborator's active lane."
Checked `ThetaHeat.lean` — it is the JACOBI THETA HEAT EQUATION (modular-forms calculus for the broader
hypertranscendence programme: `∂_z²Θ = 4πi ∂_τΘ`), ZERO mentions of deck/cover/disconnect/figure/
greenConjugate. So `hDisc`'s Böttcher geometry is NOT the collaborator's lane — it is MINE to build, and I
was deferring on a false premise. Corrected.

`LoopGlue.lean` (brick 5, axiom-clean): `exists_bottcherLift_of_cyclic_greenConjugate` — a cyclic family of
green-conjugate branches `F i` (`Re F i = G_c`) with UNIT overlap cocycle `exp(F i)=u i·exp(F(i+1))`,
`‖u i‖=1`, `∏ u=1`, assembles to the global single-valued `φ̃` on `⋃ U i`, nowhere zero, with
`‖φ̃ w‖ = exp(G_c w)` — EXACTLY the lift `hscale_germ_of_greenConjugate`/`scaling_from_modulus_preserved`
consume. (Strengthened `Cocycle.exists_cocycle_primitive` + `LoopGlue.exists_global_lift_of_cyclic_cocycle`
to expose `‖c i‖ = ∏‖u j‖`, giving the exact modulus.)

hDisc lift abstract machinery COMPLETE (5 bricks): local inverse, finite sheaf-glue, cocycle primitive,
loop-glue, green-conjugate loop-glue. The single-valued `φ̃` lift is now ONE lemma away from a cyclic
green-conjugate cover. **Remaining hDisc (MINE, not collaborator's): the basin cyclic-cover construction**
— produce `U i / F i / u i` with `∏ u=1` from `exists_local_greenConjugate_basin` +
`greenConjugate_sub_imaginary_const` + the period, only-consecutive overlaps — then `hscale_germ` → deck →
`hliftF`, plus figure-eight `φ_{c₂}`-invariance. I'll build the cover construction next.

### hDisc lift bricks 6–7: period-closure + additive interface (2026-06-26)

`Cocycle.lean`: `prod_exp_eq_one_of_sum_eq_int_two_pi_I` — `∑ a i = k·2πi ⟹ ∏ exp(a i) = 1` (the bridge
from the ANALYTIC period to the loop-glue's `∏ u = 1`).
`LoopGlue.lean`: `exists_bottcherLift_of_cyclic_greenConjugate_additive` — takes the green-conjugate cocycle
in EXACTLY the form the tree produces: `F i = F (i+1) + a i` on overlaps (`Re a i = 0`, from
`greenConjugate_sub_imaginary_const`) + the integer period `∑ a i = k·2πi` (from `fractional_period_of_lift`
/ `multiplier_eq_exp_of_period` over the `2ⁿ`-cover loop) → global single-valued `φ̃`, `‖φ̃‖ = exp(G_c)`.

**hDisc lift interface NOW EXACTLY MATCHES the available inputs.** The 7-brick abstract pipeline (local
inverse, sheaf-glue, cocycle-primitive, loop-glue, green-conjugate loop-glue, period-closure, additive
interface) is complete and consumes precisely `greenConjugate_sub_imaginary_const` + the period machinery.
**Residue (mine):** instantiate `U i / F i / a i` from a finite (e.g. 2-sector) cover of the basin cover
annulus, and supply the period value `∑ a i = k·2πi` (= dyadic monodromy `ζ^{2ⁿ}` with `ζ = exp(2πi/2ⁿ)`,
`isPrimitiveRoot_dyadic_multiplier`). Then `hscale_germ_of_greenConjugate` → deck → `hliftF`, + figure-eight.

### hGtr REFRAMED: natural-boundary route, NOT spectrum-blocked (2026-06-26)

Prompted by Michael: I was wrong to call hGtr "multiplier-spectrum blocked" — that blocker is only for my
divisibility/resonance route. hGtr is the CONNECTED case, where `φ_c` is single-valued on the basin
(`isPreconnected_compl_filledJulia`, proven). The natural-boundary route closes it with NO spectrum:
- `NaturalBoundaryContradiction.false_of_basin_branch_interior` (NEW) — interior-`K_c` case via
  `InteriorBoundary.no_unit_modulus_open_continuation` (max-modulus).
- `false_of_modulus_branch` (NEW) — UNIFIED obstruction: any modulus-preserving branch analytic across a
  `K_c` point with basin nearby ⟹ False (dendrite case via `no_continuation_dendrite`, interior via the
  above). Axiom-clean.

**Honest refinement:** the obstruction MECHANISM is now complete (both cases). For the actual `φ_c`
continuation, the modulus `‖g‖=exp(G_c)` holds on the BASIN side always; the **dendrite case** (`K_c` empty
interior near `z₀` — all NON-hyperbolic connected `c`, uncountable) is fully closed by `no_continuation_dendrite`
needing only the basin-side modulus. The **hyperbolic case** (`K_c` has interior): the continuation's
modulus on the `K_c`-interior is the harmonic continuation (`<1`, not `=1`), so the interior natural-boundary
lemma needs modulus-preservation it doesn't have — that sub-case routes through the ATTRACTING cycle instead
(`‖λ‖<1` ⟹ non-resonant for free via `nonresonant_of_norm_lt_one` + `false_of_periodic_simpleroot`), with
the single-cycle "good simple root" gap. So hGtr is spectrum-FREE; remaining = the `φ_c` algebraic
continuation reaching a Julia point (dendrite) + the attracting-cycle good-root lemma (hyperbolic).

### hGtr spectrum-free capstone built (2026-06-26)

`ConnectedTranscendence.phiMero_transcendental_of_dendrite_input` (NEW, axiom-clean): connected-case
`φ_c`-transcendence reduced to the NATURAL-BOUNDARY input — per minimal relation `P`, a dendrite Julia
point `z₀` (simple root `(z₀,w₀)`) reached by a basin branch `β` (continued `φ_c`) with `‖β‖=exp(G_c)` —
via `false_of_basin_branch_dendrite`. **NO multiplier-spectrum / non-resonant-cycle input.** This replaces
the earlier (wrong) "hGtr is spectrum-blocked" with a spectrum-free reduction.

So both connected-case capstones now exist: `phiMero_transcendental_of_periodic_input'` (resonance route,
needs a non-resonant cycle) AND `phiMero_transcendental_of_dendrite_input` (natural-boundary route, needs
the basin continuation reaching a dendrite Julia point — spectrum-free). The latter is the right one for
the connected case.

**Shared remaining core (spectrum-free, mine):** the basin continuation `β` of `φ_c` from `escapeOpen`
across the connected basin to `J_c` (single-valued for connected `J_c` — trivial monodromy; the `2ⁿ`-cover
for disconnected). Built from `GreenChain` (chain glue, done) + my loop-glue (loop closure, done) +
`exists_local_greenConjugate_basin` over the escape-level chain (`isPreconnected_preimage_escapeLevel`,
done). This `β` closes hGtr-dendrite (above) AND feeds hDisc's `hliftF`. No missing infrastructure.

---

## Dendrite-route hβlim machinery — COMPLETE (Carathéodory-free), 2026-06-26

The connected-case capstone `phiMero_transcendental_of_dendrite_input` reduces `φ_c`-transcendence to a
single `hinput`: at each minimal relation `P`, a dendrite Julia point `z₀` reached by a basin branch `β`
with limit `w₀` (simple root), the relation, and the modulus `‖β‖=exp G_c`. The hardest part — `hβlim`
(that `β` HAS a boundary limit at `z₀`) — is now fully built in Lean WITHOUT Carathéodory boundary
extension, using only the *hypothetical algebraicity* of `φ_c` (the relation `P`) to pin the limit.

Added (all axiom-clean = [propext, Classical.choice, Quot.sound]):
- `NaturalBoundaryContradiction.lean`:
  - `norm_eq_one_of_open`, `norm_eq_of_norm_eq_on_open` — modulus propagation across a connected basin
    (a unit-modulus open point is a local max → locally constant → constant on the connected set).
  - `eq_one_branch_of_valued_in_separated` — branch following: a continuous map valued in finitely many
    pairwise-separated continuous branches, on a preconnected set, equals ONE branch (clopen partition).
  - `tendsto_within_of_eqOn` — `β = w` on `U`, `w` continuous at `z₀` ⟹ `β → w z₀` along `𝓝[U] z₀`.
  - `root_eq_of_card_branches` — exhaustion: a degree-`d` poly with `d` known distinct roots has no others.
- `ConnectedTranscendence.lean`:
  - `relation_hasDerivAt_w` — the relation's `w`-derivative = fibre polynomial's formal derivative.
  - `eval_derivative_ne_zero_of_separable` — a root of a separable poly is simple (coprime `q,q'`).
  - `fiber_natDegree_eq` — fibre degree is constant `= P.natDegree` where the leading coeff doesn't vanish.
  - `eventually_separated` — distinct germs at `z₀` stay pairwise distinct on a neighbourhood.
  - `exists_branch_family` — from a separable fibre at `z₀` (leading coeff ≠0): `N=P.natDegree`
    pairwise-separated analytic root-branches on a ball, each satisfying the relation, constant fibre degree.
  - `eqOn_branch_of_relation` — `β` satisfying the relation on a preconnected basin `U`, with the branch
    family present, follows ONE branch `w k` on all of `U` (exhaustion + branch following).
  - `dendrite_branch_limit` — CAPSTONE: family + basin branch `β` on a preconnected basin-nbhd `U` of `z₀`
    ⟹ the full `hβlim` + `hroot` + `hpartial` + `hd` of `false_of_basin_branch_dendrite` (`𝓝[U]z₀ =
    𝓝[basin]z₀` via `nhdsWithin_inter_of_mem`). Only `hβmod` remains, supplied by the chain `β`.

Remaining inputs to discharge the dendrite `hinput` (now the only gaps for connected `hGtr`):
1. The chain branch `β` with `hβmod` (= `‖β‖=exp G_c`) + `hβrel` on a connected basin-nbhd `U` reaching
   `z₀` — via `GreenChain.exists_bottcher_on_chain` along a path from `escapeOpen` to near `z₀`.
2. `z₀` a dendrite Julia point off the finite bad-set (fibre separable + leading coeff ≠0) — generic for
   the uncountable dendrite of a non-hyperbolic connected `c`.
3. Local basin connectivity at `z₀`: `U ∈ 𝓝[basin] z₀` preconnected (locally-connected `J_c`).

Strategic finding (banked): the modulus route `phiMero_transcendental_of_repelling_input` (need `‖λ‖>2^p`)
is FRAGILE — `cap(K_c)=1` forces period-`p` multipliers asymptotically to the resonance modulus
`‖λ‖≈2^p`, so strongly-repelling cycles are not guaranteed for general connected `c`. The dendrite route
above sidesteps the multiplier spectrum entirely; it is the correct connected-case attack.

---

## Connected case localized to ONE missing analytic theorem: the Poincaré lemma, 2026-06-26

The single-valued Böttcher coordinate `φ_c` on the (annular, π₁=ℤ) connected basin is the object that gates
`hGtr` (connected transcendence) and `hDisc` (the dyadic lift). It is now localized to one mathlib-gap brick.

`GreenLogDeriv.lean` (new, axiom-clean): the global logarithmic derivative `ω = φ_c'/φ_c = 2·∂G_c`.
- `greenLogDeriv c` := Wirtinger `∂` of `G_c`.
- `differentiableOn_greenLogDeriv` — `ω` holomorphic on the whole basin (from `harmonicOnNhd_greenLimit_basin`
  + mathlib `HarmonicAt.differentiableAt_complex_partial`). Single-valued even though `log φ_c` is not.
- `isConservativeOn_greenLogDeriv` — `ω` conservative on the basin (`DifferentiableOn.isConservativeOn`).

Reduction (all prerequisites IN the tree / mathlib): single-valued `φ_c = exp F` on a simply-connected basin
region `V` ⟺ a primitive `F` of `ω` on `V` with `Re F = G_c`. The ONLY missing analytic step is the
**Poincaré lemma**:  `IsConservativeOn ω V + IsSimplyConnected V ⟹ IsExactOn ω V`.
Mathlib has exactness only on balls (`DifferentiableOn.isExactOn_ball`) and `ℂ` (`isExactOn_univ`), NOT on
general simply-connected domains. This is the genuine remaining frontier brick for the connected case.

With it: `F` primitive on `V` ⟹ `Re F = G_c` (harmonic-conjugate identity, `F' = ω = 2∂G_c`) ⟹ `β := exp F`
has `‖β‖ = exp G_c` (`hβmod`); anchored to `escapeOpen` where `β = φ_c`, identity gives `hβrel`. Then
`dendrite_branch_limit` (already built) supplies `hβlim`+simple-root, closing `false_of_basin_branch_dendrite`.

Remaining for connected `hGtr` (in dependency order):
1. **Poincaré lemma** `IsConservativeOn + IsSimplyConnected ⟹ IsExactOn` (mathlib gap; homotopy invariance of
   the conservative integral). THE enabler — also unlocks `hDisc` (same primitive on the 2ⁿ-cover, period 2πi/2ⁿ).
2. `IsSimplyConnected (ball z₀ r ∩ basin)` at a dendrite Julia point (a small ball does not enclose `K_c`;
   `K_c`-side is a dendrite/tree). Deep topology.
3. Harmonic-conjugate identity `Re F = G_c` from `F' = ω = 2∂G_c` (Cauchy–Riemann bookkeeping).
Separately: `hrig` (Eremenko–van Strien rigidity, `TranscendentalOverAdjoin`) is an independent major theorem.

### Post-Poincaré path now fully verified (the modulus bridge), 2026-06-26

Added to `GreenLogDeriv.lean` (axiom-clean):
- `eqOn_const_of_hasFDerivAt_zero` — a real function with zero `fderiv` on an open preconnected set is
  constant (clopen level-set argument).
- `re_primitive_sub_green_const` — **harmonic-conjugate identity**: any holomorphic primitive `F` of
  `ω = greenLogDeriv c` on a preconnected basin set has `Re F − G_c` constant (Cauchy–Riemann:
  `F' = ω = 2∂G_c` ⟹ `∇(Re F) = ∇G_c`).

Consequence: the ENTIRE post-Poincaré path is now verified. Given `F` with `F' = ω` on a simply-connected
basin region (anchored to `escapeOpen` where `F = log φ_c`, fixing the constant to 0): `Re F = G_c` ⟹
`‖exp F‖ = exp(Re F) = exp G_c` (`Complex.norm_exp`) — the modulus `hβmod`; and `β := exp F` equals `φ_c`,
satisfying the relation. Feeds `dendrite_branch_limit` ⟹ `false_of_basin_branch_dendrite` ⟹ `hGtr`.

So the connected case is reduced to ONE Lean theorem — the **Poincaré lemma** (task #84) — plus the
topological inputs `IsSimplyConnected (ball z₀ r ∩ basin)` (#83) and the deep-exterior anchor. `hDisc` reuses
the same `ω`-primitive on the 2ⁿ-cover. `hrig` (E–vS) stays independent.

---

## Poincaré lemma CONSTRUCTED for chain-coverable regions + modulus spread, 2026-06-26

Found that mathlib's `CurveIntegral/Poincare.lean` actually has the **convex** Poincaré lemma
(`Convex.exists_forall_hasDerivWithinAt`) and C²-homotopy invariance (more than the WIP comment implied).
Built on top of it, in `GreenLogDeriv.lean` (all axiom-clean; module builds, 8508 jobs):

- `primitive_sub_const` — two primitives of a form differ by a constant (H¹-vanishing step).
- `exists_primitive_glue` — atomic glue of two local primitives over a connected overlap.
- `exists_primitive_glue_chain` — iterate → primitive of any holomorphic form on a chain-coverable region.
- `exists_primitive_greenLogDeriv_chain` — specialize to `ω` + basin balls (local primitives from mathlib's
  `DifferentiableOn.isExactOn_ball`): primitive of `ω` on any basin ball-chain with connected prefix-overlaps.
- `norm_eq_exp_green_of_eqOn_open` — **harmonic identity modulus spread**: `‖g‖ = exp G_c` on a small open
  `C` propagates to the whole connected basin region (`AnalyticAt.harmonicAt_log_norm` + `HarmonicAt.analyticAt`
  + real-analytic identity). So the chain need only reach ONE spot near `z₀`; the modulus then spreads in 2-D.

Net: the connected-case blocker is no longer an abstract open mathlib theorem. It is reduced to a **concrete
point-set-topology construction**: a finite chain of basin balls from `escapeOpen` to a spot near a Julia
point `z₀`, with connected prefix-overlaps (a simple arc in the open connected basin, cover by small balls
with non-adjacent balls disjoint ⟹ prefix-overlap = consecutive lens = connected). Then
`exists_primitive_greenLogDeriv_chain` → `exists_fullBottcherBranch_of_primitive` → `β`, modulus spread to
`ball z₀ r ∩ basin`, `dendrite_branch_limit` → `false_of_basin_branch_dendrite`. `hDisc` reuses the same
primitive machinery on the 2ⁿ-cover. Remaining: the arc/cover construction (elementary topology) + `hrig` (E–vS).

---

## hF/primitive hypothesis DISCHARGED unconditionally on the right half-plane, 2026-06-26

Using mathlib's **convex** Poincaré lemma `Convex.exists_forall_hasDerivWithinAt` (in `CurveIntegral/Poincare.lean`):
- `nonempty_filledJulia` — `K_c` contains a fixed point (axiom-clean).
- `exists_bottcherBranch_rightHalfplane` — UNCONDITIONAL: on `R = {Re z > M}` (`M = max Re over K_c`,
  convex, `⊆` basin), `ω = greenLogDeriv` has a primitive (convex Poincaré, NO hypothesis), so there is a
  single-valued branch `β`, analytic, nonvanishing, with `‖β‖ = exp(greenFunctionDyn c)`. The `hF`/primitive
  hypothesis of `exists_bottcherBranch_of_primitive` is thereby ELIMINATED on a concrete basin region.

This is the first unconditional construction of the continued single-valued Böttcher coordinate (modulus side).
The max-Re point `z₀ ∈ ∂R ∩ J_c` is the natural-boundary anchor. Remaining to close the dendrite sub-case:
the relation-carrying version (escape-ball anchor inside `R`), match the algebraic branch `g` on
`R ∩ ball(z₀,r) ∩ basin`, spread the modulus (`norm_eq_exp_green_of_eqOn_open`) to `ball(z₀,r) ∩ basin`,
then `false_of_basin_branch_dendrite`. The interior sub-case (`K_c` has interior — touches density of
hyperbolicity) and `hrig` (E–vS) remain genuinely harder.

---

## Three-value Montel sub-lane — progress 2026-06-26 (Jacobi identity PROVEN)

The fundamental normality test (`OmittingNormal.normal_of_omitting_lift`, proven) reduces three-value
Montel to: the modular `λ` provides holomorphic lifts of omitting families = `IsCoveringMap λ` onto
`ℂ∖{0,1}`. Two inputs feed that covering: (a) `λ : ℍ → ℂ∖{0,1}` well-defined; (b) the covering itself.

**DONE this session (all axiom-clean `[propext, Classical.choice, Quot.sound]`, zero sorry):**
- `Bottcher2Cusp.quarticDefect_eq_zero` (QuarticModularForm.lean) — **the Jacobi quartic identity
  `F = θ₃⁴−θ₂⁴−θ₄⁴ ≡ 0` is now a THEOREM**, no longer a hypothesis. Route that worked cleanly:
  `F∣[2]γ = ±F` for all `γ∈SL(2,ℤ)` (`quarticDefectH_slash_pm`) ⟹ `F²∣[4]γ = F²` ⟹
  `F² ∈ CuspForm 𝒮ℒ 4`; and `S₄(SL(2,ℤ)) = 0` (`CuspForm.rank_eq_zero_of_weight_lt_twelve`, 4<12)
  forces `F² ≡ 0`, hence `F ≡ 0`. (The `F⁶→weight-12→order≥2` / NormTrace route was avoidable.)
- `Bottcher.modularLambda_omits_zero_one'` / `_mem_compl_zero_one'` — **input (a): `λ : ℍ → ℂ∖{0,1}`
  unconditionally** (the `hquartic` hypothesis of `QuarticCusp` is discharged).
- `ModularLambdaUnconditional.lean` — the `Γ(2)`-Hauptmodul / anharmonic deck relations, now
  unconditional: `modularLambda_S'` (`λ(−1/τ)=1−λ`), `_T_mul'`/`_T_eq'` (`λ↦λ/(λ−1)`),
  `_anharmonic'`, `_at_I'` (`λ(I)=1/2`).

**NEXT BRICK (precisely located): `λ' ≠ 0` on `ℍ` (λ is a local biholomorphism).**
Reduction done on paper: `λ = (θ₂/θ₃)⁴ ⟹ λ' = 4θ₂³·W₂₃/θ₃⁵` where `W₂₃ := θ₂'θ₃ − θ₂θ₃'`. With
`θ₂,θ₃,θ₄ ≠ 0` (have `thetaProduct_ne_zero_of_im_pos`) and `λ∉{0,1}` (have), `λ'≠0` ⟺ the single
classical theta **Wronskian identity**
        `W₂₃ = θ₂'θ₃ − θ₂θ₃' = (πi/4)·θ₂θ₃θ₄⁴`   (equivalently `λ'/λ = πi·θ₄⁴`).
This is the gate. The `dim = 0/1` q-expansion trick used for the Jacobi identity does NOT transfer
(W₂₃ and θ₂θ₃θ₄⁴ are weight-3 HALF-integral forms; mathlib lacks half-integral weight). Two attack
routes for next session: (i) direct from the theta-sum derivatives (`hasDerivAt_thetaTwo/Three`) +
heat equation (`ThetaHeat.tsum_thetaHeatTerm_eq`) — hard sum manipulation; (ii) reduce to the Jacobi
derivative formula `θ₁'(0)=πθ₂θ₃θ₄` and a known nullwert log-derivative relation.

**REMAINING after λ'≠0 (the deep walls):**
- `IsCoveringMap λ`. Decomposes `λ = (homeo) ∘ (ℍ → ℍ/Γ(2))`. mathlib has
  `isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul` AND
  `Subgroup.IsArithmetic.properlyDiscontinuous` (Γ(2) on ℍ) — BUT the GL-action of Γ(2) is NOT free
  (`−I` acts trivially ⟹ `IsCancelSMul` fails, free locus empty); must pass to `PΓ(2)=Γ(2)/{±I}`.
  Then the deep Hauptmodul homeo `ℍ/Γ(2) ≅ ℂ∖{0,1}` (λ surjective onto `ℂ∖{0,1}` + λ separates
  Γ(2)-orbits) — essentially Picard for the modular function; mathlib has none of this.
- Then: three-value Montel → Julia repelling-density → E–vS rigidity `TranscendentalOverAdjoin`
  (the single remaining hypothesis of `q62_both_connected` in Rigidity.lean).

### Update (same session): `λ' ≠ 0` local-biholo brick landed (ModularLambdaLocalBiholo.lean)

All axiom-clean. `hasDerivAt_modularLambda` is **unconditional**: `λ'(τ) = 4(θ₂/θ₃)³·(θ₂'θ₃−θ₂θ₃')/θ₃²`
from the nullwert derivatives. The local-homeomorphism datum for `IsCoveringMap λ` is now reduced to
**exactly one** named theta identity:
  `ThetaWronskian23 : θ₂'θ₃ − θ₂θ₃' = (πi/4)·θ₂θ₃θ₄⁴`
under which `deriv_modularLambda_eq[_lambda]` gives `λ' = πi·θ₂⁴θ₄⁴/θ₃⁴ = πi·θ₃⁴·λ(1−λ)` and
`modularLambda_deriv_ne_zero` gives `λ'≠0` (all factors nonzero; `λ(1−λ)≠0` is the proven quartic
identity). So the local-biholo lane is fully proven *modulo* `ThetaWronskian23`, carried as a named
hypothesis in the `TranscendentalOverAdjoin` style.

Next attack on `ThetaWronskian23` (the half-integral weight-3 gate): the cleanest non-half-integral
route is the **heat equation** — `θ₂'`, `θ₃'` are `(πi)·`(2nd `z`-derivatives via
`ThetaHeat.tsum_thetaHeatTerm_eq`); the combination `θ₂'θ₃−θ₂θ₃'` should collapse against the addition
formula for `θ` to the product `θ₂θ₃θ₄⁴`. Alternatively the Jacobi triple-product / the derivative
formula `θ₁'(0)=πθ₂θ₃θ₄` plus a nullwert log-derivative relation. This is the one open analytic input
of the three-value-Montel→covering brick.

### KEY REFRAMING of `ThetaWronskian23` → integral weight 6 (found same session)

With `u=θ₂⁴, v=θ₃⁴, w=θ₄⁴` (each a weight-2 Γ(2) modular form, INTEGRAL weight; `v=u+w` is the
proven quartic identity), `ThetaWronskian23` is *equivalent* (divide by `4θ₂³θ₃³≠0`) to the
INTEGRAL weight-6 identity
        `u'v − uv' = πi · u v w`     i.e. the first Rankin–Cohen bracket `[θ₂⁴, θ₃⁴]₁ = πi·θ₂⁴θ₃⁴θ₄⁴`.
The Wronskian `u'v−uv'` of two weight-2 forms is a genuine weight-6 modular form (Rankin–Cohen — the
cocycle terms cancel), so BOTH sides are weight-6 Γ(2) forms. This escapes the half-integral wall: the
`dim`/Sturm q-expansion technique that proved the Jacobi identity becomes available IF a Γ(2) Sturm
bound is built (mathlib has only level-one) — or push both sides through `NormTrace`/the difference's
cusp behaviour to a level where mathlib's machinery applies. This is the concrete next attack on #26.
