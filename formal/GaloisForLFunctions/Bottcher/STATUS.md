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

## VERIFIED so far (sorry-free, from Mathlib up): 11 modules, 55 results
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
