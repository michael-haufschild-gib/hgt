# The weld-class table: obstruction classes of generator pairs as one homomorphism

- **ID:** weld-class-table
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) — `[PROVED HERE]`, axiom-clean. Executes conjecture H3 of the RHTower status report (`docs/reports/rhtower_status_0707.md` §3): compute `obstructionClass` for generator pairs beyond `(∂_s, {σ_p})`, and turn the case-by-case Mahler results into a uniform statement.
- **Statement:** The abstract second-cohomology obstruction machinery (`OmegaObstruction.lean`) is instantiated on concrete generator pairs. The whole weld-class table is a **single injective group homomorphism** `weldClassHom : ℝ ↪ H²`, `θ ↦ [weldCocycle θ]`, where `θ` is the pair's logarithmic *conversion constant*. Every entry is read off `θ`: shift `→ 0` (trivial), Mahler `σ_k → log k` (nonzero, uniform), prime `σ_p → log p` (nonzero). For two bases the obstruction rank is governed by an elementary (transcendence-free) arithmetic dichotomy, and two distinct primes give a genuine rank-two piece of the founding weld.

## What is proved (`formal/GaloisForLFunctions/RHTower/WeldClassTable.lean`, 35 declarations)

**§1 The universal weld cocycle.** `WeldGroup = Multiplicative (ℤ²)` with the trivial ℝ-action; `weldCocycle θ` is the bilinear (Heisenberg) 2-cocycle whose commuting-pair antisymmetry `ω(∂,σ) − ω(σ,∂)` equals `θ` (`weldCocycle_antisymm`). `weldCocycle_isTwoCocycle` (any bilinear form is a cocycle for the trivial action). **The weld-triviality criterion** `weld_obstruction_ne_zero_iff : obstructionClass ≠ 0 ↔ θ ≠ 0`. `weld_latticeValued` — the cocycle is valued in the rank-one lattice `⟨θ⟩`.

**§2–3 The table + uniform Mahler.** `shift_weld_obstruction_eq_zero` (the shift `σ = exp ∂` is the derivation's own time-one flow, `θ = 0`, obstruction **zero**); `mahler_weld_obstruction_ne_zero` (`θ = log k ≠ 0` for `k ≥ 2`, obstruction **nonzero**); `prime_weld_obstruction_ne_zero` (`θ = log p`). `mahler_weld_uniform` — the single `∀ k ≥ 2` statement of which the case-by-case Mahler-independence results (u0/Böttcher corpus) are instances.

**§4 The log–power bridge.** `weld_logRelation_iff`: `a·log j + b·log k = 0 ↔ jᵃ kᵇ = 1` (transcendence-free). `weld_two_base_indep_iff` — the two conversion constants are `ℤ`-independent (rank-two obstruction) exactly when the bases are multiplicatively independent. The obstruction rank is an *elementary arithmetic* invariant.

**§5 The whole table is one homomorphism.** `weldClassHom : ℝ →+ H²` with `weldClassHom_injective` and `weldClassHom_mul_base` (`σ_j ∘ σ_k = σ_{jk}` ⟹ classes **add**). `ℝ` embeds in `H²` as the line of weld classes; each generator pair's entry is the image of its log-scale.

**§6 Rank at the level of classes.** `weldClass_two_base_indep_iff` transports the arithmetic dichotomy through the injective homomorphism to `H²`.

**§7 Integration with the founding prime–archimedean weld.** `weld_isLatticeValued_primeLog_iff : IsLatticeValued primeLogLattice (weldCocycle θ) ↔ θ ∈ primeLogLattice` — a pair's weld is a sublattice of the founding `(∂_s, {σ_p})` weld iff its conversion constant is a `ℤ`-combination of `log p`'s. `prime_weld_isLatticeValued_primeLog` (each prime shift is a rank-one sublattice). `two_prime_log_indep` / `two_prime_weld_class_indep` — from the unique-factorization independence of `{log p}` **already in the tree** (`primeIndexedLogExpansion_coeff_eq_zero_of_sum_eq_zero`), two distinct primes give a **rank-two** independent piece: the founding weld is provably not rank-one. `log_nat_mem_primeLogLattice` / `mahler_weld_isLatticeValued_primeLog` — the **whole integer Mahler column sits inside the founding weld**: for every base `k ≥ 1`, `log k = Σ vₚ(k)·log p ∈ primeLogLattice`, so each Mahler weld is a sublattice of `(∂_s, {σ_p})`. **`primes_weld_class_indep` — the founding weld has unbounded rank**: the entire family `{weldClass (log p) : p prime}` is `ℤ`-linearly independent in `H²`, so `(∂_s, {σ_p})` is countably infinite-dimensional — the *maximal* weld, of which every single generator pair is a rank-one slice.

## Constraint, not flow
Every object is a cohomology class (obstruction to a global section) and its lattice value — a fixed constraint invariant of the generator pair. No joint carrier / solution is constructed. The generators are abstract group elements; the pair's non-commutation is read as the antisymmetry, not propagated by any flow.

## Novelty / significance
Unifies prime, Mahler, and shift welds into one parametrized cocycle whose class is governed by a single conversion constant, exhibits the entire table as an injective homomorphism `ℝ ↪ H²`, and reduces the two-base obstruction rank to elementary multiplicative independence — bridging the cohomological obstruction language to elementary multiplicative number theory. Pillar (iii) of the branch (the new category `𝓜⁺` where `∂` and `{σ}` coexist) is populated by computation of the actual classes, not case-by-case. The Mahler column, previously case-by-case in the u0/Böttcher corpus, becomes one theorem.

## Lean
`RHTower.{WeldGroup, weldCocycle, weldCocycle_isTwoCocycle, weldCocycle_zero, weldGenD, weldGenS, weldGen_comm, weldCocycle_antisymm, weld_obstruction_ne_zero_iff, weld_latticeValued, shift_weld_obstruction_eq_zero, mahler_weld_obstruction_ne_zero, prime_weld_obstruction_ne_zero, mahler_weld_uniform, weld_logRelation_iff, weld_two_base_indep_iff, weldCocycle_add, obstructionClass_add, cocycleOf_weldCocycle_add, weldClassHom, weldClassHom_apply, weldClassHom_eq_zero_iff, weldClassHom_injective, weldClassHom_mul_base, weldClass_two_base_indep_iff, weldCocycle_genD_genS, weld_isLatticeValued_primeLog_iff, prime_weld_isLatticeValued_primeLog, log_nat_mem_primeLogLattice, mahler_weld_isLatticeValued_primeLog, two_prime_log_indep, two_prime_weld_class_indep, primes_weld_class_indep}` in `formal/GaloisForLFunctions/RHTower/WeldClassTable.lean`, imported in the `RHTower` umbrella. `lake build` green, axiom-clean (`propext, Classical.choice, Quot.sound` only), lint pass.

## Open continuations
- **n-base rank law**: the weld classes of a finite base set are `ℤ`-independent iff the bases are multiplicatively independent iff the multiplicative subgroup they generate in `ℚˣ` is free of full rank — generalizing §6 (needs `LinearIndependent`-over-`ℤ` machinery for arbitrary `n`).
- **Polarization gate**: feed the weld class through `ClassInducesJ` to the Krein/signature structure (couples the weld-class table to the T1 inertia = charge target).

## Log
- 2026-07-08 — created in 3-formalized; H3 executed: concrete obstruction classes for the generator-pair table, the `ℝ ↪ H²` homomorphism, the rank dichotomy, the founding-weld integration (whole Mahler column ⊂ founding weld), and the punchline that the founding prime weld has unbounded rank (countably infinite-dimensional). Lean axiom-clean, 35 declarations.
