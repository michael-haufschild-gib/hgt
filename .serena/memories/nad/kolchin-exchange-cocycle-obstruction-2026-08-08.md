# Card `kolchin-exchange-cocycle-obstruction` — IN PROGRESS (2026-08-08)

Card: `docs/drafts/pipeline/2-fully-proven/nad/kolchin-exchange-cocycle-obstruction.md`.
Open Lean gate: *"formalize Lechner's analytic/Hilbert intertwiner and the conjugated
creation-operator formula"*.  (Other open gates are audits / physical-admissibility — not Lean.)

## Already in the tree

`HTGeometry/KolchinExchangeGaugeObstruction.lean` proves the **algebraic** obstruction (7)–(10):
`DifferentialAlgEquiv`, `differentialAlgebraicOver_ratio_of_daExchangeGaugeEquivalent`,
`not_daExchangeGaugeEquivalent_of_ratio_hypertranscendental`,
`no_daExchangeGauge_trivialization_of_hypertranscendental`,
`halfPhase_hypertranscendental_of_exchangeLaw`.  Do not rebuild.

## Built 2026-08-08 — `HTGeometry/LechnerPairMultiplier.lean`

`pairMultiplier y θ n = ∏_{k<l<n} y (θ k − θ l)` — equation (5).  Indexed over `ℕ` with
`θ : ℕ → ℝ` and nested `Finset.range`, which makes both recursions `Finset.prod_range_succ`
one-liners; a `Fin n × Fin n` filtered-pair definition would need a reindexing bijection instead.

* `pairMultiplier_zero/one/two`, `pairMultiplier_succ` (new **last** particle).
* **`pairMultiplier_shift`** = (10a): new **first** particle ⟹ multiply by
  `∏_{j<n} y (θ 0 − θ (j+1))`, shifted multiplier untouched.  Proof: induction + `prod_range_succ'`
  (peels the *first* factor) against `prod_range_succ`.  **This string is exactly the dressing
  factor of (10b)** — the conjugated creation operator's algebraic content.
* **`norm_pairMultiplier`** — unimodular half-phase ⟹ unimodular multiplier (unitarity at each `n`).
* **`exchangeLaw_of_pairMultiplier_swap`** = (6): `S = ε·y/(y∘neg)` is the swap ratio of the
  two-particle multiplier.  The swap is `fun k => θ (1 - k)` using ℕ-subtraction (0↦1, 1↦0).

## Second instalment (same file)

* `pairMultiplier_ne_zero`, **`norm_pairMultiplier_mul`** — multiplication by the multiplier
  preserves modulus ⟹ pointwise isometry (unitarity of `Y_n` before any measure-theoretic packaging).
* **`intertwine_two`** — the trivialization's content: `ψ(b,a) = S(a−b)ψ(a,b)` becomes
  `y(b−a)ψ(b,a) = ε·(y(a−b)ψ(a,b))`.  Only (6) is used.
  **field_simp trap**: `hy : ∀ t, y t ≠ 0` is not instantiated by `field_simp` — add explicit
  `have h1 : y (b-a) ≠ 0 := hy _` etc. first.
* **`intertwine_two_pairMultiplier`** — same, written through the multiplier.

## Third instalment — the n-particle intertwining (same file)

* `swapIdx m k = if k = m then m+1 else if k = m+1 then m else k`; `swapAt m θ = θ ∘ swapIdx m`.
  **Design choice that made it cheap**: defining `swapAt` as *precomposition* makes
  `swapAt m θ k = θ (swapIdx m k)` true by `rfl`, so `Finset.prod_nbij'` along the involution
  closes `prod_range_swapAt` with `rw [swapAt_apply]` as the value step.
* **`pairMultiplier_swapAt`** — the adjacent transposition ratio
  `Y_n(swap θ)·y(θ_m − θ_{m+1}) = Y_n(θ)·y(θ_{m+1} − θ_m)`.  Induction from `n = m+2` via
  `Nat.le_induction`.  **Write both branches as explicit `have`s** — chained
  `rw [pairMultiplier_succ, …]` picks the wrong occurrences and `ring` then fails.
* **`intertwine_swapAt`** — the gate's theorem: an `S`-exchange section becomes a constant-`ε`
  section after multiplication by the multiplier.  Adjacent transpositions generate, so this *is*
  the intertwining of the two representations.

## Fourth instalment — the `L^p` isometry layer (same file)

* **`eLpNorm_mul_of_norm_eq_one`** — multiplication by a unimodular function preserves *every*
  `L^p` seminorm.  One line from `eLpNorm_congr_norm_ae`: equal pointwise modulus, so neither `p`
  nor the measure enters.  (Needs `open scoped ENNReal` for `ℝ≥0∞`.)
* `memLp_mul_of_norm_eq_one`, **`eLpNorm_pairMultiplier_mul`** — the intertwiner is an isometry at
  each particle number, measure-theoretically and not only pointwise.

## Fifth instalment — `UnimodularMulLp.lean` (bundled operator)

* `eLpNorm_aeEqFun_mul`, `mulLp`, `coe_mulLp`, `norm_mulLp`, **`mulLpₗᵢ : Lp ℂ p μ →ₗᵢ[ℂ] Lp ℂ p μ`**.
* `aeEqFun_mul_add`, `aeEqFun_mul_smul` — **mathlib gives `α →ₘ[μ] ℂ` a `Mul` and an `Add` but no
  `Distrib` instance**, so `mul_add` / `mul_smul_comm` are unavailable; prove them through `coeFn`
  with `AEEqFun.ext` + `filter_upwards` + `simp only [coeFn lemmas, Pi.*_apply]` + `ring`.
* `Lp`'s normed structure needs **`[Fact (1 ≤ p)]`**; the seminorm-level lemmas do not (use
  `omit [Fact (1 ≤ p)] in`, placed **before** the docstring).
* `Lp` lives in `Mathlib/MeasureTheory/Function/LpSpace/Basic.lean` — importing only
  `LpSeminorm/Basic` gives `eLpNorm` but not `Lp`.

## Sixth instalment — the operator on rapidity coordinates (same file)

* `embedFin`, `pairMultiplierFin`, `norm_pairMultiplierFin`.
* **`pairMultiplierFin_succ`** — (10a) in `Fin n → ℝ` coordinates; this *is* (10b)'s dressing string.
* `measurable_embedFin_apply`, `measurable_pairMultiplierFin` (`Finset.measurable_prod`; must
  `rw` an explicit `hfun : … = fun θ => ∏ … := rfl` first or the instance search gets stuck on
  `MeasurableMul₂ ?m`).
* **`lechnerIntertwiner`** — the bundled `Lp ℂ p (volume : Measure (Fin n → ℝ)) →ₗᵢ[ℂ] …` for a
  measurable unimodular half-phase.

## State of the gate

Formalized in full **at each particle number**: the intertwiner is an operator, it is isometric, it
converts the `S`-exchange law into the constant law (`intertwine_swapAt`), and the conjugated
creator's dressing string is `pairMultiplierFin_succ`.

## Seventh instalment — **THE LEAN GATE IS CLOSED**

* `HTGeometry/LpFamilyIsometry.lean` — **mathlib has `lp` and `lp.single` but no componentwise
  family map**.  `memℓp_of_norm_eq` + **`lpFamilyIsometry`** (family of linear isometries ⟹ one on
  the `lp` sum, finite exponent).  General infrastructure, reusable.
* `HTGeometry/LechnerFockIntertwiner.lean` — `rapidityFock = lp (fun n => L² (Fin n → ℝ)) 2`;
  **`lechnerFockIntertwiner`** = `Y = ⊕ₙ Yₙ` as a linear isometry of it;
  **`conjugated_creation_multiplier`** = equation (10b).

Gate items and their declarations:
- intertwiner as an operator → `lechnerFockIntertwiner`, `norm_lechnerFockIntertwiner`
- it converts `S`-exchange into constant `ε` → `intertwine_swapAt`
- conjugated creation formula (10b) → `conjugated_creation_multiplier`

**Card's remaining gates are research/review, not formalization**: novelty audit, physical
admissibility theorem, localization/OPE invariant.  Consider stage-3 promotion only if the project
treats those as non-blocking (the kubalalika and quasi-abelian cards were promoted with an open
novelty audit).

### (superseded) former item 1
1. The **n-particle transposition ratio**: `Y_n(σθ)/Y_n(θ) = y(θ_{i+1}−θ_i)/y(θ_i−θ_{i+1})` for an
   adjacent swap.  Needs reindexing the nested-`range` pair product along the involution
   (`Finset.prod_nbij` or a bijection on pairs) — the only genuinely fiddly piece left.
2. The direct sum over particle number as a unitary between Fock spaces (measure-theoretic wrapper).
