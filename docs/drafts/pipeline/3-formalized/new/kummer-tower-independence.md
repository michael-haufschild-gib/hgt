# u₀ ⟂ the whole finite Böttcher root tower of ψ (Kummer-layer independence)

- **ID:** kummer-tower-independence
- **Stage:** 3-formalized (fully proven, axiom-clean, non-vacuous with a concrete branch)
- **Type:** THEOREM (Lean, unconditional) — grade **BRIDGE**
- **Source:** the "full finite Böttcher tower" strengthening of `m-step-window-branch`; requested as
  the next stronger theorem after the m-step independence closed.
- **Axioms:** `[propext, Classical.choice, Quot.sound]` only (verified by `#print axioms`).
- **Files:** `formal/GaloisForLFunctions/U0/U0MStepKummer.lean` (algebraic descent),
  `U0KummerBranch.lean` (analytic root lift + concrete branch);
  capstone pillar 5 `U0Capstone.u0_kummer_tower_independence`.

## Statement

For EVERY viable parameter `b` and EVERY level `k`, there is a window disk `ball 0 r` (`r > 1`,
crossing `|z| = 1`) carrying a genuine analytic, nowhere-zero branch `χ` with `χ^(2^k) = ψ_N`
(`ψ_N = bottcherCoord ∘ f_b^[N]`), and `u₀` and `χ` are algebraically independent over `ℂ(z)`
(`NoRelation`).  So `u₀` is independent not of a single branch but of the ENTIRE `2`-power root
tower of `ψ` — the sub-threshold inverse Böttcher branch `φ_b` at every Böttcher level.

## The two halves

**Algebraic half — the Kummer descent** (`U0MStepKummer.noRelation_pow_descent`, general fields
`K ⊆ M`): `NoRelation K (F^n) G ⟹ NoRelation K F G` for any `n`.  Because `F^n ∈ K[F]`,
`trdeg K(F,G) = trdeg K(F^n,G)`; a relation between root and `G` would descend to one between power
and `G`.  Proved directly on the bivariate-eval definition of `NoRelation` (no MvPolynomial bridge,
no transcendence-basis machinery) by the two-case split on whether `P.map (aeval G)` degenerates:
either `G` is algebraic over `K` (nonzero coefficient killed), or `F` is algebraic over the
subalgebra `range(aeval G)`, whence `F^n` is (`IsAlgebraic.pow`) and the relation lifts back through
the surjection `K[Y][X] ↠ (range aeval G)[X]`.  Feeding the m-step `NoRelation ℂ(z) ψ_N u₀` with
`n = 2^k` gives `u0_mstep_kummer_independence`.

**Analytic/geometric half — the root lift** (`U0KummerBranch`):
- **FE identification** (`psiN_eq_bottcherCoord_pow`): on the escape region `ψ_N = (bottcherCoord)^(2^N)`
  (committed `bottcherCoord_iterate`), so the actual window branch `φ_b = bottcherCoord` IS a
  `2^N`-th root of `ψ_N` where defined.
- **Analytic root existence** (`exists_analyticOnNhd_pow_eq`): the window disk `ball 0 r` is convex
  hence simply connected, and `ψ_N` is analytic and nowhere zero on it, so `ψ_N` has a genuine
  analytic `2^k`-th root there.  `bottcherLog` cannot serve (it carries the slit); the root is
  `exp(L/2^k)` for a slit-free analytic log `L` on the disk.
- **Continuous ⟹ analytic upgrade** (`analyticOnNhd_of_continuousOn_exp_eq`, reusable): a continuous
  branch of `log g` (`g` analytic) is analytic — proved by `exp`-injectivity on a ball of radius
  `1 < π`, agreeing with the explicit branch `f(z₀) + log(g z / g z₀)`, then `DifferentiableOn ⟹
  AnalyticOnNhd`.

Combined: `u0_mstep_kummer_branch_independence` = the concrete branch theorem (capstone pillar 5).

## The coherent tower (`u0_coherent_kummer_tower`)

The level-indexed branches assemble into a SINGLE coherent inverse system.  Built from ONE analytic
logarithm `L` of `ψ_N` on the window (not a fresh log per level): `χ k := exp(L / 2^k)` for all `k`.
Then, unconditionally for every viable `b`:

* `χ 0 = ψ_N`;
* **coherence** `(χ (k+1))² = χ k` — a genuine `ℤ₂`-Kummer pro-branch, automatic from the single `L`;
* `(χ k)^(2^k) = ψ_N`;
* every level `χ k` is algebraically independent of `u₀` over `ℂ(z)`.

Strictly stronger than pillar 5's one-at-a-time family: the whole `2`-power root tower is one
pro-object with a distinguished generating log.  Axiom-clean.

## What this OPENS

- **Root-level Kummer for the actual `φ_b`:** the FE pins `χ` to `bottcherCoord` on the overlap; the
  next object is the precise identification of `χ` with the analytic continuation of `φ_b` ACROSS the
  natural boundary (the branch that lands on `|z| = 1`), and its `2^k`-root Galois structure.
- **A general lemma banked for reuse:** `noRelation_pow_descent` turns any single-generator
  independence in the codebase into whole-`n`-power-tower independence — usable for the q62 Böttcher
  pairs and the Hurwitz rows, not just `u₀`.
- **Transcendence-degree bridge:** the direct proof shows `NoRelation` behaves as a rank-2
  algebraic-matroid statement; a full `NoRelation ↔ AlgebraicIndependent` bridge would import
  mathlib's matroid API for free.

## Gates
- [x] 0 → 1  in-progress
- [x] 1 → 2  fully-proven
- [x] 2 → 3  formalized: build + lint green, axiom-clean, non-vacuous (concrete analytic branch)
- [ ] 3 → 4  publication-ready

## Log
- 2026-07-03 — proven end to end.  Abstract Kummer descent (`noRelation_pow_descent`) +
  application to ψ (`u0_mstep_kummer_independence`) + analytic root lift (`U0KummerBranch`) +
  concrete branch (`u0_mstep_kummer_branch_independence`) = capstone pillar 5.  All axiom-clean;
  the reusable `analyticOnNhd_of_continuousOn_exp_eq` and `exists_analyticOnNhd_pow_eq` banked.
- 2026-07-03 — coherent tower `u0_coherent_kummer_tower` banked: one log ⟹ the whole `2`-power root
  tower as a coherent inverse system (`(χ (k+1))² = χ k`), every level ⟂ `u₀`.  Axiom-clean.
