# Kleinbock–Margulis: Flows on homogeneous spaces and Diophantine approximation on manifolds

- **ID:** km98
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean)
- **Source:** arXiv math/9810036 = Ann. of Math. 148 (1998), 339–360
- **Statement:** Formalize, unconditionally and hypothesis-free, every lemma / proposition /
  theorem of Kleinbock–Margulis 1998 in the Lean corpus.

## Goal
Full Lean 4 certification of the KM quantitative-nondivergence machine:
`(C,α)`-good functions, the marked-point covering theorem, quantitative nondivergence on the
space of lattices, and strong extremality of nondegenerate manifolds (Sprindžuk's conjectures
H1, H2 / Baker's conjecture).

## Inventory of targets (paper order)

| Label | Statement | Lean module | Status |
|---|---|---|---|
| Lemma 2.1 | `(1.1M)` ⟹ `δ(g_t Λ_y) ≤ r` | `KleinbockMargulis/Reduction.lean` `lemma_2_1` | **DONE** |
| Cor 2.2 | VWMA ⟹ ∞ many `t ∈ ℤ₊ⁿ` with `δ(g_tΛ_y) ≤ e^{-γt}` | `Reduction.lean` `corollary_2_2` | **DONE** |
| Prop 2.3 | measure bound `|{x∈B : δ(g_tΛ_{f(x)})<ε}| ≤ D(ε/ρ)^{1/dl}|B|` | `KleinbockMargulis/Prop23.lean` `prop_2_3` | **DONE** |
| Theorem A | a.e. nondegenerate ⟹ strongly extremal | | TODO |
| Lemma 3.1 | (a) `|f|`, (b) `λf`, (c) `sup_i|f_i|` stay `(C,α)`-good | `Good.lean` `isGood_abs_iff`, `IsGood.const_mul`, `IsGood.sup` | **DONE** |
| Prop 3.2 | `deg f ≤ k` ⟹ `(2k(k+1)^{1/k},1/k)`-good on ℝ | `PolynomialGood.lean` `isGood_polynomial` | **DONE** |
| Lemma 3.3 (+3.3.1, 3.3.2) | `C^k` derivative-sandwich ⟹ cube estimate `(3.5)` | `SmoothGoodOne.lean` `exists_good_const_one_dim`, `SmoothGoodCube.lean` `exists_isGood_of_sandwichedChains` | **DONE** |
| Prop 3.4 | nondegenerate point ⟹ all linear combos of `1,f_1,…,f_n` are `(C,1/dl)`-good near it | `KleinbockMargulis/Nondegenerate.lean` `prop_3_4` | **DONE** |
| Theorem 4.1 | measure of unmarked points `≤ kC(3^d N_d)^k (ε/ρ)^α |B|` | `Marked.lean` `measure_not_marked_le` | **DONE** |
| Lemmas 4.2–4.6 | supporting | `Marked.lean` | **DONE** |
| Lemma 5.1 | `‖Λ‖ ≤ k‖Γ‖·‖v‖` | `LatticeNorm.lean` `lemma_5_1` (sharper constant `rank Γ + 1`) | **DONE** |
| Theorem 5.2 | quantitative nondivergence | `Nondivergence.lean` `theorem_5_2` | **DONE** |
| Theorem 5.3 | unipotent one-parameter version | | TODO |
| Theorem 5.4 | `h = g_t u_{f(x)}` version | `LinearForms.lean` `theorem_5_4` | **DONE** |
| Theorem B (§6.3) | Khintchine-type convergence statement | | TODO — **the paper states it without proof** ("the details will appear elsewhere"); only a recipe is given (modify Lemma 2.1 in the spirit of [K1, Thm 8.3], then apply Prop 2.3 with `t = (t/n,…,t/n)`) |

## Missing infrastructure (mathlib gaps) to build
1. `(C,α)`-good functions — new.
2. Higher-order symmetry of `iteratedFDeriv` (mathlib has only `second_derivative_symmetric`),
   and polarization: symmetric multilinear map with vanishing diagonal is zero.  **DONE** —
   `HTGeometry/IteratedFDerivSymmetric.lean` (`iteratedFDeriv_comp_perm`) and
   `HTGeometry/MultilinearDiagonal.lean` (`continuousMultilinearMap_eq_zero_of_diagonal`,
   `exists_diagonal_ne_zero_of_iteratedFDeriv_ne_zero`).
3. Sup-norm ("Plücker") norm on `⋀^j ℝ^k` for subgroups of `ℤ^k`, basis independence,
   and `‖w ∧ v‖ ≤ k‖w‖‖v‖`.
4. Poset of nonzero primitive subgroups of `ℤ^k`; length = rank.

Available in mathlib and to be reused: `Besicovitch.exist_disjoint_covering_families`,
`Besicovitch.multiplicity`, `Besicovitch.isEmpty_satelliteConfig_multiplicity`,
`Real.volume_pi_ball`, `Measure.addHaar_image_linearMap`.

## Approach
Work in `Fin d → ℝ` with the sup norm, where metric balls **are** cubes and Lebesgue measure is
`volume = Measure.pi`.  This removes the paper's cube/ball circumscription step.  Prop 3.4's
"rotation of the coordinate system" is replaced by a general invertible linear change of
variables (goodness is stable under `GL_d` with constant `C‖T‖^d/|det T|`), and the required
basis is produced by a one-parameter polynomial non-vanishing argument (`u_i = v + t e_i`)
rather than by a Haar-measure genericity argument on `O(d)`.

## Deviation from the paper's constants
Lemma 3.3 is proved by a route that avoids counting the connected components of `{|f| < ε}`:
the paper's `k+1` components are replaced by the `|Z| + 1` bound of `CutInterval.volume_le_of_cuts`
with `|Z| ≤ 2k` (the number of solutions of `f = ±ε`), and the interpolation nodes are `k+2`
equally spaced points rather than `k+1`.  The resulting constant therefore differs from the
paper's `C_{k,A₁,A₂} = k(k+1)((A₁/A₂)(k+1)(2k^k+1))^{1/k}`; only the dependence on `k, A₁, A₂`
(which is all that Prop 3.4 and Theorem A consume) is preserved.

## Errata found in the published proof
* Theorem 5.2, last display: the chain `‖h(x)v‖ ≥ ‖h(x)Λ‖/(k‖h(x)Γ_{i-1}‖) ≥ ε/(kρ) ≥ ε` uses
  `‖h(x)Γ_{i-1}‖ ≤ ρ`, which fails for `i = 1`, where `Γ_0 = {0}` and `‖h(x)Γ_0‖ = 1 > ρ`.
  The case `i = 1` has to be treated separately: there `Λ = ℚv ∩ ℤ^k`, `v` is an integer multiple
  of a generator `w` of `Λ`, and `‖h(x)v‖ ≥ ‖h(x)w‖ = ‖h(x)Λ‖ ≥ ε` directly (equivalently, the
  constant in Lemma 5.1 is `rank Γ + 1`, which is `1` when `Γ = {0}`).

## Log
- 2026-08-21 — created; paper source read in full (arXiv e-print `mb.tex`).
- 2026-08-21 — §2 (Lemma 2.1, Cor 2.2), §3 (Lemma 3.1, Prop 3.2) and §4 (Theorem 4.1 with
  Lemmas 4.2-4.6) Lean-complete and wired into `GaloisForLFunctions.HTGeometry`.
- 2026-08-21 — §5 core complete: `WedgeNorm.lean` (Plücker calculus, `‖w∧v‖ ≤ (j+1)‖w‖‖v‖`),
  `PluckerSpan.lean` (Cramer's rule; the span is determined by the Plücker vector),
  `IntegerLattice.lean` (`rank(W ∩ ℤ^k) = dim_ℚ W`), `LatticeNorm.lean` (Lemma 5.1),
  `LatticeFinite.lean` (condition (A3)), `Nondivergence.lean` (Theorem 5.2).
  Remaining: Theorems 5.3, 5.4, Prop 2.3, Theorem A, Lemma 3.3, Prop 3.4, Theorem B.
- 2026-08-21 — Theorem 5.4 done (`LinearForms.lean`): the Plücker coordinates of `g_t u_y Γ` are
  positive multiples of affine forms in `y` with integral coefficients.  All twelve modules
  compile with zero warnings.  Remaining: Lemma 3.3, Prop 3.4, Prop 2.3, Theorem A,
  Theorem 5.3, Theorem B.
- 2026-08-21 — §3 infrastructure: `DerivChain.lean` (iterated Rolle, divided-difference mean value
  theorem, Lagrange interpolation remainder — all for a `C^k` derivative chain, so no `C^∞`
  hypothesis is needed), `CutInterval.lean` (level sets of a chain with nonvanishing top member
  are small; the `|Z|+1`-interval counting estimate), `SmoothGoodOne.lean` (Sublemma 3.3.1 (a)).
- 2026-08-21 — Lemma 3.3 complete.  `SmoothGoodOne.lean` closes the one-dimensional case
  (Sublemma 3.3.1 (a), (b) and the `τ`-optimisation, packaged as `exists_good_const_one_dim`);
  `SmoothGoodCube.lean` adds `SandwichedChains` (the Lean form of `(3.4≤)`, `(3.4≥)` for a `C^k`
  function: a `k`-fold derivative chain along every coordinate line with the top member between
  `A₂` and `A₁`), Fubini in the first coordinate, Sublemma 3.3.2, the induction step with the
  `λ = σd/(d+1)` optimisation, and `exists_isGood_of_sandwichedChains`.  The induction is run in
  the *pointwise* form of the estimate, which lets the same point `z` be used on the face and on
  the line; the paper's use of Lemma 3.1(c) on the face-supremum function is therefore avoided.
  Both modules compile with zero warnings and are wired into `GaloisForLFunctions.HTGeometry`.
  Remaining: Prop 3.4, Prop 2.3, Theorem A, Theorem 5.3, Theorem B.
- 2026-08-21 — mathlib gap closed: all-order symmetry of `iteratedFDeriv` for `C^n` maps
  (`IteratedFDerivSymmetric.lean`), by induction with `iteratedFDeriv_succ_apply_right`, Clairaut
  at nearby points pushed through `ContinuousLinearMap.iteratedFDeriv_comp_left`, and generation of
  the symmetric group by adjacent transpositions.  `MultilinearDiagonal.lean` then shows a
  symmetric continuous multilinear map with vanishing diagonal is zero (by differentiating the
  diagonal restriction), giving the polarization step Proposition 3.4 needs.
- 2026-08-21 — Proposition 3.4 complete (`Nondegenerate.lean` `prop_3_4`).  Supporting modules:
  `GoodLinearChange.lean` (goodness under an invertible linear change of variables, replacing the
  paper's circumscribed-cube step, with constant `C |det T| ‖T⁻¹‖^d`), `BasisDirections.lean`
  (a basis `v + s eᵢ` of directions avoiding the zero set of a continuous function, replacing the
  paper's "appropriate rotation"), `LineChain.lean` (directional derivative chains, so the
  hypotheses of Lemma 3.3 for `f ∘ T` are bounds on directional derivatives of `f`).
  `IsDerivChain` was refactored to a *bounded* chain `IsDerivChain k F U` (`∀ j < k`), since a
  `C^k` function only supplies `k` links.  The uniformity in the coefficient vector is obtained by
  compactness of the coefficient sphere; the constant term `c₀` is carried through because chains
  of order `k ≥ 1` do not see it.  Remaining: Prop 2.3, Theorem A, Theorem 5.3, Theorem B.
- 2026-08-21 — Proposition 2.3 complete (`Prop23.lean` `prop_2_3`), together with
  `indep_of_nondegenerate` (nondegeneracy ⟹ `1, f₁, …, f_n` linearly independent near the point,
  via `EventuallyEq.iteratedFDeriv`) and `exists_supGe` (hypothesis (ii) of Theorem 5.4, by
  compactness of the coefficient sphere — only linearity in the coefficients is used, no
  continuity of `f`).  Also added `isGood_const` to `Good.lean`.
  All new modules are wired into `GaloisForLFunctions.HTGeometry`; the formal lint gate reports no
  problem in any of them (its single error concerns `HTGeometry.TwoComponent`, an untracked module
  owned by another agent).
  Remaining: Theorem A, Theorem 5.3, Theorem B.

## Plan for Theorem A (next step)
`prop_2_3` + `corollary_2_2` + Borel–Cantelli.  Concretely:
1. Fix a nondegenerate `x₀`; `prop_2_3` gives `r₀, D, ρ`.
2. For `j ≥ 1` put `E_m = {x ∈ B(x₀,r₀) | δ(g_m Λ_{f(x)}) ≤ e^{-(1/j)∑ m_i}}` and apply `prop_2_3`
   with `ε = 2 e^{-(1/j)∑ m_i}`.  A *global* majorant `volume (E_m) ≤ K e^{-(α/j)∑ m_i}` is
   available: for the finitely many `m` with `2e^{-(1/j)∑m} > ρ` one has `∑ m < j log(2/ρ)`, so the
   trivial bound `volume (E_m) ≤ volume B` is itself of that form.  This avoids splitting off a
   finite exceptional set.
3. `MeasureTheory.ae_finite_setOf_mem` (Borel–Cantelli, arbitrary countable index) then gives
   `∀ᵐ x, {m | x ∈ E_m}.Finite`.  Still needed: summability of `∑_{m : Fin n → ℕ} r^{∑ m_i}` for
   `0 ≤ r < 1` — mathlib has no pi-type product-summability lemma, so induct on `n` with
   `Summable.mul_of_nonneg` along `(Fin (n+1) → ℕ) ≃ ℕ × (Fin n → ℕ)`.
4. `corollary_2_2` turns `VWMA (f x)` into an infinite such set for some `γ > 0`; taking `1/j ≤ γ`
   puts `x` in the `j`-th null set, so `{x ∈ B | VWMA (f x)}` is null.
5. Globalise with `MeasureTheory.measure_null_of_locally_null` applied to
   `{x ∈ U | VWMA (f x)} ∩ {nondegenerate points}`, plus the null set of degenerate points.
- 2026-08-22 — **Theorem A complete** (`KleinbockMargulis/TheoremA.lean`).  The Borel--Cantelli
  assembly followed the plan: `prop_2_3` at `ε = 2 e^{-c ∑ mᵢ}`, with the *global* geometric
  majorant `volume (E_m) ≤ ofReal (B rᵏ) · volume B` (`B = (D+1)(2/ρ)^α`, `r = e^{-cα} < 1`)
  covering the finitely many `m` where `ε > ρ` by the trivial bound, then
  `MeasureTheory.ae_finite_setOf_mem` (no measurability hypothesis — it is stated for any
  `OuterMeasureClass`), then `corollary_2_2` at rate `1/(j+1) ≤ γ`.  The mathlib gap
  `∑_{m ∈ ℕⁿ} r^{∑ mᵢ} < ∞` is `summable_pow_sum`, proved by induction along
  `Fin.consEquiv` and `Summable.mul_of_nonneg`.
  Two forms are exported: `theoremA` (uniform nondegeneracy order `l`, null degenerate locus) and
  `theoremA_allOrders` (only the *all-order* degenerate locus must be null — the form a spectral
  family needs, since its nondegeneracy order is not uniform).
- 2026-08-22 — **Khintchine transference, the half the recurrence exponents need**
  (`KleinbockMargulis/Transference.lean`).  `VWA` (simultaneous `(1.2)`) is defined and
  `vwma_of_vwa` proves `VWA y → VWMA y`, so strong extremality gives the *simultaneous*
  Diophantine exponent `1/n`.  The proof is pure pigeonhole, not Minkowski: the index-`q`
  sublattice `{a : q ∣ a·p}` meets the cube of side `⌊q^{1/n}⌋` by
  `Fintype.exists_ne_map_eq_of_card_lt` on `(Fin n → Fin (Q+1)) → ZMod q`
  (`exists_small_dvd_dotProd`); then `|a·y + b| = |a·δ|/q ≤ n q^{-1-ε}` and `Π₊(a) ≤ q`
  (`exists_transfer_point`).  Infinitude of the resulting dual set is obtained by contradiction
  against `Finset.inf'` of the distances `dist(a·y, ℤ)`, after splitting off the degenerate case
  `∃ a ≠ 0, a·y ∈ ℤ` (where the multiples `k·a` are themselves an infinite witness).
- 2026-08-22 — `KleinbockMargulis/Extremal.lean` packages the two:
  `theoremA_simultaneous`, `theoremA_simultaneous_allOrders`, `finite_of_not_vwa`, and
  `measure_exists_dioph_exponent_eq_zero`.  All three modules are axiom-clean
  (`propext`, `Classical.choice`, `Quot.sound`) and wired into `GaloisForLFunctions.HTGeometry`.
  Remaining: Theorem 5.3, Theorem B.
