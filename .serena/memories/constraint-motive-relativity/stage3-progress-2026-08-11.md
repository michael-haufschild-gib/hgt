# CMR folder → stage 3: progress ledger (2026-08-11)

Goal: unconditionally formalize every card in
`docs/drafts/pipeline/2-fully-proven/constraint-motive-relativity/` (18 cards, all started as
`[NO LEAN WRITTEN OR BUILT]`), then `git mv` each paper card to
`docs/drafts/pipeline/3-formalized/constraint-motive-relativity/` with a `-formalized.md` companion.

Lean home: `formal/GaloisForLFunctions/HTGeometry/ConstraintMotiveRelativity/`,
namespace `HTGeometry.ConstraintMotiveRelativity`.  Wire every new module into
`formal/GaloisForLFunctions/HTGeometry.lean` (flat import list, append at EOF with a here-doc).
Audit wiring with: `for f in .../ConstraintMotiveRelativity/*.lean; do grep -q ...; done`.

## DONE: 3 of 18 (paper card moved + `-formalized.md` companion written)

1. **cofinal-inverse-capacity-vertical-fibre-law**
2. **cofinal-capacity-polar-horizon-moore-penrose-law**
3. **finite-lattice-direction-capacity-verticality-pontryagin-law**

15 modules built, all axiom-clean (`propext, Classical.choice, Quot.sound` only), no sorry/axiom.

## Reusable machinery (USE IT, don't rebuild)

- `PortTower` / `HilbertPortTower` over `LinearPMap`; `portFillNorm`, `fillNormInf`,
  `multivaluedHorizon_eq`, `isClosable_iff`, `scalar_horizon_dichotomy`,
  `mem_multivaluedHorizon_of_tendsto`, `multivaluedHorizonSubmodule`.
- `portGram/portCoLift/portCapacity/portInvGram/portMinLift`, `portFillNorm_sq`,
  **`portCoLift_eq` / `portGram_eq_of_coLift`**, `HilbertPortTower.limitInvGram`,
  `multivaluedHorizon_eq_ker`.
- `CapacityChart` on a fin-dim real inner product space: `fenchel`, `cometricLimit`,
  `boundedCapacity_eq`, `range_cometricLimit_eq_orthogonal`, `pseudoInverse`,
  `tendsto_gram_pseudoInverse`, `isCompl_boundedCapacity`, `cometric(Limit)_congr`;
  `HilbertPortTower.capacityChart` bridge.
- `rankOne`, `LatticeDirectionData`, `divergentSpan`; `symSqrt`/`eigBasis`/`eigVal`/`apply_eq_sum`.
- **`weightedPort` on `lp (fun _ : J => ℝ) 2`** with `portStage`, `portGram_portStage`
  (`= ∑_{j∈F} wt j ^2 • rankOne (dir j)`) — the generic realization of a positive Gram family as
  a literal nested port tower.
- `latticePart` + primitive/free-quotient + character exact sequence (Pontryagin).
- `WeightedPortCapacity.lean` — `portCap`, `portEnergy`, `portValue`, `portValue_normSq_le`
  (weighted Cauchy–Schwarz), `portMinimizer`, `portValue_portMinimizer`,
  `portEnergy_portMinimizer`, **`isLeast_portEnergy`**, `portCap_mul_minEnergy`
  = card 18 Theorem 1 `(CA.4)–(CA.6)`.
- `PortAdmissionCapacity.lean` — `SourceL2 P = lp (fun _ : P => ℂ) 2`, `srcBasis`, `srcEmb`,
  `srcEmb_apply` (scaffold for card 18 Theorem 2).

## CURRENT CARD: weighted-port-capacity-admission-recurrence (task #18)

Done: Theorem 1 (CA.4)–(CA.6).
Remaining plan (realize `H_w` isometrically as `ℓ²(P)` with `c p = conj(a p · phase p)/√(w p)`;
document this identification in the companion):
* **Theorem 2 / (CA.7)**: `Summable (fun p => ‖c p‖²)` ↔ ∃ continuous `Λ : ℓ² →L[ℂ] ℂ` agreeing
  with `∑ c p l p` on `srcEmb l`; then `‖Λ‖² = ∑' ‖c p‖²` (Riesz with the vector `conj ∘ c`).
  Reverse: test on the aperture minimizer of value `1`, giving `C_F ≤ ‖Λ‖²` for all finite `F`.
* **(CA.8) / Corollary 2.1**: if not summable, the algebraic kernel is dense — for finitely
  supported `y` with value `S`, pick `F` disjoint from `supp y` with `C_F > ‖S‖²/ε²` and subtract
  `portMinimizer`; then use density of finitely supported vectors in `lp 2`.
* **Theorem 3 / (CA.9)**: the orbit `t ↦ λ_t` is the diagonal unitary orbit of `(a_p/√w_p)`;
  norm-continuous, totally bounded (truncate + finite torus), recurrent; `C^n` iff `C_n < ∞`
  with `n`-th derivative coefficient `(-i log p)^n a_p p^{-it}` and squared norm `C_n`.
* **Corollary 3.1 / (CA.10)–(CA.11)**: `a_p = 1`, `w_p = p (log p)²` gives `C_0 < ∞`
  (compare `∑ 1/(n (log n)²)`) and `C_1 = ∑ 1/p = ∞` (Euler / mathlib
  `Nat.Primes.not_summable_one_div`).
* **§5 specializations** 1–4.

## REMAINING 15 cards

compact-observer-local-gauge-cofinal-horizon, finite-reporter-admission-hyperbolic-composition,
gauge-collapse-stratified-observation-density-reconstruction, ghz-coherence-graph-state-history,
helson-coefficient-fredholm-crossing-response, kummer-gamma-one-sided-corona-flow,
linear-hyperbolic-double-three-doctrine-nonconservativity,
marked-euler-shell-mellin-gns-ht-recurrence-wall, marked-mellin-normalization-exchange-response,
prime-gamma-bockstein-rees-event-germ, prime-phase-port-recurrence-completion,
prime-port-algebraic-continuous-separation, puiseux-cluster-split-one-port-lorentz-exchange,
valuation-coframe-operation-defect-rank-determinant-line,
weighted-port-capacity-admission-recurrence (in progress).

Cards 14/15/18 share the prime-port ℓ² machinery — do them together.

## Hard-won Lean facts (toolchain v4.32.2)

- `LinearMap.adjoint` will NOT unify for `S : Submodule 𝕜 ↥T.domain` (nested submodule instance
  diamond). Use `S : Submodule 𝕜 X` with `h : S ≤ T.domain` and `Submodule.inclusion h`.
- `variable (h : P)` is NOT auto-included in a theorem when used only in the proof body — pass it
  explicitly (this bites constantly).
- `simp only [lemma]` loops whenever the RHS re-exposes the LHS pattern → use `Tendsto.congr`.
- After `intro` on `Monotone fun n => f n`, add `show f m ≤ f n` (no automatic beta).
- `0 + n` is NOT defeq to `n` for `Nat`.
- Renames/absences: `Basis.constr` gone (use
  `Finsupp.linearCombination R f ∘ₗ b.repr.toLinearMap`); `tendsto_finset_sum` → `tendsto_finsetSum`;
  `orthogonalProjection` → `Submodule.orthogonalProjectionOnto`;
  `Submodule.isCompl_orthogonal_of_completeSpace` → `Submodule.isCompl_orthogonal`;
  `push_neg` → `push Not`; gone: `le_or_lt`, `pow_le_pow_left`, `Finset.range_subset` (as ↔),
  `Finset.product_subset_product_left`, `Finset.inner_mul_le_norm_mul_norm`
  (→ `Finset.sum_mul_sq_le_sq_mul_sq`); `real_inner_comm x y : ⟪y,x⟫ = ⟪x,y⟫` (reversed!);
  `Real.summable_one_div_nat_pow`; `not_isRegular_zero (R := ℤ)`; `div_le_div_iff` →
  `div_le_iff_of_neg` when the denominator is negative.
- `Module.Projective` instance search fails on `↥Λ ⧸ N` even with `Module.Free` in scope; build the
  splitting by hand from `Module.Free.chooseBasis`.
- `!₂[a, b] : EuclideanSpace ℝ (Fin 2)`; inner via
  `simp [EuclideanSpace.inner_eq_star_dotProduct]` then `ring`.
- `lp.inner_single_left/right`, `lp.single_apply` are the ℓ² coordinate API.
- `omit [Inst] in` must go BEFORE the docstring, not between docstring and `theorem`.
- Tail tactics after `field_simp`/`simp` often have no goals — wrap in `try`.
- `multivaluedHorizon` lives in `HTGeometry/ObserverHorizonStability.lean` (`LinearPMap` based).
- Another agent concurrently edits
  `HTGeometry/ConstraintRelativity/PhaseSubdiscriminantKaehlerSmith.lean`; a red
  `lake build GaloisForLFunctions.HTGeometry` may be theirs — check the failing target name.
