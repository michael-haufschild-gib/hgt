# Irreducible n-ary L∞ law Lean layer (ULF-IRR-1)

Module: `GaloisForLFunctions.HTGeometry.ConstitutiveIrreducibleInteraction`
(wired into `HTGeometry.UniversalLawField`). Card promoted to Stage 3.

## Reuse, do not rebuild

- The **minimal-formal-law layer already exists**:
  `GaloisForLFunctions.HTGeometry.NomologicalHomotopyGeometry.MinimalLawLeadingJet`
  (namespace `HTGeometry.NomologicalHomotopyGeometry.MinimalLawLeadingJet`, NOT under
  `GaloisForLFunctions`) supplies `MinimalLaw`, `MinimalLawEquiv`, `FirstNonzero`, `IsAbelian`,
  `abelian_iff`, `firstNonzero_order_eq`, `not_target_abelian_of_source_firstNonzero`.
  Also present in that folder: `TensorCoalgebra` (reduced tensor coalgebra, Taylor families,
  coderivation extension), `CyclicAInfinityLaw` (`square`, `oddBracket`, MC equation),
  `SplitLInfinityObserverExtension`.
- New here: `interactionBracket N` (alternating `det(colours) • z` on `(Fin N → ℝ) × ℝ`),
  `bracketFamily N r`, `bracket_composite_eq_zero`, `linfty_identity`, `colorFace`, `faceLaw`,
  `irreducibleLaw`, `arityTruncation`, `TowerCarrier`/`towerBracket`, `zTail`/`towerHead`,
  `not_locallyCompactSpace_pi_real`.

## Method notes

- **Sign-convention-free L∞ minimality**: instead of formalizing Koszul signs, prove every
  *composite* vanishes; then any signed sum of composites is zero for any sign function. This is
  exactly the paper argument and is strictly stronger than one convention.
- The graded-antisymmetric extension of `ℓ_N(x_1,…,x_N)=z` **is** the determinant of the colour
  coordinates — all colours have degree 0, so graded antisymmetry = ordinary antisymmetry. Use
  `Matrix.detRowAlternating.compLinearMap (LinearMap.fst …)` then
  `LinearMap.toSpanSingleton …|>.compAlternatingMap`. Proper-face vanishing is
  `Matrix.det_eq_zero_of_column_eq_zero`, composite vanishing is `det_eq_zero_of_row_eq_zero`.
- **Avoid dependent casts on linear maps** when defining an arity-indexed operation family: put the
  `if h : r = N` on the *AlternatingMap* and reindex with
  `AlternatingMap.domDomCongr (finCongr h.symm)`. `finCongr_refl` + `domDomCongr_refl` then give the
  `r = N` reduction. Casting `⋀^r M →ₗ M` directly is far worse.
- `exteriorPower` lives in namespace `ExteriorAlgebra` (file
  `Mathlib/LinearAlgebra/ExteriorAlgebra/Basic.lean`); the notation is `⋀[R]^n M`. The lemma
  namespace `exteriorPower.*` (e.g. `alternatingMapLinearEquiv`) is at root, in
  `Mathlib/LinearAlgebra/ExteriorPower/Basic.lean`. Importing only a corpus module does NOT bring
  either in — add `import Mathlib.LinearAlgebra.ExteriorPower.Basic` explicitly.
- `subst h` with `h : r = N` eliminates `N`, so later references to `N` break; use `_`.
- `AlternatingMap.pi` exists and is the clean way to build a product law.
- `¬ LocallyCompactSpace (ℕ → ℝ)`: `exists_compact_mem_nhds` + `nhds_pi` + `Filter.mem_pi` gives a
  finite constraint set `I`; pick `i₀ ∉ I`, use `mem_of_mem_nhds` to get `0 ∈ V i` and
  `Function.update 0 i₀ a` to fill the fibre; then `IsCompact.image (continuous_apply i₀)` and
  `NoncompactSpace.noncompact_univ`. Mathlib has no ready non-local-compactness lemma for products.
