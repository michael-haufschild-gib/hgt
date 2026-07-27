# Archimedean--finite global-adele separated-product density

- **ID:** `field-one-semilocal-product-l2-density`
- **Stage:** 3-formalized
- **Type:** THEOREM / CONSTRUCTION
- **Label:** `F1-L2-DENSITY-1`
- **Parent:** `field-one-finite-bruhat-l2-density`
- **Target:** prove that the canonical algebraic
  Schwartz--Bruhat realization has dense range in
  \(L^2(\mathbb R\times\mathbb A_f)\).

## Theorem

Let \(\mu,\nu\) be sigma-finite measures.  Finite linear combinations of
separated \(L^2\) functions
\[
  (x,y)\longmapsto f(x)g(y)
\]
are dense in \(L^2(\mu\times\nu)\).  Consequently, if
\(A\to L^2(\mu)\) and \(B\to L^2(\nu)\) have dense range, the algebraic
tensor realization
\[
  A\otimes B\longrightarrow L^2(\mu\times\nu)
\]
has dense range.

Specializing to real Schwartz functions and finite-adele
Bruhat--Schwartz functions identifies
`FieldOneSemilocalBruhatHilbertCompletion` with all product-Haar
\(L^2(\mathbb R\times\mathbb A_f)\). The later type audit in
`field-one-global-adele-comparison` proves this ambient ring is the full
rational adele ring; “semilocal” survives only in historical Lean names.

## Iterative proof plan

1. Bundle pointwise separated multiplication on scalar \(L^2\) and prove
   its product norm law from Tonelli.
2. For sigma-finite factors, use finite spanning sets and density of finite
   unions of measurable rectangles in symmetric-difference measure.
3. Convert rectangle-indicator approximation to \(L^2\) density via
   `Lp.induction`.
4. Use continuity of separated multiplication and dense factor maps.
5. Specialize with `SchwartzMap.denseRange_toLpCLM` and
   `fieldOneFiniteBruhatToL2Linear_denseRange`.
6. Upgrade the existing completion-to-closure equivalence to an equivalence
   with full product \(L^2\).

## No-go checks

- Do not assume the desired product-density theorem through a completed
  tensor-product equivalence.
- Do not use finite total Haar mass: both semilocal factors have infinite
  mass.
- Rectangle approximants must have finite factor measures so their
  indicators are genuine \(L^2\) vectors.
- No trace, divisor, Xi, Hodge, positivity, or RH premise may enter.

## Formalization

- `L2SeparatedProductDensity.lean` proves the exact separated-product
  `eLpNorm` and norm laws, constructs the algebraic tensor map, proves that
  finite-measure rectangles generate the product sigma algebra, approximates
  finite-measure sets by finite disjoint unions of rectangles, and proves
  dense range by `Lp.induction`.
- The same module proves that tensoring arbitrary dense factor maps still
  has dense separated-product image.
- `FieldOneSemilocalBruhatL2Density.lean` applies this to real Schwartz and
  finite-adele Bruhat maps, proves the swap-transported semilocal Haar measure
  equals direct product Haar, identifies the transported map with the
  pre-existing semilocal Bruhat realization on all algebraic tensors, and
  proves its range dense.
- The closed image is therefore `⊤`; the existing completion realization is
  surjective and yields
  `fieldOneSemilocalBruhatCompletionEquivL2`.
- Algebraic faithfulness survives both completion and transport to the full
  product-Haar space:
  `fieldOneSemilocalBruhatCompletionWeylUnitary_injective` and
  `fieldOneSemilocalL2WeylUnitary_injective`.
- `L2HilbertTensorProduct.lean` equips the algebraic \(L^2\) tensor with its
  canonical inner product, completes it, and proves a linear isometric
  equivalence with product \(L^2\).
- `FieldOneSemilocalFactorwiseHilbertTensor.lean` composes that equivalence
  with the semilocal Bruhat completion and proves exact agreement on pure
  Schwartz--Bruhat tensors.
- `FieldOneGlobalAdeleComparison.lean` proves the ambient product is
  mathlib's full rational adele ring and explicitly rules out identifying it
  with a finite-\(S\) unit quotient by type alone.

## Audit

- [x] Repo/mathlib research found no existing full theorem.
- [x] Finite-adele sigma-finiteness formalized.
- [x] Finite-adele Bruhat density formalized.
- [x] Generic separated \(L^2\) product and exact norm law.
- [x] Finite-union rectangle density.
- [x] Dense-factor specialization.
- [x] Completion upgrade.
- [x] Independent factorwise Hilbert-tensor comparison.
- [x] Direct `lake env lean` checks passed with cached `.olean` output.
- [x] `#print axioms` reports only `propext`, `Classical.choice`, and
  `Quot.sound`.
- [x] No computation, trace, Hodge, positivity, spectral, or RH premise.
