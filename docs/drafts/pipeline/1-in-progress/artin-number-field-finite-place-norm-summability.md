# Number-field finite-place norm summability

- **ID:** `artin-number-field-finite-place-norm-summability`
- **Stage:** 1-in-progress
- **Type:** THEOREM (literature infrastructure)
- **Status:** `[LITERATURE] [PAPER-PROVED] [BRIDGE] [NOT NEW]`
- **Statement:** for every number field \(K\) and every real \(\sigma>1\),
  \(\sum_{v\in\operatorname{Spec}_1(\mathcal O_K)}N(v)^{-\sigma}\) converges; equivalently,
  \(\sum_v\lVert N(v)^{-s}\rVert\) converges for every complex \(s\) with
  \(\Re(s)>1\).

## Goal

Supply the exact M-test budget for the genuine Artin Euler product.  The theorem is fully
unconditional number-field infrastructure: it contains no representation, Artin L-function,
meromorphic continuation, or assumed analytic convergence interface.

## Exact Lean target

```text
numberField_summable_finitePlace_absNorm_rpow:
  1 < sigma ->
  Summable (fun v : HeightOneSpectrum (𝓞 K) =>
    (v.asIdeal.absNorm : ℝ) ^ (-sigma)).

numberField_summable_finitePlace_norm_cpow:
  1 < s.re ->
  Summable (fun v : HeightOneSpectrum (𝓞 K) =>
    ‖((v.asIdeal.absNorm : ℂ) ^ (-s))‖).
```

## Paper proof

Let \(a(n)\) count nonzero integral ideals of norm \(n\).  Finite norm fibres give
\(\sum_{n\le X}a(n)=\#\{I\ne0:N(I)\le X\}\).  Mathlib's already-proved ideal asymptotic makes
these partial sums \(O(X)\).  The standard L-series summability theorem therefore yields
\(\sum_n a(n)n^{-\sigma}<\infty\) for \(\sigma>1\).  Reindex nonzero ideals by norm through
finite fibres, then compare the injective map from height-one primes to nonzero ideals.  Finally,
\(\lVert N(v)^{-s}\rVert=N(v)^{-\Re(s)}\) because finite-prime norms are positive.

This proof is dependency-closed on the existing number-field ideal-count asymptotic and generic
L-series summability; it proves only the source-chamber summability needed later.

## Exact Lean route

- `NumberField.Ideal.tendsto_norm_le_div_atTop₀` for nonzero ideal counts;
- `Asymptotics.isBigO_atTop_natCast_rpow_of_tendsto_div_rpow` and
  `LSeriesSummable_of_sum_norm_bigO_and_nonneg`;
- `Ideal.finite_setOf_absNorm_eq`, `Equiv.sigmaFiberEquiv`, and
  `HeightOneSpectrum.asIdeal_injective` for the reindexing/comparison;
- `Complex.norm_natCast_cpow_of_pos` for the complex corollary.

## Anti-theatre boundary

- Northcott alone proves only finite norm fibres; it is not summability.
- This proves a scalar norm budget, not local-factor bounds, local uniformity, an analytic Euler
  product, continuation, or Artin holomorphy.
- It will be consumed immediately by the finite-image local-factor estimate.  It may not be used
  to postulate `Multipliable` or analyticity.

## Exact formal result

`formal/GaloisForLFunctions/RHTower/NumberFieldFinitePlaceNormSummability.lean` proves both
displayed targets.  Its proof explicitly reconstructs the norm-count partial sums, applies the
existing ideal-count asymptotic to obtain the L-series estimate, reindexes through finite norm
fibres, and only then restricts from all ideals to height-one primes by the actual injective
`asIdeal` map.

## Verification

- `lake env lean GaloisForLFunctions/RHTower/NumberFieldFinitePlaceNormSummability.lean` passed.
- `lake build GaloisForLFunctions.RHTower.NumberFieldFinitePlaceNormSummability` passed; targeted
  leaf only.
- `/tmp/NumberFieldFinitePlaceNormSummabilityAxioms.lean` reports only
  `[propext, Classical.choice, Quot.sound]` for both the real and complex theorems.
- The leaf is wired into `formal/GaloisForLFunctions/RHTower.lean`; no umbrella build was run.
- The most recent repository-wide lint remains blocked by unrelated concurrent modules, so this
  card remains Stage 1 rather than claiming a whole-tree formal-gate pass.

## Log

- 2026-08-15 — opened after source-verified Mathlib audit found no direct finite-prime summability
  theorem but a complete ideal-count-to-L-series proof route.  This is the next required analytic
  source input after the formal Euler source.
- 2026-08-15 — formalized the full norm-count/reindexing proof, source-checked, target-built,
  axiom-audited, and wired the leaf.  The next consumer is the finite-image local-factor bound;
  no analytic product or continuation claim has been made.
