# power-canonical-product-exact-moment-borel-lattice-law — CLOSED, promoted to Stage 3 (2026-08-14)

Equation `(1)` (the Barnes expansion of `H_s(x) = x W_s'(x)/W_s(x)`) is now unconditional at every
genus, so the card is complete and was `git mv`-ed to
`docs/drafts/pipeline/3-formalized/new_scientific_knowledge/other/`.

## Capstone
`RHTower.barnes_expansion_powerCanonicalProduct`
(`formal/GaloisForLFunctions/RHTower/BarnesCanonicalProductExpansion.lean`, axiom-clean):
for `s > 0` with `1/s ∉ ℕ`, `g = ⌊1/s⌋`, every `K`, ∃ `C ≥ 0` ∀ `x > 0`

```
‖ x W_s'(x)/W_s(x) − (π/s)csc(π/s)x^{1/s} − ∑_{k<K} barnesTerm s x (k−g) ‖ ≤ C x^{−(K−1−g+1/2)}
```

`barnesTerm s x j = (−1)^j ζ(−sj) x^{−j}` (ℤ-indexed): `j<0` = the ascending middle sum,
`j=0` = `ζ(0) = −1/2`, `j>0` = the Barnes tail `b_k x^{−k}`.  `barnesTerm_natCast` bridges it to
`zetaMomentCoeff`, the coefficient the transform theory `(2)`–`(11)` is built from.

## New modules (all umbrella-wired, axiom-clean)
- `HTGeometry/PowerCanonicalProductLogDeriv.lean` — `ofReal_mul_logDeriv_powerCanonicalProduct`:
  `x W_s'/W_s = ∑_n (−1)^g barnesModel g (x/(n+1)^s)` on `x > 0`.  Uses mathlib
  `logDeriv_tprod_eq_tsum` + corpus `canonicalProduct_hasProdLocallyUniformlyOn`,
  `canonicalProduct_sub_one_norm_summable` and mathlib `tprod_one_add_ne_zero_of_summable` for
  `powerCanonicalProduct_ne_zero` on the positive axis.
- `RHTower/BarnesMellinGenusRepresentation.lean` — **the key identity**
  `mellin_barnesModel_eq`: on `−(g+1) < Re w < −g`, `mellin (barnesModel g) w = (−1)^g(−π/sin πw)`.
  The genus parity cancels the parity of the logarithmic derivative, so the summed representation
  `hasSum_barnesModel_verticalIntegral'` has the SAME integrand `barnesIntegrand s x` as genus 0,
  only on a shifted strip.  Envelope/integrability/interchange chain mirrors
  `HTGeometry/CauchyKernelMellin.lean`.
- `RHTower/BarnesMellinNegResidues.lean` — simple pole at a negative integer + shift across it.
- `RHTower/BarnesMellinGenusExpansion.lean` — ladder `σ_0 = −((g+1)+1/s)/2`, `σ_1 = −(g+1/s)/2`,
  `σ_{k+2} = k−g+1/2`; `verticalIntegral'_shift_int` (either sign),
  `verticalIntegral'_shift_genusZetaPole`, telescoping, `barnes_genus_poincare_expansion`.

## Reusable assets found (do not rebuild)
- `HTGeometry/GammaVerticalStripDecay.exists_bound_norm_Gamma_vertical_strip` —
  `‖Γ(σ+it)‖ ≤ C|t|^N e^{−π|t|/2}` uniformly on `a ≤ σ ≤ M`.  Also `GammaVerticalUniformDecay`,
  `GammaVerticalModulus`.
- `RHTower/ZetaVerticalStripPolynomialBound.exists_bound_norm_riemannZeta_strip` — polynomial
  growth of ζ on ANY vertical strip.
- `HTGeometry/SineVerticalDecay` — `norm_inv_sin_le_exp`, `isBigO_inv_sin_sub_inv_at_nat` /
  `_at_neg_nat` (pole data at every integer), `isBigO_analytic_mul_simplePole`.
- `HTGeometry/VerticalContourShift.verticalIntegral'_sub_of_simple_pole` (on PNTPlus's
  `tendsto_truncated_vertical_shift_with_simple_pole`) — the one-pole shift.
- The genus-0 chain `RHTower/BarnesMellin{IntegrandBound,IntegrandAnalysis,Residues,PowIntegrand,
  PowResidues,Shift,Representation,Expansion,Remainder,EulerDerivative}.lean`.

## Lean notes
- `HTGeometry.primaryFactor` / `powerGenus` / `powerCanonicalProduct` live in the BARE `HTGeometry`
  namespace; `barnesModel`, `cauchyKernel`, `mellin_barnesModel` in `GaloisForLFunctions.HTGeometry`.
  A new module needs `namespace HTGeometry` + `open GaloisForLFunctions.HTGeometry` (existing
  convention in `BankOddExponentDichotomy.lean`).
- `inv_neg : (-a)⁻¹ = -a⁻¹` (mathlib's `neg_inv` is the other direction).
- `HasDerivAt.comp` produces `f ∘ g`; give it a `have` without an expected type, then `exact`.
