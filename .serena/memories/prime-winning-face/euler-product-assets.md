# Prime-winning face Euler products — assets and traps

State after closing the analytic Lean gate of
`docs/drafts/pipeline/3-formalized/prime-winning-cech-divisor-resolution.md`.

## New reusable asset (do not rebuild)

`RHTower.hasProd_one_sub_primeCpow_neg {w : ℂ} (hw : 1 < w.re) :`
`HasProd (fun p : Nat.Primes => 1 - ((p : ℕ) : ℂ) ^ (-w)) (riemannZeta w)⁻¹`
in `formal/GaloisForLFunctions/RHTower/PrimeWinningFaceAugmentation.lean`,
with `multipliable_one_sub_primeCpow_neg` and `summable_norm_primeCpow_neg` beside it.
Before this the corpus owned only the value `w = 2`
(`RHTower.hasProd_one_sub_prime_cpow_neg_two`, `ProjectivePrimeWeylModel`) and an unnamed `calc`
step inside `HTGeometry.FredholmDeterminantZeta.fredholmDet1_eq_inv_riemannZeta`.

## The HasProd technique that unlocks these products

`ℂ` is not a group under multiplication, so a `HasProd` cannot be inverted, and mathlib only gives
the zeta Euler product in the *inverse* factor form
`riemannZeta_eulerProduct_hasProd : HasProd (fun p => (1 - p^(-s))⁻¹) (riemannZeta s)`.
Never try to invert a `HasProd`.  Instead:

1. get `Multipliable` for the family you want (for `1 - p^(-w)` this is
   `Complex.multipliable_one_add_of_summable` plus `Summable.of_norm`);
2. take `⟨M, hM⟩` and form `hM.mul (riemannZeta_eulerProduct_hasProd _)`;
3. the combined family is pointwise `1`, so `HasProd.unique` against `hasProd_one` pins
   `M * riemannZeta w = 1`.

The same trick computes the reduced face Euler product: multiplying the reduced series HasProd by
`riemannZeta ((m+1) * s)` makes every local factor collapse to `(1 - p^(-s))⁻¹` off the face and to
`(1 - p^(-(m+1)s))⁻¹` on it, so uniqueness against `riemannZeta_eulerProduct_hasProd * (finitely
supported correction)` gives the identity without ever dividing an infinite product.
The finitely supported factor comes from `hasProd_prod_of_ne_finset_one`.

## Trap: the winner-face indicator is not multiplicative

`b_{F,m}(n) = 1` iff every prime of `F` has exponent exactly `m` and no prime exceeds `m`.
It fails `b(1) = 1`, so `ArithmeticFunction.IsMultiplicative` does **not** apply.  Divide out the
winner block `A = ∏_{p ∈ F} p^m` first: `IsReducedFace` (no prime of `F` divides `n`, all exponents
`≤ m`) *is* multiplicative on coprime arguments.  Coprimality is essential — the exponent cap does
not factor over general products.  The reindexing lemma is
`RHTower.faceSeries_eq_faceBlock_mul` (via `Function.Injective.tsum_eq` along `n ↦ A * n`).

## Corpus facts confirmed while auditing

- `RHTower.LSeries_mFree_eq_riemannZeta_div` (`MFreeLadder`) already gives
  `∑ n^{-s}` over `(m)`-free numbers `= ζ(s)/ζ(ms)`; `mPart`, `LSeries_mPart_moebius` there too.
- `RHTower.shellMultiplier m s = ζ((m+1)s)⁻¹ - ζ(ms)⁻¹` and `LSeries_shellIndicator` already exist
  in `HighExponentShellZeroFree`; new face work should land on that definition, not a fresh one.
- `RHTower.analyticAt_riemannZeta_of_ne_one` exists in `BoundedExponentMovingPole`; if you do not
  want that import, use mathlib `analyticOn_riemannZeta s (by simpa using hne)` directly.
