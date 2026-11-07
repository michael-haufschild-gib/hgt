# The natural boundary is Liouville-odd (PTT hull, open topic 8)

- **ID:** ptt-liouville-odd-boundary
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** PrimeTorusTheory README §9.8 (the hull over order-two points)
- **Statement:** for almost every order-two point `ω` (fair coins), the fibres over `ω` and over its antipode `½ − ω`
  both extend zero-free to `Re s > ½` with the critical line as natural boundary, and their product is `ζ(2s)` on all of
  `Re s > ½`.

## Paper proof
1. Twin product: if `f(p) = ±1` and `g(p) = −f(p)`, the Euler factors multiply to `(1 − p^{−2s})^{−1}`, so
   `L_f(s)L_g(s) = ζ(2s)` on `Re s > 1`.
2. The antipode `ω ↦ ½ − ω` swaps the two atoms of each coin, so it preserves the product coin measure, and it sends
   `X_p = ±1` to `−X_p`.
3. `ae_sign_natural_boundary` holds a.e., hence a.e. for the antipode too; the extensions multiply to an analytic function
   on the connected half-plane `Re s > ½` that equals `ζ(2s)` on `Re s > 1`, hence everywhere there.

## Lean
Module `PrimeTorusTheory/TheNaturalBoundaryIsLiouvilleOdd.lean`: `tsum_mul_tsum_twin`, `flip`, `measurePreserving_flip`,
`X_prime_flip`, `HasNaturalBoundary`, `ae_twin_natural_boundary`. Axioms: `propext`, `Classical.choice`, `Quot.sound`.

## What it says
The boundary lives in the odd part `Σ_p Σ_{k odd} f(p)^k p^{−ks}/k` of the logarithm, which the antipode reverses; the even
part is the fixed function `log ζ(2s)`. Along any ray on which a typical fibre is unbounded, its antipode tends to zero at
the reciprocal rate. The pair `(ζ, ζ(2s)/ζ(s))` (trivial point and Liouville point) has the same product.
