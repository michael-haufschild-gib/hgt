# Literature capstones: facts

## Closed in Lean

- **Toeplitz:** PSD data admits exact nonnegative unit-circle atomic Vandermonde factorization.
- **CCM:** formal Lambert and finite normalized-determinant coefficients lie in `ℤ^cyc[1/2]`; no convergence theorem.
- **Burnol:** literal Riesz zero jets are complete iff aperture `a ≥ 1`; cosine closure detects exact completed jets.

## Q8 capstone

- SST field `N/ℚ`: `Gal(N/ℚ) ≃ Q8`; faithful irreducible `2D` representation; conductor `6`.
- `N` is totally real.
- Maximal abelian field `K=ℚ(√5,√41)`; `disc(K)` is supported on `{5,41}`.
- `D₅=I₅=Stab(√41)` and `D₄₁=I₄₁=Stab(√5)` are `C₄`; `P₅=P₄₁=1`.
- Actual `5` source/inverse have conductor `5`, literal Tate equations, unit phases, product `−1`.
- At `41`, direct `C₄→F₄₁×` pullback has exponent `≤2`. Reverse `F₄₁×→C₄≃I₄₁` is surjective and preserves both literal Artin eigenchannels.
- Actual `41` source/inverse have conductor `41`, literal Tate equations, unit phases, product `+1`.
- At `2`, every primitive quadratic conductor-`8` pair has phase product `χ(-1)`; parity uniquely selects `χ₈` (`+1`) or `χ₋₈` (`−1`).
- For every dyadic `E/K`, `E⊗_KN ≃ E[ω]/(ω²−δ)` and `u` is its determinant algebra norm, via `a²=u+δ(u+1)²`.
- The completed decomposition involution fixes each contracted dyadic prime and sends `u↦1−u`; hence the actual selected total local norm is `u(1−u)=−1`.
- Pinned Lean CFT supplies actual finite local Artin reciprocity, kernel = local norms, and concrete finite-place tensor-norm comparison.
- The completed Hensel witness is unit-valued; its norm `u` has trivial actual finite-place Artin symbol for `N/K` at every dyadic `K=ℚ(√5,√41)` place.
- Over `S=ℚ(√41)`, `u` has minimal polynomial `X²−X−1`; hence `N_{K/S}(u)=−1`.
- At `2`, source primes have `e=f=1` over `ℚ`; completed lower groups are `C₂` at `0,1,2`, then `1`; upper groups satisfy `G²=C₂`, `G³=1`; local conductor is `8`. Genuine reciprocity factors the source character through `(ℤ/8ℤ)×`; the quotient is even. Source central value is `−1`.
- Fröhlich 6(i)'s hypothesis holds; wild `2` is permitted. Finite sign and odd local product equal `α_Kβ_K=−1`.
- Fröhlich's proof uses Artin induction/local Gaussian `ε`, pure-field evaluation, then quadratic-twist invariance.
- **Open:** transport central nontriviality to the quotient, identify `χ₈`, prove dyadic `ε`, assemble `W_N=−1`.
