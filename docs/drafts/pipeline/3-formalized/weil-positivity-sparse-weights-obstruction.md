# Weil positivity forces a pole (sparse weight systems)

**Status:** formalized (Lean, unconditional, standard axioms).
**Module:** `formal/GaloisForLFunctions/RHTower/WeilPositivitySparseWeightsObstruction.lean`

## Statements
- `weilPositive_farPolar_inequality`: Chebyshev inequality at every scale. For Weil-positive `lam` and every `X ≥ 0`:
  `−∫|ψ̂|²A − (2c_X + c_X²)∫|ψ̂|²|A| ≤ 4π Σ_n lam(n) n^{−½}(c_X R(log n − X) − (c_X²/4) R(log n − 2X))`,
  with `c_X = 1/cosh(X/2)`, `ψ` the Fejér test and `R` its autocorrelation.
- `not_weilPositive_of_localAtomMass`: local atom mass `o(e^{X/2})` ⇒ not Weil-positive.
- `not_weilPositive_of_sparse_support`: support with `#(P∩[2,N]) ≤ CN^θ`, `θ < ½` ⇒ not Weil-positive.

## Proof
1. The far polar test is `f_X = ψ − c_X(ψ(·−X) + ψ(·+X))/2`, with `f̂_X = ψ̂·(1 − c_X cos(Xz))`. It vanishes at `±i/2`, since `cos(±iX/2) = cosh(X/2)`.
2. Archimedean energy: `|(1 − c cos)² − 1| ≤ 2c + c²`, so it tends to `∫|ψ̂|²A < 0` (corpus Fejér negativity).
3. Atom at `log n`: `∫|f̂_X|²cos(τ log n) = 2π((c²/4)R(log n − 2X) − cR(log n − X))`, by product-to-sum and `R = 0` beyond `17/25 < log 2`.
4. Sparse mass makes the atom terms `O(e^{−X/2}M(X) + e^{−X}M(2X)) → 0`. For sparse supports this uses the Weil box `|lam(n)| ≤ √n(log n + C₀)`.

## Context
- This is the existence half of the Minkowski split (L68/L70). It extends the corpus summable-weights obstruction to all sparse, non-summable systems.
- For Λ, PNT-density atoms reproduce exactly Weil's pole term, and the far energy tends to the full Weil functional `W_Λ(ψ) ≥ 0`.
- It is the positive survivor of the L72 far-correction attack on PBAP: that attack succeeds exactly below √N position density.
