# Literature capstones: live facts

## Closed in Lean

- **Toeplitz reverse:** `exists_atomic_caratheodoryFejer_psd_factorization` gives exact nonnegative unit-circle atomic Vandermonde factorization of normalized Hermitian PSD Toeplitz data.
- **CCM:** `ccmLambertEntrySeries_coeff_literal_dyadicCyclotomic` gives every coefficient of the full formal Lambert entry series in `ℤ^cyc[1/2]`; `ccmActualFiniteQNormalizedDeterminant_coeff_dyadicCyclotomic` transports containment to every finite normalized determinant coefficient. No analytic-convergence claim.
- **Burnol:** `isCompleteSystem_burnolZetaJetVector_iff_one_le` gives exact aperture threshold for literal Riesz zero-jet vectors. `BurnolCoPoissonSourceHasExactXiJetOrder` gives cosine-closed exact completed-jet detection. No quotient-system completeness claim.

## Open

- **Q8 witness:** actual SST field, `Gal ≃ Q8`, unique 2D representation, maximal abelian fixed field, Euler product, two-adic decomposition/inertia, lower groups, conductor `6`, and finite Fröhlich sign `-1` are formalized.
- **Primary-source correction:** Fröhlich Theorem 6(i) requires every prime divisor of `disc(K)` to be `1 mod 4`; it does **not** require `disc(N)` odd for `W_N = α_K β_K`. Here `K = ℚ(√5,√41)`, so primes are `5,41`. Wild ramification of `N` at `2` is no obstruction.
- **Lean applicability:** `deningerQ8_froehlichTheoremSix_i_applicability` bundles maximal-abelian fixed-field identity, the exact discriminant-prime gate, and `α_Kβ_K=-1`; leaf build and standard-axiom audit pass.
- Missing proof obligation: formalize Theorem 6(i) against an independently defined Artin root number and instantiate `W_N = α_K β_K = -1`. No local-ε detour and no definition-by-fiat.

## Current target

Formalize and instantiate Fröhlich Theorem 6(i), preserving independent global Artin ε/root-number semantics.
