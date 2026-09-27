# Cofinal three-prime Stokes holonomy at every nonzero grade — Lean certificate

- **Paper card:** `stc-cofinal-triangle-holonomy-all-grades.md`
- **Lean modules:** `GaloisForLFunctions.RHTower.STCCofinalTriangleHolonomy`
  (log form (2) in `GaloisForLFunctions.RHTower.STCOrderedCurvatureRank`)
- **Umbrella:** `GaloisForLFunctions.RHTower`
- **Verification:** `lake --old build`; `lake --old env lean` clean; `#print axioms` =
  `propext`, `Classical.choice`, `Quot.sound`; no `sorry`.

`Ω_pqr(g) = stokesTriangleCharge p q r g`; the limit is along all natural `r → ∞`, hence along primes.

| Card item | Lean theorem |
|-|-|
| oddness `c_pq(-g) = -c_pq(g)` | `routeRCrossPrimeStokesOddCurvature_neg_grade`, `stokesTriangleCharge_neg_grade` |
| `R_pr = sinh z / sinh x` | `routeRCrossPrimeStokesRatio_eq_sinh_div` |
| (2) polar form | `routeRCrossPrimeStokesOddCurvature_log_form` |
| (2a) rational normal form in `P = p^g`, `R = r^g` | `routeRCrossPrimeStokesOddCurvature_rational` |
| (3) `c_pr(g)/r^g → -1/(1-p^{-g})` | `tendsto_stokesOddCurvature_div_rpow` |
| (1) `Ω_pqr(g)/r^{|g|} → sign(g)[…]` | `tendsto_stokesTriangleCharge_div_rpow` |
| bracket strictly positive | `stokesHolonomyCoefficient_pos` |
| sign of `g`, growth `≥ C r^{|g|}` | `eventually_stokesTriangleCharge_growth` |
| no one-prime potential at any nonzero grade | `no_stokes_prime_potential` |
| sign change between `(3,5,7)` and `(3,5,r)` at small `g > 0` | `stokes_triangle_sign_change` |
| (4) correction triangle identity | `stokes_correction_triangle` |
| (5) `|B_pr| + |B_qr| ≥ C r^{|g|}` | `stokes_correction_row_growth` |
| rows not both in the reciprocal-Euler Hilbert space | `stokes_correction_rows_not_hilbert` |
