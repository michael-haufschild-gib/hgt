# Prime-center bound at exponent 5/6 for the sharp Chebyshev midpoint

- **ID:** elt-prime-centers-five-sixths-midpoint
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** `docs/reports/review-1911/todo.md` #12 · `formal/GaloisForLFunctions/ExceptionalLayerTheory/SquareConductors/PrimeCentersOfTheSharpMidpoint.lean`
- **Statement:** Prove that for every `5 / 6 < t < 1` there exists `C : ℝ` such that for every prime `p : ℕ`, `primeMidpointPrice p ≤ C * (p : ℝ) ^ t`, where `primeMidpointPrice n = 2 * θ(3n) - θ(2n) - θ(4n)`.

## Goal
Improve the unconditional zero-free half-plane for `ζ(s)` from `Re s > 20999 / 24000` (`SubSevenEighthsZeroFreeHalfPlane`) to `Re s > 5 / 6` (`zetaZeroAbscissa ≤ 5 / 6`), yielding `|seventeenNinthsConductorPrefix N| ≤ C * N ^ (11 / 3)`, the sixth-power reciprocal-prime octave deficit bound, and removable prime heads through `X ^ (3 / 5)`.

## Gates
- [x] 0 → 1  in-progress: exact equivalences (`prime_centers_iff_eleven_thirds`, `ordinary_prime_center_spectrum`, `one_prime_range_at_each_midpoint`, `exceptional_count_midpoint_spectrum`) verified
- [ ] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [ ] 2 → 3  formalized: Lean theorem in `ExceptionalLayerTheory/SquareConductors/`, `lake --old env lean` green, standard axioms only

## Approach and Open Mathematical Core

1. **Established equivalences.**
   By `ordinary_prime_center_spectrum` (`SparseExceptionsAtTheOrdinaryPrimeMidpoint.lean:127`) and `prime_centers_iff_eleven_thirds` (`PrimeCentersOfTheSharpMidpoint.lean:71`), for `b = 5 / 6`:
   - `(∀ t, 5 / 6 < t → t < 1 → ∃ C, ∀ p, p.Prime → primeMidpointPrice p ≤ C * p ^ t)`
   - `↔ zetaZeroAbscissa ≤ 5 / 6`
   - `↔ ∃ C ≥ 0, ∀ N, |seventeenNinthsConductorPrefix N| ≤ C * N ^ (11 / 3)`
   - `↔ (∀ t, 5 / 6 < t → t < 1 → ∃ C K, 0 ≤ K ∧ ∀ᶠ x in atTop, deletedCount {p | C * p ^ t < primeMidpointPrice p} x ≤ K * x ^ t)`.

2. **Available prime-center and five-band decompositions.**
   - At a prime center `p`, `p.divisors = {1, p}`, `squarefreeDivisorMass p = 2`, and `prime_center_clipped_density` bounds `|primitiveCofactorLength p Q - reflectedDensity * (p - 1)| = O(1)` uniformly for `1 ≤ Q`, `Q^2 ≤ 4p`.
   - For `x = 4p` and `b = 5 / 6`, `ordinary_prime_bands_measure_midpoint` shows that every `a ∈ [1/6, 5/6]` (in particular the five disjoint bands `a_j = j / 6`, `j ∈ {1, 2, 3, 4, 5}`, supported on `x^{j/6} < q < x^{(j+1)/6}` with cofactor cut `V_j = ⌊x^{(5-j)/6}⌋`) satisfies `|ordinaryPrimeBandPrice (5/6) a p - primeMidpointPrice p| ≤ C_ε p^{5/6 + ε}`.
   - `first_projected_cofactor_octave` identifies the projected weight `truncMoebiusDivisorSum V v = -μ(v)` on `V < v ≤ 2V`.

3. **Formalized reductions, sieves, column identities, and obstructions.**
   - `SquareConductors/TheTopPrimeBandAndReflectedShellBarrier.lean`: exact `V = 1` (`a = b`) algebraic collapse (`remainingPrimitivePrimePrice p Q 1 = unrestrictedLargePrimePrice p Q`, `ordinaryPrimeBandPrice b b p` identity), Chebyshev-`θ` cofactor-slice self-duality (`cofactorThetaSlice_eq_chebyshev_theta`, `cofactorThetaSlice_mul_eq_neg_primeMidpointPrice`), and `prime_centers_shell_eight_ninths_iff_five_sixths`.
   - `CoherenceTheoryOfReciprocityFamilies/TheShortSexticLargeSieve.lean`: unrestricted fifth-power conjugation `\overline{χ_u(x)} = χ_u(x)^5` across all `x ∈ ℤ[ω]` and smooth Schur sextic large sieve (`short_sextic_large_sieve`).
   - `OrderSixMetaplecticTheory/CubeTwistedColumnsAndCrossPhaseCollapse.lean`: phase-free column Hasse–Davenport (`rowRoot_column_hasseDavenport_clean`), cube-multiplied column shift (`sexticGauss_mul_cube`, `orderB_coupled_column_collapse`), and purely cubic cross-phase factorization (`sexticGauss_mul_quadGauss_prod_cubic_cross`).
   - `FamilyContinuationTheory/CyclotomicParityAndTwistCouplingObstructions.lean`: cyclotomic Gauss-monomial index `n / 6` conservation (`unique_low_cover_quadratic_order`), $L^{2r}$ Hölder-reflection duality gap, planted conjugate-character multilinear saturation, twist-coupling Cauchy–Schwarz and off-diagonal noise bounds, double obstruction at `(1/3, 1/3, 1/3)`, outer-CS `11/12` floor, and direct vs. reflected `w`-contour identity.

4. **`[OPEN CORE]`:**
   Obtain an unconditional upper bound `≤ C_t p^t` (`5 / 6 < t < 1`) either directly on `min_{1 ≤ j ≤ 5} ordinaryPrimeBandPrice (5/6) (j/6) p` / recombined cofactor octaves / cube-root composite decomposition at prime centers `p`, or analytically on `zetaZeroAbscissa ≤ 5 / 6`.

## Log
- 2026-11-20 — created in `1-in-progress` with exact equivalence audit and prime-center / five-band structure.
