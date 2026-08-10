# Prime-winning Čech resolution of the Riemann shell divisor — formalized closure

- **ID:** `prime-winning-cech-divisor-resolution-formalized`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Paper proof:** `./prime-winning-cech-divisor-resolution.md`
- **Scientific status:** `[PAPER-PROVED] [LEAN-PROVED] [OPEN CORE REMAINS]`

## Lean modules

New in this closure:

- `GaloisForLFunctions.RHTower.PrimeWinningFaceSeries` — the winner-face Dirichlet series, its
  reduction to a multiplicative function, and the Euler product `(13)`–`(14)`–`(16)`.
- `GaloisForLFunctions.RHTower.PrimeWinningFaceDivisor` — the face divisor `(17)` and the principal
  conormal jets `(19)`–`(20)`.
- `GaloisForLFunctions.RHTower.PrimeWinningFaceAugmentation` — the complementary factorization
  `(22)` and the identification of the augmentation with the shell multiplier `(21)`.

Pre-existing and reused:

- `PrimeWinningFaceUnit` (the unit `U_{F,m}`, its nonvanishing, holomorphy and flat transition);
- `PrimeDilationTropicalBoundaryTomography` (the source semilattice and the alternating Čech
  augmentation of the shell indicator, i.e. `(4)`–`(7)`);
- `MFreeLadder` (`natCast_mul_cpow`, `natCast_pow_cpow`);
- `HighExponentShellZeroFree` (`shellMultiplier`, the corpus form of `H_m`);
- mathlib `riemannZeta_eulerProduct_hasProd`, `ArithmeticFunction.IsMultiplicative.eulerProduct_hasProd`.

Umbrella: `GaloisForLFunctions.RHTower`.

## Formal theorem chain

1. **Faithfulness of the face condition.**  `IsWinnerFace F m n` is `(3)`; for a nonempty face and
   `m ≥ 1`, `isWinnerFace_iff_maxPrimeExponent` proves it is exactly `M(n) = m` together with every
   prime of `F` being a winner, where `maxPrimeExponent` is `M(n)` of `(1)`.
2. **Winner-block reindexing.**  The face indicator is not multiplicative (it vanishes at `n = 1`),
   so the block `faceBlock F m = ∏_{p ∈ F} p^m` is divided out:
   `isWinnerFace_faceBlock_mul_iff` characterizes the quotient condition, and
   `faceBlock_dvd_of_isWinnerFace` shows the block divides every winner.
   `faceSeries_eq_faceBlock_mul` is the first line of `(14)`.
3. **Euler product of the reduced series.**  `isReducedFace_mul_iff` proves multiplicativity of the
   reduced condition on coprime arguments (coprimality is essential: the exponent cap does not
   factor over general products), `isMultiplicative_reducedFaceCpow` and
   `summable_norm_reducedFaceCpow` feed the mathlib Euler product, and the local factors are `1` on
   the face and the truncated geometric sum off it.
4. **The face Euler product `(16)`.**  `tsum_reducedFaceCpow_mul_zeta` multiplies the reduced Euler
   product by `ζ((m+1)s)`, turning it factorwise into the zeta Euler product corrected on the finite
   face; `faceSeries_eq_zeta_mul_faceUnit` is `B_{F,m}(s) = ζ(s) U_{F,m}(s)` for `Re s > 1`.
5. **The face divisor `(17)`.**  `analyticOrderAt_faceFunction`: on `Re s > 1/2`, the continued face
   function `faceFunction F m = ζ · U_{F,m}` has exactly the analytic order of `ζ`, with
   multiplicity, because the unit is analytic and nonvanishing there.
6. **The principal conormal chart `(19)`–`(20)`.**  `iteratedDeriv_faceFunction_eq_zero` and
   `iteratedDeriv_faceFunction` are the jet law at a zeta zero of order `d`;
   `iteratedDeriv_faceFunction_ratio` gives
   `B^{(d)}_{F ∪ {p},m}(ρ) / B^{(d)}_{F,m}(ρ) = R_{p,m}(ρ)`.
7. **Euler augmentation `(21)`–`(22)`.**  `sum_alternating_prod_faceTransitionUnit` is the finite
   inclusion–exclusion `∑_{∅ ≠ t ⊆ S} (-1)^{|t|+1} ∏_{p ∈ t} R_{p,m} = 1 - ∏_{p ∈ S}(1 - R_{p,m})`;
   `one_sub_faceTransitionUnit` is `1 - R_{p,m} = (1 - p^{-ms})/(1 - p^{-(m+1)s})`;
   `hasProd_one_sub_faceTransitionUnit` evaluates the product over all primes as
   `ζ((m+1)s)/ζ(ms)`; and `faceAugmentation_eq_shellMultiplier` identifies the corrected
   complementary product with the corpus `shellMultiplier m s = ζ((m+1)s)⁻¹ - ζ(ms)⁻¹`.

## New reusable asset

`hasProd_one_sub_primeCpow_neg` : `HasProd (fun p : Nat.Primes => 1 - p^(-w)) (riemannZeta w)⁻¹`
for `Re w > 1`.  The corpus previously owned only the value at `w = 2`
(`hasProd_one_sub_prime_cpow_neg_two`) and an unnamed `calc` step inside
`fredholmDet1_eq_inv_riemannZeta`.  The proof multiplies the multipliable reciprocal family against
the mathlib zeta Euler product and uses uniqueness of infinite products, so it needs no Möbius
inversion.

## Verification

- `lake env lean` clean, with no warnings, on all three new modules.
- `lake build GaloisForLFunctions.RHTower.PrimeWinningFaceAugmentation` — green, with all three
  modules wired into the area umbrella.
- `#print axioms` on the ten capstones above: `propext`, `Classical.choice`, `Quot.sound` only.

## Scope boundary

The Euler product `(16)` is stated on `Re s > 1`, where the face Dirichlet series converges; the
unit and divisor statements hold on the whole strict critical half-plane, and the continued face
function is the object carried there.  The infinite alternating sum over *all* finite prime sets in
`(21)` is formalized through its complementary-product form `(22)` rather than as a sum indexed by
`Finset Nat.Primes`.

The three gates left open on the paper card are the card's own open core and are not Lean gates:
the reflected controlled completion, conservative Xi conormal base change, and determinant
identification.

## Gates

- [x] 0 → 1
- [x] 1 → 2
- [x] 2 → 3 formalized
- [ ] 3 → 4 publication-ready
