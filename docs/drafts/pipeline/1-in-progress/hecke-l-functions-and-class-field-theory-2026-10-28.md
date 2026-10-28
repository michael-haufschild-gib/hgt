# Hecke L-functions and class field theory

- **ID:** hecke-cft
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean) programme
- **Source:** user goal 2026-10-28; ArtinMertens S8 (non-rational Artin characters)
- **Statement:** for a number field `K` and a modulus `𝔪 = 𝔪₀ 𝔪∞`: the ray class group `Cl_𝔪` is finite;
  every character `ψ` of `Cl_𝔪` has an L-function `L(s, ψ) = Σ_𝔞 ψ(𝔞) N𝔞^{−s}` with Euler product,
  meromorphic continuation to the complex plane, the completed functional equation for primitive
  characters, a pole at `s = 1` exactly for `ψ = 1`, and `L(1, ψ) ≠ 0` for `ψ ≠ 1`;
  for every finite abelian `L/K` the Artin map gives `Cl_𝔪/H ≅ Gal(L/K)` (reciprocity), and
  every congruence subgroup `H` is the norm group of an abelian extension (existence).

## Goal
Programme folders `formal/GaloisForLFunctions/HeckeLFunctions/` (first) and
`formal/GaloisForLFunctions/ClassFieldTheory/` (second), each with its umbrella.

## Gates — Hecke L-functions
- [x] HL1 moduli; ideals coprime to `𝔪`; `K_𝔪` (elements prime to `𝔪`), the ray group `K^{𝔪,1}_+`;
      reduction `K_𝔪 → (𝓞/𝔪)ˣ × {±1}^{𝔪∞}` with kernel `K^{𝔪,1}_+`; `Cl_𝔪 = I^𝔪/P_𝔪`; map to `Cl_K`
      surjective with finite kernel ⇒ `Cl_𝔪` finite — `finite_rayClassGroup`,
      `toClassGroup_surjective`, `range_rayResidueClass`
- [x] HL2 ray class characters on integral ideals; multiplicativity; convergence for `Re s > 1` —
      `heckeValue_mul`, `lSeriesSummable_heckeCoeff`
- [ ] HL3 `L(s, ψ)`: absolute convergence `Re s > 1`, Euler product over prime ideals, `ψ = 1` vs `ζ_K`
- [x] HL4 ray-class ideal counts with power saving and equal densities —
      `exists_abs_ncard_rayClassIdeals_sub_le` (`#{𝔞 ∈ c : N𝔞 ≤ x} = κ_𝔪 x + O(x^{1−1/n})`, one
      `κ_𝔪` for all `c`); `exists_norm_sum_heckeCoeff_le` (`Σ_{N𝔞≤x} ψ(𝔞) = O(x^{1−1/n})`, `ψ ≠ 1`)
- [x] HL5 continuation to `Re s > 1 − 1/n`; holomorphic at `1` for `ψ ≠ 1`; residue for `ψ = 1` —
      `differentiableOn_heckeLCont`, `exists_norm_heckeL_le`, `heckeL_one_eq`,
      `tendsto_sub_one_mul_heckeL_one` (via `HTGeometry.BoundedPartialSums.contLSeries`)
- [ ] HL6 `L(1, ψ) ≠ 0` for non-real `ψ` by Euler-factor positivity; real `ψ` by full continuation
      and Landau positivity after HL7; Mertens for Hecke characters
- [ ] HL7 Hecke's functional equation (theta series, Poisson summation, Mellin transform)

## Gates — class field theory
- [ ] CFT1 Artin map on ideals prime to the ramification of an abelian `L/K`
- [ ] CFT2 norm groups `P_𝔪 N(I_L^𝔪)`; primes splitting completely; logarithmic densities
- [ ] CFT3 second inequality `[I^𝔪 : P_𝔪 N] ≤ [L : K]` (analytic, HL5)
- [ ] CFT4 first inequality for cyclic `L/K` (Herbrand quotients of units and local norm indices)
- [ ] CFT5 Artin reciprocity (Artin's cyclotomic crossing)
- [ ] CFT6 existence theorem (Kummer theory)
- [ ] CFT7 consequences: Chebotarev, `L(1, ψ) ≠ 0` for all `ψ ≠ 1`, abelian Artin `L` = Hecke `L`,
      Mertens for every Artin `L`-function (ArtinMertens S8)

## Building blocks (corpus/Mathlib)
- Mathlib: `FractionalIdeal.count`, `toPrincipalIdeal`, `ClassGroup`, adic valuations, `LSeries`,
  Euler products, Dedekind zeta and residue, Hilbert ramification theory, `IsArithFrobAt`.
- ArtinMertens: lattice counts in dilates of Lipschitz domains, `normLeOne` frontier, Weber's theorem,
  Abel summation, Frobenius counting in fixed fields.
- `RHTower/Artin`: Artin Euler products, Frobenius reciprocity, virtual characters.
- `HTGeometry/ABHN`: local Brauer invariants, cyclic algebras, unramified local reciprocity, norm
  quotients of cyclic Galois extensions.

## Log
- 2026-10-28 — created; corpus/Mathlib survey: no ray class groups, Hecke characters, idèle class
  group or reciprocity map.

## Current work

HL3: identify the absolutely convergent coefficient L-series with the sum over nonzero ideals,
then use unique ideal factorization and the existing
`HTGeometry.hasProd_inv_one_sub_nome` to prove the prime-ideal Euler product.
The trivial character must also be compared with Dedekind zeta by deleting the finitely many
Euler factors in the finite modulus. No analytic continuation or reciprocity premise is to be
introduced. Existing HL1, HL2, HL4 and HL5 sources were inspected; HL6, HL7 and CFT remain open.

- `NonzeroIdealsArePrimeExponentVectors.lean`: compiled successfully. Defines
  `primeExponentsIdealEquiv`, with inverse identities and valuation readback.
- `HeckeLSeriesHaveEulerProducts.lean`: compiled successfully. Includes
  absolute convergence over individual ideals, equality with the coefficient series, the
  prime-ideal Euler product and nonvanishing on `Re s > 1`.
- `TheTrivialCharacterRemovesTheModulusEulerFactors.lean`: compiled successfully.
  Compares the unit-modulus series with Dedekind zeta
  and removes precisely the finite-modulus Euler factors.
- Audited reused inputs `HTGeometry.hasProd_inv_one_sub_nome` and
  `lSeriesSummable_heckeCoeff`: only `propext`, `Classical.choice`, `Quot.sound`.
- The new factorization equivalence, ideal summability, coefficient/ideal sum equality,
  prime-ideal Euler product, nonvanishing on `Re s > 1`, and finite Euler-factor deletion theorem
  also passed `#print axioms` with only those three standard axioms.
- Source audit found no positivity theorem for `heckeDensity` or `rayDensity`. The existing
  residue limit alone does not certify a genuine pole. `TheTrivialCharacterHasAPositiveResidue.lean`
  now derives the explicit Euler-corrected residue and its positivity; awaiting compilation.

## Next analytic input

For HL6, the corpus search did not find general Hecke nonvanishing at one. Mathlib
`NumberTheory/LSeries/Nonvanishing.lean` supplies the Dirichlet-character model:
`norm_LSeries_product_ge_one` uses the local `3 + 4 cos θ + cos 2θ ≥ 0` inequality and
summable logarithms. Its generic local logarithm lemma is private. Adapt the mechanism to the
actual prime-ideal Euler factors, then combine with the existing continuation and residue
bounds for characters with `ψ ^ 2 ≠ 1`. This is a next proof obligation, not a completed theorem.
The requested ordering is Hecke first, CFT second. Real-character nonvanishing therefore needs
the analytic route through HL7 and Landau positivity; it must not be postponed to reciprocity.
