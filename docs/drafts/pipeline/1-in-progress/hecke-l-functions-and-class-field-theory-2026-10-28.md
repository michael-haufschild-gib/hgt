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
- [x] HL3 `L(s, ψ)`: absolute convergence over ideals for `Re s > 1`, prime-ideal Euler product,
      nonvanishing there, and `ψ = 1` vs `ζ_K` — `summable_norm_heckeIdealTerm`,
      `heckeL_eq_tsum_ideals`, `heckeL_eulerProduct_hasProd`, `heckeL_ne_zero`,
      `heckeL_one_eq_dedekindZeta_mul`
- [x] HL4 ray-class ideal counts with power saving and equal densities —
      `exists_abs_ncard_rayClassIdeals_sub_le` (`#{𝔞 ∈ c : N𝔞 ≤ x} = κ_𝔪 x + O(x^{1−1/n})`, one
      `κ_𝔪` for all `c`); `rayDensity_pos`; `exists_norm_sum_heckeCoeff_le`
      (`Σ_{N𝔞≤x} ψ(𝔞) = O(x^{1−1/n})`, `ψ ≠ 1`)
- [x] HL5 continuation to `Re s > 1 − 1/n`; holomorphic at `1` for `ψ ≠ 1`; residue for `ψ = 1` —
      `differentiableOn_heckeLCont`, `exists_norm_heckeL_le`, `heckeL_one_eq`,
      `tendsto_sub_one_mul_heckeL_one` (via `HTGeometry.BoundedPartialSums.contLSeries`),
      `heckeDensity_eq_dedekindZeta_residue_mul`, `heckeDensity_pos`
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

## Completed Euler-product and residue batch

See [the formalized proof and declarations](../3-formalized/hecke-prime-ideal-euler-product-and-positive-residue.md).
Four modules identify ideals with prime exponent vectors, transfer the existing occupation
Euler product to the actual coefficient L-series, prove nonvanishing on `Re s > 1`, remove
the finite-modulus Euler factors from Dedekind zeta, and identify the positive residue and
positive ray-class densities. The prior residue limit alone did not establish positivity.

All nine audited results depend only on `propext`, `Classical.choice`, and `Quot.sound`.
All four modules passed final direct source checks with `lake --old env lean`.
The programme is wired into `MainTheorems.lean`;
no umbrella is compiled. HL6, HL7 and CFT remain open.

## Next analytic input

For HL6, the corpus search did not find general Hecke nonvanishing at one. Mathlib
`NumberTheory/LSeries/Nonvanishing.lean` supplies the Dirichlet-character model:
`norm_LSeries_product_ge_one` uses the local `3 + 4 cos θ + cos 2θ ≥ 0` inequality and
summable logarithms. Its generic local logarithm lemma is private. Adapt the mechanism to the
actual prime-ideal Euler factors, then combine with the existing continuation and residue
bounds for characters with `ψ ^ 2 ≠ 1`. This is a next proof obligation, not a completed theorem.
The requested ordering is Hecke first, CFT second. Real-character nonvanishing therefore needs
the analytic route through HL7 and Landau positivity; it must not be postponed to reciprocity.

### Active nonquadratic proof

Construct the summable prime-ideal Euler logarithm and prove the local `3–4–1` inequality.
For real `σ > 1` this gives `|L(σ,1)^3 L(σ,ψ)^4 L(σ,ψ²)| ≥ 1`.
If `ψ² ≠ 1` and `L(1,ψ) = 0`, the existing holomorphic continuation gives a finite
limit for `L(σ,ψ)/(σ-1)`, while `(σ-1)L(σ,1)` and `L(σ,ψ²)` have finite limits.
Their product times `σ-1` is the displayed product and tends to zero, contradicting
the lower bound. No full-plane continuation or reciprocity is needed for this case.

### Full-continuation dependency audit

Corpus leads inspected while formalizing HL6:

- `RHTower/EpsteinCharacterFunctionalEquation.lean` proves a binary-lattice theta
  transformation with a Dirichlet character modulo a prime. It is a concrete model,
  not the arbitrary-number-field theorem.
- `HTGeometry/DirichletCoefficientTheta.lean` supplies convergence and the Mellin transform
  of a theta series attached to any absolutely convergent coefficient series. It supplies
  no arithmetic theta inversion and therefore cannot by itself extend `heckeL` to all `ℂ`.
- `HTGeometry/FinitePiProductSummability.lean` has polynomial-Gaussian summability on `ℤ^n`.
- `HTGeometry/RemovableSingularity.lean` supplies the derivative quotient limit used for HL6.

HL7 must construct the ideal-lattice theta transformation, account for the unit action and
archimedean signs, and identify its Mellin transform with the actual Hecke ideal series.
These identities remain proof obligations; no functional-equation interface is assumed.
