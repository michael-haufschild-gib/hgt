# Hecke L-functions and class field theory

- **ID:** hecke-cft
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean) programme
- **Source:** user goal 2026-10-28; ArtinMertens S8 (non-rational Artin characters)
- **Statement:** for a number field `K` and a modulus `𝔪 = 𝔪₀ 𝔪∞`: the ray class group `Cl_𝔪` is finite;
  every character `ψ` of `Cl_𝔪` has an L-function `L(s, ψ) = Σ_𝔞 ψ(𝔞) N𝔞^{−s}` with Euler product,
  continuation to `Re s > 1 − 1/n`, a pole at `s = 1` exactly for `ψ = 1`, and `L(1, ψ) ≠ 0` for
  `ψ ≠ 1`; for every finite abelian `L/K` the Artin map gives `Cl_𝔪/H ≅ Gal(L/K)` (reciprocity), and
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
- [ ] HL6 `L(1, ψ) ≠ 0` for non-real `ψ` (product of all `L(s, ψ)` has `|·| ≥ 1`); Mertens for Hecke
      characters; real `ψ` after CFT
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
