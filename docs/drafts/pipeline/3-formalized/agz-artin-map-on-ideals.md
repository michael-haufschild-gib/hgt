# The Artin map on ideals

- **ID:** agz-artin-map-on-ideals
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** docs/reports/review-1211/obstacles-summary.md §2.14 question 4 (A154); gates G2, G3 of
  `agz-artin-reciprocity-law`
- **Statement:** Let `L/K` be an abelian extension of number fields with group `G` and `𝔪` a
  modulus of `K` divisible by the ramified primes. The Artin map `ω : I^𝔪 → G`, `v ↦ Frob_v`, is
  a surjective homomorphism, `N_{L/K}(I_L^𝔪) ⊂ ker ω` and `[I^𝔪 : ker ω] = [L : K]`. If
  `P_𝔪 ⊂ ker ω`, then for every character `χ` of `G`, `χ ∘ ω` is a ray class character modulo `𝔪`
  and `L(s, χ, L/K) = L(s, χ ∘ ω) · Π_{v | 𝔪} (1 − (χ, v) N(v)^{-s})^{-1}` for `Re s > 1`.

## Goal
The reciprocity law becomes one inclusion: `P_𝔪 ⊂ ker ω`.

## Gates
- [x] A1 `Frob_v` does not depend on the prime above an unramified `v`
- [x] A2 norms are in the kernel
- [x] A3 an extension in which almost all primes split completely is trivial
- [x] A4 the Artin map is onto
- [x] A5 `P_𝔪 ⊂ ker ω` gives the Hecke `L`-series

## Approach
**A1.** Two primes `Q`, `gQ` above `v` have Frobenius elements conjugate by `g`; `G` is abelian,
so they agree modulo the inertia group, which is trivial. ∎

**A2.** For a prime `P` above `v`, `N_{L/K}(P) = v^f`, `f = f(P | v)`. `Frob_P^f` acts on the
residue field of `P`, of `N(v)^f` elements, as `x ↦ x^{N(v)^f}`, the identity. So `Frob_P^f` is in
the inertia group of `P`: for unramified `v`, `Frob_v^f = 1`; for ramified `v` the value of `ω`
is `1`. Multiplicativity gives `ω(N_{L/K} 𝔄) = 1`. ∎

**A3.** Let `M/K` be finite and every prime `P` of `M` above a prime `v` with `N(v) > B`
unramified with `N(P) = N(v)`. By `Σ e f = [M : K]`, exactly `[M : K]` primes lie above such
`v`, so `#{P : N(P) = p} ≥ [M : K] · #{v : N(v) = p}` for every rational prime `p > B`. With
`D_F(x) = Σ_{p ≤ x} #{P ⊂ 𝓞_F : N(P) = p} log p / p = log x + O(1)` for `F = K, M`:
`[M : K] (log x − C) ≤ log x + C'`. Hence `[M : K] = 1`. ∎

**A4.** Let `H` be the image of `ω`, `M = L^H`, `P` a prime of `M` above `v ∤ 𝔪` and `Q` a prime
of `L` above `P`. `σ = Frob_Q ∈ H` fixes `M` and acts on the residue field of `Q` as
`x ↦ x^{N(v)}`: on the residue field of `P`, `x^{N(v)} = x`, so it has at most `N(v)` elements
and `N(P) = N(v)`. `e(Q | v) = |I_Q| = 1` and `e(P | v)` divides it. By A3, `M = K`, so
`|H| = [L : M] = [L : K] = |G|`. ∎

**A5.** `χ ∘ ω` descends to `Cl_𝔪` and has the value `χ(Frob_v) = (χ, v)` at `v ∤ 𝔪`. ∎

## Lean
`formal/GaloisForLFunctions/RHTower/Artin/`:
- `TheArtinMapOnIdealsKillsNorms.lean`: `IsUnramifiedPrime`, `frobeniusElement`,
  `arithFrobAt_eq_frobeniusElement` (A1), `artinSymbol_eq_apply_frobeniusElement`,
  `arithFrobAt_pow_inertiaDeg_mem_inertia`, `artinMap`, `artinMap_idealUnit_relNorm` (A2),
  `artinHeckeCharacter`, `artinEulerProduct_eq_heckeL_mul_of_rayPrincipal_le_ker` (A5).
- `ExtensionsInWhichAlmostAllPrimesSplitCompletelyAreTrivial.lean`:
  `card_primesOverFinset_eq_finrank`, `finrank_mul_degreeOneCount_le`,
  `finrank_eq_one_of_forall_split` (A3).
- `TheArtinMapIsSurjective.lean`: `absNorm_under_eq_of_isArithFrobAt_fixes`,
  `ramificationIdx_under_eq_one_of_inertia_eq_bot`, `eq_top_of_forall_frobeniusElement_mem`,
  `exists_mem_idealGroup_artinMap_eq`, `index_ker_artinMap` (A4).

## Log
- 2026-11-13 — A1–A5 proved and formalized
