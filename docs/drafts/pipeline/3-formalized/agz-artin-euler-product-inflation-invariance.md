# Artin Euler products are invariant under inflation

- **ID:** agz-artin-inflation
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** docs/reports/review-1211/obstacles-summary.md §2.14 question 4 (A154); gate G1 of
  `agz-artin-reciprocity-law`
- **Statement:** Let `K ⊂ M ⊂ L` be number fields, `L/K` and `M/K` Galois with groups `G`, `G'`,
  `π : G → G'` the restriction, `ρ'` a representation of `G'`. Then the local Euler polynomial of
  `ρ' ∘ π` over `L/K` at every prime of `K` is that of `ρ'` over `M/K`, and
  `L(s, ρ' ∘ π, L/K) = L(s, ρ', M/K)`. For a linear character `χ'` of `G'`:
  `(χ' ∘ π, v)_{L/K} = (χ', v)_{M/K}`.

  Consequence: if `L = K(ζ_m)`, every linear character `χ'` of `Gal(M/K)` has a ray class
  character `ψ` modulo `(m)∞` with
  `L(s, χ', M/K) = L(s, ψ) · Π_{v | m} (1 − (χ', v) N(v)^{-s})^{-1}` for `Re s > 1`.

## Goal
The third law of the Artin formalism of the Euler products (additivity, induction, inflation).
It carries the cyclotomic reciprocity law to every abelian extension inside a cyclotomic
extension of `K`.

## Gates
- [x] F1 means along a surjective homomorphism; Frobenius traces along a homomorphism onto the
  inertia group
- [x] F2 restriction maps the inertia group of `Q` onto the inertia group of `Q ∩ B`
- [x] F3 local polynomials; Euler products; Artin symbols; cyclotomic towers

## Approach

**F1.** `p : I → J` a surjective homomorphism of finite groups, `F` on `J`. All fibres of `p` have
`c = |ker p|` elements and `|I| = c |J|`, so `|I|^{-1} Σ_I F∘p = |J|^{-1} Σ_J F`. Let
`π : Γ → Γ'` with `π(I) = I'`, `φ ∈ Γ`. Then
`|I|^{-1} Σ_{τ∈I} χ'(π(φ^m τ)) = |I'|^{-1} Σ_{τ'∈I'} χ'(π(φ)^m τ')`: the Frobenius traces of
`χ' ∘ π` for `(I, φ)` are those of `χ'` for `(I', π(φ))`. They depend on `φ` only through the
coset `φ I` when `φ` normalizes `I`. ∎

**F2.** `A ⊂ B ⊂ C` rings, `G` acting on `C`, `G'` on `B`, `π : G → G'` surjective with
`(πg) b = g b` on `B`; `H ≤ ker π` with `C^H = B`, `H` finite. `Q` a prime of `C`, `Q' = Q ∩ B`.
(⊆) `τ ∈ I_Q`: `(πτ) b − b = τ b − b ∈ Q ∩ B`.
(Frobenius) `φ c ≡ c^q mod Q` for all `c` gives `(πφ) b ≡ b^q mod Q'`.
(⊇) Let `πg ∈ I_{Q'}`. Then `(gQ) ∩ B = (πg) Q' = Q'`, and `H` is transitive on the primes of `C`
above `Q'`: `hgQ = Q` for some `h ∈ H`; `σ = hg` has `πσ = πg`. The automorphism of `C/Q` induced
by `σ` fixes the image of `B/Q'` (`σ b − b = (πg) b − b ∈ Q`). The decomposition group of `Q` in
`H` maps onto `Aut((C/Q)/(B/Q'))`: there is `n ∈ H` with `nQ = Q` and `σ c ≡ n c mod Q` for all
`c`. Then `τ = σ n^{-1} ∈ I_Q` and `πτ = πg`. ∎

**F3.** By F2 and F1 the Frobenius traces of `ρ' ∘ π` for `(I_Q, φ_Q)` are those of `ρ'` for
`(I_{Q'}, π φ_Q)`, and `π φ_Q ∈ φ_{Q'} I_{Q'}` (two Frobenius elements at `Q'` differ by inertia).
A polynomial with constant term `1` is determined by its power traces
(I2(b) of `agz-artin-euler-factors-under-induction`): the local polynomials at `Q` and `Q'` agree.
For number fields: `π` is the restriction, `H` the automorphisms of `L` fixing `M`
(`C^H = B` for the rings of integers); a prime `Q` of `L` above `v` has `Q ∩ M` above `v`. The
Euler products agree factor by factor. For a linear character the line of `χ' ∘ π` is the line
of `χ'` composed with `π`. If `L = K(ζ_m)`, apply R3 of `agz-cyclotomic-reciprocity-law` to
`χ' ∘ π`. ∎

## Lean
All in `formal/GaloisForLFunctions/RHTower/Artin/`.
- F1, F2 `ArtinLocalEulerFactorOfAnInflatedRepresentation.lean`:
  `inv_card_mul_sum_comp_surjective`, `frobeniusTrace_mul_mem`,
  `frobeniusTrace_comp_of_map_eq`, `map_mem_inertia_under`, `isArithFrobAt_map_under`,
  `under_smul_eq_map_smul_under`, `exists_mem_inertia_map_eq`,
  `map_inertia_eq_inertia_under`, `frobeniusInertiaEulerPolynomial_comp_eq`.
- F3 `ArtinEulerProductIsInvariantUnderInflation.lean`: `linearCharacterLine_comp`,
  `algebraMap_restrictHom_smul_ringOfIntegers`, `restrictHom_eq_one_of_mem_fixingSubgroup`,
  `numberFieldFinitePlaceLocalEulerPolynomial_inflation`,
  `numberFieldFinitePlaceArtinEulerReciprocalProduct_inflation`, `artinSymbol_inflation`,
  `exists_artinEulerProduct_eq_heckeL_mul_of_adjoin_eq_top_of_tower`.

## Log
- 2026-11-13 — F1–F3 proved and formalized
