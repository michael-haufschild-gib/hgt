# The reciprocity law for cyclotomic characters

- **ID:** agz-cyclotomic-reciprocity
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** docs/reports/review-1211/obstacles-summary.md §2.14 question 4 (A154)
- **Statement:** Let `L/K` be a Galois extension of number fields with group `G`, `ζ ∈ 𝓞_L` a
  primitive `m`-th root of unity, `κ : G → (ℤ/m)^×` the cyclotomic character (`σζ = ζ^{κ(σ)}`) and
  `ψ₀` a character of `(ℤ/m)^×`. Then `ψ₀ ∘ N̄` is a ray class character of `K` modulo `(m)∞`, and
  for `Re s > 1`

  `L(s, ψ₀ ∘ κ, L/K) = L(s, ψ₀ ∘ N̄) · Π_{v | m} (1 − (ψ₀ ∘ κ, v) N(v)^{-s})^{-1}`.

  If `L = K(ζ)`, every linear character of `G` is of the form `ψ₀ ∘ κ`.

## Goal
The reciprocity law of A154 in the cyclotomic case. By
`agz-artin-euler-factors-under-induction` and `agz-artin-euler-product-brauer-decomposition`,
every Artin Euler product is a product of integer powers of Euler products of linear characters
over intermediate fields; here those of cyclotomic type are identified with Hecke `L`-series. The
general linear character is `agz-artin-reciprocity-law` (class field theory).

## Gates
- [x] R0 the Artin symbol of a linear character; an Euler product with ray class values is a
  Hecke `L`-series; the trivial character and the Dedekind zeta function of an intermediate field
- [x] R1 the Artin symbol of `ψ₀ ∘ κ` at `v ∤ m` is `ψ₀(N(v) mod m)`
- [x] R2 the norm residue is a ray class character modulo `(m)∞`
- [x] R3 the `L`-series identity; cyclotomic extensions

## Approach

**R0.** `χ` linear, `I ⊴ D`, `φ ∈ D`. `Σ_{τ∈I} χ(φ^k τ) = χ(φ)^k Σ_{τ∈I} χ(τ)`, and the last sum
is `|I|` if `χ|_I = 1` and `0` otherwise (a non-trivial character of a finite group has sum `0`).
So the Frobenius traces of `χ` are the powers of `(χ; I, φ) := χ(φ)` (if `χ|_I = 1`) or `0`, and
by I2(b) of `agz-artin-euler-factors-under-induction` the local polynomial is `1 − (χ; I, φ)X`.
The Artin symbol `(χ, v)` is this value for the inertia group and a Frobenius element of a prime
of `L` above `v`. If `(χ, v) = ψ(v)` for every `v`, the Euler factors of `L(s, χ)` and `L(s, ψ)`
agree and both products converge for `Re s > 1`. For `χ = 1`: `(1, v) = 1`, the Euler product of
`ζ_K`. With I3: `ζ_M(s) = L(s, Ind_H^G 1, L/K)` for `H = Gal(L/M)`. ∎

**R1.** Let `Q` be an ideal of a domain `S`, `m ∉ Q`.
(i) If `η^m = 1` and `η ≡ 1 mod Q`, then `η = 1`: otherwise `1 + η + ⋯ + η^{m−1} = 0`, and the
sum is `≡ m mod Q`.
(ii) If `ξ^m = ζ^m = 1` and `ξ ≡ ζ mod Q`, then `ξ = ζ`: apply (i) to `η = ξ ζ^{m−1}`.
Let `Q` be a prime of `L` above `v`, `m ∉ v`; then `m ∉ Q`. For `τ ∈ I_Q`: `τζ ≡ ζ mod Q`, so
`τζ = ζ` by (ii), `κ(τ) = 1`. For the Frobenius element `φ` of `Q`: `φζ ≡ ζ^{N(v)}`, and both are
`m`-th roots of unity, so `φζ = ζ^{N(v)}` and `κ(φ) = N(v) mod m`. In particular `N(v)` is prime
to `m`; directly: a prime `p | (N(v), m)` gives `x ≠ 0` of additive order `p` in the field
`𝓞_K/v`, and `m x = 0` with `m ≠ 0` there. So `ψ₀ ∘ κ` is trivial on `I_Q` and
`(ψ₀ ∘ κ, v) = ψ₀(κ(φ)) = ψ₀(N(v) mod m)`. ∎

**R2.** `𝔪 = (m)∞` with all real places. For `u` on the primes with values in an abelian group,
`I ↦ Π_v u(v)^{v(I)}` is a homomorphism on the fractional ideals. Take `u(v) = N(v) mod m` for
`v ∤ m` (and `1` for `v | m`): `N̄ : I^𝔪 → (ℤ/m)^×`.
(a) For an integral ideal `I` prime to `m`: `N̄(I) = N(I) mod m`, by induction on the prime
factors (`N̄` and `N` are multiplicative and agree on the primes `v ∤ m`).
(b) If `a ≡ b mod m𝓞_K`, then `N(a) ≡ N(b) mod m`: the norm is the determinant of the
multiplication on an integral basis, and the matrices of `a` and `b` are congruent modulo `m`.
(c) If `α ∈ K^×` is positive at every real place, `N(α) > 0`: `N(α)` is the product of the
conjugates; above a real place there is one conjugate, positive; above a complex place a pair
`σα, conj(σα)` with product `|σα|² > 0`.
Let `α ∈ K^{𝔪,1}_+`, `α = a/b` with `a, b ∈ 𝓞_K` prime to `m`. Then `a ≡ b mod m`, so
`N(a) ≡ N(b)` by (b); `N(a) = N(b) N(α)` and (c) give `N(a)`, `N(b)` the same sign; hence
`|N(a)| ≡ |N(b)| mod m`. By (a), `N̄((a)) = |N(a)|`, `N̄((b)) = |N(b)|`, and `(α)(b) = (a)`:
`N̄((α)) = 1`. So `N̄` factors through `Cl_𝔪`, and `ψ₀ ∘ N̄` is a ray class character with value
`ψ₀(N(v) mod m)` at `v ∤ m` and `0` at `v | m`. ∎

**R3.** By R1 and R2, `(ψ₀ ∘ κ, v) = (ψ₀ ∘ N̄)(v)` for `v ∤ m`. For `v | m` the Hecke factor is
`1`. So the Euler factor of `L(s, ψ₀ ∘ κ)` at `v` is the Hecke factor times `F(v)`, `F(v) = 1` for
`v ∤ m` and the Artin factor for `v | m`; both products converge for `Re s > 1` and `F` has finite
support. If `L = K(ζ)`: `κ(σ) = 1` gives `σζ = ζ`, so `σ` fixes `K(ζ) = L` and `σ = 1` (the action
is faithful); `κ` is injective, a character of `G ≅ κ(G) ≤ (ℤ/m)^×` extends to `(ℤ/m)^×`
(characters of a subgroup of a finite abelian group extend), so `χ = ψ₀ ∘ κ`. ∎

## Lean
All in `formal/GaloisForLFunctions/RHTower/Artin/`.
- R0 `ArtinEulerProductOfALinearCharacter.lean`: `frobeniusValue`,
  `frobeniusTrace_linearCharacter`, `eulerPolynomial_linearCharacter`, `artinSymbol`,
  `artinSymbol_eq_frobeniusValue`,
  `numberFieldFinitePlaceLocalEulerPolynomial_linearCharacterLine`, `artinSymbol_one`,
  `artinEulerProduct_linearCharacter_eq_heckeL`, `artinEulerProduct_one_eq_dedekindZeta`,
  `artinEulerProduct_induced_one_eq_dedekindZeta`.
- R1 `ArtinSymbolOfACyclotomicCharacterIsTheNormResidue.lean`:
  `eq_one_of_pow_eq_one_of_sub_mem`, `eq_of_pow_eq_one_of_sub_mem`,
  `absNorm_coprime_of_natCast_notMem`, `cyclotomicCharacter`,
  `cyclotomicCharacter_eq_one_of_mem_inertia`, `coe_cyclotomicCharacter_arithFrobAt`,
  `artinSymbol_cyclotomic`.
- R2 `NormsOfTotallyPositiveElementsArePositive.lean`: `norm_pos_of_forall_isReal_pos`,
  `intCast_norm_eq_of_sub_mem`. `NormResiduesOfIdealsAreRayClassCharacters.lean`:
  `primeValuesHom`, `normModulus`, `normResidueUnit`,
  `coe_primeValuesHom_normResidueUnit_idealUnit`, `normResidueHom`,
  `normResidueHom_eq_one_of_mem`, `normResidueClass`, `normHeckeCharacter`,
  `heckeValue_normHeckeCharacter`.
- R3 `ArtinEulerProductOfACyclotomicCharacterIsAHeckeLSeries.lean`:
  `artinEulerProduct_linearCharacter_eq_heckeL_mul`, `artinSymbol_cyclotomic_eq_heckeValue`,
  `artinEulerProduct_cyclotomic_eq_heckeL_mul`, `cyclotomicCharacter_injective`,
  `exists_eq_comp_cyclotomicCharacter`,
  `exists_artinEulerProduct_eq_heckeL_mul_of_adjoin_eq_top`.

## Log
- 2026-11-13 — R0–R3 proved and formalized
