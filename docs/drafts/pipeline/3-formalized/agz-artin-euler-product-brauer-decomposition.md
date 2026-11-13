# Every Artin Euler product is a product of integer powers of abelian Euler products

- **ID:** agz-artin-brauer-decomposition
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** docs/reports/review-1211/obstacles-summary.md §2.14 question 4 (A154)
- **Statement:** Let `L/K` be a Galois extension of number fields with group `G` and `ρ` a
  representation of `G`. There are integers `n_q`, indexed by finitely many pairs `q = (E, χ)` of
  a Brauer-elementary subgroup `E ≤ G` and a linear character `χ` of `E`, such that for `Re s > 1`

  `L(s, ρ, L/K) = Π_q L(s, χ_q, L/L^{E_q})^{n_q}`.

## Goal
Second half of the formal part of A154. After this the only missing input for the index of an
Artin character is the reciprocity law for one linear character `χ` of `Gal(L/M)`: its Euler
product is the Euler product of a Hecke character of `M` (class field theory; not attempted
here).

## Gates
- [x] B1 local: the local Euler polynomial is a homomorphism on integer relations between
  characters
- [x] B2 global: `L(s, ρ) = Π_i L(s, τ_i)^{n_i}` for `χ_ρ = Σ_i n_i χ_{τ_i}`, `Re s > 1`
- [x] B3 Brauer: the decomposition into abelian Euler products over fixed fields

## Approach

Notation of `agz-artin-euler-factors-under-induction` (I1–I3). Fix a prime `v` of `K` and a prime
`Q` of `L` above it; `T_m(θ) = a_m(θ; I_Q, φ_Q)` for a function `θ` on `G`. `T_m` is linear in
`θ`.

**B1.** Let `χ_ρ = Σ_{i∈S} n_i χ_{τ_i}` with representations `τ_i` of `G` and `n_i ∈ ℤ`;
`n^+ = max(n, 0)`, `n^- = max(−n, 0)`. By I2(d), `P_v(τ)` has constant term `1` and the power
traces `T_m(χ_τ)`. By I2(a) (products add power traces), `P_v(ρ) Π_i P_v(τ_i)^{n_i^-}` has the
power traces `T_m(χ_ρ) + Σ_i n_i^- T_m(χ_{τ_i})` and `Π_i P_v(τ_i)^{n_i^+}` has
`Σ_i n_i^+ T_m(χ_{τ_i})`. These agree by linearity. Both have constant term `1`, so by I2(b)

  `P_v(ρ) Π_i P_v(τ_i)^{n_i^-} = Π_i P_v(τ_i)^{n_i^+}`.

**B2.** Evaluate at `N(v)^{-s}` and invert: the same identity for the Euler factors. For
`Re s > 1` the Euler products converge; finite products and powers of convergent products
converge to the products and powers of the limits, so
`L(s, ρ) Π_i L(s, τ_i)^{n_i^-} = Π_i L(s, τ_i)^{n_i^+}`. The Euler products do not vanish for
`Re s > 1`, hence `L(s, ρ) = Π_i L(s, τ_i)^{n_i}`.

**B3.** By `brauer_induction`, `χ_ρ = Σ_q n_q Ind_{E_q}^G χ_q`, a finite sum over
Brauer-elementary pairs. `Ind χ_q` is the character of the induced representation `τ_q` of the
line of `χ_q`. By B2 `L(s, ρ) = Π_q L(s, τ_q)^{n_q}`, and by I3
`L(s, τ_q, L/K) = L(s, χ_q, L/L^{E_q})` (`E_q` is the Galois group of `L` over its fixed
field). ∎

Lean (B1, B2): `formal/GaloisForLFunctions/RHTower/Artin/ArtinEulerProductOnIntegerRelationsOfCharacters.lean`
(`frobeniusTrace_sum_zsmul`, `HasPowerTraces.pow`, `HasPowerTraces.mul_prod_pow_toNat_eq`,
`numberFieldFinitePlaceLocalEulerPolynomial_mul_prod_pow_eq`,
`numberFieldFinitePlaceArtinEulerReciprocal_mul_prod_pow_eq`,
`numberFieldFinitePlaceArtinEulerReciprocalProduct_eq_prod_zpow`).
Lean (B3): `formal/GaloisForLFunctions/RHTower/Artin/ArtinEulerProductIsAProductOfAbelianEulerProducts.lean`
(`linearCharacterLine`, `linearCharacterLine_character`, `brauerAbelianEulerProduct`,
`exists_artinEulerProduct_eq_prod_zpow_abelian`).

## Log
- 2026-11-13 — created; B1–B3 proved and formalized
