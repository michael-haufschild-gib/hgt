# The conductor of a linear Artin character is supported on its ramified primes

- **ID:** agz-conductor-ramification
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** docs/reports/review-1311/obstacles-summary.md §2.14 (question 5); open item of
  `3-formalized/agz-ray-class-characters-at-their-conductors.md` and of
  `3-formalized/agz-artin-characters-zero-configuration-with-orders.md`
- **Statement:** Let `L/K` be a Galois extension of number fields with group `G` and `χ` a linear
  character of `G`. There is a primitive ray class character `ψ` of `K` with `(χ, v) = ψ(v)` at
  every prime `v` of `K`. So a prime divides the conductor of `ψ` iff `χ` is ramified at it, and
  `L(s, χ, L/K) = L(s, ψ)` for `Re s > 1`, with no correcting Euler factor. Hence every Artin
  `L`-function is a product of integer powers of `L`-functions of primitive ray class characters,
  and its completion has a functional equation and, at every point of `ℂ`, the order of its
  virtual configuration.

## Goal

The finite product of Euler factors in the reciprocity law with a primitive character is `1`: the
Artin `L`-function of a linear character is the `L`-function of its primitive ray class
character. The zero configuration of `χ` is then the configuration of `ψ` on all of `Re s > 0`.

Not a statement on the position of the zeros.

## Gates
- [x] 0 → 1  in-progress
- [x] 1 → 2  fully-proven
- [x] 2 → 3  formalized

## Proof

`(χ, v)` is the Artin symbol: `χ(Frob_v)` if `χ` is trivial on the inertia groups above `v`, and
`0` otherwise. `(𝔞, L/K)` is the Artin map of an abelian extension on the fractional ideals:
`Frob_v` at the unramified primes, `1` at the ramified ones. A modulus is `I ∞` with `I ≠ 0` an
ideal and `∞` all real places; `K_{I,1}` is its ray (`α ≡ 1 mod^× I`, totally positive) and
`P_I` the group of the principal ideals `(α)`, `α ∈ K_{I,1}`.

Known (formalized): for abelian `L/K` there is `c ≥ 1`, divisible by the ramified primes, with
`P_{(c)} ⊂ ker (·, L/K)`. The integer `c` is divisible by unramified primes as well.

### 1. Ray elements

**1a.** Every `α ∈ K_{I,1}` is `a₁/a₂` with `a_i ∈ 𝓞_K ∖ 0`, `a_i ≡ 1 mod I`, `a_i` totally
positive. Write `α = a/b` with `a, b` integers prime to `I`, `a ≡ b mod I`. Take an integer
`b'` with `b b' ≡ 1 mod I` and the signs of `b` (integers with a given residue and given signs
exist). Then `a₂ = b b'` and `a₁ = a b' = α a₂` are `≡ 1 mod I` and totally positive.

**1b.** A non-zero integer `a ≡ 1 mod I`, totally positive, lies in `K_{I,1}`.

**1c.** Let `γ ∈ K_{I,1}`, `u ∤ I` a prime, `e ≥ 1`, `v_u(γ − 1) ≥ e`. Then `γ ∈ K_{I u^e,1}`.
Indeed `v_u(γ) = 0`; write `γ = a/b` with `a, b` integers prime to `I u`. Then `a − b ∈ I` and
`v_u(a − b) = v_u(γ − 1) ≥ e`, so `a − b ∈ I ∩ u^e = I u^e`.

### 2. Norms

Let `E/K` be an extension of number fields.

**2a.** For `μ ∈ 𝓞_K ∖ 0` and `x, y ∈ 𝓞_E` with `x ≡ y mod μ 𝓞_E`:
`N_{E/K} x ≡ N_{E/K} y mod μ 𝓞_K`. The conjugates of `x` and `y` in an algebraic closure are
congruent modulo `μ` in the ring of algebraic integers, so `(N x − N y)/μ` is an algebraic
integer of `K`.

**2b.** Let `E/K` be Galois with group `Δ` and `𝔔` a prime of `E` with `τ 𝔔 ≠ 𝔔` for `τ ≠ 1`.
Let `a ∈ 𝓞_K`, `x ∈ 𝓞_E`, `k ≥ 0` with `x ≡ a mod 𝔔^k` and `x ≡ 1 mod (τ 𝔔)^k` for `τ ≠ 1`.
Then `N_{E/K} x ≡ a mod 𝔔^k`: `N x = Π_τ τ x`, and `τ x ≡ 1 mod 𝔔^k` for `τ ≠ 1` since
`x ≡ 1 mod (τ^{-1} 𝔔)^k`.

**2c.** If moreover `e(𝔔 | u) = 1` for `u = 𝔔 ∩ K`, then `y ∈ 𝓞_K`, `y ∈ 𝔔^k` give `y ∈ u^k`
(`v_𝔔 = v_u` on `K`).

### 3. The decomposition field

Let `M/K` be abelian with group `Γ`, `u` a prime of `K` unramified in `M`, `φ = Frob_u`,
`H = ⟨φ⟩`, `E` the fixed field of `H`, `Δ = Γ/H` its group over `K`, `𝔓` a prime of `M` above
`u` and `𝔔 = 𝔓 ∩ E`. Then `e(𝔔 | u) = f(𝔔 | u) = 1` and `τ 𝔔 ≠ 𝔔` for `τ ≠ 1` in `Δ`.

`e(𝔓 | u) = e(𝔓 | 𝔔) e(𝔔 | u)` and `e(𝔓 | u) = 1`. The element `φ` fixes `E`, so `f(𝔔 | u)`
divides `1` (formalized: if `Frob^g` fixes `E` then `f(𝔔 | u)` divides `g`). The stabilizer of
`𝔔` in `Δ` has order `e f = 1`.

### 4. Removing an unramified prime from the modulus

**Theorem 4.** Let `L/K` be abelian with group `G`, `I ≠ 0` an ideal of `𝓞_K` such that the
primes `v ∤ I` are unramified in `L`, `u ∤ I` a prime and `e ≥ 1`. If
`P_{I u^e} ⊂ ker (·, L/K)` then `P_I ⊂ ker (·, L/K)`.

Proof. By 1a it suffices to show `((a), L/K) = 1` for a non-zero integer `a ≡ 1 mod I`, totally
positive. Let `j = v_u(a)` and `k = e + j`.

*The crossing.* Choose `μ ∈ I ∖ u` (`u ∤ I`). Let `m₀` be such that `Φ_m` is irreducible over `L`
for `m` prime to `m₀`. There is `m ≥ 1` prime to `m₀ N(u)` such that the order of `N(u)` modulo
`m` is divisible by `|G|`. Let `M = L(ζ_m)`: abelian over `K` with group `Γ ≅ G × (ℤ/m)ˣ` by
`γ ↦ (γ|_L, κ(γ))`, `κ` the cyclotomic character. The prime `u` is unramified in `M`
(`u ∤ m`, unramified in `L`). Let `φ = Frob_u(M/K)`, `H = ⟨φ⟩`, `E`, `Δ`, `𝔔` as in 3. The
character `κ` is injective on `H`: `κ(φ) = N(u) mod m`; if `κ(φ^x) = 1` then `|G|` divides `x`,
so `φ^x` restricts to `1` on `L` and has `κ = 1`, hence `φ^x = 1`. So `M/E` lies in a cyclotomic
extension and the cyclotomic reciprocity law holds over `E`: `((β), M/E) = 1` for
`β ≡ 1 mod^× m`, totally positive.

*The element.* By the Chinese remainder theorem take `ε ∈ 𝓞_E` with `ε ≡ 1 mod 𝔔^k` and
`ε ≡ 0 mod (τ 𝔔)^k` for `τ ≠ 1` (the primes `τ 𝔔` are distinct by 3), and `c₀ ∈ 𝓞_K` with
`μ m c₀ ≡ 1 mod u^k` (`μ m ∉ u`). Let `q ≥ 1` be an integer in `u^k`, and for `t ≥ 0`

  `β = 1 + μ m c₀ ε (a − 1) + t (μ m)² q ∈ 𝓞_E`.

For `t` large `β` is totally positive, since `(μ m)² q > 0` at every real place. Further
`β ≡ 1 mod μ m 𝓞_E`, `β ≡ 1 + (a − 1) = a mod 𝔔^k` and `β ≡ 1 mod (τ 𝔔)^k` for `τ ≠ 1`.

*The norm.* Let `b = N_{E/K} β ∈ 𝓞_K`. By 2a `b ≡ 1 mod μ m`, so `b ≡ 1 mod I`; `b` is totally
positive; by 2b, 2c and 3, `b ≡ a mod u^k`. So `b ≠ 0`, `b ∈ K_{I,1}` (1b), and
`v_u(b) = v_u(a) = j` since `v_u(b − a) ≥ k > j`. Hence `v_u(a/b − 1) = v_u(a − b) − j ≥ e`, and
1c gives `a/b ∈ K_{I u^e,1}`. So `((a/b), L/K) = 1` by the hypothesis.

*The symbol of the norm.* `β ≡ 1 mod μ m`, so `β` is a unit at the primes of `E` above the
primes dividing `m` or `I` (`μ ∈ I`). The primes of `(β)` therefore lie above primes of `K`
unramified in `L` and in `M`, and

  `((b), L/K) = (N_{E/K}(β), M/K)|_L = ((β), M/E)|_L = 1`.

Hence `((a), L/K) = ((a/b), L/K) ((b), L/K) = 1`. ∎

### 5. Reciprocity with a modulus supported on the ramified primes

**Theorem 5.** Let `L/K` be abelian. There is an ideal `I ≠ 0` whose prime divisors are the
primes ramified in `L`, with `P_I ⊂ ker (·, L/K)`.

Proof. Let `c` be as above, `J` the product of the primes dividing `c` and `e ≥ 1` with
`J^e ⊂ (c)`. Let `R` be the set of the ramified primes (they divide `c`), `U` the set of the
unramified primes dividing `c`, `I = Π_{v ∈ R} v^e`. Then `J^e = I Π_{u ∈ U} u^e` and
`P_{J^e} ⊂ P_{(c)} ⊂ ker`. Remove the primes of `U` one by one with Theorem 4. ∎

### 6. Exact reciprocity

**Theorem 6.** For a linear character `χ` of the group of a Galois extension `L/K` there are a
modulus `𝔪` and a ray class character `ψ` modulo `𝔪` with `(χ, v) = ψ(v)` for every prime `v`
(`ψ(v) = 0` for `v | 𝔪`). So `L(s, χ, L/K) = L(s, ψ)` for `Re s > 1`.

Proof. `χ` is inflated from a faithful character `χ'` of the cyclic group `G / ker χ` of the
fixed field `F` of `ker χ`, with the same Artin symbols. Let `I` be as in Theorem 5 for `F/K`
and `ψ = χ' ∘ (·, F/K)` modulo `I ∞`. For `v ∤ I`: `v` is unramified in `F` and
`ψ(v) = χ'(Frob_v) = (χ', v)`. For `v | I`: `v` is ramified in `F`, the inertia group is not
trivial and `χ'` is faithful, so `(χ', v) = 0 = ψ(v)`. ∎

### 7. The ramified primes divide the conductor

**Lemma 7a.** Let `F` be a number field. `ζ_F(s) ≠ 0` for `Re s = 0`, `Im s ≠ 0`. With
`E(s) = (s − 1) ζ_F(s)`, the completion `Ξ` and its Gamma factor `γ`: `Ξ(s)/γ(s) = c(s) s E(s)`
on `ℂ` with `c` without zeros, and `Ξ(1 − s) = W Ξ(s)`. The Gamma factor is finite and non-zero
off the real axis. If `ζ_F(s₀) = 0` then `Ξ(s₀) = 0`, so `Ξ(1 − s₀) = 0` and
`ζ_F(1 − s₀) = 0` with `Re (1 − s₀) = 1`, `1 − s₀ ≠ 1`: excluded.

**Theorem 7.** Let `L/K` be abelian with group `G`. For every character `η` of `G` let
`(𝔪_η, ψ_η)` be a modulus and a ray class character with `(η, v) = ψ_η(v)` at every prime `v`
(they exist by Theorem 6), and `ψ'_η` the primitive character of `ψ_η`, of conductor `𝔣_η`.
Then every prime dividing `𝔪_η` divides `𝔣_η`.

Proof. For `Re s > 1`

  `ζ_L(s) = Π_η L(s, η) = Π_η L(s, ψ_η) = Π_η L(s, ψ'_η) R_η(s)`,
  `R_η(s) = Π_{v | 𝔪_η} (1 − ψ'_η(v) N v^{−s})`.

The first equality: the regular character is the sum of the characters of `G`, and the Euler
product of the regular character is `ζ_L` (induction from the trivial subgroup). Both sides are
analytic on `ℂ ∖ {1}`, which is connected: the identity holds there. Let `v₁ | 𝔪_{η₁}`,
`v₁ ∤ 𝔣_{η₁}`. Then `z = ψ'_{η₁}(v₁)` has `|z| = 1`; the point
`s₀ = (log z + 2π i)/log N v₁` has `Re s₀ = 0`, `Im s₀ > 0` and `N v₁^{−s₀} = z^{−1}`, so
`R_{η₁}(s₀) = 0`. The other factors are finite at `s₀ ≠ 1`: `ζ_L(s₀) = 0`, against 7a. ∎

### 8. The theorem

Let `χ`, `F`, `χ'`, `(𝔪, ψ)` be as in Theorem 6 and `ψ'` the primitive character of `ψ`. For
`v ∤ 𝔪`: `ψ'(v) = ψ(v) = (χ, v)`. For `v | 𝔪`: `(χ, v) = 0`, and `v` divides the conductor by
Theorem 7 for the extension `F/K`: take the pairs of Theorem 6 for the characters of `G / ker χ`,
with the given pair `(𝔪, ψ)` for `χ'`. So `ψ'(v) = 0 = (χ, v)`. ∎

### 9. The completion and the functional equation

`Ξ(s, ψ)` is the entire completion of a primitive ray class character `ψ`:
`Ξ = P γ L(·, ψ)` on `Re s > 1`, `P = s(s − 1)` for `ψ = 1` and `1` otherwise, `γ` the conductor
and Gamma factor; `Ξ(1 − s, ψ) = W(ψ) Ξ(s, ψ⁻¹)`, `|W(ψ)| = 1` (formalized). `Z_ψ` is the
configuration of the zeros of `Ξ(·, ψ)` with their orders.

**9a.** `(χ⁻¹, v) = conj (χ, v)` at every prime: `χ⁻¹` and `χ` are trivial on the same inertia
groups and `χ⁻¹(φ) = conj χ(φ)`. So if `ψ` is the primitive character of `χ` (§8) then `ψ⁻¹`,
primitive of the same conductor with `ψ⁻¹(v) = conj ψ(v)`, is the primitive character of `χ⁻¹`.

**Theorem 9.** For a linear character `χ`, with `ψ` as in §8: `Ξ(·, ψ) = P γ L(·, χ, L/K)` and
`Ξ(·, ψ⁻¹) = P γ' L(·, χ⁻¹, L/K)` on `Re s > 1`, `Ξ(1 − s, ψ) = W Ξ(s, ψ⁻¹)` on `ℂ`, and the von
Mangoldt coefficients of `ψ` are `Σ_{N v^k = n} (χ, v)^k log N v`: the explicit formula of `Z_ψ`
has the Artin symbols of `χ` on its prime side, at every prime. ∎

**9b.** Induction commutes with conjugation: `Ind(conj f) = conj Ind(f)`.

**Theorem 10.** Let `ρ` be a representation of `G` and `ρ*` one with the conjugate character.
There are integers `n_q` on the Brauer pairs `q = (E_q, χ_q)` and primitive ray class characters
`ψ_q` of the fixed fields `F_q` of the `E_q`, with `(χ_q, v) = ψ_q(v)` at every prime of `F_q`,
such that for `Re s > 1`

  `L(s, ρ, L/K) = Π_q L(s, ψ_q)^{n_q}`,  `L(s, ρ*, L/K) = Π_q L(s, ψ_q⁻¹)^{n_q}`.

Let `Ξ_ρ = Π_q Ξ(·, ψ_q)^{n_q}` and `Ξ_{ρ*} = Π_q Ξ(·, ψ_q⁻¹)^{n_q}`, quotients of entire
functions. Then

* `Ξ_ρ = γ_ρ L(·, ρ)` and `Ξ_{ρ*} = γ_{ρ*} L(·, ρ*)` on `Re s > 1`, with `γ_ρ = Π_q (P_q γ_q)^{n_q}`;
* `Ξ_ρ(1 − s) = W Ξ_{ρ*}(s)` on `ℂ`, `W = Π_q W(ψ_q)^{n_q}`, `|W| = 1`;
* if `A`, `B` are entire, `B ≢ 0`, `A = B Ξ_ρ` on `Re s > 1`, then
  `ord_w A − ord_w B = Σ_q n_q m_{Z_q}(w)` at every `w ∈ ℂ`;
* `Σ_q n_q W_{Z_q}` has `m` negative squares on some family of `m` tests iff at least `m` points
  are zeros or poles of `A / B` right of the critical line, or poles on the line.

Proof. Brauer: `χ_ρ = Σ_q n_q Ind χ_q`. Conjugate and use 9b: `χ_{ρ*} = Σ_q n_q Ind χ_q⁻¹`. The
Euler product is a homomorphism on integer relations between characters and the Euler product of
an induced character is the Euler product over the fixed field, so
`L(s, ρ) = Π_q L(s, χ_q, L/F_q)^{n_q}` and `L(s, ρ*) = Π_q L(s, χ_q⁻¹, L/F_q)^{n_q}`; apply §8
and 9a to each factor. The identities with `γ` and the functional equation are those of the
factors. For the orders: on `Re s > 1`, where the `Ξ(·, ψ_q)` have no zeros,
`A Π_{n_q < 0} Ξ_q^{−n_q} = B Π_{n_q > 0} Ξ_q^{n_q}`; both sides are entire, so the identity
holds on `ℂ`, orders add, and `ord_w Ξ_q = m_{Z_q}(w)`. The index: the form of an integer
combination of tempered configurations has `m` negative squares on some family iff the
combination has `m` points right of the line with net multiplicity `≠ 0` or on the line with net
multiplicity `< 0`. ∎

With a correcting Euler factor `Π_{v | c} (1 − (χ, v) N v^{−s})^{−1}` the continuation has poles
on `Re s = 0` and no functional equation: §8 is what gives the statement on `ℂ`.

## Lean

Modules in `formal/GaloisForLFunctions/`; every theorem is proved without hypothesis.

| § | Module | Theorems |
|---|---|---|
| 1, 2a | `RHTower/Artin/RayElementsAreQuotientsOfIntegersOfTheRay.lean` | `exists_integral_of_mem_rayGroup` (1a), `mk0_mem_rayGroup` (1b), `mem_rayGroup_mul_pow` (1c), `intNorm_sub_intNorm_mem_span` (2a) |
| 2b, 2c, 3 | `RHTower/Artin/NormsFromTheDecompositionFieldOfAnUnramifiedPrime.lean` | `algebraMap_intNorm_sub_mem_pow`, `exists_intNorm_sub_mem_pow` |
| 4, 5 | `RHTower/Artin/TheArtinMapIsTrivialOnARayWithOnlyRamifiedPrimesInTheModulus.lean` | `rayPrincipal_le_ker_artinMap_of_mul_pow` (Theorem 4, `e ≥ 1`), `exists_ideal_rayPrincipal_le_ker_artinMap` (Theorem 5) |
| 6 | `RHTower/Artin/TheArtinSymbolsOfALinearCharacterAreTheValuesOfARayClassCharacterAtEveryPrime.lean` | `exists_heckeCharacter_forall_artinSymbol`, `exists_artinEulerProduct_linearCharacter_eq_heckeL` |
| 7 | `RHTower/Artin/TheDedekindZetaFunctionOfAnAbelianExtensionIsTheProductOfTheLSeriesOfItsCharacters.lean` | `dedekindZeta_eq_prod_artinEulerProduct` |
| 7 | `AbsoluteGeometryOfSpecZ/InAFactorizationOfADedekindZetaFunctionEveryPrimeOfAModulusDividesTheConductor.lean` | `heckeXi_ne_zero_of_one_le_re`, `heckeXi_ne_zero_of_re_le_zero` (7a), `dvd_heckeFiniteConductor_of_dedekindZeta_eq_prod` |
| 7, 8 | `AbsoluteGeometryOfSpecZ/TheArtinLFunctionOfALinearCharacterIsTheLFunctionOfItsPrimitiveRayClassCharacter.lean` | `dvd_heckeFiniteConductor_of_forall_artinSymbol_eq` (Theorem 7), `exists_primitive_heckeCharacter_forall_artinSymbol` (§8) |
| 9a, 9b | `RHTower/Artin/TheArtinEulerProductOfTheConjugateRepresentationRunsOverTheInverseCharacters.lean` | `artinSymbol_inv`, `inducedFunction_star`, `exists_artinEulerProduct_eq_prod_zpow_abelian_conj` |
| 9 | `AbsoluteGeometryOfSpecZ/EveryArtinLFunctionHasACompletionWithAFunctionalEquation.lean` | `exists_completion_linearCharacter` (Theorem 9), `exists_artinEulerProduct_eq_prod_zpow_primitive_heckeL`, `exists_completion_artin` (Theorem 10) |

## What stays open

- The conductor exponent at a ramified prime (the Artin conductor through the higher
  ramification groups).
- The Gamma factor `γ_ρ` and the conductor of the completion as invariants of `ρ` (here they are
  products over a Brauer decomposition), and with it the uniqueness of the primitive character
  of a linear character.
- `Σ_{q : ψ_q = 1} n_q` is the multiplicity of the trivial character (Brauer pairs).

## Log
- 2026-11-14 — created in 1-in-progress with the paper proof
- 2026-11-14 — formalized; moved to 3-formalized
