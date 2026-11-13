# The reciprocity law for linear characters

- **ID:** agz-artin-reciprocity
- **Stage:** 1-in-progress
- **Type:** THEOREM (classical; not in the corpus, not in Mathlib)
- **Source:** docs/reports/review-1311/obstacles-summary.md §2.14 question 5 (A154)
- **Statement:** Let `L/K` be a Galois extension of number fields with group `G` and `χ` a linear
  character of `G`. There are a modulus `𝔪` of `K` and a ray class character `ψ` modulo `𝔪` with
  `(χ, v) = ψ(v)` for every prime `v ∤ 𝔪`. Then
  `L(s, χ, L/K) = L(s, ψ) · Π_{v | 𝔪} (1 − (χ, v) N(v)^{-s})^{-1}` for `Re s > 1`
  (`artinEulerProduct_linearCharacter_eq_heckeL_mul`).

## Goal
The last input of A154. Every Artin Euler product is a product of integer powers of Euler
products of linear characters over intermediate fields
(`agz-artin-euler-product-brauer-decomposition`). With the statement above each of them is a
Hecke `L`-series up to finitely many Euler factors, and the index law of virtual Hecke characters
applies to every Artin character.

## Status
Proved and formalized for characters that factor through the cyclotomic character of a root of
unity in `L` (`agz-cyclotomic-reciprocity-law`). The general case is global class field theory.

## Gates
- [x] cyclotomic characters (`agz-cyclotomic-reciprocity-law`)
- [x] G1 inflation: for `K ⊂ L' ⊂ L` and a character `χ'` of `Gal(L'/K)`, the Artin symbol and
  the Euler product of `χ' ∘ res` over `L/K` are those of `χ'` over `L'/K`
  (`agz-artin-euler-product-inflation-invariance`); hence the reciprocity law for every abelian
  extension inside a cyclotomic extension of `K`
- [x] G2 the Artin map `ω : I^𝔪 → G`, `v ↦ Frob_v`, for abelian `G` and `𝔪` divisible by the
  ramified primes; it is onto, `[I^𝔪 : ker ω] = [L : K]` (`agz-artin-map-on-ideals`)
- [x] G3 norms from `L` are in the kernel of the Artin map; `P_𝔪 ⊂ ker ω` gives the Hecke
  `L`-series (`agz-artin-map-on-ideals`)
- [x] G4 first inequality: `[I^𝔪 : P_𝔪 N(I_L^𝔪)] ≤ [L:K]`, for every finite `L/K`
  (`agz-norm-index-inequality`, from the Mertens bounds of the ray class characters)
- [x] G5 second inequality for cyclic `L/K`: `[L : K]` divides
  `[K^× : N(L^×) · (K^× ∩ W_k ∩ P) · K_S]`, `P` the elements positive at the ramified places
  (`card_dvd_index_norm_sup_congruence_sup_sUnits`,
  `RHTower/Artin/TheDegreeDividesTheNormIndexOfACyclicExtension`)
  - [x] G5a index calculus of a pair of endomorphisms `f g = g f = 0` (Herbrand quotient)
    (`agz-herbrand-quotient-of-units`)
  - [x] G5b units: `n · h_f(E_L) · h_g(ℤ^X) = h_f(ℤ^X) · h_g(E_L)`, `X` the infinite places of `L`
    (`agz-herbrand-quotient-of-units`)
  - [x] G5c `S`-units: `n · [K_S : N L_S] = Π_ω |G_ω|` (orbits on `X` and on `S`), from
    `H¹(G, L_S) = 0`; such `S` exist above every finite set of primes of `K`
    (`agz-norm-index-of-s-units`)
  - [x] G5d semi-local norm index: a `G`-stable congruence subgroup `W ⊂ L^×` at `S` with
    `H¹(G, W) = 0`; then `Π_{ω ⊂ S} |G_ω|` divides `[K^× : (K ∩ W) N(L^×)]`
    - [x] G5d1 permutation modules: `H¹(G, ℤ^X) = 0`, `|Ĥ⁰(G, ℤ^X)| = Π_ω |G_ω|`
      (`agz-norm-index-of-s-units`)
    - [x] G5d2 lattice filtration `Λ_j` of a normal basis, groups `W_k = 1 + Λ_k`
      (`congruenceSubgroup`, `RHTower/Artin/CongruenceSubgroupsOfANormalBasisLattice`)
    - [x] G5d3 `H¹(G, W_k) = 0` (`exists_mem_congruenceSubgroup_actionDiff_eq`)
    - [x] G5d4 `[L^{(S)} : W_k] < ∞` (`relIndex_congruenceSubgroup_ker_divMap_ne_zero`)
    - [x] G5d5 `[K^× : (K ∩ W_k) N(L^×)] = Π_{ω ⊂ S} |G_ω| · h_g(L^×/W_k)`
      (`relIndex_range_actionNorm_sup_range_baseIncl`)
    - [x] G5d6 signs: `[N L^× (K ∩ W_k) : N L^× (K ∩ W_k ∩ P)] = Π_{ω ⊂ X} |G_ω| = 2^ρ`
      (`relIndex_norm_sup_congruence_inf_positive`, `prod_card_stabilizer_infinitePlace`,
      `RHTower/Artin/NormsArePositiveAtTheRamifiedRealPlaces`)
  - [x] G5e assembly: `[K^× : U] = n · h_g(L^×/W_k) · [K_S ∩ V₁ : N L_S]`
    (`dvd_index_sup_of_relIndex`)
- [ ] G6 the kernel of the Artin map lies in `P_c N` for cyclic `L/K` (crossing with cyclotomic
  extensions)
  - [x] G6b towers `K ⊂ E ⊂ M`, `M/K` abelian with group `Γ ⊃ H`: `Frob_w = Frob_v^{f(w|v)}`,
    `(𝔅, M/E) = (N_{E/K} 𝔅, M/K)`, `f(w|v) | g` if `Frob_v^g` fixes `E`, and then `v^g` is a norm
    from `E`; `N_{E/K}` maps the ray modulo `(N) ∞` of `E` into that of `K`
    (`map_frobeniusElement_eq_pow`, `map_artinMap_eq_artinMap_idealNormHom`,
    `inertiaDeg_under_dvd_of_pow_smul_eq`, `exists_idealNormHom_pow_eq_idealUnit_pow`,
    `norm_mem_rayGroup`, `idealNormHom_mem_rayPrincipal`)
  - [ ] G6a kernel inside a cyclotomic extension: `M/E` abelian with group `H`, the cyclotomic
    character of `ζ_m ∈ M` injective on `H`, `Λ' ≤ H`, `m | N`. An ideal `𝔅` prime to `N` with
    `(𝔅, M/E) ∈ Λ'` lies in `P_{(N)∞} · ⟨𝔔 ∤ N : Frob_𝔔 ∈ Λ'⟩`
  - [ ] G6c the same over `K`: for `H ≤ Γ` with injective cyclotomic character and `Λ ≤ Γ`,
    `D_H ∩ ω_Γ^{-1}(Λ) ⊂ P_{(N)∞} · D_Λ` with `D_H = ⟨v^g : Frob_v^g ∈ H⟩`; and `ω_Γ(D_H) = H`
  - [ ] G6d the auxiliary modulus: a prime `p ∉ T` with `n | ord_p(a)`; `m` and `b` with
    `a_v^x b^y ≡ 1 (m) ⇒ n | x, n | y` for the norms `a_v` of the primes of `𝔞`
  - [ ] G6e `Φ_m` is irreducible over `L` for `m` prime to a finite set of primes
  - [ ] G6f `M = L(ζ_m)`: `Γ ↪ G × (ℤ/m)^×`, and `ρ = (σ, b) ∈ Γ`
  - [ ] G6g crossing: `v ≡ 𝔟^{d_v}` modulo `P_c N` for the primes `v` of `𝔞`, `(v, L/K) = σ^{d_v}`
- [ ] G7 the reciprocity law for cyclic `L/K`, and for every linear character by G1

## Approach

`L/K` cyclic of degree `n`, `G = ⟨σ⟩`, `f = σ − 1`, `g = N = Σ_τ τ`, `h_f(A) = [ker f : im g]`,
`h_g(A) = [ker g : im f]`.

**Setting (G5c).** `S_K` a finite set of primes of `K`, `S` the primes of `L` above, with
(a) `L/K` unramified outside `S_K`; (b) every prime `v ∉ S_K` of `K` is principal up to `S_K`:
`v_v(c) = 1`, `v_{v'}(c) = 0` for `v' ∉ S_K ∪ {v}`; (c) the same for `L` and `S`. Such `S_K` exist
above every finite set (ramified primes divide the different; primes dividing integral
representatives of the ideal classes). Put `K_S`, `L_S` for the `S`-units and
`Θ_S(α) = Π_{v ∉ S_K} Frob_v^{v_v(α)}`, a homomorphism `K^× → G`.

- `N(L^×) K_S ⊂ ker Θ_S` (G3) and `Θ_S` is onto (G2 and (b)): `[K^× : ker Θ_S] = n`.
- `α ≡ 1 mod 𝔪`, `𝔪` supported on `S_K`, gives `Θ_S(α) = ω((α))`. So the reciprocity law is
  `K_{𝔪,1} ⊂ ker Θ_S`.

**G7 from G5, G6.** With `U = K_{𝔪,1} N(L^×) K_S`: `ker Θ_S ⊂ U` (G6), `[K^× : U] ≥ n` (G5), so
`U = ker Θ_S ⊃ K_{𝔪,1}`. A linear character of a Galois group factors through a cyclic quotient;
G1 transports the statement.

**G5c.** `H¹(G, L_S) = 0`: an `S`-unit of norm one is `σy/y` (Hilbert 90); the divisor of `y`
outside `S` is invariant, so by (a), (b) it is the divisor outside `S` of some `c ∈ K^×`, and
`y/c ∈ L_S`. The valuations `L_S → ℤ^S` have kernel `E_L` and image of finite index (class
number), so with G5b and G5d1: `n · h_f(L_S) = Π_{ω ⊂ X} |G_ω| · Π_{ω ⊂ S} |G_ω|`.

**G5d.** `S` any `G`-stable finite set of primes of `L`, `O_j = {y ∈ L : v_w(y) ≥ j, w ∈ S}`,
`R_j = K ∩ O_j`. Take `θ` with `(τθ)_τ` a basis of `L/K` and
`Λ_j = {Σ_τ a_τ τθ : a_τ ∈ R_j}`. Then `Λ_j` is `G`-stable, `R_i Λ_j ⊂ Λ_{i+j}`,
`Λ_i Λ_j ⊂ Λ_{i+j−c}` (`c` from the products `τθ · τ'θ`), every element of `L` lies in some
`Λ_{−c'}`.
- *Groups.* For `k ≥ k₀`, `W_k = {x ≠ 0 : x − 1 ∈ Λ_k}` is a `G`-stable group: products by
  `Λ_k Λ_k ⊂ Λ_k`; `x⁻¹ = Π_{τ ≠ 1} τx / N(x)` and `N(x) ∈ 1 + R_1` is invertible in `1 + R_j`
  inside `K`, where valuations are multiplicative. `v_w(x) = 0` for `x ∈ W_k`, `w ∈ S`.
- *Layers.* `a = Σ_τ a_τ τθ = Σ_τ (τ − 1)(a_τ θ) + s θ`, `s = Σ_τ a_τ`, and `Tr a = s · Tr θ`. For
  a `G`-stable subgroup `C` and `a ∈ C`, `(τ − 1) a ∈ (σ − 1) C`. So `a ∈ Λ_k` with
  `Tr a ∈ Λ_{k+1}` is `(σ − 1) b + Λ_{k+1}` with `b ∈ Λ_k`. For `x = 1 + a ∈ W_k` of norm one,
  `Tr a ∈ Λ_{k+1}`, and `x · z/σz ∈ W_{k+1}` for `z = 1 + b`.
- *Loss.* For `u = σy/y ∈ W_M` (Hilbert 90), `τy/y ∈ W_M` for all `τ`. With `c₀` of trace one
  the average `z = Σ_τ (τy/y) τc₀` has `z − 1 = Σ_τ (τy/y − 1) τc₀ ∈ Λ_{M−c''}` and
  `zy = Tr(y c₀) ∈ K`, so `u = σ(z⁻¹)/z⁻¹`.
- `H¹(G, W_k) = 0`: descend through the layers to level `M = k + c''`, then apply the loss step.
- *Finiteness.* `O_{j+c} ⊂ Λ_j`: the coordinate of `y` at `τθ` is `Tr(y d_τ)` for the dual
  basis of the trace form. For `x` integral at `S` choose `y ∈ 𝓞_L`, `y ≡ 1 mod w^J` (`w ∈ S`),
  divisible by the denominator of `x` (Chinese remainder theorem): `xy ∈ 𝓞_L`,
  `x − xy ∈ O_J`. Elements of `L^{(S)}` (`v_w = 0` on `S`) whose approximations agree modulo
  `w^J`, `w ∈ S`, differ by a factor in `1 + O_J ⊂ W_k`; `𝓞_L / w^J` is finite.
- *Index.* `A' = L^× / W_k`. By `H¹(G, W_k) = 0` and Hilbert 90, `f⁻¹ W_k = K^× W_k`:
  `h_f(A') = [K^× : (K ∩ W_k) N(L^×)]`. The valuations `A' → ℤ^S` have finite kernel
  `L^{(S)} / W_k` and image of finite index, so `h_f(A') = Π_{ω ⊂ S} |G_ω| · h_g(A')` (G5d1).
  No finiteness of `h_g(A')` is used; it follows in G5e from `[K^× : U] < ∞`.
- *Signs.* The orbits on `X` are the infinite places of `K`; `|G_ω| = 2` exactly at the `ρ`
  places `v` with a complex place `w = |ψ|` above a real one. There complex conjugation on `ψ(L)`
  is an involution `c ∈ G`, `ψ(τx) ψ(cτx) = |ψ(τx)|²`, so norms are positive at `v`. For `N ≥ 1`
  every sign pattern at the real places is attained by some `1 + Nγ`, `γ ∈ 𝓞_K` (weak
  approximation, then a denominator is cleared), and `1 + Nγ ∈ W_k` for `N` a high power of the
  norms of the primes of `S`. With `P` the elements positive at the `ρ` places:
  `[N L^× (K ∩ W_k) : N L^× (K ∩ W_k ∩ P)] = 2^ρ`.

**G5e.** `V₀ = N(L^×)(K ∩ W_k)`, `V₁ = N(L^×)(K ∩ W_k ∩ P)`, `U = V₁ K_S`. Then
`[K^× : V₁] = Π_S h_g · 2^ρ = [K^× : U] · [K_S : K_S ∩ V₁]` and
`n · [K_S : K_S ∩ V₁] · [K_S ∩ V₁ : N L_S] = 2^ρ Π_S`, hence
`[K^× : U] = n · h_g · [K_S ∩ V₁ : N L_S]`. No finiteness is assumed: the identities hold with
the value `0` for an infinite index.

**G6.** Statement: `c ≥ 1` divisible by the ramified primes, `𝔞` prime to `c` with
`(𝔞, L/K) = 1`; then `𝔞 ∈ P_{(c)∞} · N_{L/K}`. All towers have two layers: a base, the fixed
field `E_H` of a subgroup `H` of `Γ = Gal(M/K)`, and `M`.

*Modulus.* Let `a_v = N v` for the primes `v` of `𝔞`, `(v, L/K) = σ^{d_v}`. For `a ≥ 2`, `n ≥ 1`
and a finite set `T` there is a prime `p ∉ T`, `p ∤ a`, with `n | ord_p(a)`: with `n' = nℓ` not a
prime power and `k = Π_{t ∈ T ∪ primes(n'), t ∤ a} (t − 1)`, `Φ_{n'}(a^k) ≡ Φ_{n'}(1) = 1` modulo
each such `t`, and a prime factor `p` of `Φ_{n'}(a^k) > 1` has `ord_p(a^k) = n'`. Take `P₀` with
`n | P₀ − 1` and `g` of order divisible by `n` modulo `P₀`, then `P_v` with
`lcm(n, ord_{P₀}(a_v)) | ord_{P_v}(a_v)`; `m = P₀ · Π P_v` (distinct values), `b ≡ g (P₀)`,
`b ≡ 1 (P_v)`. Then `a_v^x b^y ≡ 1 (m)` forces `n | x` and `n | y`.

*Irreducibility.* `L` has finitely many subfields, and `ℚ(ζ_m) ∩ ℚ(ζ_{m'}) = ℚ` for coprime
`m, m'`; so `L ∩ ℚ(ζ_m) = ℚ` and `Φ_m` is irreducible over `L` for `m` prime to a finite set of
primes. Then `Gal(L(ζ_m)/L) = (ℤ/m)^×`, `Γ ↪ G × (ℤ/m)^×`, and `ρ = (σ, b) ∈ Γ`.

*Fields.* `φ_v = Frob_v(M/K) = (σ^{d_v}, a_v)`, `H_v = ⟨φ_v, ρ⟩`. The cyclotomic character is
injective on `H_v`: `a_v^x b^y = 1` gives `n | x, y`, so `σ^{d_v x + y} = 1`.

*Norm groups over `K`.* `D_H = ⟨v^g : v ∤ N, Frob_v^g ∈ H⟩`. By G6b it is the group of norms
from `E_H` of ideals prime to `N`, and `ω_Γ(D_H) = H` by G2 over `E_H`. If the cyclotomic
character is injective on `H`, then `D_H ∩ ω_Γ^{-1}(Λ) ⊂ P_{(N)∞}(K) · D_Λ` (G6c): lift to `E_H`,
apply G6a, take norms. G6a: the quotient of the ray class group modulo `(N) ∞` of `E` by the
primes with Frobenius in `Λ'` has order at most `[E_{Λ'} : E] = [H : Λ']` by G4 (a prime of
degree one of `E_{Λ'}` has Frobenius in `Λ'`), and it maps onto `H/Λ'` by cyclotomic reciprocity
and G2.

*Crossing.* Take `𝔟 ∈ D_{⟨ρ⟩}` with `ω_Γ(𝔟) = ρ`. For each `v`: `v 𝔟^{−d_v} ∈ D_{H_v}` has symbol
in `Λ = Gal(M/L)`, so it lies in `P_{(N)∞} · D_Λ`, and `D_Λ ⊂ N_{L/K}` (if `Frob_v(L/K)^g = 1`
then `f_L(v) | g`). With `𝔟^n ∈ N_{L/K}` and `n | Σ a_v d_v`: `𝔞 ∈ P_{(c)∞} · N_{L/K}`.

**G7.** Choose `S₀` closed under residue characteristic, `c` a power of `Π_{S₀} N v`, so that
`γ ≡ 1 mod^× c` totally positive lies in `W_k ∩ P`. `PrincipalOutside` turns `𝔞 = (γ) N(𝔄)` into
`α ∈ γ · N(L^×) · K_S`.

## Log
- 2026-11-13 — created; cyclotomic case formalized and moved to its own card
- 2026-11-13 — G5 formalized (G5a–G5e)
- 2026-11-13 — G6b formalized; G6 restated over `K` with two-layer towers. Order of work of
  review-1311 §2.14: after B192 at ratio three and the realization on the dyadic windows
