# The reciprocity law for linear characters

- **ID:** agz-artin-reciprocity
- **Stage:** 1-in-progress
- **Type:** THEOREM (classical; not in the corpus, not in Mathlib)
- **Source:** docs/reports/review-1211/obstacles-summary.md §2.14 question 4 (A154)
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
- [ ] G6 `ker Θ_S ⊂ K_{𝔪,1} N(L^×) K_S` for cyclic `L/K` (crossing with cyclotomic extensions)
  - [ ] G6a kernel for extensions inside `F(ζ_m)`: `ker ω = P_𝔫 N` for every multiple `𝔫` of `m ∞`
  - [ ] G6b transfer: `ω_{L/K}(N_{F/K} 𝔟) = ω_{LF/F}(𝔟)|_L`
  - [ ] G6c auxiliary fields (orders modulo `m`; fixed fields in `L(ζ_m)`)
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

**G6.** Let `α ∈ ker Θ_S`, `𝔞 = Π 𝔭_i^{a_i}` its divisor outside `S`, `ω(𝔭_i) = σ^{d_i}`. For each
`i` take `m_i` (prime to `S`, to the `𝔭_j` and to each other) with `n | ord_{m_i}(N𝔭_i)` and
`τ_i` of order divisible by `n` with `⟨τ_i⟩ ∩ ⟨N𝔭_i⟩ = 1` modulo `m_i`, and `F_i` the fixed
field of `⟨(σ^{d_i}, N𝔭_i), (σ, τ_i)⟩` in `L(ζ_{m_i})`: `𝔭_i` splits completely in `F_i`,
`L ∩ F_i = K`, `L F_i ⊂ F_i(ζ_{m_i})`. With `𝔫 = 𝔪 · m_1 ⋯ m_r · ∞`: over `F_i` the kernel of
`ω_{LF_i/F_i}` on ideals prime to `𝔫` is `P_𝔫 N` (G6a: cyclotomic reciprocity, G2, G3, and G4
for `LF_i/F_i`). Choose `𝔟` in the compositum `F` with `ω_{LF/F}(𝔟)|_L = σ`; then
`𝔠_i = 𝔓_i · N_{F/F_i}(𝔟)^{−d_i}` (`𝔓_i | 𝔭_i` in `F_i`) lies in that kernel (G6b), so
`N_{F_i/K} 𝔠_i ∈ P_𝔫 N ⊂ P_𝔪 N`; and `Σ a_i d_i ≡ 0 (n)` makes the remaining power of
`N_{F/K} 𝔟` a norm from `L`. Hence `𝔞 = (γ) N_{L/K}(𝔄)`, `γ ∈ K_{𝔪,1}`; by (c),
`𝔄` is the divisor outside `S` of some `y ∈ L^×`, and `α / (γ N y) ∈ K_S`.

## Log
- 2026-11-13 — created; cyclotomic case formalized and moved to its own card
- 2026-11-13 — G5 formalized (G5a–G5e)
