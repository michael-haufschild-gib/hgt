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
- [ ] G5 second inequality for cyclic `L/K`: `[I^𝔪 : P_𝔪 N(I_L^𝔪)] ≥ [L : K]` for a suitable `𝔪`
  - [x] G5a index calculus of a pair of endomorphisms `f g = g f = 0` (Herbrand quotient)
    (`agz-herbrand-quotient-of-units`)
  - [x] G5b units: `n · [E_K : N E_L] ≤ 2^ρ · |H¹(G, E_L)|`, `ρ` the number of real places of
    `K` that ramify (`agz-herbrand-quotient-of-units`)
  - [ ] G5c `S`-units: `n · [K_S : N L_S] ≤ 2^ρ Π_{v ∈ S} n_v`, from `H¹(G, L_S) = 0`
  - [ ] G5d local norm index: `[K^× : K(v^j) N(L^×)] ≥ e_v f_v` for `j` large
  - [ ] G5e approximation and assembly
- [ ] G6 `ker ω ⊂ P_𝔪 N(I_L^𝔪)` for cyclic `L/K` (crossing with cyclotomic extensions)
  - [ ] G6a kernel for extensions inside `K(ζ_m)`: `ker ω = P_𝔪 N`
  - [ ] G6b transfer: `ω_{L/K}(N_{F/K} 𝔟) = ω_{LF/F}(𝔟)|_L`
  - [ ] G6c auxiliary fields (orders modulo primes; fixed fields in `L(ζ_m)`)
- [ ] G7 the reciprocity law for cyclic `L/K`, and for every linear character by G1

## Approach

`L/K` cyclic of degree `n`, `G = ⟨σ⟩`, `ω` the Artin map on `I^𝔪`, `N = N_{L/K}(I_L^𝔪)`.
Known: `N ⊂ ker ω`, `[I^𝔪 : ker ω] = n` (G2, G3), `[I^𝔪 : P_𝔪 N] ≤ n` (G4).

**G7 from G5, G6.** `ker ω ⊂ P_𝔪 N` (G6) and `[I^𝔪 : P_𝔪 N] ≥ n = [I^𝔪 : ker ω]` (G5) give
`ker ω = P_𝔪 N ⊃ P_𝔪`. A linear character of a Galois group factors through a cyclic quotient;
G1 transports the statement.

**G5.** For endomorphisms `f, g` of an abelian group `A` with `f g = g f = 0` put
`h_f(A) = [ker f : im g]`. For a stable subgroup `A'` with quotient `A''`:
`h_f(A) · δ = h_f(A') · h_f(A'')`, `δ = [gA ∩ A' : gA'] · [fA ∩ A' : fA']`, symmetric in `f, g`.
Hence `q = h_f / h_g` is multiplicative, `q = 1` on finite groups (G5a). With `f = σ − 1`,
`g = 1 + σ + … + σ^{n−1}`: `h_f = |Ĥ⁰|`, `h_g = |Ĥ¹|`.

Let `S` be a finite set of primes of `K` containing the ramified ones and generating the class
groups of `K` and of `L` (with the primes above), `𝔪 = Π_{v ∈ S} v^j · (ramified real places)`,
`U = K_{𝔪,1} N(L^×)`. Then `I^𝔪 / P_𝔪 N ≅ K^× / U K_S` and
`[K^× : U K_S] = [K^× : U] / [K_S : K_S ∩ U] ≥ [K^× : U] / [K_S : N(L_S)]`.
- `[K_S : N(L_S)] = h_f(L_S) = q(L_S) h_g(L_S) = 2^ρ Π_{v ∈ S} n_v / n`, `n_v = e_v f_v` (G5c):
  `H¹(G, L_S) = 0` by Hilbert 90 (an invariant ideal prime to `S` comes from `K`, and is
  principal up to `S`); `q(L_S) = q(E_L) Π_{v ∈ S} n_v` from the valuations
  `L_S / E_L ↪ ⊕_{w | S} ℤ` with finite cokernel and `q(ℤ[G/G_v]) = n_v`.
- `q(E_L) = 2^ρ / n` (G5b): for each infinite place `w` of `L` a unit `η_w` with `|η_w|_{w'} < 1`
  for `w' ≠ w`, chosen `G`-equivariantly; the `η_w` generate a subgroup of finite index with
  one relation, `0 → ℤ → ⊕_{v | ∞} ℤ[G/G_v] → W → 0`.
- `[K^× : U] ≥ 2^ρ Π_{v ∈ S} e_v f_v` (G5d, G5e): approximation reduces to one prime; the
  valuation gives `f_v`; for the units, with a normal basis `θ` and `V_k = 1 + v^k 𝓞_K[G]θ`:
  `H¹(V_k / V_M) = 0` for all `M ≥ k` (induced graded pieces), the finite module `U / V_k` has
  `h_f = h_g`, and `σϖ/ϖ` has order `≥ e_v` in `H¹(U / V_M)` (`ϖ` of valuation one above `v`;
  an element invariant modulo a deep unit is close to `K`, by the trace).

**G6.** Let `F/K` be finite with `LF ⊂ F(ζ_m)`. Then `ker ω_{LF/F} = P N_{LF/F}` (G6a: G1, G2, G3
and G4 for `LF/F`) and restriction `Gal(LF/F) → G` is injective, so
`N_{F/K}(𝔟) ∈ ker ω_{L/K} ⇒ N_{F/K}(𝔟) ∈ P_𝔪 N` (G6b). For admissible `F` (`L ∩ F = K`) this gives
`θ_F : G → I^𝔪 / P_𝔪 N` with `[N_{F/K} 𝔟] = θ_F(ω(N_{F/K} 𝔟))`. For a prime `𝔭` with
`ω(𝔭) = σ^d` take `m` with `n | ord_m(N𝔭)` and `τ` of order divisible by `n` independent of
`N𝔭` modulo `m`, and `F` the fixed field of `⟨(σ^d, N𝔭), (σ, τ)⟩` in `L(ζ_m)`: `𝔭` splits
completely in `F` and `F` is admissible. Two admissible fields are compared through a third one
built from a prime `ℓ ≡ 1 (n)` unramified in both; so `θ_F = θ` does not depend on `F` and
`[𝔞] = θ(ω(𝔞))` for all `𝔞` (G6c).

## Log
- 2026-11-13 — created; cyclotomic case formalized and moved to its own card
