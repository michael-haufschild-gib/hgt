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
- [ ] G2 the Artin map `I^𝔪 → G^{ab}`, `v ↦ Frob_v`, for `𝔪` divisible by the ramified primes
- [ ] G3 norms from `L` are in the kernel of the Artin map
- [x] G4 first inequality: `[I^𝔪 : P_𝔪 N(I_L^𝔪)] ≤ [L:K]`, for every finite `L/K`
  (`agz-norm-index-inequality`, from the Mertens bounds of the ray class characters)
- [ ] G5 second inequality for cyclic `L/K` (Herbrand quotients of units and of ideal classes)
- [ ] G6 Artin's lemma (crossing with cyclotomic extensions) and the kernel `P_𝔪 N(I_L^𝔪)`

## Approach

**G2–G6.** The classical ideal-theoretic proof: the Artin map is surjective (G4 applied to the
fixed field of its image) and kills norms (G3: `Frob_v` has order `f(v)`), so its kernel has index
`[L:K]` and contains `N(I_L^𝔪)`; G4 and G5 give `[I^𝔪 : P_𝔪 N(I_L^𝔪)] = [L:K]` for cyclic `L/K`;
G6 shows `P_𝔪 ⊂` kernel by comparing with cyclotomic extensions, where the reciprocity law is
proved.

## Log
- 2026-11-13 — created; cyclotomic case formalized and moved to its own card
