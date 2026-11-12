# Brauer's induction theorem

- **ID:** A150-brauer
- **Stage:** 1-in-progress
- **Type:** THEOREM (classical; formalization)
- **Source:** `docs/reports/review-1211/obstacles-summary.md` §2.1 (A150), §2.14 question 4
- **Statement:** for a finite group `G`, every virtual character is an integer combination of
  characters induced from linear characters of Brauer-elementary subgroups:
  `AddSubgroup.closure (Set.range (brauerElementaryMonomialVirtualCharacter G)) = ⊤`
  (objects of `formal/GaloisForLFunctions/RHTower/Artin/ArtinBrauerElementary.lean`).

## Goal

The integral monomial span of the virtual characters. For the index law of an Artin character
the rational statement suffices and is proved (`exists_nsmul_mem_closure_monomial`,
`exists_le_negIndex_power_iff`; card `3-formalized/agz-virtual-character-index-law.md`, V9). The
integral statement is needed for the function `L(s, χ)` itself. Both uses also need the
reciprocity law (the `L`-function of an induced linear character is a Hecke `L`-function), which
is class field theory and is not in the corpus.

## Gates

- [x] B0 induced character formula: the character of `Representation.ind H.subtype ρ` at `g` is
  `Σ_{q ∈ H\G, r_q g r_q⁻¹ ∈ H} χ_ρ(r_q g r_q⁻¹)`, and `(1/|H|) Σ_{x, x g x⁻¹ ∈ H} χ_ρ(x g x⁻¹)`
- [x] B1 induction of functions by the formula: class-function property, the projection formula
  `Ind(f · Res ψ) = Ind(f) · ψ` (transitivity is deferred to B9, where it is used)
- [x] B2 products of characters are characters; for every family of subgroups the span of the
  induced characters is an ideal of the ring of virtual characters, equal to it as soon as it
  contains the constant `1`
- [ ] B3 irreducible characters: an orthonormal integer basis of the virtual characters; descent:
  a virtual character that is a combination of members of a subgroup `V` with algebraic integer
  coefficients, after multiplication by an integer `l`, has `l·χ ∈ V`
- [ ] B4 cyclic groups: `θ_C` (value `|C|` on generators, `0` elsewhere) is a virtual character
  of `C`; `|G| = Σ_C Ind θ_C`; a class function with values in `|G|·𝓞` is an `𝓞`-combination of
  characters induced from cyclic subgroups
- [ ] B5 congruence: an integer-valued `𝓞`-combination of characters has `f(x) ≡ f(x_r) mod p`,
  `x_r` the `p`-regular part
- [ ] B6 for a `p`-regular `x`: the subgroup `⟨x⟩ × P`, `P` a Sylow `p`-subgroup of the
  centralizer, is Brauer-elementary; the induced function of `|⟨x⟩|·1_{x}` ⊗ `1` is integer
  valued, `≢ 0 mod p` at `x`, and vanishes at the `p`-regular elements not conjugate to `x`
- [ ] B7 with `|G| = p^n l`: `l` lies in the `𝓞`-span of the characters induced from
  `p`-elementary subgroups
- [ ] B8 the virtual characters are spanned over `ℤ` by characters induced from elementary
  subgroups
- [ ] B9 every irreducible character of a Brauer-elementary group is induced from a linear
  character of a subgroup
- [ ] B10 the theorem

## Approach

Serre, *Linear representations of finite groups*, §10.1–10.5 and Theorem 16 [C]. `𝓞` is the
ring of algebraic integers in `ℂ` (in place of `ℤ[ζ_{|G|}]`); `𝓞 ∩ ℚ = ℤ`.

**B0.** Coinduced model: functions `f : G → V` with `f(h x) = ρ(h) f(x)`, `G` acting by right
translation; evaluation at representatives `r_q` of the right cosets identifies it with
`(H\G → V)` (corpus, `coinducedRightCosetEquiv`). There `g` acts by
`(T_g a)(q) = ρ(r_q g r_{q·g}⁻¹) a(q·g)`. The trace of an operator on `(Q → V)` is the sum of
the traces of its diagonal blocks, so `tr T_g = Σ_{q·g = q} χ_ρ(r_q g r_q⁻¹)`, and `q·g = q` iff
`r_q g r_q⁻¹ ∈ H`. Induction and coinduction are isomorphic for a subgroup of finite index
(Mathlib), and isomorphic representations have one character. Averaging over the `|H|`
representatives of each coset (`χ_ρ` is a class function on `H`) gives the second form.

**B1–B2.** By the formula. `Ind(f · Res ψ)(g) = (1/|H|) Σ f°(xgx⁻¹) ψ(xgx⁻¹) = Ind(f)(g) ψ(g)`.
Products: tensor products of representations (Mathlib). If `ψ` is a character of `G` and `χ` one
of `H`, then `χ · Res ψ` is a character of `H`, so `Ind(χ)·ψ` is in the span.

**B3.** Maschke and orthogonality (Mathlib, corpus). Descent: write the members of `V` and `χ`
in the basis of irreducible characters; the coefficients of `lχ = Σ a_k v_k` are equations in
the finitely generated torsion-free `ℤ`-module `ℤ[a_k]`, in which `ℤ·1` is a direct summand
(`ℤ[a_k] ∩ ℚ = ℤ`); apply a retraction onto `ℤ`.

**B4–B8.** Serre §10.2–10.4, Lemmas 5–11 and Theorems 18, 19.

**B9.** Serre Theorem 16 for groups with a normal abelian subgroup not in the center, by
induction on the order: restriction to that subgroup is not isotypic, so the representation is
induced from the stabilizer of an isotypic component, a proper subgroup that is again
elementary (corpus: subgroups of a product of a `p'`-group and a `p`-group split).

## Lean

Folder `formal/GaloisForLFunctions/RHTower/Artin/`.

| Gate | Module | State |
|---|---|---|
| — | `ArtinMonomialRationalSpan` | Artin's rational theorem (not a gate of this card) |
| B0 | `ArtinInducedCharacterFormula` | done: `trace_pi_eq_sum_blocks`, `extendByZero`, `conj_coind_apply`, `coind_character_apply`, `induced_character_apply`, `rightCosetProdEquiv`, `induced_character_apply_average` |
| B1 | `ArtinClassFunctionInduction` | done: `inducedFunction`, `induced_character_eq_inducedFunction`, `monomialVirtualCharacter_val`, `inducedFunction_conj`, `inducedFunction_mul_restrict` |
| B2 | `ArtinInducedSpanIsAnIdeal` | done: `mul_mem_fdCharacterSet`, `one_mem_fdCharacterSet`, `mul_mem_virtualCharacterGroup`, `inducedSpan`, `inducedSpan_le`, `mul_mem_inducedSpan`, `inducedSpan_eq_of_one_mem` |
| B4 (first half) | `ArtinCyclicInductionIdentity` | done: `generatorWeight`, `cyclicSubgroups`, `inducedFunction_generatorWeight`, `sum_inducedFunction_generatorWeight` (`Σ_C Ind θ_C = \|G\|`). Open: the `𝓞`-span and the lemma on class functions with values in `\|G\|·𝓞` |

## Log
- 2026-11-12 — created; plan fixed
- 2026-11-12 — B0 formalized
- 2026-11-12 — B1, B2 formalized
- 2026-11-12 — B4 first half (Artin's identity) formalized
