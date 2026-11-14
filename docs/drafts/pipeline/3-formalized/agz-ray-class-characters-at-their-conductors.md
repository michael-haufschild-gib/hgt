# Ray class characters at their conductors: an Artin character has a zero configuration

- **ID:** agz-conductor-descent
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** docs/reports/review-1311/obstacles-summary.md §2.14 (question 5, construction IV); programme `formal/GaloisForLFunctions/AbsoluteGeometryOfSpecZ` (README question 5: "the ray class characters at their conductors, so that an Artin character has a zero configuration")
- **Statement:** Every ray class character `ψ` modulo `𝔪 = 𝔪₀ 𝔪∞` of a number field is `ψ' ∘ r`
  for exactly one character `ψ'` modulo `𝔫 = 𝔣(ψ) 𝔪∞`, `r : Cl_𝔪 → Cl_𝔫` the canonical surjection;
  `ψ'` is primitive, `ψ'(𝔞) = ψ(𝔞)` on the ideals prime to `𝔪₀`, and
  `L(s, ψ) = L(s, ψ') Π_{v | 𝔪₀} (1 − ψ'(v) N v^{−s})` on `ℂ ∖ {1}`. Hence the zeros of `L(s, ψ)`,
  `ψ ≠ 1`, in `Re s > 0` are the zeros of the completion of `ψ'`, and the index law holds for every
  nontrivial ray class character in the zeros of its own `L`-function. The Artin symbols of a
  linear character of a Galois group are the values of a primitive ray class character outside
  finitely many primes.

## Goal

The index law (`exists_le_negIndex_heckeGram_iff`) and the explicit formula are proved for
primitive characters. The reciprocity law produces a character modulo `(c) ∞` with no control of
its conductor. The descent removes the hypothesis: each ray class character gets the zero
configuration of its primitive character, and the character of a linear Artin character can be
taken primitive.

Not a statement on the position of the zeros.

## Gates
- [x] 0 → 1  in-progress
- [x] 1 → 2  fully-proven
- [x] 2 → 3  formalized: `primitiveHecke`, `heckeFiniteConductor_primitiveHecke`, `heckeLFunction_eq_primitiveHecke_mul`, `exists_le_negIndex_rayClassGram_iff`, `exists_primitive_heckeCharacter_artinSymbol`

## Proof

`K_𝔪` = elements prime to `𝔪₀`; `I^𝔪` = ideals prime to `𝔪₀`; `K^{𝔪,1}_+` = kernel of
`rayHom_𝔪 : K_𝔪 → (𝓞/𝔪₀)ˣ × {±1}^{𝔪∞}` (residue and signs); `P_𝔪` its principal ideals;
`Cl_𝔪 = I^𝔪 / P_𝔪`. Let `J ⊇ 𝔪₀` be an ideal, `𝔫 = J 𝔪∞`, `π : (𝓞/𝔪₀)ˣ → (𝓞/J)ˣ`.

**1. The map `r`.** The primes of `J` are primes of `𝔪₀`, so `K_𝔪 ≤ K_𝔫`, `I^𝔪 ≤ I^𝔫`. For
`α = a/b ∈ K_𝔪` with `a, b` prime to `𝔪₀`: `red_𝔫 α = π(red_𝔪 α)`, and the signs agree; so
`rayHom_𝔫 α = (π × id)(rayHom_𝔪 α)`, `K^{𝔪,1}_+ ≤ K^{𝔫,1}_+`, `P_𝔪 ≤ P_𝔫`, and `[I] ↦ [I]` is a
homomorphism `r : Cl_𝔪 → Cl_𝔫` commuting with the maps to `Cl_K`.

**2. `r` is onto.** Let `c ∈ Cl_𝔫`. `Cl_𝔪 → Cl_K` is onto: take `d ∈ Cl_𝔪` with the ideal class
of `c`. Then `c · r(d)⁻¹` has trivial ideal class: it is `[(γ)]`, `γ ∈ K_𝔫`. Units lift along
surjections of finite rings, so `π` is onto, and `rayHom_𝔪` is onto: there is `δ ∈ K_𝔪` with
`π(red_𝔪 δ) = red_𝔫 γ` and the signs of `γ`. Then `rayHom_𝔫(δ) = rayHom_𝔫(γ)`, so
`[(γ)]_𝔫 = [(δ)]_𝔫 = r([(δ)]_𝔪)` and `c = r(d · [(δ)])`.

**3. The kernel.** Let `I ∈ I^𝔪` with `r([I]) = 1`: `I = (α)`, `α ∈ K^{𝔫,1}_+`. As `(α)` is prime
to `𝔪₀`, `α ∈ K_𝔪`, and `ψ([I]) = χ_f(red_𝔪 α) · χ_∞(signs of α) = χ_f(red_𝔪 α)` with
`π(red_𝔪 α) = red_𝔫 α = 1`. So if the finite part `χ_f` of `ψ` is trivial on `ker π`, then
`ker r ≤ ker ψ` and `ψ = ψ' ∘ r` for exactly one `ψ' ∈ Ĉl_𝔫` (step 2). `ψ' = 1` iff `ψ = 1`.

**4. The finite part of `ψ'`.** `r` maps the class of `(α)`, `rayHom_𝔪 α = (u, σ)`, to the class
with `rayHom_𝔫 = (π u, σ)`. So `χ'_f ∘ π = χ_f`. For `J = 𝔣(ψ)`, the conductor of `χ_f`, the
hypothesis of step 3 holds, and `χ'_f` is the primitive character of `χ_f`: `𝔣(ψ') = 𝔣(ψ) = 𝔫₀`.

**5. Values and Euler products.** For an integral ideal `𝔞` prime to `𝔪₀`: `ψ'(𝔞) = ψ(𝔞)`; for
`𝔞` not prime to `𝔪₀`: `ψ(𝔞) = 0`. The Euler factors of `ψ` and `ψ'` agree at `v ∤ 𝔪₀`, and the
factor of `ψ` at `v | 𝔪₀` is `1`:

  `L(s, ψ) = L(s, ψ') Π_{v | 𝔪₀} (1 − ψ'(v) N v^{−s})`, `Re s > 1`.

**6. Zeros.** Both sides continue analytically to `ℂ ∖ {1}`, a connected open set; the identity
holds there. For `Re s > 0`: `|ψ'(v) N v^{−s}| < 1`, so the finite product does not vanish, and
`L(s, ψ) = 0 ⇔ L(s, ψ') = 0`. For `ψ ≠ 1` and `Re s > 0` the completion of `ψ'` is `L(s, ψ')`
times nonvanishing factors. So the zeros of `L(s, ψ)` right of the critical line are the right
zeros of the configuration of `ψ'`, and Weil's form of `ψ'` has `n` negative squares on some `n`
tests iff `L(s, ψ)` has at least `n` zeros with `Re s > 1/2`.

**7. Linear Artin characters.** For a linear character `χ` of the group of a Galois extension
`L/K`, the reciprocity law gives `c ≥ 1` and `ψ` modulo `(c) ∞` with `(χ, v) = ψ(v)`, `v ∤ c`.
With `ψ'` the primitive character of `ψ`: `(χ, v) = ψ'(v)` for `v ∤ c`, and for `Re s > 1`

  `L(s, χ) = L(s, ψ') Π_{v | c} (1 − ψ'(v) N v^{−s}) (1 − (χ, v) N v^{−s})^{−1}`. ∎

## Lean

| Step | Declaration | Module |
|---|---|---|
| 1 | `divisorModulus`, `rayHom_divisorModulus`, `rayClassReduction` | `RHTower/Artin/EveryRayClassCharacterIsInducedFromAPrimitiveCharacterOfItsConductor.lean` |
| 2 | `rayClassReduction_surjective` | same |
| 3 | `ker_rayClassReduction_le`, `descendHecke`, `descendHecke_apply`, `descendHecke_eq_one_iff` | same |
| 4 | `finiteResidueCharacter_descendHecke`, `primitiveHecke`, `heckeFiniteConductor_primitiveHecke` | same |
| 5 | `heckeValue_descendHecke`, `heckeValue_primitiveHecke_prime`, `heckeL_eq_heckeL_primitiveHecke_mul` | same |
| 6 | `heckeLFunction_eq_primitiveHecke_mul`, `heckeLFunction_eq_zero_iff_heckeXi_primitiveHecke`, `rayClassZeros`, `rightZeros_rayClassZeros`, `exists_le_negIndex_rayClassGram_iff`, `forall_negIndex_rayClassGram_eq_zero_iff` | `AbsoluteGeometryOfSpecZ/TheZerosOfARayClassLFunctionAreTheZerosOfItsPrimitiveCharacter.lean` |
| 7 | `exists_primitive_heckeCharacter_artinSymbol` | `RHTower/Artin/TheArtinSymbolsOfALinearCharacterAreTheValuesOfAPrimitiveRayClassCharacter.lean` |

## What stays open

- The conductor exponent at a ramified prime (the Artin conductor through the higher
  ramification groups).

Closed elsewhere: `χ ≠ 1 ⇒ ψ' ≠ 1` and the virtual configuration of a general Artin character
with its orders (card `agz-artin-characters-zero-configuration-with-orders`); the
conductor–ramification theorem, `(χ, v) = ψ'(v)` at every prime, with which the finite product
in step 7 is `1` (card `agz-conductor-ramification`).

## Log
- 2026-11-13 — created in 1-in-progress with the paper proof
- 2026-11-13 — formalized (three modules, each one clean compile), moved to 3-formalized
