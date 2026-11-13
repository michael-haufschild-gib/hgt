# Specialization of the generic folded equation; the Jensen equations

- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Questions:** review-1211 §2.19 Q4 (group of one Jensen polynomial over the field of its
  coefficients); tool: specialization and genericity.

`K` a field of characteristic `≠ 2`, `F = K(x₁, …, x_n)`, `W_n = C₂ ≀ S_n` acting by
`x_i ↦ ± x_{σ i}`. `γ_k` (`k < n`) are the coefficients of `∏ (Y − x_i²)`, so
`∏ (X² − x_i²) = X^{2n} + Σ_k γ_k X^{2k}`.

## Theorems

1. The `2n` elements `± x_i` of `F` are pairwise distinct; `∏ (X² − x_i²)` is separable.
2. Every automorphism of `F` over `K(γ)` is `z ↦ a · z` for one `a ∈ W_n`.
   `Gal(F/K(γ)) ≅ W_n`.
3. `F` is a splitting field of `X^{2n} + Σ γ_k X^{2k}` over `K(γ)`; `F/K(γ)` is Galois of
   degree `2ⁿ n!`.
4. `F^{W_n} = K(γ)`.
5. `γ₀, …, γ_{n−1}` are algebraically independent over `K`.
6. If `c₀, …, c_{n−1}` in an extension of `K` are algebraically independent over `K`, then the
   Galois group of `X^{2n} + Σ c_k X^{2k}` over `K(c)` is isomorphic to `W_n`; the image of the
   uniform flip is central.
7. `E_n` the even quotient of the centred Jensen equation of `ξ`:
   `[Y^k] E_n = (−1)^{n−k} C(2n, 2(n−k)) μ_{2(n−k)}/μ₀` for `k ≤ n`. The Jensen equation of
   degree `2n` is `X^{2n} + Σ_k ([Y^k]E_n) X^{2k}`. Its coefficient family is algebraically
   independent over `ℚ` iff `μ₂/μ₀, …, μ₂ₙ/μ₀` is.
8. The Galois group of the Jensen equation of degree `2n` over `ℚ(its coefficients)` is
   isomorphic to `W_n`, or there is a nonzero `P ∈ ℚ[T₁, …, T_n]` with
   `P(μ₂/μ₀, …, μ₂ₙ/μ₀) = 0`.

## Proof

1. `x_i = x_j` gives `i = j` (variables of a polynomial ring). `x_i = −x_j` gives
   `X_i + X_j = 0`; evaluate at `(1, …, 1)`: `2 = 0`.
2. `σ` fixes the coefficients, so `σ(x_i)` is a root: `σ(x_i) = ε_i x_{π(i)}`. If
   `π(i) = π(j)` then `σ(ε_j x_i) = σ(ε_i x_j)`, so `ε_j x_i = ε_i x_j` and `i = j` by 1. So
   `π` is a permutation and `a = (π, ε)` agrees with `σ` on the constants and the `x_i`, hence
   on `F`. Conversely `W_n` fixes each `γ_k`. Faithfulness gives the isomorphism.
3. The roots `± x_i` are algebraic over `K(γ)`, so the algebra they generate is a field; it
   contains `K` and the `x_i`, hence `F`. Separable by 1.
4. `z ∈ F^{W_n}` is fixed by `Gal(F/K(γ))` by 2, so `z ∈ K(γ)` by 3.
5. `γ_k = (−1)^{n−k} e_{n−k}(x₁², …, x_n²)` (Vieta). The `e_j` are algebraically independent,
   `X_i ↦ X_i²` is injective on polynomials, the passage to `F` is injective, and scaling by
   nonzero constants and reindexing preserve independence.
6. `K(c) ≅ K(T₁, …, T_n) ≅ K(γ)` by `c_k ↦ γ_k` (5). The isomorphism carries the equation to
   the generic one. Let `K(c)` act on `F` through it: `F` is a splitting field of the equation
   over `K(c)`, and the automorphisms of `F` over `K(c)` are those over `K(γ)`. Apply 2.
7. Coefficient formula of the centred Jensen polynomial; `E_n` is monic of degree `n` and
   `E_n(X²)` is the Jensen equation. The factors `(−1)^{n−k} C(2n, 2(n−k))` are nonzero
   rationals; reverse the index.
8. 6 and 7.

## Formalization

`GaloisTheoryOfZeros/TheFoldedCoefficientsGenerateTheFixedFieldOfTheSignedPermutations.lean`:
`signedRoot_inj`, `separable_genericFoldedF`, `genericFoldedF_eq_foldedEquation`,
`exists_signed_smul_eq`, `foldedCoeffGaloisEquiv`, `isSplittingField_genericFoldedOver`,
`isGalois_foldedCoeffField`, `foldedPartField_eq_foldedCoeffField`, `finrank_foldedCoeffField`.

`GaloisTheoryOfZeros/AFoldedEquationWithIndependentCoefficientsHasTheFullSignedPermutationGroup.lean`:
`algebraicIndependent_const_mul`, `autEquivOfCompatible`, `isSplittingField_of_compatible`,
`foldedCoeff_eq`, `algebraicIndependent_foldedCoeff`, `coeffFieldEquiv`,
`foldedGaloisEquivOfAlgebraicIndependent`, `card_foldedGal_of_algebraicIndependent`,
`foldedGal_uniformFlip_comm`, `not_algebraicIndependent_of_card_foldedGal_ne`.

`GaloisTheoryOfZeros/TheJensenEquationsHaveTheFullGroupUnlessTheMomentsAreDependent.lean`:
`jensenCoeff_eq`, `foldedEquation_jensenCoeff`, `algebraicIndependent_jensenCoeff_iff`,
`map_jensenEquationOver`, `jensenGal_full_or_exists_moment_relation`,
`exists_moment_relation_of_card_jensenGal_ne`. Input added to
`CenteredJensenDiscriminantField.lean`: `evenCenteredQuotient_coeff`.

Checked with `lake --old env lean`; umbrella imports wired.

## Open

The class of complex conjugation in the group of a Jensen equation as a signed permutation.
The algebraic independence of the normalized moments.
