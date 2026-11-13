# The generic folded equation has the full signed permutation group

- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Questions:** review-1211 §2.19 T4g (the function-field case with its signed-permutation
  group); calibration of Q4; T3g (class of the reflection).

`K` a field with `2 ≠ 0`, `F = K(x₁, …, x_n)`. `W_n = C₂ ≀ S_n` (`FibreSignedPerm (Fin n)`)
acts on `F` by `x_i ↦ ε x_{σ i}`. `F^W` is the fixed field.

## Theorem

The polynomial `P = ∏ (X² − x_i²) = E(X²)`, `E = ∏ (Y − x_i²)`, has coefficients in `F^W`;
`F` is its splitting field over `F^W`; `Gal(P / F^W) ≅ W_n`, of order `2ⁿ n!`, and
`[F : F^W] = 2ⁿ n!`. The uniform flip `x_i ↦ −x_i` is central and negates every root.

## Proof

A signed permutation carries the factor `X² − x_i²` to `X² − x_{σ i}²`, so `P` is invariant
and its coefficients lie in `F^W`. `P = ∏ (X − x_i)(X + x_i)` splits in `F`. The subalgebra
generated over `F^W` by the roots contains `K` and every `x_i`, hence every polynomial; it is
a field because `F/F^W` is algebraic, so it contains every quotient. The action is faithful:
`ε x_{σ i} = ε' x_{σ' i}` forces `σ i = σ' i` and `ε = ε'` since `1 ≠ −1`. Artin's theorem
gives `Aut(F/F^W) = W_n`. The uniform flip is central in `W_n`.

## Formalization

`GaloisTheoryOfZeros/TheGenericFoldedEquationHasTheFullSignedPermutationGroup.lean`:
`signedMvPolynomialAction`, `signedMvPolynomialFaithful`, `foldedPart`, `finrank_foldedPart`,
`genericFolded`, `genericFoldedF_eq_expand`, `map_genericFoldedF`,
`isSplittingField_genericFolded`, `genericFoldedGaloisEquiv`, `card_genericFoldedGal`,
`uniformFlip_smul_foldedRoot`, `genericFoldedGaloisEquiv_uniformFlip_comm`,
`natDegree_genericFolded`.

Checked with `lake --old env lean`; umbrella import wired. Not formalized: `F^W = K(e_k(x²))`
and the transfer to a polynomial with algebraically independent coefficients.
