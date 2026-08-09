# Rank-one source-naturality rigidity and framing law — formalized

- **ID:** `rank-one-source-naturality-rigidity-and-framing-law-formalized`
- **Stage:** 3-formalized
- **Paper proof:** `rank-one-source-naturality-rigidity-and-framing-law.md` (same directory)
- **Status:** `[LEAN COMPLETE] [UNCONDITIONAL] [NO SORRY] [NO NEW AXIOMS]`

## Lean modules

| Module | Path |
|---|---|
| `GaloisForLFunctions.HTGeometry.ConstraintRelativity.RankOneFraming` | `formal/GaloisForLFunctions/HTGeometry/ConstraintRelativity/RankOneFraming.lean` |

Wired into `GaloisForLFunctions.HTGeometry`.

## Formal theorem chain

All declarations live in namespace `HTGeometry.ConstraintRelativity`.

Theorem 1 — unframed rank-one naturality rigidity:

1. `line_mul_eq_zero` — **card `(2)`**.  A bilinear law on `ℂ ⊕ L` natural under the line
   automorphisms `f = λ · id_L` (card `(1)`) satisfies `L² = 0`.  The proof is the card's: the
   scalar component obeys `λ²β = β` and the line component `λ²α = λα` (card `(4)`), and `λ = 2`
   kills both.
2. `dualMul`, `dualMul_natural`, `dualMul_line` — the converse: the square-zero law is natural, so
   the classification is exactly one law rather than none.

Only the automorphisms of the fixed line are used, which is precisely the naturality instance the
card's proof invokes; the statement therefore needs no family of algebra structures indexed by all
lines.

Theorem 2 — framed quadratic classification:

3. `quadPoly`, `quadAlgebra`, `quadDiscr` — card `(5)` and `(6)`.
4. `quadPoly_natDegree`, `quadPoly_ne_zero`, `quadAlgebra_finiteDimensional`,
   `finrank_quadAlgebra` — the framed algebra is two-dimensional, so `1, e` is a basis and the
   presentation `(5)` is the general two-dimensional monogenic commutative algebra.
5. `eval₂_quadPoly`, `root_sq` — the defining relation `e² = a e + b`.
6. `root_ne_zero` — the frame is nonzero.
7. `exists_algEquiv_prod_of_discr_ne_zero` — **card `(7)`, first case**: `Δ ≠ 0` gives
   `quadAlgebra a b ≃ₐ[ℂ] ℂ × ℂ`.  The proof takes a square root `d` of `Δ`, forms the two distinct
   roots `r, s = (a ± d)/2`, lifts to `ℂ × ℂ`, proves surjectivity by exhibiting explicit
   preimages, and concludes injectivity from equal finite dimension.
8. `exists_algEquiv_dual_of_discr_eq_zero` — **card `(7)`, second case**: `Δ = 0` gives
   `quadAlgebra a b ≃ₐ[ℂ] quadAlgebra 0 0`, by the translation `y = e − a/2` in both directions.
9. `exists_nilpotent_quadAlgebra_zero`, `not_nonempty_algEquiv_dual_prod` — the two types are not
   isomorphic: the degenerate type has a nonzero square-zero element and the split type is reduced.
   (Non-isomorphic unital algebras are in particular not Morita equivalent through their centres,
   which is the card's argument.)

Corollary:

10. `quadAlgebra_zero_not_algEquiv_one` — **the framing corollary**: the laws `e² = 0` and `e² = 1`
    have one generator, one relation and the same rank, yet are not isomorphic.  Rank, generator
    count and relation count therefore do not determine the successor law.

## Verification

```text
lake env lean GaloisForLFunctions/HTGeometry/ConstraintRelativity/RankOneFraming.lean  # clean
lake build GaloisForLFunctions.HTGeometry                                              # green
```

`#print axioms` on `line_mul_eq_zero`, `exists_algEquiv_prod_of_discr_ne_zero`,
`exists_algEquiv_dual_of_discr_eq_zero`, `quadAlgebra_zero_not_algEquiv_one` returns only
`[propext, Classical.choice, Quot.sound]`.
