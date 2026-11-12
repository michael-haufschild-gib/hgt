# Signed permutations of the complete zero fibres

- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:** The entire source Galois action is a closed faithful subgroup of the product of weighted signed-permutation groups.

Let `K` be the complete-fibre source field and `L=ℚ(all w)`. For each
ordinate `t` and analytic multiplicity `m`, let `B_(t,m)` be the distinct
roots in that fibre with positive imaginary part and multiplicity `m`.
These are finite sets of canonical conjugate-pair representatives.

## Theorem

The multiplicity-preserving centralizer `C_t` of conjugation on the
complete distinct-root support has the exact group description

```
C_t ≅ ∏_m (C₂ ≀ Sym(B_(t,m))).
```

A signed permutation consists of a pair permutation `π` and a sign `ε`
per output pair. Its action and multiplication are

```
(p,u) ↦ (πp, ε(πp)u),
(ε,π)(η,τ) = (ε·(η∘π⁻¹), πτ).
```

The possible real root of a fibre is unique and fixed. Consequently

```
Gal(L/K) ↪ ∏_(t,m) (C₂ ≀ Sym(B_(t,m)))
```

is faithful and continuous, with closed image. Centered conjugation is
the identity pair permutation with uniform negative sign in every block.
A full signed family belongs to the arithmetic image exactly when its
inverse-coordinate fibre actions are realized in every finite complete-fibre
source compositum. Equality with the ambient product is not asserted.

## Proof

Conjugation sends `Im w` to `−Im w`, preserves analytic multiplicity,
and has precisely the real roots as fixed points. All roots of one fibre
have the same real part, so its real support has at most one element.
Every nonreal root has a unique positive-imaginary representative and sign.
A conjugation-commuting permutation therefore induces a pair permutation
and one sign; preserving multiplicity separates the blocks.

Conversely independent signed actions on all multiplicity blocks, together
with the identity on the real support, assemble into a permutation of the
whole fibre preserving conjugation and multiplicity. These constructions
are inverse and respect the displayed multiplication.

Transport the established full divisor action through these equivalences.
It remains faithful. Every finite signed coordinate is continuous; compactness
of the source Galois group gives closed image in the Hausdorff product.
Transporting the intrinsic finite-source compatibility criterion gives
exactly the claimed extension condition. The common conjugation swap
becomes uniform negative sign under the positive-root coordinates.

## Formalization

`GaloisTheoryOfZeros/TheSignedPermutationsOfTheZeroFibres.lean`:
`fibrePairEquiv`, `fibreSignedEquiv`, `allSignedFibreAction_injective`,
`allSignedFibreAction_continuous`, `allSignedFibreAction_range_isClosed`,
`allSignedFibreAction_source_compatibility`, and
`allSignedFibreAction_conjugation`.

Direct source audit passed with `lake --old env lean`. Audited dependency
closures contain only `propext`, `Classical.choice`, and `Quot.sound`.
