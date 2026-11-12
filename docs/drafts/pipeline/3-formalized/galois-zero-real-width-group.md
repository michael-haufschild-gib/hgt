# The real width group and ordinary conjugation

- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Questions:** Full source-field Galois group; functional-equation reflection.

For the complete-fibre source field `K`, write `w_q=t_q+iδ_q`,
`L=ℚ(all w)`, `M=L(i)`, and `F=K(all δ_q)`.

## Theorem

1. `M=F(i)` and `F=M∩ℝ`. The entire width extension `F/K` is normal.
2. Restriction and Gaussian sign give
   `Gal(M/K) ≅ Gal(F/K) × C₂` unconditionally.
3. Ordinary conjugation has coordinates `(id,−1)`.
4. Simultaneous width negation extends to a `K`-automorphism of `F`
   exactly when functional-equation reflection lifts to `M`, equivalently
   when `i∉L`. Such a width reversal is unique.
5. For any nonzero anchor, the criterion is `δ₀∉E`, where
   `E=K(δ_qδ_r : q,r)`.

These are statements about the complete infinite extensions. They decide
neither which Gaussian regime occurs nor whether any width is nonzero.

## Proof

The identities `δ_q=−i(w_q−t_q)` and `w_q=t_q+iδ_q` give `M=F(i)`.
Every element has coordinates `a+bi`, with `a,b∈F⊆ℝ`; realness forces
`b=0`. Thus `F` is the fixed field of ordinary conjugation. Centrality of
that conjugation makes `F/K` normal.

Restriction to `F` and sign on `i` are jointly injective. Normality extends
any automorphism of `F` to `M`. Composing with ordinary conjugation changes
its Gaussian sign independently, proving surjectivity and the direct product.

Since `ρ_q=1/2−δ_q+it_q`, width negation together with Gaussian sign `−1`
provides functional-equation reflection. Conversely that reflection reverses
`i` and fixes every centered zero, hence negates every width. The Gaussian
obstruction and even-width anchor criterion give the equivalences. Widths
generate `F`, proving uniqueness.

## Lean

`formal/GaloisForLFunctions/GaloisTheoryOfZeros/TheRealWidthFieldOfTheZeros.lean`

- `gaussianZeroExtension_eq_realWidth_adjoin`, `realWidthField_eq_real_part`
- `realWidthField_comap_eq_fixedField`, `realWidthField_normal`
- `realWidthGaloisProduct`, `realWidth_conjugation_coordinates`
- `realWidth_negation_iff_functional_equation`, `realWidth_negation_iff`
- `realWidth_negation_iff_anchor`, `realWidth_negation_unique`

Final source audit passed. All seven audited dependency closures contain
only `propext`, `Classical.choice`, and `Quot.sound`.
