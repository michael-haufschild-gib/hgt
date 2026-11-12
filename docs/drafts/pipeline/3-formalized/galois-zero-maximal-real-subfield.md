# The maximal real subfield of the infinite zero field

- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Questions:** Conjugation's fixed field; the Gaussian obstruction.

Let `K` be the complete-fibre source field and `L=ℚ(all w)`, with
`w_q=t_q+iδ_q`, `t_q∈K`, and real signed widths `δ_q`. Define

```
E=K(δ_qδ_r : q,r),       F=K(δ_q : q).
```

## Theorem

1. `E=L∩ℝ`. It is the fixed field of centered conjugation and is normal over `K`.
2. If `δ₀≠0`, then `L=E(iδ₀)` and `[L:E]=2`. Without such a width, `L=K`.
3. For every nonzero anchor, `F=E(δ₀)`. This is either `E` or a quadratic extension.
4. For a nonzero anchor, `F=E ⇔ δ₀∈E ⇔ i∈L`.

All statements concern the entire zero field, with no height cutoff or
simplicity assumption.

## Proof

The imaginary offsets `w_q−t_q=iδ_q` belong to `L`, so their products put
`δ_qδ_r` in `L`. These products are real, giving `E⊆L∩ℝ`.
For `δ₀≠0`,

```
iδ_q = (δ₀δ_q/δ₀²) iδ₀,       δ_q = (δ₀δ_q)/δ₀.
```

Hence `L=E(iδ₀)` and `F=E(δ₀)`. Since `E` is real, the imaginary anchor is
outside `E`; its square belongs to `E`, so the first extension is quadratic.
Writing any element as `a+b iδ₀` shows that real elements are exactly `E`.
When all widths vanish, all centered zeros already belong to `K`.

Conjugation is central in `Gal(L/K)`. Its fixed subgroup is therefore normal,
and its fixed field `E` is normal over `K`; the argument applies to the
infinite extension.

If `i∈L`, write `i=a+b iδ₀`. Real and imaginary parts give `a=0` and
`bδ₀=1`, hence `δ₀∈E`. The converse follows by division. The width-anchor
formula identifies this membership with `F=E`; otherwise its square gives
a genuinely quadratic real extension.

## Lean

`formal/GaloisForLFunctions/GaloisTheoryOfZeros/TheMaximalRealSubfieldOfTheZeroField.lean`

- `evenWidthField_eq_real_part`, `evenWidthField_comap_eq_fixedField`
- `evenWidthField_normal`
- `zeroExtension_width_anchor_quadratic`, `centered_zero_field_dichotomy`
- `realWidthField_eq_width_anchor`, `realWidthField_anchor_quadratic`
- `gaussianUnit_mem_zeroExtension_iff_width_mem`
- `realWidthField_eq_even_iff_gaussianUnit`, `realWidthField_anchor_dichotomy`

Final source audit passed. All seven principal dependency closures contain
only `propext`, `Classical.choice`, and `Quot.sound`.

The theorem does not establish the existence of a nonzero width or decide
which Gaussian regime occurs. The full real-width group and source equations
remain on [the width-field candidate](../1-in-progress/galois-zero-real-width-field.md).
