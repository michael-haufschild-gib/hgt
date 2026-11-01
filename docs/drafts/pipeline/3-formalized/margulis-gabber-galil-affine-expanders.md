# Margulis–Gabber–Galil affine expanders

- **Stage:** 3-formalized
- **Statement:** On `(ℤ/nℤ)²`, `n ≥ 3`, the eight-edge normalized affine walk satisfies
  `‖Wf − mean(f)‖₂ ≤ (5√2/8) ‖f − mean(f)‖₂`, with `5√2/8 < 1`.

## Objects and proof

Vertices are `ZMod n × ZMod n`. The forward maps are `(x+2y,y)`, `(x,y+2x)`,
`(x+2y+1,y)`, `(x,y+2x+1)`; the other four are their inverses.
`mggAffineKernel` is their symmetric bistochastic matrix average, retaining loops
and edge multiplicities.

1. Pairing inverse permutations expresses the quadratic form as one quarter of
   the four forward correlations.
2. `cyclicPairFourier` applies the corpus cyclic Fourier transform in each coordinate.
   Parseval gives factor `n²`; affine pullbacks become dual shears with translation
   phases of modulus `2|cos(πa/n)|`.
3. Reciprocal edge weights, determined by distance to the axes, have row bound
   `5√2/2` off zero. Summed reciprocal Young inequalities give correlation bound
   `5√2/4`. Mean zero removes the zero frequency; normalization gives quadratic
   bound `5√2/8`.
4. Restriction to the finite zero-sum subspace and the symmetric Rayleigh norm
   formula give Euclidean contraction. Centering uses the existing `finiteMean`.

The pointwise residue estimate adapts the argument in
[girving/aks, Young.lean](https://github.com/girving/aks/blob/c7fb62ed80a4a610f87f34db0082cadbd7c00c9f/AKS/MGG/Young.lean).
The Fourier transform, Schur inequality, matrix kernel, and centering are integrated
with existing corpus definitions.

## Lean endpoints

Namespace `GaloisForLFunctions.HTGeometry`:

- `mggAffineMatrix_quadratic_le`: absolute zero-sum quadratic bound.
- `mggAffine_centered_norm_le`: contraction about the finite mean for `n ≥ 3`.
- `mggAffine_expander_family`: unconditional family at modulus `n+3`, including strict bound below one.

Modules: `HTGeometry/AffineExpanders/QuadraticBound.lean` and `Contraction.lean`.
`Audit.lean` guards their transitive axiom lists: only `propext`, `Classical.choice`,
`Quot.sound`. All checks use default elaboration limits. Imported by `HTGeometry.lean`.
