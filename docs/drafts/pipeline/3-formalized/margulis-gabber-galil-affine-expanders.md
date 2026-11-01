# Margulis–Gabber–Galil affine expanders

- **Stage:** 3-formalized
- **Type:** THEOREM (Lean), classical literature
- **Statement:** The eight affine shear/translation edges on `(ℤ/nℤ)²`, `n ≥ 3`,
  have normalized walk `W` satisfying `‖W − P‖ ≤ 5√2/8 < 1`, with `P` the mean projection.
- **Source:** [girving/aks](https://github.com/girving/aks),
  `c7fb62ed80a4a610f87f34db0082cadbd7c00c9f`; Apache-2.0.

## Objects and proof

The four forward maps are `(x+2y,y)`, `(x,2x+y)`, `(x+2y+1,y)`,
and `(x,2x+y+1)`, modulo `n`; the other four are their inverses.
Repeated edges and loops are counted by ports. Vertices use the bijection
`(x,y) ↦ xn+y` from `Fin n × Fin n` to `Fin (n*n)`.

1. `mgg_rot_involution` proves edge reversal. Consequently the walk is self-adjoint,
   preserves constants, and preserves the mean.
2. `mgg_walkCLM_inner_eq_corr` pairs forward and inverse edges. For the unnormalized
   finite Fourier transform, `parseval_2d` gives energy factor `n²`; the four
   `dft2d_comp_shear*` identities identify affine pullbacks with dual shears and phases.
3. `norm_one_add_ω_inv` turns each phase pair into `2|cos(πa/n)|`.
   The reciprocal weight is `√2` toward smaller axis distance, `√2/2` toward larger
   distance, and `1` for incomparable points. `pointwiseCondition_forall` proves the
   bound `5√2/2` at every nonzero frequency by the diamond and complementary cases.
   `young_assembly` sums the reciprocal Young inequalities, giving `5√2/4` times energy.
4. Mean zero removes the zero Fourier mode. Parseval and walk normalization yield
   `|⟨f,Wf⟩| ≤ (5√2/8)‖f‖²`. Polarization and orthogonal centering give
   `spectralGap_mgg`. Here `spectralGap` denotes the nonconstant spectral radius.
5. Since `(√2)²=2`, `5√2/8<1`. `norm_mgg_centered_le` gives the corresponding
   contraction for every centered function without a cancellation premise.

## Lean endpoints

Directory: `formal/GaloisForLFunctions/HTGeometry/AffineExpanders/`.

- `AffineExpanders.spectralGap_mgg`: bound for every `n ≥ 3`.
- `AffineExpanders.mgg_expander_family`: uniform family indexed by `n+3`, including strict bound below one.
- `AffineExpanders.norm_mgg_centered_le`: `‖Wf−Pf‖ ≤ (5√2/8)‖f−Pf‖`.

All dependency modules compile at default limits. Final check:
`lake --old env lean GaloisForLFunctions/HTGeometry/AffineExpanders/Audit.lean`.
Guarded transitive axiom lists contain only `propext`, `Classical.choice`, `Quot.sound`.
Imported by `HTGeometry.lean`; no umbrella build. No mathematical novelty claimed.
