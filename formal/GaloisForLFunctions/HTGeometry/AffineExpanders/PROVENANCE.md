# Affine expanders

Adapted from [girving/aks](https://github.com/girving/aks), commit
`c7fb62ed80a4a610f87f34db0082cadbd7c00c9f`, under Apache-2.0 (see `LICENSE`).

| Local file | Upstream source |
|---|---|
| `Fin.lean` | First four arithmetic lemmas of `AKS/Misc/Fin.lean` |
| `Regular.lean`, `Square.lean` | `AKS/Graph/Regular.lean`, `AKS/Graph/Square.lean` |
| `Rayleigh.lean` | Polarization lemma `sa_opNorm_le_of_inner_le` in `AKS/ZigZag/RVWBound.lean` |
| `Defs`, `DFT`, `WalkExpansion`, `YoungDefs`, `Young`, `YoungAssembly`, `Spectral` | Corresponding `AKS/MGG/` files |
| `Family.lean`, `Audit.lean` | Project-owned family corollaries and transitive dependency checks |

Adaptations: project-local imports and `AffineExpanders` namespace; Lean 4.32.2 compatibility;
default elaboration limits; removal of unused reflexive `abs_one_add_rootOfUnity`;
extraction of the required polarization lemma without the unrelated zig-zag development;
explicit Fourier reindexing summands, targeted cast normalization, shared spatial reindexing,
and corrections to explanatory weight and normalization conventions.
The substantive identity is `norm_one_add_ω_inv`.

Mathematical target: the eight affine shear/translation maps on `(ℤ/nℤ)²` have normalized
walk operator `W` satisfying `‖W − P_constants‖ ≤ 5√2/8` for `n ≥ 3`.
Upstream calls this quantity `spectralGap`; it is the nonconstant spectral radius, so the
gap from `1` is at least `1 − 5√2/8`.

Locally verified endpoints: `AffineExpanders.spectralGap_mgg`,
`AffineExpanders.mgg_expander_family`, and `AffineExpanders.norm_mgg_centered_le`.
`Audit.lean` guards their transitive axiom lists: only `propext`, `Classical.choice`, `Quot.sound`.
