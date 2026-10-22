# Parity-split Evans Gram law — formalized closure

- **ID:** `ccm-parity-split-evans-gram-law-formalized`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Paper proof:** `./ccm-parity-split-evans-gram-law.md`
- **Scientific status:** `[PAPER-PROVED] [LEAN-PROVED] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT RH]`

## Lean module

- `GaloisForLFunctions.RHTower.CCM.CCMParityInvolutionGrading`

Umbrella: `GaloisForLFunctions.RHTower`.

## Clause-by-clause audit

| card equation | Lean declaration | content |
|---|---|---|
| splitting | `parityPlus`, `parityMinus`, `isCompl_parity` | `F = F⁺ ⊕ F⁻` for any involution, with explicit halves `(v ± Jv)/2` |
| orthogonality | `inner_eq_zero_of_parity` | the two sectors are orthogonal for a reflection that is an isometry — the "reflection-invariant Hermitian metrics" step |
| `(1)` | `map_parityPlus_eq_parityMinus`, `finrank_parityPlus_eq_finrank_parityMinus`, `finrank_parityPlus_eq_half` | equal parity dimensions. The isolated mechanism is sharper than the card's basis count: it suffices that *some* automorphism `S` anticommute with the reflection, and then `S` carries one sector isomorphically onto the other |
| `(7)` | `residualParity`, `residualBranch`, `finrank_residualParity_parityPlus`, `finrank_residualParity_parityMinus` | the concrete residual model spanned by `x^j e^x, x^j e^{-x}` for `0 ≤ j < L`, reflection acting as `(-1)^j` times the branch swap; the branch-sign map is the anticommuting automorphism, so `dim F⁺ = dim F⁻ = L_a` |
| `(2)`–`(3)` | `map_parityPlus_le`, `map_parityMinus_le` | an equivariant map is graded, each sector landing in the corresponding target sector |
| `(5)` | `ker_eq_bot_iff_parity` | the map is injective exactly when both graded blocks are; the proof is the card's — apply the target reflection to `M p + M q = 0` and add |
| `(4)` | `det_eq_det_restrict_mul_det_restrict`, `mapsTo_parityPlus_of_commute`, `mapsTo_parityMinus_of_commute` | a reflection-commuting endomorphism has block-diagonal matrix in a parity-adapted basis, so its determinant is the product of the two sector determinants; by conjugation with `Submodule.prodEquivOfIsCompl` and `LinearMap.det_prodMap` |
| `(6)` | `prodInvolution`, `parityPlus_prodInvolution`, `parityMinus_prodInvolution`, `finrank_evansExcess_parityPlus`, `finrank_evansExcess_parityMinus` | the three-dimensional excess target graded as two even channels (mean, affine constant) and one odd channel (affine slope) |

## Axioms

`#print axioms` on every theorem returns exactly `[propext, Classical.choice, Quot.sound]`.

## Deliberately outside the Lean statement

The analytic inputs making the concrete `F_a`, `R_(L_a)`, `M_a` reflection-equivariant: evenness of
the corrected symbol `W_a`, commutation of the normalized Fourier multipliers `b_a, c_a` with
reflection, and parity-preservation of the supported logarithmic form and its Dirichlet inverse.
These are source facts; once each is available the statements above apply verbatim.

## Verification performed

- `lake env lean` on a scratch file importing the module: no errors.
- `#print axioms` on every theorem: clean.
