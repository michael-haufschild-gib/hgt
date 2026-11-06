# W4 — invariant characters and exact tensor growth

- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** [W4](../1-in-progress/w4-purity-on-a-non-fibred-base.md).
- **Scope:** Finite spectra and standard complex `SL₂` representations; no arithmetic base is constructed.

## Invariant characters

Every `SL₂(ℂ)`-invariant multilinear form of degree `2k` transforms under an invertible matrix `A` by `det(A)^k`. Conversely, this transformation law characterizes invariance. Odd-degree invariant forms vanish. Every even degree has a nonzero invariant.

**Proof.** Choose `c² = det(A)` and write `A = c g`, where `det(g)=1`. Multilinearity gives `c^(2k) = det(A)^k`. Conversely specialize to determinant one. For odd degree, invariance under `−I` gives `f=−f`. Products of `k` determinants of consecutive pairs are invariant and evaluate to one on repeated standard bases.

Lean: `invariant_even_det`, `mem_invariantForms_even_iff`, `invariant_odd_eq_zero` in `WeightFamilies/InvariantForms.lean`; `determinantPairs_mulVec`, `exists_nonzero_even_invariant` in `WeightFamilies/PairingForms.lean`.

## Exact growth law

For a finite complex spectrum `z_i`, `m>0`, and `B≥0`,

`∃ C, ∀ n, |Σ_i z_i^n|^m ≤ C B^n  ↔  ∀ i, |z_i|^m ≤ B`.

**Proof.** The `m`th trace power is the power sum on the tensor spectrum indexed by words of length `m`. Finite power-sum rigidity bounds each tensor eigenvalue by `B`. Constant words give the asserted bound. Conversely, choose an eigenvalue of largest modulus; the triangle inequality gives the estimate with `C=(#ι)^m`. For an empty spectrum, take `C=0`.

Consequently, a single `B` working for every positive even degree, with arbitrary constants `C_k`, is equivalent to `|z_i|≤1`. Indeed, the powers of any modulus greater than one are unbounded. For the converse take `B=1`.

Lean: `tensor_powerSum`, `tensor_moment_bound_iff`, `fixed_base_tensor_bound_iff` in `WeightFamilies/TensorGrowth.lean`. The rigidity input is the existing `WeilKloosterman.norm_le_of_power_sums_bound`.

## Curve windows

For `CurveDatum`, reciprocal symmetry upgrades `|β_i|≤1` to `|β_i|=1`: the paired moduli multiply to one. Hence the common tensor-rate condition is equivalent to purity and to nonnegativity of the Toeplitz form on the window of size equal to the number of distinct eigenvalues.

Lean: `curve_fixed_base_tensor_bound_iff`, `curve_tensor_bound_iff_spectrum_window` in `WeightFamilies/CurveTensorReceivers.lean`, using the existing `CurveDatum.unitary_iff_toeplitz_nonneg_on_spectrum_window`.

All four modules pass `lake --old env lean`. These equivalences identify the required estimate; they do not prove it for a new arithmetic family.
