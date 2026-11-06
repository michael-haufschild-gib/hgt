# W4 — purity on a non-fibred base

- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Source:** `docs/reports/review-0611/obstacles-summary.md`, W4.
- **Target:** Construct an arithmetic family containing ζ, prove purity of its monodromy-invariant part, and recover the function-field window receivers.

## Mathematical obligations

1. Specify the base, family, monodromy action, and arithmetic specialization without assuming purity or an equivalent positivity statement.
2. Prove the tensor-power weight bound from the constructed family; direct tensor amplification alone does not produce a bound.
3. Identify the invariant spectrum and prove its purity.
4. Recover `CurveDatum` window receivers from a function-field family.
5. Formalize each dependency-closed result and wire modules into their mathematical owner's umbrella.

## Current frontier

`TheWindowReceiversOfACurve.lean` proves equivalence between normalized spectral purity and positivity on one window of size equal to the number of distinct eigenvalues. This receiver alone does not construct a family or prove its purity.

## Invariant-weight obstruction

For the standard complex plane, every `SL₂`-invariant multilinear form of degree `2k` transforms under an invertible `A` by `det(A)^k`; odd-degree invariants vanish. Proof: write `A = c g`, `c² = det(A)`, `det(g)=1`, then use multilinearity. The central matrix `-1` kills odd-degree invariants. Products of pairwise determinants give nonzero invariants in every even degree.

Consequently `diag(√5 φ, √5/φ)` and `√5 I` act identically on every invariant form. The former is the impure Golden spectrum. Invariant weights alone cannot select local purity, even when invariance is imposed under the entire group `SL₂`. This is an algebraic countermodel, not a sheaf over an arithmetic base.

This does not refute W4. Identifying ζ's actual spectrum with a pure invariant part would be a new arithmetic input. The obstruction concerns inference from invariant tensor weights to purity of a fibre without that identification or a global trace identity.

**Positive survivor:** exact determinant-character classification in every even degree, with nonzero paired-volume forms. [Paper proofs and checked Lean declarations](../3-formalized/w4-invariant-characters-and-tensor-growth.md). The [Golden obstruction](../5-failed/w4-invariant-weights-alone.md), including its sharp tensor rate `φ^m`, is also formalized.

## Global obligation

Deligne's [Weil I, §3.3–3.7](https://www.jmilne.org/math/Documents/DeligneWeilI.pdf) uses nonnegative local even-tensor Euler coefficients, coefficient domination by the global product, and a cohomological expression whose poles have weight `kβ+1`. The base contributes the fixed `+1`; invariant weights identify the denominator but do not prove the global identity.

## Tensor-growth classification

For a finite spectrum `z_i`, positive tensor degree `m`, and `B ≥ 0`,

`∃ C, ∀ n, |Σ_i z_i^n|^m ≤ C B^n  ↔  ∀ i, |z_i|^m ≤ B`.

Expand `(Σ_i z_i^n)^m` as the power sum of `∏_{j<m} z_{a_j}`. Finite power-sum rigidity bounds every tensor eigenvalue; the constant word gives `|z_i|^m ≤ B`. Conversely choose an eigenvalue of largest modulus and apply the triangle inequality, with `C = (#ι)^m`. This also handles the empty spectrum when `m > 0`.

Thus one `B` working for all even degrees, with unrestricted constants `C_k`, is equivalent to confinement to the unit disk (`fixed_base_tensor_bound_iff`). Reciprocal symmetry upgrades this to purity for `CurveDatum`, hence to the existing spectrum-window receiver (`curve_tensor_bound_iff_spectrum_window`). Both are Lean-checked. The global bound remains an equivalent input, not a proved estimate for a new family.

## Canonical arithmetic symmetry

For divisor monodromy `ρ ↦ 1 − conj(ρ)`, [canonical compression](../3-formalized/w4-canonical-monodromy-compression.md) has exactly the pure point spectrum `1/2 + i Im(ρ)` unconditionally. Merely preserving its invariant subspace under Frobenius is already equivalent to RH. The lost off-diagonal coupling is exactly `Re(ρ)−1/2`. A pure compression therefore does not supply the required invariant restriction.

## Next conjecture

The [split Weil-group model](w4-split-weil-model.md) tests whether Frobenius normalization of full `SL₂` monodromy adds any restriction: its degree-one image should be every matrix of the prescribed determinant.

The arithmetic target remains a trace identity producing the common `B` from cohomological degrees rather than from the unknown spectrum. The ζ family, its spectral identification, and recovery from a constructed function-field family remain open. The existing ζ result `riemannHypothesis_of_sublinear_tensor_loss` already covers sublinear losses; weakening a fixed loss to a sublinear one does not supply the missing estimate.
