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

## Current frontier

`TheWindowReceiversOfACurve.lean` proves equivalence between normalized spectral purity and positivity on one window of size equal to the number of distinct eigenvalues. This receiver alone does not construct a family or prove its purity.

## Invariant-weight obstruction

For the standard complex plane, invariant forms of degree `2k` transform by `det(A)^k`; odd-degree invariants vanish. Every even invariant space is nonzero. These weights retain the determinant and discard the eigenvalue-modulus ratio.

Consequently Golden Frobenius and `√5 I` act identically on every invariant form, although the Golden spectrum is impure. Its even-tensor local Euler coefficients are nonnegative and its optimal degree-`m` growth rate is `φ^m`.

This algebraic obstruction does not refute W4. Identifying ζ's actual spectrum with a pure invariant restriction, or proving a global trace identity, remains additional arithmetic content.

**Positive survivor:** exact determinant-character classification in every even degree, with nonzero paired-volume forms. [Paper proofs and checked Lean declarations](../3-formalized/w4-invariant-characters-and-tensor-growth.md). The [Golden obstruction](../5-failed/w4-invariant-weights-alone.md), including its sharp tensor rate `φ^m`, is also formalized.

## Global obligation

Deligne's [Weil I, §3.3–3.7](https://www.jmilne.org/math/Documents/DeligneWeilI.pdf) uses nonnegative local even-tensor Euler coefficients, coefficient domination by the global product, and a cohomological expression whose poles have weight `kβ+1`. The base contributes the fixed `+1`; invariant weights identify the denominator but do not prove the global identity.

The [positive global trace theorem](../3-formalized/w4-positive-global-trace.md) discharges the finite spectral step: if `Re(Σ a_i^n − Σ b_j^n) ≥ 0` for `n ≥ 1` and `|a_i| ≤ B`, then `|b_j| ≤ B` and the trace is at most `(#a+#b)B^n`. Thus no separate purity input for negative cohomology is needed once the global trace identity and its positive spectrum are constructed.

## Tensor-growth classification

For a finite spectrum `z_i`, positive tensor degree `m`, and `B ≥ 0`,

`∃ C, ∀ n, |Σ_i z_i^n|^m ≤ C B^n  ↔  ∀ i, |z_i|^m ≤ B`.

Thus one `B` working for all even degrees, with unrestricted constants `C_k`, is equivalent to confinement to the unit disk (`fixed_base_tensor_bound_iff`). Reciprocal symmetry upgrades this to purity for `CurveDatum`, hence to the existing spectrum-window receiver (`curve_tensor_bound_iff_spectrum_window`). Both are Lean-checked. The global bound remains an equivalent input, not a proved estimate for a new family.

## Canonical arithmetic symmetry

For divisor monodromy `ρ ↦ 1 − conj(ρ)`, [canonical compression](../3-formalized/w4-canonical-monodromy-compression.md) has exactly the pure point spectrum `1/2 + i Im(ρ)` unconditionally. Merely preserving its invariant subspace under Frobenius is already equivalent to RH. The lost off-diagonal coupling is exactly `Re(ρ)−1/2`. A pure compression therefore does not supply the required invariant restriction.

## Frobenius compatibility

The [split Weil-group model](../3-formalized/w4-split-weil-model.md) realizes every prescribed-determinant matrix in degree one, with full `SL₂` degree-zero image and Frobenius normalization. Golden Frobenius has such a lift. Abstract compatibility therefore adds no local purity restriction beyond the determinant.

## Concrete function-field source

The [Kloosterman moment hypersurface](../3-formalized/w4-kloosterman-moment-hypersurface.md) gives a concrete source: every degree-`m` family moment equals `#F` times a character sum on `Σxⱼ=0` in `(F×)^m`, with an exact correction for the singular parameter. Even moments are nonnegative without invoking purity. The remaining cancellation on this hypersurface is not supplied by the fixed factor `#F`.

The [Kloosterman window calibration](../3-formalized/w4-kloosterman-window-receiver.md) constructs a pure `CurveDatum` for every nonzero parameter over an odd prime field, identifies all extension-field traces, and proves every finite window form nonnegative. Its arithmetic estimate is the existing Artin–Schreier–Stepanov proof; a monodromy weight proof remains distinct.

The [projective count identity](../3-formalized/w4-kloosterman-moments-are-point-counts.md) removes the character sum: every positive-degree moment is exactly `q(qA−B)`, where `A,B` count normalized torus tuples satisfying two or one vanishing-sum equations. Even degrees give the unconditional incidence bound `B≤qA` over every finite field.

## Next conjecture

The [hyperplane contribution](../3-formalized/w4-hyperplane-trace-is-explicit.md) is an explicit Tate trace: `qB_m=(q−1)^m−(−1)^m`, hence `M_{m+1}=q²A_m−(q−1)^m+(−1)^m`. Its extension-field spectrum consists of integral powers of `q`. The remaining double-zero locus has [critical points exactly at normalized sign coordinates](../3-formalized/w4-reciprocal-torus-singularities.md), with nondegenerate transverse Hessian when `2≠0`. On the [coordinate boundary](../3-formalized/w4-reciprocal-projective-boundary.md), one zero is excluded, two zeros give a nonzero differential, and three zeros annihilate the differential.

The complete [boundary Tate trace](../3-formalized/w4-coordinate-boundary-tate-trace.md) is formalized for actual projective scalar quotients over every finite extension. Its count is `D_n=Σ_{j=0}^{n−2}q^j−B_{n−1}−nB_{n−2}`, and its Tate eigenvalues are bounded by `q^(n−4)`. The [compactified moment identity](../3-formalized/w4-compactified-moment-trace.md) now separates this explicit boundary from the actual projective reciprocal locus. The corrected even trace is nonnegative over every finite extension without a character or purity premise.

The [critical-point trace](../3-formalized/w4-critical-point-tate-trace.md) is also formalized: every normalized torus critical point descends through field embeddings. Its trace is constant, with an exact characteristic-dependent binomial formula and the separate characteristic-two count. The [actual transverse quadratic determinant](../3-formalized/w4-transverse-quadratic-determinant.md) is `−Πx_i`, with a complete tangent chart and exact reciprocal-series coefficient. The [transverse quadric count and extension trace](w4-transverse-quadric-trace.md) are the next local input.

Realize the difference of these explicit counts cohomologically, with its positive spectrum bounded by the invariant tensor weights and fixed base loss. The positive global trace theorem then controls the negative spectrum automatically. The ζ family and its spectral identification remain open. The existing ζ result `riemannHypothesis_of_sublinear_tensor_loss` already covers sublinear losses; weakening a fixed loss to a sublinear one does not supply the missing estimate.
