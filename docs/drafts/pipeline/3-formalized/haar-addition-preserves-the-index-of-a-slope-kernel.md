# Haar addition preserves the index of a slope kernel

- **ID:** HAAR-SLOPE-INDEX-PRESERVATION
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Parent:** [Finite-index Mautner rigidity](../1-in-progress/finite-index-mautner-rigidity-for-the-haar-successor.md)
- **Statement:** For every Hermitian group kernel `ψ : ℚˣ → ℂ`, the affine kernel `Φ(g)=haarState(g)+ψ(slope(g))` has exactly the negative index of `ψ`.

## Dependency-closed paper proof

Positivity of Haar and surjectivity of the slope homomorphism give `κ(Φ)≤κ(ψ)`.

Fix a finite slope family `u_a`, its dilation lifts `x_a`, the Gram matrix `A_ab=ψ(u_a⁻¹u_b)`, and the Haar Gram matrix `P_ab=haarState(x_a⁻¹x_b)`. For every positive integer `N`, choose rational translations `t_1,…,t_N` such that distinct translated families are Haar-orthogonal. Construct these inductively: the large-prime-denominator argument `den_ne_one_of_prime` separates any existing finite family from the next translated copy. Hermitian symmetry supplies the reverse pairings.

On `y_(a,j)=T_(t_j)x_a`, the affine Gram entries are `A_ab+δ_ij P_ab`. The coefficient map `c_a↦c_a/N` on each copy pulls this form back to `A+P/N`. Thus `ν(A+P/N)≤κ(Φ)`. These matrices converge entrywise to `A`; `eventually_le_hermNegIndex` gives `ν(A)≤κ(Φ)`. Taking the supremum over finite slope families proves the reverse inequality.

The existing index-one logarithmic perturbation is one instance. The separable valuation-assembly formula concerns a different kernel; no novelty claim is made for the general averaging principle.

## Consequence to audit

After matching the value at the identity, a slope correction from Haar's dilation reading to Weil's would give an explicit extension with both readings. The normalization and index of that correction still need auditing. This concerns separable corrections; it does not exhaust O5's possible carriers.

## Verification

`AdelicKreinGeometry/Haar/IndexPreservation.lean` proves `negIndex_haar_add_slope`.
The direct `lake --old env lean` check passed; the transitive axiom audit contains exactly
`propext`, `Classical.choice`, and `Quot.sound`. The module is wired into the umbrella.

[Positive Haar carriers](positive-haar-carriers-preserve-the-index-of-slope-corrections.md)
extends the same index law to every positive affine kernel with integer successor.
