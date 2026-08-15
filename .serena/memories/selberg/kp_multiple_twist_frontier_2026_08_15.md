# Kaczorowski–Perelli multiple-standard-twist frontier (2026-08-15)

Current user goal requires honest Lean reconstruction of Kaczorowski–Perelli 2026 before claiming Selberg C1/C2 progress.

## Verified completed modules
- `GaloisForLFunctions/SelbergClass/MeromorphicTensor.lean`: function-level global quotient of entire functions on `Fin N → ℂ`; displayed denominator regular locus only.
- `MeromorphicTensorAgreement.lean`: fraction-field equality implies equality on common displayed regular locus; candidate polar set semantics.
- `MeromorphicTensorAlgebra.lean`: entire additive shifts preserve displayed denominator/candidate divisor and add values on regular locus.
- `MultipleStandardTwistGammaClearing.lean`: reciprocal-Gamma affine entire denominator and gamma-cleared presentation.
- `MultipleStandardTwistGammaGeometry.lean`: nonzero affine functional reaches 1; named Gamma candidate hyperplanes and union/complement theorems.
- `MultipleStandardTwistDataGammaGeometry.lean`: `Σ d_i s_i` nonzero directly from `MultipleStandardTwistData.degree_pos`; denominator requires no supplied nonzero proof.
- `MultipleStandardTwistMellinBarnesFubini.lean`: initial-domain exact sum/integral interchange, including `MultipleStandardTwistData.damped_eq_smul_integral_mellinBarnes`.
- `MultipleStandardTwistDegreeResonanceTrace.lean`: finite fibre tangent Bohr trace selects `m^dG=n^dF`, equal degree selects `m=n`.

All above source-check/exact-module-build/axiom-audited (only propext, Classical.choice, Quot.sound), and are wired into `SelbergClass.lean`.

## Exact source facts audited
Kaczorowski–Perelli arXiv:2603.13885v1:
- L(s)=Σ d_i s_i; b=−(d+1)/2+iθ; H_l={L+b=−l}.
- spectrum α_n=Π(n_i/(q_i κ_i^{d_i}))^{κ_i}; finite Xi uses conjugated coefficients / n_i^(1−s_i).
- Xi_l is normal-direction residue using Σd_i(w_i−s_i); Xi_l=C_D W_l Xi.
- Paper does not imply Selberg orthogonality/prime correlations.

## Actual open cores
1. Functional-equation localization/contour shifts/residue accounting.
2. Exact source spectrum/fibre/Xi layer and structural invariants.
3. C^N analytic normal-family/Vitali theorem. Mathlib has no multivariable Montel/Vitali; one-variable `Complex.analyticOnNhd_iff_differentiableOn` and local-uniform derivative APIs do not type-check on `Fin N → ℂ`.
4. Even after K–P, unbounded tangent trace and alpha→0 uniformity are the separate Selberg bridge.

## Research status
Finite square-fibre and degree-resonance traces are genuine exact positive survivors but BRIDGE only. No proof/disproof of Selberg C1/C2 exists; do not claim otherwise. Loop 4 establishes a standard no-go: polar data is invariant under adding entire terms while tangent Bohr mean changes, so polar information alone cannot recover regular trace.
