# Hecke ideal theta as finite parity Poisson sums

- **ID:** hecke-ideal-theta-as-finite-parity-poisson-sums
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** [Hecke and class-field programme](../1-in-progress/hecke-l-functions-and-class-field-theory-2026-10-28.md), HL7
- **Statement:** Decompose actual finite-character weighted integral-ideal theta into residue cosets, apply parity Poisson summation to each, and identify the dual phase with the field trace.

## Exact target and dependencies

For an integral ideal `b` coprime to `𝔪.fin`, the cosets of `𝔪.fin*b` in `b`
are indexed by `𝓞 K / 𝔪.fin`. The existing `residueRep` is defined for every
residue, with `residueRep_mem` and `mk_residueRep` proved in
`ConePointsOfARayClassAreLatticeCosets.lean`. This is actual arithmetic data,
not an assumed choice of compatible lattice representatives.

The finite weight is constant on each coset. The scaled lattice of `𝔪.fin*b`
has the proved norm-discriminant covolume and trace-dual description. The
already formalized parity Gaussian Poisson identity applies to each translate.
The inner product of a scaled representative with a reciprocally scaled,
conjugated dual element is the trace of their product. Real parity monomials
are unchanged by mixed complex conjugation.

The resulting dual coefficient is the explicit finite sum over residues of
the actual finite character times `exp(2πi Tr(cρ*β))`. No primitive Gauss-sum
evaluation is assumed. Finite summation and absolute convergence permit the
exchange with the dual lattice series. The coefficient bound follows from
the finite-character norm bound and unit-modulus phases.

## Corpus audit

The completed semantic query for finite-periodic lattice Poisson returned
scalar residue-class theta identities and the new general Gaussian/affine
Poisson theorems. It did not return the target arithmetic finite-coset theorem.
This query result is not a claim of global absence.

Required local sources are inspected: `residueRep`, scaled ideal lattice
equivalences, reciprocal duality, arithmetic covolume, and parity Poisson.
The actual weighted-theta kernel and unit periodicity are formalized in
[the preceding card](../3-formalized/finite-hecke-weights-give-unit-periodic-ideal-theta.md).

## Completed proof

- Restrict affine parity Poisson to actual fractional-ideal subtypes.
- Prove reciprocal scaling cancels in the trace pairing.
- Construct the ideal coset equivalence and prove the finite weighted transform.
- Audit the exact source and transitive axioms.

## Formalization progress

`HTGeometry/IntrinsicParityPoisson.lean` proves the affine parity transform over
actual lattice and integer-dual subtypes, with inverse covolume and normalized
parity factor. It also proves absolute summability on both sides. The complete
scratch and three transitive axiom audits pass with standard axioms only. The
source is wired into the HTGeometry umbrella; its final direct audit passes
without warnings. Its olean is built for the written arithmetic affine-parity
consumer. The completed intrinsic scratch is removed.
Its proof transports subtype-indexed sums with explicit equality rewrites,
avoiding failed simplification under dependent binders.

`HeckeLFunctions/HeckeThetaHasAFiniteFourierTransform.lean` contains reciprocal-scale trace
pairing, mixed-conjugation invariance of the actual real parity kernel, actual
ideal and trace-dual reindexing, and the exact affine ideal parity Poisson
formula. The complete affine formula passes its first scratch check and its
transitive axiom audit is standard only. Both dependency oleans are built.

The module also incorporates the actual residue/product-ideal coset
equivalence, finite-weight constancy, integral/fractional-ideal equivalence,
residue-sum decomposition, dual absolute convergence, finite Fourier
coefficients bounded by `Ideal.absNorm 𝔪.fin`, and the complete weighted theta
Poisson formula with absolute convergence of the full dual series. Its complete
scratch and final direct `lake --old env lean` source audit pass without warnings.
Nine transitive axiom audits include the affine formula, residue decomposition,
main finite Fourier transform, coefficient bound, complete dual summability,
and the imported weighted-theta results. All use only `propext`,
`Classical.choice`, and `Quot.sound`. The module is wired into the Hecke umbrella;
no umbrella was compiled. No proof limits were raised. Completed scratches are
removed. Its olean is built for the written zero-mode and uniform-tail consumer.
The imported weighted-theta axioms were checked again after
its norm-proof dependency reduction and remain standard only.

## Main Lean declarations

In [HeckeThetaHasAFiniteFourierTransform.lean](../../../../formal/GaloisForLFunctions/HeckeLFunctions/HeckeThetaHasAFiniteFourierTransform.lean):

- `numberFieldMixedPlaceScale_mul_neg`, `inner_numberFieldTraceCoordinates_scaled_conjugate`
- `numberFieldTracePhase`, `latticePhase_scaled_trace`, `parityGaussian_hecke_conjugate`
- `heckeParityKernel`, `idealParityTheta`, `idealParityTheta_poisson`
- `residueIdealEquiv`, `integralIdealEquivFractional`, `heckeIdealTheta_eq_residue_sum`
- `finiteHeckeFourierCoefficient`, `norm_finiteHeckeFourierCoefficient_le`
- `heckeThetaPoissonFactor`, `heckeIdealTheta_poisson`, `summable_norm_finiteHeckeFourierKernel`

For `b ≠ 0`, `b + 𝔪.fin = 1`, and `t > 0`, the exact transform is

`Θ_(ψ,b)(y,t) = A_(ψ,𝔪.fin*b)(y,t) Σ_(β∈dual(𝔪.fin*b)) G_(ψ,b)(β) F_ψ(-y,1/t,β)`.

Here `G(β) = Σ_(ρ mod 𝔪.fin) χ_fin(ρ) exp(2πi Tr(cρ β))`, and
`A = exp(Σ_w mult(w)y_w) / (N(𝔪.fin*b) sqrt(|disc K|)) * t^(-[K:ℚ]/2) * (-i/t)^k`.
These are actual arithmetic coefficients and lattices. No primitive Gauss formula
or Mellin identity is assumed or claimed.

Primitive finite Gauss evaluation, unit-domain integration, and Hecke Mellin
unfolding remain separate open steps; this theorem alone is not the functional
equation.
