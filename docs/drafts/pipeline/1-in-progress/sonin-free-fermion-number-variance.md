# Sonin free-fermion number variance

- **ID:** `sonin-free-fermion-number-variance`
- **Stage:** 1-in-progress
- **Type:** exact physics value relation / corpus strengthening
- **Scientific status:** source-derived and source-formalized; novelty not claimed
- **Lean targets:**
  `formal/GaloisForLFunctions/HTGeometry/HilbertSchmidtOperator.lean`,
  `formal/GaloisForLFunctions/RHTower/SoninProlateCommutatorEnergy.lean`

## Claim

Let `P` be a Fermi projection and `R` a spatial projection.  Write

```text
T = R P R,
L = (1-R) P R,
U = R P (1-R) = L†,
K = [P,R] = L-U.
```

The two transition corners are Hilbert--Schmidt orthogonal because `L^2=U^2=0`.  Therefore

```text
||K||_HS^2 = ||L||_HS^2 + ||U||_HS^2 = 2 ||L||_HS^2
             = 2 Re tr(T-T^2).
```

In free-fermion physics `Re tr(T-T^2)` is the local particle-number variance.  In the Sonin
specialization, `P` and `R` are the central physical- and Fourier-forbidden projections, and `T`
is the existing `soninAlternatingBlock`.

## Corpus value

1. `HilbertSchmidtOperator.lean` now has basis-independent Pythagorean addition and subtraction
   laws for any Hilbert--Schmidt-orthogonal pair.  They are available to the entire general
   hypertranscendental operator corpus, not only the zeta/Sonin specialization.
2. The factor-two transition-rate law is formalized for every self-adjoint observable and
   orthogonal cutoff, not merely for two projections.  The commutator and impurity-trace laws then
   specialize to arbitrary pairs of subspace projections.  Every non-Sonin module can reuse them
   once its transition corner is known to be Hilbert--Schmidt.
3. For a Hilbert--Schmidt self-adjoint observable, the two-sided ideal property now discharges the
   transition-corner Hilbert--Schmidt premise automatically.
4. The concrete Sonin transition corner is proved Hilbert--Schmidt from the already-constructed
   time-band ideal, so the central specialization introduces no Hilbert--Schmidt hypothesis.
5. The central cutoff commutator energy, one transition-corner energy, and the prolate impurity
   trace are now interchangeable with exact factors `1`, `2`, and `1/2`; no comparison constant
   or spectral assumption is required.
6. The same energy is twice the sum of the greedy spectral values of `T-T²`, connecting the
   cutoff calculus to the existing compact master-constraint spectrum API.
7. This connects the measurement-disturbance API in `SoninLudersPinching.lean` to the trace and
   Hilbert--Schmidt APIs already used by the Sonin obstruction modules.
8. The result does not prove RH and does not settle the live source-norm comparison.  Its value is
   a lossless bridge between three existing quantitative theorem surfaces.

## Physics provenance

For a quasi-free Fermi state, the compressed one-particle correlation operator has spectrum in
`[0,1]`, and its quadratic impurity gives particle-number fluctuations.  Klich--Levitov use the
full counting statistics of this compressed correlation operator to relate quantum noise and
fermionic entanglement.  The spatial free-Fermi literature states the quadratic fluctuation value
as `tr f(T)` for `f(t)=t(1-t)` and rewrites it as the squared Hilbert--Schmidt norm of the
inside/outside transition block.  The commutator factor two follows by adding the equal lower and
upper transition energies.  For a projection state `e`, the more general self-adjoint-observable
law is also the pure-projection specialization of Wigner--Yanase skew information:
`I(e,X) = -(1/2) tr([e,X]^2) = ||(1-e)Xe||_HS^2`.

Primary sources:

- I. Klich and L. Levitov, *Quantum Noise as an Entanglement Meter*, Physical Review Letters 102
  (2009), 100502, https://doi.org/10.1103/PhysRevLett.102.100502.
- E. P. Wigner and M. M. Yanase, *Information Contents of Distributions*, Proceedings of the
  National Academy of Sciences 49 (1963), 910--918, https://doi.org/10.1073/pnas.49.6.910.
- P. Pfeiffer and W. Spitzer, *Logarithmically Enhanced Area-Laws for Fermions in Vanishing
  Magnetic Fields in Dimension Two*, Integral Equations and Operator Theory 96 (2024), article
  16, https://doi.org/10.1007/s00020-024-02778-3, especially Section 3.

## Formal surface

- `ContinuousLinearMap.hsNormSq_neg_eq_self`
- `ContinuousLinearMap.hsNormSq_add_eq_of_hsInner_eq_zero`
- `ContinuousLinearMap.hsNormSq_sub_eq_add_of_hsInner_eq_zero`
- `centralProlateTransition_isHilbertSchmidt`
- `hsNormSq_commutator_eq_two_mul_crossBoundary_of_selfAdjoint`
- `hsNormSq_commutator_eq_two_mul_crossBoundary_of_selfAdjoint_hilbertSchmidt`
- `hsNormSq_starProjection_commutator_eq_two_mul_transition`
- `re_opTrace_soninAlternatingBlock_impurity_eq_transition_hsNormSq`
- `hsNormSq_starProjection_commutator_eq_two_mul_tsum_svVal_prolateImpurity`
- `hsNormSq_centralCutoffCommutator_eq_two_mul_transition`
- `re_opTrace_centralProlateImpurity_eq_transition_hsNormSq`
- `hsNormSq_centralCutoffCommutator_eq_two_mul_re_opTrace_prolateImpurity`

## Verification boundary

The declarations are source-formalized but intentionally uncompiled.  No Lean invocation, build,
lint, axiom check, numerical script, or experimental computation was run.  Promotion to Stage 3
requires later targeted checking.
