# CCM pole-projection Born survival

- **ID:** `ccm-pole-projection-born-survival`
- **Stage:** 1-in-progress
- **Type:** exact physics value relation / source-level Lean formalization
- **Scientific status:** source-derived and source-formalized; novelty not claimed or required
- **Usefulness gate:** converts an existing projection-defect theorem into a quantitative
  projective-measurement theorem without any added hypothesis or loss of constants

## Claim

Let `S` be a closed Hilbert subspace, `P_S` its orthogonal projection, and `psi` a unit vector.
The Born probability of the projective-measurement outcome `S` is

```text
p_S(psi) = Re <psi, P_S psi> = ||P_S psi||^2
         = 1 - ||P_S psi - psi||^2.
```

Hence a defect estimate `||P_S psi - psi||^2 <= epsilon` is exactly the survival estimate
`1 - epsilon <= p_S(psi)`.  No positivity lemma, comparison constant, time evolution, or
repeated-measurement limit is needed.

## Physics provenance

Projective quantum measurements use the expectation of the projection as the probability of the
corresponding outcome.  In the quantum-Zeno terminology this is the survival probability of the
measured subspace.  Becker, Datta, and Salzmann formulate the binary projective measurement
`{P, 1-P}` and identify the Zeno survival value with the initial expectation `tr(P rho_0)`;
for a pure state `rho_0 = |psi><psi|`, this is `<psi, P psi>`.  Facchi and Pascazio likewise treat
frequent projection onto a multidimensional Zeno subspace as confinement to that subspace.

Primary sources:

- S. Becker, N. Datta, and R. Salzmann, *Quantum Zeno Effect in Open Quantum Systems*,
  Annales Henri Poincare 22 (2021), 3795--3840,
  https://doi.org/10.1007/s00023-021-01075-8, especially equation (1.1) and the discussion of
  `tr(P rho_0)` as survival probability.
- P. Facchi and S. Pascazio, *Quantum Zeno dynamics: mathematical and physical aspects*,
  Journal of Physics A 41 (2008), 493001, arXiv:0903.3297,
  https://arxiv.org/abs/0903.3297.

## General HTGeometry formalization

`formal/GaloisForLFunctions/HTGeometry/ProjectionMeasurementSurvival.lean` adds:

- `re_inner_starProjection_eq_norm_sq`;
- `norm_starProjection_sub_sq_eq_norm_sq_sub_re_inner`;
- `bornSurvivalProbability_eq_one_sub_projectionDefectSq`;
- `one_sub_le_bornSurvivalProbability_of_projectionDefectSq_le`.

The module is imported by the general `HTGeometry` umbrella.  It applies to arbitrary real or
complex Hilbert spaces and is not specialized to zeta, CCM, Sonin spaces, or any particular
hypertranscendental function.

## Direct RHTower application

`CCMPrimePoleProjectionCoherence.lean` already constructs a unit pole vector whose squared defect
from every projection in a finite local-scale family is bounded by

```text
2 * (2*pi*(delta/L_i))^2.
```

The generic survival theorem now yields, for the same witness and with no new assumption,

```text
1 - 2 * (2*pi*(delta/L_i))^2 <= Re <v, P_i v>.
```

This is formalized for all three existing theorem surfaces:

- `exists_fin_ccmPrimePole_projection_common_born_survival`;
- `exists_fin_ccmPrimePole_projection_cofinal_common_born_survival`;
- `exists_fin_prime_ccmPrimePole_projection_common_born_survival`.

The downstream Calkin-boundary module already turns the cofinal witnesses into a common weakly-null
unit sequence whose projection defects tend to zero.  The same generic identity now gives
simultaneous Born survival tending to one:

- `exists_fin_ccmPrimePole_projection_common_weaklyNull_born_survival_sequence`.

This strengthens the exact boundary sequence used by the finite-sum, positive-combination, and
free-polynomial essential-boundary theorems: the approximate eigenvalue `1` is now also an
operational projective-measurement limit.

The remaining corpus-wide matches do not pass the direct-use gate.  `SoninCalkinNormBound`
controls an operator-norm tail `(1-P)C`, and
`SoninEulerCornerConcrete` uses an unnormalised correction vector; recasting either as a Born
probability would add hypotheses rather than discharge them, so no wrapper was added.

## Research value and limit

The addition upgrades the positive CCM carrier from geometric approximate membership to an
operationally normalized probability statement.  It gives a reusable exact interface for any
future finite Gram or measurement argument that consumes projection expectations rather than
distances.

It does not prove the live aperture sequence, source-column nonvanishing, normalized moment-ratio
convergence, or RH.  It only preserves the existing CCM coherence estimate exactly in a stronger
physics-facing theorem surface.

## Verification boundary

[SOURCE FORMALIZED, NOT CHECKED] No Lean command, build, linter, axiom check, numerical script, or
experimental computation was run.  Promotion to Stage 3 requires a later authorized targeted
check of only the three touched modules; a full build is neither needed nor appropriate.
