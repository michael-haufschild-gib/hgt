# Polynomial-magnitude mechanism nonidentifiability universality law

## Status

In progress — paper proof and exact Lean source check complete; literature novelty audit pending.

## Theorem-first provenance

- `HTGeometry/BoundedRelationProfileRealization.lean`
  - `exists_privatePrime_shiftedPolynomial_profile_entire_fullSupport_hypertranscendental`
- `HTGeometry/RoughSubleadingPolynomialMagnitudeHypertranscendence.lean`
  - `ae_forall_phase_hypertranscendental_roughPolynomialPhaseFunction`
  - `tendsto_roughPolynomialProfile_div_purePower`
  - `roughPolynomialFirstDifference_isEquivalent`
  - `roughPolynomialSecondDifference_isEquivalent`
- `HTGeometry/PolynomialPowerDegreeSeparation.lean`
  - `tendsto_natCast_add_rpow_div_rpow`

## Universal law

For every `3 < β` and `1 < α < β - 2`, there is one rational private-prime magnitude sequence
whose value, first forward difference, and second forward difference are asymptotically equivalent
to those of almost every rough sequence `n^β + uₙ n^α`, `uₙ ∈ [1,2]`.

The rational sequence gives an entire, full-support, hypertranscendental exponential function for
every algebraic unit-modulus complex phase.  Almost every rough sequence gives a
hypertranscendental exponential function for every real phase.  Thus a polynomial magnitude's
asymptotic two-jet cannot identify whether private-prime bounded-relation confinement or
probabilistic logarithmic shift-separation is responsible for phase-uniform hypertranscendence.

## Paper proof

Take the scale-one private-prime realization of the shifted profile `(n+1)^β`.  Its value and first
two forward differences are asymptotic to the corresponding shifted pure-power models.  A unit
shift is asymptotically invisible in every real power, so these models are equivalent to
`n^β`, `β n^(β-1)`, and `β(β-1)n^(β-2)`.

For almost every product-measure parameter sequence, all coordinates lie in `[1,2]` and every real
phase is hypertranscendental.  The rough subleading term is lower order at value level; because
`α < β-2`, it is lower order after both first and second forward differences.  Transitivity and
symmetry of asymptotic equivalence therefore identify all three jets while preserving the distinct
phase theorems of the two mechanisms.

## Lean status

Source complete in
`formal/GaloisForLFunctions/HTGeometry/PolynomialMagnitudeMechanismNonidentifiabilityUniversalityLaw.lean`.

Exact source check passed with
`lake env lean GaloisForLFunctions/HTGeometry/PolynomialMagnitudeMechanismNonidentifiabilityUniversalityLaw.lean`.

## Novelty status

Pending post-discovery literature audit. Discovery used Lean statements only. Corpus search found
the deterministic private-prime two-jet theorem and the almost-everywhere rough two-jet theorem on
separate surfaces, but no direct asymptotic two-jet equivalence joining their incompatible
hypertranscendence mechanisms.
