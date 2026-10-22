# LAW473 — Deninger entropy-production thermodynamic-limit universality

## Status

- Pipeline stage: 3 — formalized
- Conjecture label: `LAW473`
- Discovery mode: theorem-generated corpus closure
- Mathematical computations used: none
- Novelty status: `[NOVELTY UNVERIFIED]`

## Corpus parents

1. `DeningerLefschetzTrace.deningerResolventLefschetzTrace`
   identifies the multiplicity-exact centered Deninger divisor resolvent with the
   continued prime--archimedean relative source trace at each Xi-explicit-admissible point.
2. `PrimeArchEntropyProductionResponseRH.
   continuedPrimeArchUpperAntiHerglotz_of_finiteKMSEntropyProductionResponse_tendsto`
   closes the anti-Herglotz sign under pointwise thermodynamic limits of finite Hermitian
   KMS entropy-production responses.
3. `PrimeArchEntropyProductionResponseRH.
   continuedPrimeArchUpperCauchyDiagonalNonnegative_of_finiteKMSEntropyProductionResponse_tendsto`
   transports the same limit into the one-Cauchy gate.
4. `PrimeArchEntropyProductionResponseRH.
   riemannHypothesis_of_finiteKMSEntropyProductionResponse_tendsto`
   closes that source passivity condition to RH.
5. `DeningerCohomologicalResolventPassivityUniversalityLaw.
   deningerDivisorUpperAntiHerglotz_iff_continuedPrimeArchUpperAntiHerglotz`
   transfers source passivity back to cohomological resolvent passivity.

## Universal law

Let finite-dimensional Hermitian KMS systems have freely varying dimensions, inverse
temperatures, energy spectra, and amplitudes. If their entropy-production passive responses
converge pointwise on every regular point of the centered upper half-strip directly to the
Deninger divisor relative resolvent trace, then all of the following hold simultaneously:

1. the same responses converge to the continued prime--archimedean relative source trace;
2. the arithmetic source is anti-Herglotz;
3. the Deninger cohomological resolvent is anti-Herglotz;
4. the continued source satisfies the one-Cauchy diagonal nonnegativity gate;
5. the Riemann hypothesis holds.

No sign restriction on inverse temperature is required: entropy-production intensity already
contains the temperature factor and remains nonnegative by Hermitian KMS symmetry.

## Dependency-closed paper proof

Fix a regular centered upper-half-strip point `z`. Its strip inequalities and zeta nonvanishing
make it Xi-explicit-admissible. The Deninger Lefschetz identity therefore gives

`deningerDivisorRelativeResolventTrace z =
  continuedPrimeArchSourceRelativeTrace z`.

Substitution into the assumed pointwise convergence changes only the named limit, proving
convergence to the continued source at every admissible `z`.

For each finite KMS system, Hermitian symmetry makes every entropy-production transition
intensity nonnegative. The imaginary part of its passive response is consequently nonpositive
in the upper half-plane. Continuity of `Complex.im` and closedness of `(-∞, 0]` preserve this
sign in the pointwise limit, so the continued source is anti-Herglotz. The established
anti-Herglotz/one-Cauchy equivalence yields diagonal nonnegativity, and the established
prime--archimedean passivity criterion yields RH. Finally the Deninger/source Lefschetz identity
transports source anti-Herglotz passivity back to the divisor resolvent.

Every step is a theorem already present in the corpus plus equality substitution and closure of
a closed half-line under limits. No unproved analytic interchange, spectral construction, or
numerical evidence is used.

## Strength boundary

This is a sufficient thermodynamic-realization law, not an equivalence. RH alone does not
construct a sequence of finite Hermitian KMS systems converging to the Deninger divisor
resolvent. Claiming the converse would add a missing realization theorem.

## Lean target

File:
`formal/GaloisForLFunctions/RHTower/Deninger/DeningerEntropyProductionThermodynamicLimitUniversalityLaw.lean`

Planned declarations:

- `finiteKMSEntropyProductionResponse_tendsto_continuedPrimeArch_of_tendsto_deninger`
- `deninger_entropyProductionThermodynamicLimitUniversality`

## Verification log

- Paper proof: dependency-closed
- Lean exact check: passed in source-expanded scratch with
  `lake env lean /private/tmp/law472_scratch.lean`
- Direct file exact check: blocked before elaboration by absent cached
  `DeningerCohomologicalResolventPassivityUniversalityLaw.olean`; deferred to final targeted build
- Axiom audit: pending final audit
- Final targeted module build: pending final audit
- Umbrella wiring: complete in `GaloisForLFunctions/RHTower.lean`

## Novelty audit

Primary-source searches were run only after paper proof and Lean elaboration. Nearby literature
contains Deninger-style flow/Lefschetz programs, noncommutative trace-formula approaches to zeta
zeros, scaling-Hamiltonian/Weil-positivity frameworks, and general KMS entropy-production theory:

- https://arxiv.org/abs/math/0603576
- https://arxiv.org/abs/math/9811068
- https://arxiv.org/abs/1910.14368
- https://arxiv.org/abs/1710.09747

No located source states the exact theorem: arbitrary-temperature finite Hermitian KMS
entropy-production responses converging to a multiplicity-exact Deninger divisor resolvent force
the continued prime--Gamma source limit, both passivity formulations, the one-Cauchy gate, and RH.
Search coverage cannot prove absence from all literature, so status remains
`[NOVELTY UNVERIFIED]`.
