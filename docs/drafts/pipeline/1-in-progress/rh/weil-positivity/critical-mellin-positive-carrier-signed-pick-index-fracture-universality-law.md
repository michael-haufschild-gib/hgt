# Critical-Mellin positive-carrier / signed-Pick index-fracture universality law

## Status

`[LEAN PROVED — CORPUS-NOVEL EXACT SYNTHESIS; CLASSICAL GENERAL FRAMEWORK]`

## Lean-derived conjecture

Reading `HTGeometry/MeasureCarrier.lean` against
`RHTower/CCM/CCMRawStieltjesPickKernelIndexInflationUniversalityLaw.lean` exposes a same-source
sign/index fracture.

For every aperture, the finite positive polar part of the critical-Mellin source produces a
positive-semidefinite Cauchy Pick Gram at every finite upper-half-plane node packet.  Once the
actual signed prime-power atoms are restored, selected Pick kernels realize negative-definite
chambers with arbitrarily large finite dimension and maximal Hamming distance from the positive
chamber.

## Corpus inputs

- `GaloisForLFunctions.measure_pick_posSemidef`
- `RHTower.criticalMellinPolarMeasure_isFinite`
- `RHTower.exists_activeCriticalMellinPickKernel_chamber_grade_ge`

## Novelty protocol

No literature search was performed before the exact Lean proof.

Post-proof targeted searches found the classical generalized-Nevanlinna framework in which a
kernel may have a prescribed finite number of negative squares, but no source stating the exact
critical-Mellin prime-power index-inflation theorem or its joint contrast with the same source's
positive polar measure:

- Borogovac, *Inverse of generalized Nevanlinna function that is holomorphic at infinity*,
  arXiv:2001.09366, defines the class `N_kappa` through Pick kernels with `kappa` negative
  squares:
  <https://arxiv.org/abs/2001.09366>
- de Snoo--Winkler--Wojtylak, *Zeros of nonpositive type of generalized Nevanlinna functions with
  one negative square*, arXiv:1011.2081, treats the one-negative-square case:
  <https://arxiv.org/abs/1011.2081>

Verdict: the positive-versus-negative-square paradigm is classical.  Exact same-source
critical-Mellin law, including maximal chamber distance and unbounded finite prime-power index,
is absent from the Lean corpus and was not found in targeted literature.  Novelty claim is
restricted to that arithmetic specialization and joint formulation.

## Lean target

`formal/GaloisForLFunctions/RHTower/CriticalMellinPositiveCarrierSignedPickIndexFractureUniversalityLaw.lean`

## Verification

- scratch proof exact, warning-free:
  `lake env lean /tmp/hgt_law291.lean`
- source proof exact, warning-free:
  `lake env lean GaloisForLFunctions/RHTower/CriticalMellinPositiveCarrierSignedPickIndexFractureUniversalityLaw.lean`
- final module build deferred to terminal audit
