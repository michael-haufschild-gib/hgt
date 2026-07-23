# Anchored Calkin FE--Schwarz orbit universality law

## Status

`[LEAN PROVED — LITERATURE AUDITED] [CANDIDATE NEW SCIENTIFIC KNOWLEDGE]`

## Theorem-generated discovery

Two terminal modules expose complementary halves of one operator law:

- `AnchoredCalkinCriticalLineUniversalityLaw` identifies critical-line location with cofinal
  essential-norm decay, compactness of every anchored two-prime commutator, and prime-two Hurwitz
  seam vanishing;
- `XiPrimeSeamEulerOrientationReflection` transports every finite prime-packet commutator through
  the full functional-equation/Schwarz orbit by exact negation and Hilbert adjoint.

The anchored criterion had not been specialized through the reflection table, and the reflection
module did not identify its common compact zero fibre.

## Universal law

For every open-strip point `rho`, positive source scale `a`, and rational prime partner `q`, the
anchored commutator `T_q` obeys

```text
T_q(1-conj rho) = -T_q(rho),
T_q(conj rho)   = -T_q(rho)^*,
T_q(1-rho)      =  T_q(rho)^*.
```

Moreover, all three anchored diagnostics are invariant under each of the three orbit moves:

- cofinal charge-scaled essential-norm decay;
- compactness of every anchored partner-prime commutator;
- vanishing of the calibrated prime-two Hurwitz boundary seam.

Their common orbitwise zero fibre is exactly `Re rho = 1/2`.

## Corpus inputs

- `RHTower.anchoredCalkin_criticalLineUniversality`
- `RHTower.orbitwiseFinitePrimeEulerCompressionCommutator_lineReflect`
- `RHTower.adjoint_orbitwiseFinitePrimeEulerCompressionCommutator`
- `RHTower.orbitwiseFinitePrimeEulerCompressionCommutator_one_sub`
- `RHTower.firstPrimeAnchoredPacket_prime`

## Novelty protocol

No literature search was performed before exact Lean proof passed.

Post-proof searches covered Calkin and essential-norm formulations of RH, compact commutators,
Euler/Hurwitz operator models, FE--Schwarz reflection, and critical-line criteria.

Nearest sources:

- Connes, *Trace formula in noncommutative geometry and the zeros of the Riemann zeta function*,
  arXiv:math/9811068, gives an adelic noncommutative trace-formula interpretation of zeta zeros:
  <https://arxiv.org/abs/math/9811068>
- Connes--Consani, *The Scaling Hamiltonian*, arXiv:1910.14368, develops quantized differentials
  as operator commutators in the scaling-site framework:
  <https://arxiv.org/abs/1910.14368>
- Nakamura, *Functional equation and zeros on the critical line of the quadrilateral zeta
  function*, arXiv:1910.09837, combines Hurwitz/periodic zeta functions with a Riemann-type
  functional equation:
  <https://arxiv.org/abs/1910.09837>
- Sahay, *Moments of the Hurwitz zeta function on the critical line*, arXiv:2103.13542, studies
  rational-shift Hurwitz moments and their Dirichlet-L decompositions:
  <https://arxiv.org/abs/2103.13542>

No source found the exact anchored law: prime-pair Euler compression commutators transported by
the full FE--Schwarz adjoint/negation table, with cofinal essential-norm decay, all-partner
compactness, and calibrated prime-two Hurwitz seam vanishing sharing one orbit-invariant zero fibre
`Re rho = 1/2`. Novelty claim is restricted to this formal statement.

## Lean target

`formal/GaloisForLFunctions/RHTower/AnchoredCalkinFESchwarzOrbitUniversalityLaw.lean`

## Verification

- exact and warning-free:
  `lake env lean GaloisForLFunctions/RHTower/AnchoredCalkinFESchwarzOrbitUniversalityLaw.lean`
- imported by `formal/GaloisForLFunctions/RHTower.lean`
- final module, axiom, and lint audits deferred to terminal pass
