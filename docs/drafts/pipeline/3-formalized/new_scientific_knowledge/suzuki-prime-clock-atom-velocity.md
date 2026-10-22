# Suzuki prime clock-atom velocity

- **ID:** `suzuki-prime-clock-atom-velocity`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) / REFLECTED SOURCE RATIO / DIVISOR-VELOCITY TOMOGRAPHY
- **Scientific status:** `[LEAN-PROVED] [UNCONDITIONAL] [NOVELTY UNVERIFIED]`
  `[NOT AN RH PROOF]`
- **Paper theorem:**
  `../../2-fully-proven/new_scientific_knowledge/suzuki-prime-clock-atom-velocity-transference.md`
- **Lean module:**
  `formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiPrimeClockAtomVelocity.lean`

## Exact result

The module formalizes the algebraic and harmonic-analysis core of the source theorem

```text
dot x_(a,k)^prime
 =sum_m Lambda(m)/(a sqrt(m))
   sin((k+1/2)pi log(m)/a).
```

For the closed-form reflected source ratio

```text
R(Q,M,C,y)=-C [Q/M+M+y+Qy^(-1)]/(Q+1),
```

Lean proves

```text
R(Q,M,C,y^(-1))-R(Q,M,C,y)
 =-C (Q-1)/(Q+1) (y-y^(-1)).                            (1)
```

Dividing by the free-clock pole derivative cancels the same factor `(Q-1)/(Q+1)` exactly. This is
the formal source-step-to-atom-velocity connector, not an abstract assumed velocity interface.

The resulting half-shifted finite phase packet has critical amplitudes

```text
Lambda(m)/(a sqrt(m)).                                   (2)
```

At a nonresonant aperture its Bohr coefficient is `(2)` times the half phase divided by `2i`.
Explicit normalization converges to `ArithmeticFunction.vonMangoldt m` itself. The amplitude is
nonzero exactly when `m` is a prime power.

## Main declarations

```text
suzukiPrimeClockReflectedRatio_sub
suzukiPrimeClockGeometry_cancel
suzukiPrimeClockReflectedRatio_velocity
suzukiFiniteHalfShiftSinePhaseCarrier_eq_sum
tendsto_suzukiFinitePhaseCarrier_external_bohrCoefficient_zero
tendsto_suzukiFiniteHalfShiftSinePhaseCarrier_bohrCoefficient
suzukiPrimeClockHalfPhase_sq
suzukiPrimeClockAtomAmplitude_ne_zero_iff_primePow
tendsto_suzukiPrimeClockAtomVelocity_bohrCoefficient
tendsto_suzukiPrimeClockAtomVelocity_normalized_bohrCoefficient
tendsto_suzukiPrimeClockAtomVelocity_normalized_bohrCoefficient_of_nonresonant
```

## Scope boundary

Suzuki's distributional prime steps and the analytic implicit differentiation of the actual free
clock poles are paper-proved in the parent card. The concrete unbounded Friedrichs operator is not
yet represented in Lean. This module proves the exact evaluated reflected-step quotient,
geometric cancellation, half-clock velocity packet, prime-power support, and coefficient recovery
without adding a source operator axiom.

It does not integrate the velocity to a finite intermediate shift, prove cofinal tightness, or
identify a Xi divisor.

## Verification

```text
lake env lean GaloisForLFunctions/RHTower/Suzuki/SuzukiPrimeClockAtomVelocity.lean
lake build GaloisForLFunctions.RHTower.Suzuki.SuzukiPrimeClockAtomVelocity
lake env lean /tmp/SuzukiPrimeClockAtomAxioms.lean
scripts/formal_tools.py lint
```

passed. Exact module build completed successfully; repository formal lint passed. Every audited
capstone reports only `propext`, `Classical.choice`, and `Quot.sound`.

## Gates

- [x] exact reflected source ratio formalized
- [x] projective clock-geometry cancellation formalized
- [x] half-shifted finite Bohr recovery formalized
- [x] normalized von-Mangoldt recovery formalized
- [x] exact module build/lint/axiom audit
- [ ] concrete unbounded source operator in Lean
- [ ] nonlinear intermediate-shift integration and cofinal tightness
- [ ] Xi divisor identification
- [ ] specialist novelty review
