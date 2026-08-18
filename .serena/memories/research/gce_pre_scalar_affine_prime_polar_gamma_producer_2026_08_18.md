# G-CE pre-scalar affine prime–polar–Gamma producer (2026-08-18)

Constructed and formally closed the source-native affine producer requested at the G-CE frontier.

## Exact object

Charge Hilbert space:
`WithLp 2 (ℂ × EulerPositiveL2)`.

For `sigma > 1`, `u ≥ 0`, define archimedean coordinate
`Z = -2 * eulerPositivePreScalarGraphDenominator sigma u * logDeriv archFactor (eulerPositiveCriticalBoundaryParameter sigma u)`.
The charge is
`Q = (I/2) • WithLp.toLp 2 (conj Z, eulerPositivePreScalarGammaSource sigma hsigma)`.
The probe is
`R = WithLp.toLp 2 (1, eulerPositiveCriticalDampedStateLp sigma u hsigma hu)`.
Exact identity:
`inner ℂ Q R = eulerPositivePreScalarGammaXiNumerator sigma u hsigma hu`.

Affine producer:
`A(x) = (Q, mobiusClockSoninMarkedProducer ... x)`.
Charge port is exactly `Q`; odd port is exactly one half of
`soninCofinalComplexClockCommutator ... x`.
Joint readout is exactly completed division-free prime–polar–Gamma numerator plus Fisher pairing with the commutator.

## New closure

Proved `eulerPositivePreScalarGammaSource sigma hsigma ≠ 0` by evaluating at positive integer 2:
`(sigma-1) * (2 log 2) * stateWeight`, with all factors nonzero.
Hence charge and every zero-clock affine packet are nonzero. At zero clock odd jet vanishes exactly while charge remains.
Premise-free capstone:
`canonicalMobiusGammaXiPreScalarAffineProducer_closed`.

## Files

- `formal/GaloisForLFunctions/RHTower/MobiusGammaXiPreScalarAffinePrimePolarGammaProducer.lean`
- wired into `formal/GaloisForLFunctions/RHTower.lean`
- research card:
  `docs/drafts/pipeline/3-formalized/new_scientific_knowledge/ccm/g-ce-pre-scalar-affine-prime-polar-gamma-producer.md`

Target-only `lake build GaloisForLFunctions.RHTower.MobiusGammaXiPreScalarAffinePrimePolarGammaProducer` passed. All theorem axiom audits report only `propext`, `Classical.choice`, `Quot.sound`. No forbidden declarations.

## Scientific boundary

This closes existence of a lawful pre-scalar affine charge-plus-commutator carrier. It does NOT cancel exact G-CE debt or prove RH. Next RH-bearing frontier: coefficient-faithful boundary renormalization/comparison of normalized zero-mode readout with transported escaped coefficient `d`, including the required 4-unit/nonexpansive control. Do not rediscover this carrier or confuse the exact port law with a nonvanishing theorem for the positive-clock commutator.