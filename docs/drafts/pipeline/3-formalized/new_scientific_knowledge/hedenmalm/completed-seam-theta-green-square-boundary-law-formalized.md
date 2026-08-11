# Formalization certificate: completed-seam theta Green-square boundary law

- **ID:** `completed-seam-theta-green-square-boundary-law-formalized`
- **Stage:** 3-formalized
- **Paper/open card:** `../../../1-in-progress/completed-seam-theta-green-square-boundary-law.md`
- **Scientific status:** `[FORMALIZED CROSS-ROUTE LAW] [FORMALIZED PRODUCER NO-GO] [RH OPEN]`

## Lean modules

```text
formal/GaloisForLFunctions/RHTower/HedenmalmThetaGreenSquareBoundaryLaw.lean
formal/GaloisForLFunctions/RHTower/HedenmalmThetaGreenReflectionPairNoGo.lean
```

Both modules are imported by `formal/GaloisForLFunctions/RHTower.lean`.

## Closed theorem chain

Namespace `RHTower.HedenmalmThetaSource`.

| Statement | Lean declaration |
|---|---|
| every nonzero spectral value of the source inverse has positive real square iff RH | `thetaSquaredSeamSpectrumPositive_iff_riemannHypothesis` |
| individual Green-boundary neutrality iff RH | `thetaGreenBoundaryNeutral_iff_riemannHypothesis` |
| squared spectral positivity iff individual boundary neutrality | `thetaSquaredSeamSpectrumPositive_iff_greenBoundaryNeutral` |
| squared spectral positivity iff compact Markov endpoint | `thetaSquaredSeamSpectrumPositive_iff_compactMarkov` |
| squared spectral positivity iff compact Thorin endpoint | `thetaSquaredSeamSpectrumPositive_iff_compactThorin` |
| Green-square decomposition `G B^2=B^* G B+i R_2 B` | `thetaMetric_greenSquare_boundary_decomposition` |
| correction range lies in pinned affine boundary space | `range_pinnedBoundary_mul_thetaKernel_le_affineSubspace` |
| theta root energy is invariant under functional-equation reflection | `thetaXiRootEnergy_reflect` |
| boundary current is reflection-odd | `thetaXiRankTwoBoundaryFlux_reflect` |
| unsquared theta eigenvalue is reflection-odd; its square is reflection-invariant | `thetaXiReciprocalEigenvalue_reflect`, `thetaXiReciprocalEigenvalue_sq_reflect` |
| reflected-pair current cancels unconditionally | `thetaGreenReflectedPairNeutral_unconditional` |
| one folded `B²` node contains both reflected eigenmodes and zero aggregate current | `thetaGreenSquaredReflectionFiber_sameNode_zeroCurrent` |
| automatic pair neutrality plus individual neutrality is still exactly RH | `thetaGreenReflectedPairNeutral_and_fiberNeutral_iff_riemannHypothesis` |

## New obstruction law

Functional-equation reflection supplies the opposite boundary current automatically:

```text
F(q#) = -F(q),
F(q) + F(q#) = 0.
```

Thus reflected direct sums, paired traces, and supertraces can be boundary-neutral without proving
anything about RH.  A valid Route P producer must equalize incoming/outgoing intensities inside
each multiplicity-exact fibre; cancellation only after a reflected orbit is aggregated is
formally excluded.

The stronger square-fold theorem places both opposite-current vectors over the same `B²`
eigenvalue.  Therefore even zero boundary trace block by block on the folded Route P spectrum is
unconditional.  Positivity must be certified on the oriented `B` double cover before the
reflection quotient is taken.

## Verification

```text
lake env lean GaloisForLFunctions/RHTower/HedenmalmThetaGreenSquareBoundaryLaw.lean
lake build GaloisForLFunctions.RHTower.HedenmalmThetaGreenSquareBoundaryLaw
lake env lean GaloisForLFunctions/RHTower/HedenmalmThetaGreenReflectionPairNoGo.lean
lake build GaloisForLFunctions.RHTower.HedenmalmThetaGreenReflectionPairNoGo
```

All four commands pass.  `/tmp` `#print axioms` audits for every declaration above report only
`propext`, `Classical.choice`, and `Quot.sound`.

Whole-umbrella compilation is presently blocked earlier by an unrelated missing object file for
`DeningerExponentGammaSixShellTransportRigidity`; global formal lint is presently blocked only by
unrelated unreachable modules.  Neither gate reports this module or its import.
