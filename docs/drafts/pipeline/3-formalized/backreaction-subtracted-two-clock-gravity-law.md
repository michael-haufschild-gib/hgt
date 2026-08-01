# Backreaction-subtracted two-clock gravity law

- **ID:** `backreaction-subtracted-two-clock-gravity-law`
- **Stage:** 3-formalized
- **Paper proof:**
  `../2-fully-proven/new_scientific_knowledge/other/backreaction-subtracted-two-clock-gravity-law.md`
- **Lean modules:**
  `formal/GaloisForLFunctions/HTGeometry/ClockPropagatorSelfCalibration.lean`,
  `formal/GaloisForLFunctions/HTGeometry/ClockPrincipalSymbolCalibration.lean`,
  `formal/GaloisForLFunctions/HTGeometry/ClockLocalityDistributionKernel.lean`
- **Status:** complete unconditional mathematical operator/reconstruction chain; physical
  acquisition and nonlinear apparatus control remain realization obligations.

## Formalized theorem chain

For arbitrary elements of a noncommutative ring, Lean defines the probe Schur complement

\[
  K=Q-SGR
\]

and verifies all eight block equations showing

\[
  \begin{pmatrix}P&R\\S&Q\end{pmatrix}^{-1}
  =
  \begin{pmatrix}
    G+GRHSG&-GRH\\
    -HSG&H
  \end{pmatrix}
\]

from only

\[
  PG=GP=1,\qquad KH=HK=1.
\]

It then proves the exact endpoint-dressed inverse contrast

\[
\begin{aligned}
  &B^{-1}QA^{-1}
  -B^{-1}(Q-SGR)A^{-1}\\
  &\qquad=(B^{-1}S)G(RA^{-1}).
\end{aligned}
\]

Thus the coupling-off/coupling-on subtraction is exactly an endpoint-dressed hidden Green
element. Existing unconditional theorems in the same Lean module prove that two distinct central
mass shifts cancel the common geometric operator, reconstruct endpoint calibration, recover the
metric principal symbol, polarize the complete continuum inverse-metric field, and identify an
arbitrary nonlinear gravity operator from equality of its complete source/observation graph.

Lean now also proves the missing composition bridge: if the hidden Green element and effective
left/right dressings have two-sided inverses, the inverse of the backreaction-subtracted contrast
is exactly

\[
  V^{-1}P_\mu U^{-1}
\]

on both sides. No inverse is selected by metadata or assumed through a one-sided law.

The local differential-operator module then proves coefficient-by-coefficient that two masses
cancel all first- and second-order terms, reconstruct endpoint calibration, and recover the
undressed quadratic principal symbol. The distribution module identifies the corresponding
residual kernel fibers as scalar Dirac deltas with diagonal support. Existing continuum
polarization reconstructs the full symmetric bilinear form rather than only diagonal values.

## Lean declarations

- `probeSchurComplement`
- `targetSchurInverseBlock`
- `targetToProbeInverseBlock`
- `probeToTargetInverseBlock`
- `TwoChannelInverseLaws`
- `twoChannel_schurInverseLaws`
- `backreactionSubtractedHiddenGreen`
- `backreactionSubtractedHiddenGreen_eq_endpointDressedGreen`
- `backreactionSubtractedHiddenGreen_inverse_isTwoSided`
- `measuredClockInverse_difference`
- `endpointCalibrationProduct_reconstruction`
- `twoMassMetricSymbol_reconstruction`
- `ScalarSecondOrderOperator.measuredClockInverseOperator_difference`
- `ScalarSecondOrderOperator.principalSymbol_measuredClockInverseOperator`
- `ScalarSecondOrderOperator.twoMassPrincipalSymbol_reconstruction`
- `twoMassClockLocalityKernel`
- `dsupport_twoMassClockLocalityKernel_subset`
- `SelfCalibratingMetricField.twoMassObservation_injective`
- `twoMassSelfCalibratingContinuumGravityRigidity`

## Axiom and lint status

The target module compiles with

```text
lake env lean GaloisForLFunctions/HTGeometry/ClockPropagatorSelfCalibration.lean
```

Both added dependency modules also pass direct `lake env lean <file>` checks, and
`lake build GaloisForLFunctions.HTGeometry.ClockPropagatorSelfCalibration` passes.

No `sorry`, `admit`, declared `axiom`, `opaque`, or `unsafe` declaration occurs in the target.
The new theorem chain uses only standard Lean quotient/extensionality infrastructure reported by
`#print axioms`.

## Exact boundary

Lean proves noncommutative algebra and continuum injectivity. It does not manufacture:

1. a globally hyperbolic spacetime or Green-hyperbolic PDE;
2. compact local probe couplings;
3. complete experimental response data;
4. gauge-invariant conserved source completeness;
5. nonlinear gravitational backreaction control.

Those remain physical and analytic obligations. The block algebra is explicitly not claimed new;
candidate novelty lies in its operational composition with two-mass self-calibration and
continuum gravity rigidity.
