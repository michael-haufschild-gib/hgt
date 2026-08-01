# Two-mass self-calibrating clock metric law

- **ID:** `two-mass-self-calibrating-clock-metric-law`
- **Stage:** 3-formalized
- **Type:** THEOREM / CONTINUUM GRAVITY / CLOCKS / INVERSE PROPAGATORS / CALIBRATION
- **Paper proof:**
  `../2-fully-proven/new_scientific_knowledge/other/two-mass-self-calibrating-clock-metric-law.md`
- **Lean modules:**
  `formal/GaloisForLFunctions/HTGeometry/ClockPropagatorSelfCalibration.lean`,
  `formal/GaloisForLFunctions/HTGeometry/ClockPrincipalSymbolCalibration.lean`
- **Status:** unconditional noncommutative inverse algebra and exact local second-order
  principal-symbol reconstruction.

## Formalized theorem

For an arbitrary noncommutative ring, Lean proves that a two-sided Green inverse remains
two-sided after unknown invertible source and receiver dressing, with the inverse gains appearing
in reverse order.

Lean also defines exact value/first/ordered-second jets and a local scalar differential operator
of order at most two. For arbitrary derivations it proves that jet multiplication is the literal
iterated Leibniz rule. It then derives every coefficient of

\[
  B^{-1}P_\mu A^{-1}.
\]

Derivatives of the right gain occur only in zeroth- and first-order coefficients. The order-two
coefficient is exactly multiplied by \(b^{-1}a^{-1}\). Thus the principal-symbol statement is no
longer represented by an unconstrained scalar datum.

For an arbitrary field \(K\), ring \(A\), and \(K\)-algebra structure on \(A\), define

\[
  Q_\mu=B^{-1}(P_0+\mu I)A^{-1}.
\]

Lean proves

\[
  Q_{\mu_1}-Q_{\mu_2}
  =
  \operatorname{alg}(\mu_1-\mu_2)(B^{-1}A^{-1})
\]

without commuting \(P_0\) through either gain. For \(\mu_1\neq\mu_2\), multiplication by the
inverse scalar mass difference reconstructs \(B^{-1}A^{-1}\) exactly.

At a point, if

\[
  D=(\mu_1-\mu_2)\kappa,\qquad S=\kappa q
\]

with \(\kappa\neq0\), Lean proves

\[
  \kappa=\frac{D}{\mu_1-\mu_2},
  \qquad
  q=\frac{(\mu_1-\mu_2)S}{D},
\]

and proves injectivity of the joint calibration/metric-symbol data.

At differential-operator level, Lean proves the stronger structure equality

\[
  Q_{\mu_1}-Q_{\mu_2}
  =M_{(\mu_1-\mu_2)b^{-1}a^{-1}},
\]

so every first- and second-order coefficient cancels. It proves the corresponding equality on
every input jet, the exact quadratic-symbol scaling law, mass invariance of the principal symbol,
and division by nonzero endpoint values and mass difference to recover the undressed symbol.

## Unconditional declarations

- `endpointDressedGreen`
- `endpointDressedInverse`
- `endpointDressedInverse_isTwoSided`
- `measuredClockInverse`
- `measuredClockInverse_difference`
- `endpointCalibrationProduct_reconstruction`
- `twoMassCalibrationMetricData`
- `twoMassCalibration_reconstruction`
- `twoMassMetricSymbol_reconstruction`
- `twoMassCalibrationMetricData_injective`
- `ScalarTwoJet.mul`
- `ScalarTwoJet.ofFunction`
- `ScalarTwoJet.ofFunction_mul`
- `ScalarSecondOrderOperator.evalJet`
- `ScalarSecondOrderOperator.rightMultiply`
- `ScalarSecondOrderOperator.evalJet_rightMultiply`
- `ScalarSecondOrderOperator.evalJet_rightMultiply_ofFunction`
- `ScalarSecondOrderOperator.dress`
- `ScalarSecondOrderOperator.principalSymbol`
- `ScalarSecondOrderOperator.principalSymbol_dress`
- `ScalarSecondOrderOperator.massShift`
- `ScalarSecondOrderOperator.measuredClockInverseOperator`
- `ScalarSecondOrderOperator.measuredClockInverseOperator_difference`
- `ScalarSecondOrderOperator.evalJet_measuredClockInverseOperator_difference`
- `ScalarSecondOrderOperator.principalSymbol_measuredClockInverseOperator`
- `ScalarSecondOrderOperator.twoMassPrincipalSymbol_reconstruction`

## Exact boundary

Lean does not encode:

1. distributional retarded/advanced support domains;
2. reconstruction of complete dressed Green operators from laboratory clock outcomes;
3. proof that endpoint gains are species-independent;
4. gauge, diffeomorphism, or backreaction control.

These are analytic or physical realization obligations. Differential-operator coefficient
calculus, mass cancellation, principal-symbol scaling, and symbol reconstruction are closed.

## Verification

- Both Lean source files pass `lake env lean <file>`.
- `lake build GaloisForLFunctions.HTGeometry.ClockPropagatorSelfCalibration` passes, including the
  new principal-symbol dependency.
- `#print axioms` on the exact theorem chain reports only `propext`, `Classical.choice`, and
  `Quot.sound`.
- Both modules are reachable from `formal/GaloisForLFunctions/HTGeometry.lean`.
