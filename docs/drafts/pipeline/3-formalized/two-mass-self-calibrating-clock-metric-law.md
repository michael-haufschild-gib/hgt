# Two-mass self-calibrating clock metric law

- **ID:** `two-mass-self-calibrating-clock-metric-law`
- **Stage:** 3-formalized
- **Type:** THEOREM / CONTINUUM GRAVITY / CLOCKS / INVERSE PROPAGATORS / CALIBRATION
- **Paper proof:**
  `../2-fully-proven/new_scientific_knowledge/two-mass-self-calibrating-clock-metric-law.md`
- **Lean:** `formal/GaloisForLFunctions/HTGeometry/ClockPropagatorSelfCalibration.lean`
- **Status:** unconditional operator-algebra and pointwise metric-symbol core.

## Formalized theorem

For an arbitrary noncommutative ring, Lean proves that a two-sided Green inverse remains
two-sided after unknown invertible source and receiver dressing, with the inverse gains appearing
in reverse order.

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

## Exact boundary

Lean does not encode:

1. distributional retarded/advanced support domains;
2. reconstruction of complete dressed Green operators from laboratory clock outcomes;
3. the differential-operator principal-symbol theorem;
4. proof that endpoint gains are species-independent;
5. gauge, diffeomorphism, or backreaction control.

