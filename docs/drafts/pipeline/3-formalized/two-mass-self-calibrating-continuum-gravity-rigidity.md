# Two-mass self-calibrating continuum gravity rigidity

- **ID:** `two-mass-self-calibrating-continuum-gravity-rigidity`
- **Stage:** 3-formalized
- **Type:** THEOREM / CONTINUUM GRAVITY / CLOCKS / OPERATOR IDENTIFICATION
- **Paper proof:**
  `../2-fully-proven/new_scientific_knowledge/other/two-mass-self-calibrating-continuum-gravity-rigidity.md`
- **Lean:** `formal/GaloisForLFunctions/HTGeometry/ClockPropagatorSelfCalibration.lean`
- **Status:** unconditional coordinate-trivialized continuum core.

## Formalized theorem

Lean defines a continuum field consisting of:

- an arbitrary event-indexed nonzero real calibration;
- an event-indexed symmetric bilinear form on a real model covector fiber.

For distinct squared masses \(\mu_1\neq\mu_2\), its complete observation is

\[
\begin{aligned}
  D(x)&=(\mu_1-\mu_2)\kappa(x),\\
  S(x,\xi)&=\kappa(x)g_x^{-1}(\xi,\xi).
\end{aligned}
\]

Lean proves this observation map injective. The first channel recovers calibration; nonzero
calibration recovers every diagonal metric-symbol value; polarization recovers the full bilinear
form.

For any source type and arbitrary nonlinear laws \(\mathcal E_1,\mathcal E_2\), Lean then proves

\[
  \{(\mathcal E_1(g),D_g,S_g):g\}
  =
  \{(\mathcal E_2(g),D_g,S_g):g\}
  \quad\Longleftrightarrow\quad
  \mathcal E_1=\mathcal E_2.
\]

This graph theorem preserves multiple solution branches and assumes no linearity, analyticity,
perturbative expansion, or unique source-to-solution map.

## Unconditional declarations

- `SelfCalibratingMetricField`
- `SelfCalibratingMetricField.form_eq_half_calibratedSymbol_polarization`
- `SelfCalibratingMetricField.twoMassObservation`
- `SelfCalibratingMetricField.twoMassObservation_injective`
- `selfCalibratingGravityGraph`
- `twoMassSelfCalibratingContinuumGravityRigidity`

## Exact boundary

The observation channels are ideal complete principal-symbol data. Still open are their
reconstruction from finite clock experiments, Lorentzian support analysis, smooth bundle descent,
diffeomorphism/gauge quotient, species-independent physical calibration, and backreacting active
source controllability.
