# Exponential, logistic, and tanh observations preserve hypertranscendence

- **ID:** `exponential-sigmoidal-observation-hypertranscendence`
- **Status:** FORMALISED IN LEAN 4
- **Type:** differential-algebraic observability theorem / physics--ML--genomics bridge
- **Lean:** `formal/GaloisForLFunctions/HTGeometry/ExponentialObservationHypertranscendence.lean`
- **Scientific novelty:** not claimed; corpus value is the exact forward transfer interface

## Source relation

Let `source` and `phase` be elements of a differential field extension and suppose

\[
  \frac{\mathrm d\,phase}{phase}=\mathrm d\,source.
\]

This characterizes an exponential phase up to a nonzero differential constant without choosing a
logarithm or an analytic branch.  If `phase` were differentially algebraic, then its logarithmic
derivative would be differentially algebraic.  Every derivative of an HT source is HT, so the
displayed equality forces `phase` to remain HT.

Nonzero differentially algebraic gains and differentially algebraic offsets preserve HT exactly.
More generally, if an observation rationally recovers an HT source by a fractional-linear formula
with base-field coefficients, the observation is HT: a hypothetical DA observation would make the
recovered source DA by field closure.

Parent differential algebra: R. Ait El Manssour, A.-L. Sattelberger, and B. Teguia Tabuguia,
[*D-Algebraic Functions*](https://arxiv.org/abs/2301.02512), Journal of Symbolic Computation 125
(2025), gives constructive closure algorithms for arithmetic operations and compositions of
D-algebraic functions.

## Exact Lean theorem family

The module proves:

- `hypertranscendentalOver_deriv`;
- `hypertranscendentalOver_add_differentialAlgebraic_iff`;
- `hypertranscendentalOver_mul_differentialAlgebraic_iff`;
- `hypertranscendentalOver_phase_of_logDeriv_eq_deriv`;
- `hypertranscendentalOver_exponentialAffineObservable`;
- `hypertranscendentalOver_fractionalLinearObservable_of_recovery`.

The last theorem takes the recovery identity as its nondegeneracy certificate, avoiding any false
claim that arbitrary outer composition preserves hypertranscendence.

## Direct ML and genomic application

The logistic and tanh sensors are fractional-linear observations of an exponential phase:

\[
  \operatorname{logistic}=\frac{E}{1+E},\qquad
  \tanh=\frac{E-1}{E+1}.
\]

Away from their displayed poles they rationally recover `E`, so Lean proves both the phase-level
and source-to-output transfer laws:

- `hypertranscendentalOver_logisticPhase`;
- `hypertranscendentalOver_tanhPhase`;
- `hypertranscendentalOver_logisticObservable_of_logDeriv_eq_deriv`;
- `hypertranscendentalOver_tanhObservable_of_logDeriv_eq_deriv`.

This directly complements `PolynomialFirstOrderActivationBoundary.lean`.  The older theorem says
an HT logistic/tanh output cannot be generated from a DA input.  The new theorem proves the missing
forward statement: an HT latent clock cannot be hidden by the exact logistic or tanh sensor.

This matters for neural gates, observable neural ODEs, and gene-regulatory reporters.  Current
applications explicitly use observability to reconstruct latent continuous-time states in neural
ODEs (Wendland--Freitag--Kschischo,
[*Observable Neural ODEs for Identifiable Causal Forecasting in Continuous Time*](https://arxiv.org/abs/2604.26070))
and product-of-logistics response laws for Boolean-derived gene networks (Belgacem,
[*Logistic Gene Regulatory Networks: A Modelling Framework Beyond Hill Functions*](https://arxiv.org/abs/2606.11028)).
Those papers motivate the sensor classes; the HT transfer theorem is the exact corpus interface.

## Physics applications

The same theorem applies to exponential-affine channels in eikonal scattering, Wilson-line
readouts, interferometric phase clocks, cosmological oscillatory clocks, and the higher-multipole
Schwarzschild Love response.  The black-hole application is formalized in
`BlackHoleDressedLogSpectralClock.lean`.

## No-go and significant positive replacement

**No-go.** An arbitrary nonlinear sensor need not preserve HT; a constant or collapsing map can
erase it.  A first-order activation identity by itself only gives source extraction from an HT
output, not forward preservation from an HT input.

**Positive theorem.** Exponential logarithmic phases, nondegenerate affine gains, and rationally
recoverable fractional-linear sensors do preserve HT.  Logistic and tanh clocks therefore carry
the latent infinite differential source all the way to the observed value.

## RH pressure test

This does not produce the missing RH sign.  It strengthens the source-transport side of the corpus:
once an RH-relevant clock/source is proved HT, any exact exponential, sigmoid, tanh, or recoverable
Möbius readout can now inherit that status without a new hypertranscendence proof.  It discharges
sensor-preservation hypotheses, but does not orient zeros or create a positive Euler-prime source.

## Verification

- exact target: `lake build +GaloisForLFunctions.HTGeometry.ExponentialObservationHypertranscendence`
- direct file check: `lake env lean GaloisForLFunctions/HTGeometry/ExponentialObservationHypertranscendence.lean`
- dependent black-hole check: `lake env lean GaloisForLFunctions/HTGeometry/BlackHoleDressedLogSpectralClock.lean`
- no numerical computation and no full build
