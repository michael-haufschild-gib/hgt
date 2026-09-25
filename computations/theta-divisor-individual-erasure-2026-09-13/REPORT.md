# Theta-source divisor experiment report

These are numerical experiments on declared deformations of the literal theta source, not zeta counterexamples and not HB physical calculations. Let Phi(x)=sum(n>=1) exp(x/2)(4q_n^2-6q_n)exp(-q_n), q_n=pi*n^2*exp(2x). Delete an imaginary node ia using P(x)=1+x^2/a^2, or an off-axis symmetry quartet using P_z(x)=(1-x^2/z^2)(1-x^2/conj(z)^2). The transform studied is the Fourier integral of Phi/P, divided by its mass. Source-node inputs have independent100/160-digit numerical checks, not interval certificates. The13-node list is not complete.

Whole-family wall time: 53.844s. 18 / 18 saved worker tasks completed. Exact environment, source provenance, parameters, executable code and raw failures are retained. Original remote checksums verified after download.

## Question and outcome

Frozen hunch: deletion of any finite union of actual source-zero symmetry orbits preserves real Fourier zeros. Discovery produced explicit nonreal candidates, including a single imaginary orbit deletion. The hunch is numerically falsified by independent challenge, without adding restrictions to rescue it.

| Case | Deleted node indices | Real sign brackets in0..80 | Distinct nonreal candidates from admitted starts | Failed starts |
|---|---|---:|---:|---:|
| literal-control | [] | 21 | 0 | 17 |
| mixed-central-0 | [1, 0] | 15 | 4 | 16 |
| mixed-central-4 | [1, 4] | 3 | 9 | 24 |
| mixed-central-7 | [1, 7] | 6 | 9 | 17 |
| mixed-central-8 | [1, 8] | 15 | 4 | 16 |
| single-0 | [0] | 19 | 0 | 16 |
| single-1 | [1] | 2 | 13 | 18 |
| single-10 | [10] | 19 | 1 | 16 |
| single-11 | [11] | 21 | 0 | 16 |
| single-12 | [12] | 15 | 3 | 17 |
| single-2 | [2] | 2 | 11 | 32 |
| single-3 | [3] | 2 | 10 | 21 |
| single-4 | [4] | 3 | 9 | 19 |
| single-5 | [5] | 2 | 10 | 22 |
| single-6 | [6] | 11 | 5 | 17 |
| single-7 | [7] | 8 | 7 | 16 |
| single-8 | [8] | 17 | 2 | 16 |
| single-9 | [9] | 15 | 3 | 16 |

Counts describe this search, not all roots. The bare source is an implementation control. A source-specific witness is K=Phi/(1+x^2/a^2), a=0.638830053600593577...: its normalized transform has roots20.192841093769789+2.192678280433834i and29.779014778525608+0.961842369884738i. Both survived100/160digits, two shifted contours, independent Jacobi evaluation and local numerical winding1.

## Interpretation and positive survivor

Complex source zeros cannot be discarded as irrelevant logarithm singularities while assuming spectral reality survives. Removing even a pure imaginary pair matters. The exact algebraic reconstruction candidate is Fourier(Phi)=G-G''/a^2, with G the unnormalized quotient transform; this identity is derived control, not the research discovery. A useful proof route would need to characterize why this reconstruction restores the literal spectral geometry, or identify a source-specific divisor/residual coupling. Generic even positivity alone is already known to be insufficient.

The next discriminating test is whether a second actual quartet deletion can reverse rather than monotonically worsen the nonreal-zero response; the separately frozen interaction family attacks this. No exact positive-survivor theorem is claimed.

## Limits

No global root census was computed. A failed Newton start does not establish absence. Real sign brackets miss even-multiplicity roots. Actual source-node cancellation in the complex plane is justified here only to numerical precision; real-axis integrals have no denominator zeros. No Lean builds or fresh kernel/axiom audit were run. SS/SV/VV actions, temporal readers, native remainders and physical boundary work are absent. These experiments cannot establish HB identification, source extinction or RH.
