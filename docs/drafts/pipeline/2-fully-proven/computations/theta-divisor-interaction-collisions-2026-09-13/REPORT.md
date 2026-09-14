# Theta-source divisor experiment report

These are numerical experiments on declared deformations of the literal theta source, not zeta counterexamples and not HB physical calculations. Let Phi(x)=sum(n>=1) exp(x/2)(4q_n^2-6q_n)exp(-q_n), q_n=pi*n^2*exp(2x). Delete an imaginary node ia using P(x)=1+x^2/a^2, or an off-axis symmetry quartet using P_z(x)=(1-x^2/z^2)(1-x^2/conj(z)^2). The transform studied is the Fourier integral of Phi/P, divided by its mass. Source-node inputs have independent100/160-digit numerical checks, not interval certificates. The13-node list is not complete.

Whole-family wall time: 14.672s. 11 / 11 saved worker tasks completed. Exact environment, source provenance, parameters, executable code and raw failures are retained. Original remote checksums verified after download.

## Question and outcome

New hunch, independently frozen after deletion failure: extra source-node deletion can restore a nonreal spectral pair. For two mass-normalized positive source quotients K0,K1, study (1-lambda)K0+lambda K1,0<=lambda<=1. Search W=F0 F1'-F0' F1=0 and lambda=-F0/(F1-F0). These identities do not predict whether a collision occurs for the actual sources.

| Extra deletion case | Healing candidates | Complexification candidates |
|---|---:|---:|
| central-4-plus-0 | 0 | 0 |
| central-4-plus-11 | 0 | 0 |
| central-4-plus-12 | 0 | 0 |
| central-4-plus-7 | 0 | 0 |
| central-4-plus-8 | 0 | 0 |
| central-plus-0 | 5 | 0 |
| central-plus-11 | 4 | 0 |
| central-plus-12 | 2 | 0 |
| central-plus-4 | 2 | 1 |
| central-plus-7 | 2 | 0 |
| central-plus-8 | 6 | 0 |

Selected independent checks confirm healing with additional quartet z=1.018240818353034717+0.765996945998911556i: collision near w=29.428919852680604, lambda=.349106694483449. Below it, a conjugate pair is nonreal; above it, two distinct real roots appear. A different extra quartet z=.168696748273037391+.746259110771385748i has both a healing collision near64.6451 and a complexification collision near66.5786.

## Whole-route meaning and positive survivor

Deletion damage is not monotone, even for this literal-source family. Counting source zeros or demanding a zero-free residual cannot encode this behavior alone. Placement and coupling of the divisor with the remaining amplitude become the useful research objects. The positive survivor is a specific numerical local collision law with independently checked branches; an unconditional source-composition theorem remains open. Future tests should transplant or reorganize divisor groups across a separately verified arithmetic control, rather than optimize collision constants.

## Limits

No global root census was computed. A failed Newton start does not establish absence. Real sign brackets miss even-multiplicity roots. Actual source-node cancellation in the complex plane is justified here only to numerical precision; real-axis integrals have no denominator zeros. No Lean builds or fresh kernel/axiom audit were run. SS/SV/VV actions, temporal readers, native remainders and physical boundary work are absent. These experiments cannot establish HB identification, source extinction or RH.
