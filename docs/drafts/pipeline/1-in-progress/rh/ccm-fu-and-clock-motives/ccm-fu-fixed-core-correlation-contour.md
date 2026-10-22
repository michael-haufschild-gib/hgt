# CCM-FU: paired Mellin contour for the distant-head average

- **Stage:** 1-in-progress; literal source analysis.
- **Parent:** [signed-head moment](../../ccm-fu-fixed-core-signed-head-moment.md).
- **Proof chain:** Actual divisor source, renewable signed reserve, exhaustive selection, uniform signed Abel bound, RH.

## Exact target

The asymptotic of W_P(Y)=integral G_P(Y*x)*G_P(x)/x^3 dx and its strict
eventual sign are proved for every fixed nonempty finite prime core.
The positive moment gives J_P>0 uniformly over cores; the literal source
scalar supplies the remaining orientation. The [transfer to discrete
release](../../../3-formalized/ccm-fu-discrete-physical-prime-release.md) is proved.
The open target is uniform control through changing cores and cutoffs.

## Exact source contour

The literal coefficient has initial Dirichlet expression
B(w)=-zeta'(w)-zeta(w)^2+2*gamma*zeta(w). Both Laurent poles at w=1 cancel.
With h the existing entire regularized zeta, an entire definition is
B(w)=-h'(w)-h(w)^2-2*dslope(h,1,w)+2*gamma*h(w).

The finite prime factor is E_P(s)=product_(p in P)(1-p^(1/2-s)). For
nonempty P, E_P(1/2)=0. Divided differences fill that apparent Mellin pole
in F_P(s)=B(s-1/2)*E_P(s)/(2*s*(s-1/2)).

The paired Mellin source is K_P(s)=F_P(s)*F_P(2-s). Its residue at s=0
is Res_P=-B(-1/2)*E_P(0)*J_P. The normalized central contour is

`M_P(a)=(1/(2*pi))*integral_R exp(a*(1+i*t))*K_P(1+i*t) dt`.

Its limit as a tends to infinity is proved to be Res_P. The physical
identity M_P(a)=W_P(exp(a)) is also proved, so W_P(Y) tends to Re(Res_P)
as Y tends to infinity. The [strict source scalar bound](../../../3-formalized/ccm-fu-divisor-source-residue-sign.md)
B(-1/2)>1/(272*pi)>0 is proved in Lean. Consequently the residue and,
eventually, the actual W_P have sign (-1)^(card(P)+1).

## Closed source and boundary estimates

`DivisorSourceEntire` proves the entire B agrees with both the literal
absolute coefficient series and its existing conditional continuation.
`DivisorCoreMellinBoundary` constructs E_P and the filled F_P, proves
quadratic decay of K_P(s)=F_P(s)*F_P(2-s) on Re(s)=0 above height 3,
and proves absolute integrability of its pole-subtracted whole boundary.
The full punctured complex limit s*K_P(s) is its asserted residue.
The companion F_P(2) equals the actual positive moment J_P, so the residue
is exactly -B(-1/2)*E_P(0)*J_P, with E_P(0)=product(1-sqrt(p)).
`DivisorCoreMellinStrip` removes both endpoint poles by an entire second
divided difference. It proves uniform quadratic decay throughout the
closed strip 0<=Re(s)<=2 and moves every fixed exponentially weighted
vertical contour to the imaginary boundary.

`DivisorCoreMellinMean` evaluates the rational pole contribution by the
existing Cauchy Fourier transform. For a>=0 it proves

`M_P(a)=Res_P+(1/(2*pi))*integral_R exp(i*a*t)*T_P(i*t) dt`,

where T_P is the entire two-pole remainder with an absolutely integrable
boundary. Riemann-Lebesgue proves M_P(a)->Res_P. Thus the analytic contour
limit is closed, including full tails and horizontal edges. All four
leaves passed foreground scratch and exact-file checks. All 39 new public
declarations passed their external axiom audits, using only propext,
Classical.choice and Quot.sound. Global formal lint passes and the
declaration index is refreshed. Lake packaging audit remains pending.

## Closed physical identification

`DivisorContinuousHeadRegularity` extends the integer square-root bound
to the literal real interpolation, identifies the complex primitive with
its real value, and proves real-ray growth, local integrability, Mellin
holomorphy, and logarithmic L1/L2 membership for every positive dilation.
`DivisorContinuousHeadMellin` identifies the physical transform with F_P
throughout Re(s)>1/2, by the literal summatory integral, analytic identity,
finite dilation and the exact Mobius Euler product.
`MobiusDivisorDilationMean` proves absolute convergence of W_P and applies
polarized Mellin-Plancherel at sigma=-1 to G_P(exp(a)*x) and G_P(x).
Reality turns the conjugated first transform into exp(a*(1+i*t))*F_P(1+i*t),
so the full pairing is exactly the contour, without a frequency reversal.
It follows that W_P(Y)->Re(Res_P). The [formal physical theorem](../../../3-formalized/ccm-fu-fixed-core-physical-dilation-mean.md)
records the complete proof and validation.

## Remaining analytic obligations

The discrete prime-correlation series equals the physical signed dilation
integral with its exact density and dilation factors. Its actual coefficient
has the same strict eventual parity sign as the physical average.

Quantify dependence on the changing core and cutoff before claiming renewable
   reserve. The present contour constants and sign thresholds depend on P.
   Odd cores have positive distant averages and even cores have negative
   ones; a renewal construction must account for both signs.

No numerical experiment is planned. Every estimate and source identification
must be proved. No pointwise constant head remainder or residue sign is
assumed. The [formal contour result](../../../3-formalized/ccm-fu-fixed-core-correlation-contour.md)
records the closed analytic chain underlying the physical limit.
