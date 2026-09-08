# CCM-FU: paired Mellin contour for the distant-head average

- **Stage:** 1-in-progress; literal source analysis.
- **Parent:** [signed-head moment](ccm-fu-fixed-core-signed-head-moment.md).
- **Proof chain:** Actual divisor source, renewable signed reserve, exhaustive selection, uniform signed Abel bound, RH.

## Exact target

Prove the asymptotic of W_P(Y)=integral G_P(Y*x)*G_P(x)/x^3 dx for a fixed
nonempty finite prime core. The corpus's positive moment gives J_P>0
uniformly over finite cores. The missing sign must come from the distant
source, not from the positive moment alone.

## Source contour candidate

The literal coefficient has initial Dirichlet expression
B(w)=-zeta'(w)-zeta(w)^2+2*gamma*zeta(w). Both Laurent poles at w=1 cancel.
With h the existing entire regularized zeta, an entire definition is
B(w)=-h'(w)-h(w)^2-2*dslope(h,1,w)+2*gamma*h(w).

The finite prime factor is E_P(s)=product_(p in P)(1-p^(1/2-s)). For
nonempty P, E_P(1/2)=0. Divided differences fill that apparent Mellin pole
in F_P(s)=B(s-1/2)*E_P(s)/(2*s*(s-1/2)).

The expected Mellin representation of W_P uses F_P(s)*F_P(2-s). At s=0
its candidate residue is A_P*J_P, where A_P=-B(-1/2)*E_P(0). The sign of
B(-1/2) is not assumed. Nor does a residue alone prove a physical mean limit.

## Analytic obligations

1. Identify the entire B with the actual coefficient series and its existing
   continuation; construct the processed Mellin continuation without a zeta
   zero denominator.
2. Identify the paired vertical integral with the actual W_P, using the
   corpus's polarized Mellin-Plancherel theorem and proved source bounds.
3. Justify contour movement and the residue. On Re(s)=0 the reflected
   source lies on Re(w)=-1/2; the corpus has a sharp linear zeta envelope
   there and a quadratic derivative bound. The companion factor at Re(s)=2
   has an absolutely convergent coefficient series and quadratic denominator.
   These estimates suggest an integrable paired tail after pole removal.
4. Prove a signed asymptotic, then quantify dependence on the changing core
   before claiming renewable reserve.

No numerical experiment is planned. Every estimate and source identification
must be proved; this card assumes neither contour validity, a pointwise
constant head remainder, nor a sign for the candidate residue.
