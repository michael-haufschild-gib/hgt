# CCM-FU: signed head moment and averaged remainder

- **Stage:** 1-in-progress; averaged source remainder. The [uniformly positive signed moment](../3-formalized/ccm-fu-fixed-core-signed-head-moment.md) is formalised.
- **Parent:** [literal prime correlation](ccm-fu-fixed-core-prime-correlation.md).
- **Goal:** Signed reserve supply and renewal through changing processed cores, exhaustive selection, uniform signed Abel bound, RH.

## Closed source invariant

The literal finite Möbius dilation G_P of the continuous unit source is
zero below one. Its integer values equal H_P(M) at every cutoff, including
M below product(P). Every rational sample G_P(M/r) equals the exact clipped
sample I_P(M,r), for every positive integer r.

Lean proves absolute integrability and the inverse-cube signed moment law

`J_P=integral_1^infinity G_P(x)/x^3 dx`

`=J_empty*product_(p in P)(1-p^(-3/2))>0`.

The product is at least exp(-2*S), where S=sum_(n>=0) n^(-3/2) is finite.
Hence J_P has a strictly positive lower bound independent of the finite
prime core.
This is a source-specific positive signed moment, not an assertion that
G_P is pointwise nonnegative or that every prime-release correlation is positive.

## Proved mechanism

The existing square-root summatory primitive of the literal coefficients
log(n)-tau(n)+2gamma interpolates the unsigned unit channel. Its finite
Möbius dilation over divisors of product(P) gives G_P. Vanishing inactive
channels gives equality with the actual head at every integer cutoff.
Exact clipped homothety also identifies every rational sample.
For a positive dilation d, change variables in the absolutely convergent
inverse-cube moment of sqrt(d)*G_empty(x/d); its factor is d^(-3/2).
Finite Möbius factorization gives the displayed Euler product. Positivity
of the unit channel, strict positivity on its first open block, and the
existing uniform square-root envelope give a finite strictly positive
unit moment. The actual absolute L-series now converges for Re(s)>1; the
summatory Mellin formula at s=2 gives J_empty=Re(LSeries(b,3/2))/6.
Summable logarithmic deficits control all finite products.

## Remaining correlation estimate

The distant-prime correlation now has a proved physical signed mean limit
and strict eventual orientation. No pointwise constant head remainder is
assumed: H_P(M)/sqrt(M)->0 by itself would not prove that stronger limit.
The [exact discrete bridge](../3-formalized/ccm-fu-discrete-physical-prime-release.md)
identifies the actual correlation with that physical average. Uniform
control of its dependence on the changing core and cutoff remains open.

The proved signed dilation average is

`W_P(Y)=integral_1^infinity G_P(Y*x)*G_P(x)/x^3 dx`.

Its asymptotic sign and size are known for each fixed nonempty core.
The proved continuous representation of the discrete correlation series is

`kappa_P-kappa_(P+p)=2*rho_(P+p)*p^(-3/2)*W_P(p)`.

This discrete-to-continuous correlation identification is formalized,
including every quotient block and the full absolute tail.
The [literal paired Mellin contour](ccm-fu-fixed-core-correlation-contour.md)
has a proved large-dilation limit, including its entire source,
quadratic strip decay, justified contour shift and vanishing boundary
remainder. Its residue is exactly -B(-1/2)*product(1-sqrt(p))*J_P.
The [physical dilation theorem](../3-formalized/ccm-fu-fixed-core-physical-dilation-mean.md)
identifies that contour with the absolutely convergent W_P and proves
W_P(Y)->Re(-B(-1/2))*product(1-sqrt(p))*J_P for every fixed nonempty
finite prime core. Mellin holomorphy and logarithmic L1/L2 source domains
are proved. The [source scalar bound and physical orientation](../3-formalized/ccm-fu-divisor-source-residue-sign.md)
are also formalized: B(-1/2)>1/(272*pi)>0, so W_P is eventually positive
for odd card(P) and negative for even card(P). Uniform control as P changes
remains open.

No computation was used for the exact moment identities. The positive
moment alone is not reserve renewal or a proof of RH.
