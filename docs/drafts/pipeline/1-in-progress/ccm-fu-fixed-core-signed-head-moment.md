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

The distant-prime correlation needs an additional signed mean or averaged
remainder estimate. The leading-mean theorem H_P(M)/sqrt(M)->0 does not
prove H_P(M) tends a constant. A formal Mellin residue does not by itself
justify such a pointwise limit. The source's existing summatory Mellin
formula is a starting point for an averaged statement tailored to the
actual correlation weight; no pointwise constant remainder is assumed.

The precise candidate is the signed dilation average

`W_P(Y)=integral_1^infinity G_P(Y*x)*G_P(x)/x^3 dx`.

Determine its asymptotic sign and size for a fixed nonempty core, then
control its dependence on the core. The expected continuous representation
of the already proved discrete correlation series would read

`kappa_P-kappa_(P+p)=2*rho_(P+p)*p^(-3/2)*W_P(p)`.

This integral identification and an asymptotic for W_P remain unproved.
If a suitable signed mean yields W_P(Y)->A_P*J_P, the new theorem settles
the sign and nonvanishing of J_P; existence and sign of A_P remain separate
source obligations. A Mellin residue alone does not establish this limit.

No computation was used for the exact moment identities. The positive
moment alone is not reserve renewal or a proof of RH.
