# CCM-FU: the physical signed dilation mean has the source residue limit

- **Stage:** 3-formalized; scratch and exact-file checks and all 17 new public declaration axiom audits passed. Lake packaging audit remains pending.
- **Parent:** [fixed-core correlation contour](../1-in-progress/ccm-fu-fixed-core-correlation-contour.md).
- **Proof chain:** Actual divisor source → renewable signed reserve → exhaustive selection → uniform signed Abel bound → RH.
- **Closed here:** Physical Mellin identification, all pairing domains, absolute convergence of the signed dilation average, equality with the complete contour, fixed-core physical residue limit.
- **Orientation:** [Strict residue and eventual physical signs](ccm-fu-divisor-source-residue-sign.md) are proved.
- **Discrete identification:** [The actual release coefficient equals this average](ccm-fu-discrete-physical-prime-release.md), with strict distant-prime orientation.
- **Open:** Uniform control under changing cores and cutoffs, renewable reserve and RH.

## Exact theorem

For the actual continuous processed divisor head G_P, define

`W_P(Y)=integral_(x>1) G_P(Y*x)*G_P(x)/x^3 dx`.

For every finite core P and Y>0 this integral is absolutely convergent.
For every nonempty finite prime core and every real a,

`(W_P(exp(a)):Complex)=M_P(a)`.

Here M_P is the previously proved complete paired Mellin contour; the
physical average is defined independently. Consequently

`W_P(Y) -> Re(Res_P)` as `Y -> infinity`,

where the prior exact residue identity gives

`Re(Res_P) = -Re(B(-1/2))*product_(p in P)(1-sqrt(p))*J_P`.

The actual signed moment J_P has a strictly positive lower bound independent
of P. The companion source theorem proves B(-1/2)>1/(272*pi)>0 and
eventual strict sign (-1)^(card(P)+1) for W_P. A rate uniform in P remains open.

## Dependency-closed paper proof

On a unit interval, the literal unit head G_empty is affine in sqrt(x).
Both endpoints satisfy G_empty(n)<=(3/5)*sqrt(n), so the same inequality
holds throughout the interval. The head vanishes at x<=1. Its explicit
floor formula proves measurability. The full complex summatory primitive
equals this real value, including below one; no imaginary contribution is
discarded. The finite Mobius dilation

`G_P(x)=sum_(d | product(P)) mu(d)*sqrt(d)*G_empty(x/d)`

therefore has a finite bound |G_P(x)|<=C_P*sqrt(x) on the entire real ray.
Measurability and domination by a locally integrable function prove local
integrability. Vanishing below one and the square-root envelope imply
absolute Mellin convergence and holomorphy of mellin(G_P)(-s) on Re(s)>1/2.

The corpus's actual summatory Mellin formula identifies the unit transform
with B(s-1/2)/(2*s*(s-1/2)) initially on Re(s)>3/2. Both sides are
holomorphic on the connected half-plane Re(s)>1/2. Analytic identity
extends equality throughout that half-plane. Mellin scaling of each
finite dilation gives its coefficient mu(d)*d^(1/2-s). Multiplicativity
and divisor convolution factor their finite sum into

`E_P(s)=product_(p in P)(1-p^(1/2-s))`.

Thus the actual physical transform equals the filled analytic F_P(s)
on Re(s)>1/2, including the required line Re(s)=1.

For Y>0 the logarithmic source at sigma=-1 is

`h_Y(u)=exp(u)*G_P(Y*exp(-u))`.

It vanishes for u>=log(Y), and its absolute value is bounded by
C_P*sqrt(Y)*exp(u/2) on the remaining half-line. The latter bound is
integrable there, as is its square. Thus h_Y belongs to L1 and L2 for
every positive dilation. Separately, the original product kernel is
bounded in absolute value on x>1 by C_P^2*sqrt(Y)/x^2, proving its
absolute convergence directly.

Apply polarized Mellin-Plancherel at sigma=-1 with scaled source
f(x)=G_P(exp(a)*x) in the conjugated slot and g(x)=G_P(x). Both functions
are real. The conjugate of the f-transform on -1+i*t is its transform
on -1-i*t. Scaling and the physical Mellin identity give

`conj(mellin(f)(-1+i*t))*mellin(g)(-1+i*t)`

`=exp(a*(1+i*t))*F_P(1+i*t)*F_P(1-i*t)`.

This is precisely the contour integrand. On the physical side, the
paired Mellin transform at -2 is the integral of f(x)*g(x)/x^3 over
x>0. Since g vanishes below one, this equals W_P(exp(a)). The
normalization from Plancherel is 2*pi, yielding the asserted identity.
No frequency reversal is needed with this ordering of the two slots.

The established contour theorem gives M_P(a)->Res_P. Compose with
log(Y)->infinity and the continuous real-part map. Eventual positivity
of Y supplies exp(log(Y))=Y, proving the physical limit.

## Lean implementation and validation

- `DivisorContinuousHeadRegularity.lean`: ten theorems covering real-ray growth, exact reality, measurability, local integrability, Mellin convergence and holomorphy, and both logarithmic domains.
- `DivisorContinuousHeadMellin.lean`: three theorems identifying the actual unit Mellin transform, its finite Mobius Euler multiplier and its equality with the filled core transform.
- `MobiusDivisorDilationMean.lean`: physical definition, absolute convergence, exact contour equality and physical limit.

All three leaves passed foreground scratch and exact-file `lake env lean`
checks and emitted their leaf oleans. Global formal lint passed and the
declaration index was refreshed. All 17 public declarations were
audited once in an external scratch file and use only propext,
Classical.choice and Quot.sound. Their imports are wired into RHTower;
no umbrella or broad build was run. Lake packaging audit remains pending
because of the known broad stale prerequisite rebuild. No old declaration
was re-audited. No numerical experiment, computed premise, new axiom,
or unfinished proof is used.

## Remaining source problem

The physical contour and the existing discrete prime-correlation series
are now identified: the release coefficient is
2*rho_(P+p)*p^(-3/2)*W_P(p). The size of the sign threshold as P changes,
and control of the actual finite-cutoff energy before convergence, remain
open. They must be settled before the fixed-core limit can supply uniform
reserve to an exhaustive prime selection. No proof or falsification of
RH is claimed.
