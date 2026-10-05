# BAG actual square-source moving rectangle

- ID: C28.56af.2a.
- Route: BAG joint damping-height transfer and literal physical contraction matching.
- Status: four production leaves and all19 public declarations passed Lean and
  standard-axiom audits. The complete actual-window uniform square law is now
  closed in C28.56af.2b; see bag-uniform-damping-height-square-law.md.
- Paper: ../2-fully-proven/bag-uniform-damping-height-square-law.md.
- Active: ../1-in-progress/bag-physical-contraction-moving-poles.md.

## Exact new source results

ChiRamanujanDampedSquareMellin proves entire Mellin transform, arbitrary-order
uniform strip decay, vertical integrability, convergence and inversion for the
LITERAL bagPhysicalHeightWindow. Repeated Euler differentiation supplies all
orders; no smoothness, support or transform-decay premise is assumed for this
actual window.

ChiRamanujanDampedSquareContour defines the actual numerator

    g_e,X(s)=Q(s+e,-e) M(s) X^s

and normalized integrand

    F_e,X(s)=(S_e(s)-1) M(s) X^s/e^2.

For source-constructed d>0, whenever T,delta,e,b,X are positive,
delta<=d/(1+T)^9, e<delta/4 and b<=delta, the FULL rectangle with corners
(1-delta)-iT and (1+b)+iT satisfies

    rectIntegral(F)=2*pi*i*(g(1)/(2e)+g(1-2e)/(-2e)).

Both signs and all four edges remain explicit. Actual residue-factor disks
prove the entire rectangle is in the analytic domain. With p=1,q=1-2e,

    R(s)=(Q(s+e,-e)-1) M(s) X^s/e^2
         +dslope(dslope(g,p),q)(s)

is an explicit locally holomorphic remainder. The decomposition is proved
globally off the two poles, so the local rectangle theorem applies without
an assumed analytic remainder or zero-free-region premise.

ChiRamanujanDampedSquareRightLine proves from the complete finite prime
product that D_e(n)<=e log n for EVERY n>1. Its complete logarithmic-square
series is summable and bounded by 24/b^3 at real part 1+b, 0<b<=1.
Consequently, for every real height t and every e>=0,

    |S_e(1+b+it)-1| <=24 e^2/b^3.

For e>0, the normalized source is bounded by 24/b^3 independently of e.
No prime powers or integers are omitted. The retained e^2 factor, rather
than the numerical constant, is what permits e log X to tend to zero.

ChiRamanujanDampedSquarePerron proves exact summed Mellin inversion for EVERY
actual divisor-square coefficient, full-line continuity and absolute
integrability. For X>=1 the window term at n=1 is exactly zero. Therefore

    (2*pi)*sum_n D_e(n)^2 W(n/X)/e^2
      = integral_t F_e,X(sigma+i*t),  sigma>1.

The literal normalized contour line is absolutely integrable. Integral-series
exchange is proved from the complete summable majorant; no finite-sector,
interchange, or integrability assumption replaces the actual source.

## Validation

Production commands used lake --old env lean on each leaf with an explicit
olean output; all passed cleanly. Axiom audits38674 and13357 passed for all19 public
declarations, using only propext, Classical.choice and Quot.sound. The same
/tmp audit checked relevant polymorphic mathlib names with concrete types.
All four leaves are imported once into RHTower. The checked Mellin test
dependency is wired once into its HTGeometry umbrella. No full/umbrella build,
heartbeat increase, new axiom, numerical experiment or subagent was used.
Final index21998 passed; all19 API entries and every import were verified.
Final lint77120 exited1 with34 unrelated unreachable modules, no proof-debt
or new-leaf/dependency errors. No global lint pass is claimed.

## Remaining hard mathematics

Both infinite right tails, every other edge, uniform residue coalescence
including e log X->0, and the complete actual-window joint limit are now
formalized and audited in C28.56af.2b.

Even the completed smooth square law would not supply the complete signed
physical cubic. Growing profiles, finite-height near-resonances, growing
moments, moving cofactors and positive common-height self-return remain open.
RH remains unproved; no quadratic-to-cubic promotion is asserted.
