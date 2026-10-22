# BAG weighted cubic critical trace

- **ID:** BAG-C28.56y
- **Stage:** 1-in-progress
- **Current checkpoint:** C28.56aa proves the complete compact-test arithmetic
  boundary; C28.56ab proves full balanced positive-rational reindexing and
  fixed-dilation orthogonality. C28.56ac closes frequency-weighted rational/tested
  identification and termwise rational-series integration. Global actual-source
  control for Schwartz/growing tests and physical transfer remain open.
  Earlier conjectures below are historical.
- **Target:** full weighted arithmetic trace and its critical distributional
  boundary, then the finite-height physical transfer. RH remains open.
- **Previous progress:** C28.56x evaluates the complete balanced trace,
  absolute trace and literal two-axis exclusion in Lean. It does not control
  arbitrary physical profiles or near-resonances.

## Corpus basis and reuse

ChiRamanujanCompleteCubicTrace supplies the complete signed valuation family.
PMRamanujanBandEulerCorrection and PMRamanujanBandEulerSeries supply actual
normally convergent Mellin/Euler correction proofs and mathlib product APIs;
their two-factor band trace is NOT the present cubic. BoundaryCauchyKernel and
RealBoundaryDivisorLimit supply genuine Cauchy approximate identities.
The full six-zeta factorization is now proved below. The critical two-axis finite part remains to prove.

Research query weighted-critical-trace was nonpartial, inventory65385/65385,
with compiler coverage mostly pending/source-only. All candidate/source/proof/
ingredient sections inspected. Its existing C28.56x hits are the balanced
trace just proved; no complete weighted cubic cancellation was returned.

## Exact mixed factor discovered on paper

Use z=p^(-sigma), U=p^(-i*u), V=p^(-i*v), x=z*U,y=z*V. Let E denote the
COMPLETE local double sum from C28.56x with weights x^i*y^j. Extract the six
zeta factors by defining

    H_p = E*(1-x)*(1-y)*(1-z^2/x)*(1-z^2/y)
             / ((1-z*y/x)*(1-z*x/y)).

Algebra gives the stronger exact identity

    H_p - 1 = z^2*(1-U^(-1))*(1-V^(-1))
        * (U+V-1-z^2-U/V-V/U+z/U+z/V)
        / ((1-z)^2*(1-z*V/U)*(1-z*U/V)).

This proves both axis vanishing factors at once and exposes the mixed
regularity required by the principal-value trace. It is not merely a bound
on individual positive or negative sectors. Both the identity and E's equality
with the complete signed local sum are now verified in Lean.

For the normal-product argument, allow complex sigma,u,v in the open tube
Re(sigma)>7/8, |Im(u)|<1/16, |Im(v)|<1/16. Then |z|<=p^(-7/8), both U,V and
their inverses have norm<=p^(1/16), and the two cross denominators have base
norm<=p^(-3/4)<1. The numerator after the mixed factorization is bounded by
a universal constant times p^(-3/2); the three denominators are uniformly
separated from zero. This supplies a normal Euler product across sigma=1,
and Cauchy regularity can supply all fixed derivatives. Constants only serve
summability; optimizing them is not a research target.

## Boundary to prove

Use the exact Z_sigma and D_sigma factorizations and the J,A,B,M pole removal
recorded in bag-rational-product-trace-euler-cancellation. Prove the action
of Z_sigma-D_sigma(u)-D_sigma(v)+1 on test functions, retaining both the
product principal value and -pi^2 times the intersection point mass. A mere
local algebra identity or generic conditional boundary receiver is not closure.

Physical transfer still needs the full near-resonant neighborhood, grouped
Ramanujan cutoffs, moving V/W amplitudes and a justified coupled damping/band
limit. Arithmetic frequency axes cannot be substituted for literal prime
diagonals until their different damping/logarithmic scales are matched.

## C28.56y proved arithmetic step, 2026-10-04

The complete weighted six-zeta trace, normal H across the critical plane,
joint holomorphy of H, both complete axis transforms, K(0)=1, K'(0)=0
after the infinite product, and literal two-axis masking are formalized.
Exact statement and proof: ../../../3-formalized/bag-weighted-six-zeta-cubic-trace.md.
The positive advance is the complete weighted signed arithmetic aggregate,
not another quadratic or selected-packet estimate. All frequencies remain.

A second corpus deep search was nonpartial (inventory65404/65404) and
returned the actual MultivariableVitali/PolydiscWeierstrass closure theorem.
Using that theorem closes joint regularity of H; it is not an assumed
separate-holomorphy principle. Finite coordinate products were proved in
small explicit lemmas to avoid unification/heartbeat blowups; no limits raised.

Next conjecture remains the stated full distributional boundary. Do not
replace the pole-removed J at (sigma,u)=(1,0) by mathlib's assigned ζ(1).
The source correction H is now available jointly analytically, and the
complete K first derivative is zero, so the next work must prove the actual
mixed/quadratic removable quotients and boundary test action. Numerical
constant tuning and re-proving the six-zeta identity would not move this frontier.

## Next conjecture: source finite part via integral quotients

The boundary-next deep search is nonpartial (inventory65411/65411; compiler
coverage mostly pending/source-only). Source inspection identifies the exact
entire regulator already in `ZetaResidueFactorDerivative`:

    F(s)=zetaResidueFactor(s), F(1)=1, F(s)=(s-1)*zeta(s) off 1,
    differentiable_zetaResidueFactor : Differentiable C F.

`ZetaLineLowerBound.zetaPoleFactor_ne_zero` gives the same regulator's
nonvanishing on Re(s)>=1 (the equality of the two definitions is elementary
but has not been added here). `Sieve.InvZetaRegular.invZeta` supplies a
regular reciprocal whose pole value is ZERO; raw reciprocal zeta at its
assigned value at 1 must not be substituted.

For real sigma>=1 define J_sigma(u)=F(sigma+i*u)F(sigma-i*u), so J is even
and never zero, including u=0. Define a,A,B,M as in the prior card using
this J. The source H is now jointly analytic; K has its full-product zero
first derivative. The following integral formulas should produce the
actual smooth quotients, including their axes:

    B_sigma(u,v) = integral_0^1 integral_0^1
                      partial_u partial_v A_sigma(t*u,s*v) ds dt,
    M_sigma(u) = integral_0^1 (1-t)
                      partial_u^2 [J_sigma*K_sigma](t*u) dt.

The identities A(u,0)=A(0,v)=a and (JK)'(0)=0 give these formulas by the
fundamental theorem of calculus. They avoid an unsupported division at
u*v=0 or u=0. On each fixed compact frequency box their derivatives follow
from joint regularity on a neighborhood of the compact sigma=1 face.
This is a proposed dependency-closed PAPER mechanism; these quotient
identities and their uniform derivative bounds are NOT yet Lean theorems.

Write epsilon=sigma-1 and use three real kernels

    Q_e(u)=epsilon/(epsilon^2+u^2),
    P_e(u)=u/(epsilon^2+u^2),
    R_e(u)=u^2/(epsilon^2+u^2).

The exact connected expression should then be

    -a*Q_e(u)*Q_e(v) - 2*a*P_e(u)*P_e(v)
    + v*B*P_e(u) + u*B*P_e(v) - epsilon^2*B*P_e(u)*P_e(v)
    - 2*B*R_e(u)*R_e(v) - M(u)*R_e(u) - M(v)*R_e(v) + 1.

This also specifies the moving remainder that must tend to zero; it cannot
be discarded solely because it has an epsilon^2 factor. Uniform control of
P_e tensor P_e against the moving B times test requires two derivatives of
that test. For compact tests, subtract each coordinate's value at zero
using the symmetric interval [-1,1]. The double compensated numerator is
bounded by |u*v| times the mixed derivative on the inner square; the two
outer strips and outer corner are integrable as well. Dominated convergence
then supplies the product principal value and a uniform order-two bound.
The epsilon^2 remainder vanishes only AFTER this bound is proved. The two
Q kernels supply the -pi^2 intersection mass. All remaining R kernels are
bounded by one and converge almost everywhere to one.

Existing source `HTGeometry/BoundaryCauchyKernel` proves the one-dimensional
Cauchy approximate identity. `ConnesPrincipalValueInverse` defines the
compensated PV and proves inner/outer integrability for Schwartz tests;
`ConnesSgnPrincipalValue` proves an oscillatory PV regularization. These are
usable ingredients, not the required two-variable damped boundary theorem.
The next formal work must attach this argument to the actual J,H,K above.
Physical-profile growth and the coupled near-resonance transfer remain open
beyond compact frequency tests.

## C28.56z checkpoint

The pole-removed A/T sources and joint critical-plane smoothness are now
Lean-checked. The actual signed intersection summand has compact-test
boundary -pi^2*Phi(0,0), proved with simultaneous two-frequency scaling and
product-space DCT. See P3 bag-cubic-regular-source-intersection-mass. The
finite-part/product-PV assembly remains open; its current exact reflected
remainder proof mechanism is in P1 bag-critical-cubic-finite-part. Continue
that mechanism without redoing the six-zeta product or intersection mass.


## C28.56aa completed boundary

The COMPLETE fixed compact-test boundary is now production- and axiom-audited
in ChiRamanujanCubicBoundaryCancellation, ChiRamanujanCubicCompensatedBoundary
and ChiRamanujanCubicCriticalBoundary. All30 public theorems use only standard
logical axioms. P3 bag-cubic-critical-boundary gives the exact formula and proof.

Both finite parts, all four mixed quadrants, the actual intersection mass,
and the ordinary test term survive the final assembly. The finite-prime
trace limit is explicitly identified with the kernel. Every positive-damping
full-plane integral is integrable and the boundary is independent of the
containing box. Smooth compact test regularity is the test class; there is
no assumed arithmetic bound or RH premise.

Next hard problem: rational reindexing/fixed-dilation orthogonality and
physical contraction matching, followed by the actual-profile and finite-height
near-resonance transfer with coupled damping/band limits. A fixed compact-test
boundary alone does not exchange the prime net with integration or prove the
physical cubic. Do not redo the now-closed boundary. RH remains unproved.
