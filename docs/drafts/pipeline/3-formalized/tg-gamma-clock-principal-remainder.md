# TG C9.14: actual Gamma clock principal term and relative ground completion

- **ID:** TG-C9.14
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Route:** TG, source-faithful Gamma endpoint completion
- **Statement:** The explicit symmetrically regularized clock-divided Gamma vector diverges on every positive-aperture cutoff ground state; retaining its forced homogeneous principal term leaves an absolutely Bochner-integrable ground remainder with a unique cofinal limit.

## Exact objects

Write gamma(u)=exp(u/2)/(exp(u)-exp(-u)), f_a=soninCutoffMonomial a 0,
B_a(u)=exp(-u/2) D_exp(u) f_a, and
F_a(u)=D_exp(u)f_a+D_exp(-u)f_a-2f_a.
All dilations and vectors are the existing physical Sonin objects.
For eps>0, define K_(eps,b)f_a=integral_[eps,b] gamma(u)/u F_a(u)du.
The homogeneous term is H_(eps,b)f_a=integral_[eps,b] F_a(u)/(2u^2)du.
Set r(u)=gamma(u)/u-1/(2u^2) exactly.

## Dependency-closed paper proof [PROVED HERE]

The corpus ground covariance is <B_a(u),B_a(v)>=2a exp(-max(u,v)).
Thus S_eps=B_a(0)-B_a(eps) has squared norm
M_eps=2a(1-exp(-eps)), and for u>=eps>=0,
<S_eps,F_a(u)>=M_eps(exp(-u/2)-2).
Finite-interval continuity justifies moving this pairing through the literal
Bochner integral. Therefore <S_eps,K_(eps,1)f_a>=-M_eps J_eps, where
J_eps=integral_[eps,1](2-exp(-u/2))gamma(u)/u du.

For 0<u<=1, exp(-u/2)>=1/2 and 1-exp(-2u)<=2u, so the exact alternative expression gamma(u)=exp(-u/2)/(1-exp(-2u)) gives gamma(u)>=1/(4u).
For 0<eps<=1/2, restrict J_eps to [eps,2eps] to obtain
J_eps>=1/(16eps). Also 1-exp(-eps)>=eps/2, so M_eps>=a eps.
Cauchy-Schwarz then gives eps ||K_(eps,1)f_a||^2>=a/256.
For a>0 this proves divergence of the norm for every eps->0+.
The constants only certify the structural domain obstruction.

The exact ground dilation covariance also gives
||D_exp(u)f_a-f_a||^2=4a(1-exp(-|u|/2)).
Using both directions, ||F_a(u)||^2<=8a u for u>=0; uniformly in u,
||F_a(u)||<=4||f_a|| by unitary dilation.

Rewrite gamma(u)=exp(3u/2)/(exp(2u)-1). On 0<u<=1/2, the exponential
Taylor inequalities |exp(x)-1|<=2|x| and |exp(x)-1-x|<=x^2 for |x|<=1
bound the numerator of gamma(u)-1/(2u) by 10u^2 and its denominator
below by 4u^2. Consequently |r(u)|<=5/(2u). Multiplication by the
square-root ground modulus gives an integrable u^(-1/2) majorant.
For u>=1/2, gamma(u)/u<=2 exp(-u/2)/(1-exp(-1)), hence |r(u)| is
bounded by that exponential plus 1/(2u^2). The uniform ground norm
bound makes this tail integrable. Measurability follows from continuity
of the dilation orbit and the explicit measurable density. Thus
r(u)F_a(u) is Bochner integrable on (0,infinity).

Linearity of the finite Bochner integrals proves the exact identity
K_(eps,b)f_a-H_(eps,b)f_a=integral_[eps,b] r(u)F_a(u)du.
For every cofinal removal eps->0+ and b->infinity, these integrals
converge to integral_(0,infinity) r(u)F_a(u)du. This follows from
absolute Bochner integrability and eventual coverage by [eps,b],
with no prescribed relation between the two endpoints.

## Positive survivor and scope

The singular principal term is fixed by the corpus limit u gamma(u)->1/2.
The survivor retains it and proves that the exact residual density admits
the physical cutoff ground vector. This replaces an invalid bounded-ground
assembly candidate with a principal operator plus an admitted relative
remainder. It does not yet identify that reference operator's full Sonin
domain, construct the full remainder response in Schatten one, or prove
that this candidate is the completed TG source. The scalar-source primitive
identity, Hardy compatibility, arithmetic energy finiteness and strict
sub-unit law remain open. This is not an RH falsification.

## Verification

- Production leaf `formal/GaloisForLFunctions/RHTower/SoninGammaClockEndpoint.lean` passes `lake --old env lean GaloisForLFunctions/RHTower/SoninGammaClockEndpoint.lean -o .lake/build/lib/lean/GaloisForLFunctions/RHTower/SoninGammaClockEndpoint.olean` with empty diagnostics.
- All fifteen public foundation queries in `/tmp/tg-c914-axioms.lean` pass: only propext, Classical.choice and Quot.sound. No added axioms or proof holes.
- Umbrella wired; index exits 0, all fifteen public declarations present. Global lint exits 1 on twelve unrelated unreachable leaves, no finding in this leaf; `/tmp/tg-c914-lint.log` records them.
- Main endpoints: `gammaGroundTruncated_norm_tendsto_atTop`, `gammaClockRemainder_ground_integrable`, `gammaGroundTruncated_sub_homogeneous_tendsto`.
