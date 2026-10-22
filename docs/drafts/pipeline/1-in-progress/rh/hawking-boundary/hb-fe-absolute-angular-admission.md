# HB FE: absolute angular admission of the original horizon caps

Target: full temporal/metric/left-QNM matching. This card concerns the absolute
angular admission needed to differentiate the two original noncompact caps.
Full matching and RH remain open. Frontier map is read-only.

## Frozen bridge

[BRIDGE] The actual combination `F=B-s(s-1)Q/4` is absolutely integrable
against the original fixed-plane horizon kernel and all its target derivatives,
locally uniformly in the physical target coordinates. No differentiated-source
growth premise is introduced. The original clock and both characteristic arms
remain fixed.

Corpus starting point: FixedSourceHorizon proves the exact common source-radius
integral; FullAngularAssembly gives `B=globalCuspCutoff+globalResponse`;
GlobalSmoothResponse identifies the remainder a.e. with the modular lift of
the original native L2 vector. The previous norm-of-mean bound alone cannot
give a mean-of-norm bound.

## Analytical proof

Write `E=exp(R)`, `R>=0`, and suppose `z` lies in the hyperbolic radius-R ball
about i and `A*z` lies in the closed modular cell. Height distortion gives
`Im(A*z) <= E/(c^2+d^2)`. The cell has height >=1/2, hence
`c^2+d^2<=2E`. The modular height bound also gives `Im(A*z)<=E`.
For a cell point w, `|Re(w)|<=1/2<=Im(w)`, so
`Im(S*w)=Im(w)/|w|^2 >=1/(2 Im(w)) >=1/(2E)`.
Applying the first distortion inequality to `S*A` gives
`a^2+b^2<=2E^2`. In particular all four integer entries satisfy `|entry|<=2E`.
Put `N=ceil(2E)`. There are at most `(2N+1)^4<=(7E)^4` such integer matrices.
Passing to PSL2Z only decreases this count.

Distinct open modular-cell pullbacks are disjoint. Thus the squared L2 norm
of a native vector's lift over the ball is at most `2401 E^4 ||u||_2^2`.
Hyperbolic ball area is `2*pi*(cosh(R)-1)<=2*pi*E`. Cauchy--Schwarz gives
`integral_ball |globalLift u| <=49*sqrt(2*pi)*||u||_2*exp(5R/2)`.
Consequently shell summation admits every weight `exp(-p*d(i,z))`, `p>5/2`.
The numerical constants are inessential; every estimate is analytical.

The actual cutoff principal response consists of three height powers with
real exponents `2 Re(q)`, `1`, `2-2 Re(q)`. Their maximum beta is below 2.
Its orbit height bound gives ball supremum `C exp(beta R)` and hence L1
growth `C exp((beta+1)R)`, with beta+1<3. The full square Q has exactly the
needed absolute bound in `FullSourceCircleGrowth.fullSquarePotential_global_growth`:
`|Q(z)|<=C max(1,y,1/y)^gamma`, where `1<=gamma<2` is proved by
`sourceGrowthExponent_bounds`. The complete remainder is retained. On the
radius-R ball `max(1,y,1/y)<=exp(R)`; this gives the same L1 growth bound.
Thus for F there are constants C and
`a=max(5/2,beta+1,gamma+1)<3` such that `integral_ball |F|<=C exp(aR)`.
For each integer shell `[n,n+1)`, multiply this bound by `exp(-pn)`.
The resulting series is geometric with ratio `exp(a-p)<1` for every p>3.
Changing the center changes only the constant, by the distance triangle inequality.

For the fixed-plane kernel, put `D=cosh(x)*cosh(d)+sinh(x)`. On a compact
target neighborhood D is positive and comparable to cosh(d). After onset,
the kernel is `cosh(x)*onsetFirst(2s,tau+log(D))/D`, with decay exponent
`p=1-2 Re(s)>3`. All target derivatives have the same decay: derivatives of
log(D) and their finite products are bounded locally uniformly. More explicitly,
for target `(X,Y)` and source `(a,y)`,
`cosh(d)=((X-a)^2+Y^2+y^2)/(2Yy)`. On compact positive-Y target sets,
every target derivative of this rational function is bounded by a constant
times itself. Since `D>=exp(-|x|)*cosh(d)`, repeated differentiation of
`exp(2s*(tau+log(D)))/D` preserves the same radial decay exponent. This
argument avoids differentiating the nonsmooth distance at coincident points.
Finite-distance integration uses source smoothness and the smooth, positive D.
Tail integration uses the above locally uniform L1 majorant.

The exact polar measure is `sinh(d) dd dtheta`. In the established fixed-radius
arm integral substitute `h=log(cosh(d))`, so `dh=tanh(d) dd`. Its Jacobian
`cosh(x)*cosh(d)/D` then gives precisely `cosh(x)*sinh(d)/D`; the angular
mean contributes `dtheta/(2*pi)`. Absolute admission justifies Fubini and this
change of variables. Dominated differentiation at every finite order proves
joint angular/temporal/radial C-infinity regularity of both original caps.
This is an analytical proof; the global parameter-integral theorem and its
attachment to the original caps are not yet formalised.

## Evidence and limits

Lean-verified leaf: `ThetaCuspHawkingBMModularBallGrowth`.
`modular_ball_cell_cover` proves the quantitative finite covering;
`globalLift_ball_square_bound` proves the native lift's actual ball estimate;
`globalResponse_ball_square_bound` transfers it to the original smooth
full-forcing response through its established a.e. equality. The right-hand
constant is the finite integral of the squared native zero extension.
No source-growth premise is assumed. Scratch check: 43.48 seconds; isolated
exact-module audit: 8.59 seconds, two jobs, no warnings. Default heartbeats;
one owned foreground Lean process. Umbrella import wired without building it.
The lint gate reports the pre-existing unreachable OnsetTransgressionHorizon
module and old size warnings; it reports no error in this leaf.
Audited source bytes match the installed leaf; the installed olean is 945160
bytes. Owned checks, audit and searches exited. Temporary scratch, search
outputs and isolated audit directory were removed; successful verification
logs remain under `/tmp/hb-fe-{check,exact-audit,formal-lint}.log`.

Broad corpus searches: Poincare, automorphic. Deep/method discovery: modular
unfolding, quantitative cell counts, and L2 disjoint translates. All four
completed JSON searches report partial=false; compiler coverage is mostly
source-only/pending, so retrieved declarations require direct Lean verification.
Most method hits were unrelated; no generated ingredient set was accepted as proof.

Broad recent literature check: [Li--Malhotra--Veerapaneni, 2026](https://arxiv.org/abs/2605.30805)
separates source geometry from kernels in periodic Stokes boundary integrals,
but its net-force compatibility and numerical proxy construction do not prove
this hyperbolic estimate. No theorem from that paper is assumed here.

Whole-route consequence of the analytical result: the admitted original future pulse and
both original caps become jointly smooth fields, allowing the literal metric
and current derivatives to be compared. Noncompact physical left-QNM pairing
and identification with the canonical action remain separate obligations.

Remaining formal work: hyperbolic polar disintegration/ball area; shellwise
weighted absolute admission; compact-target kernel derivative bounds; dominated
parameter differentiation and attachment to both original caps. These are
not supplied by the new ball estimate alone. The physical left-QNM pairing
must still retain the complete field and both characteristic cap contributions.
