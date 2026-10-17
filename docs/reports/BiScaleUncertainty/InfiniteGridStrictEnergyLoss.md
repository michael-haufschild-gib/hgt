# Strict energy loss for smooth signed sources, with infinite-grid witnesses

Write h_f(x)=integral f(u)f(u+x)du, R_f=h_f(0), J(f) for the raw Levy energy,
and E(f)=J(f)/R_f. The weight and source class are those of the certified preceding
packages. This construction requires no polar constraint and makes no claim about
polar closedness.

The governing field guide is now
`formal/GaloisForLFunctions/BiScaleUncertainty/README.md` (read-only). Its Trap 9
requires separating general signed correlation statements from blind-subspace
special cases. Sections 1–3 impose no grid blindness. The main obstruction is
therefore stated for unrestricted smooth compact real sources: bounded normalized
energy, common support, strong L² convergence and uniform normalized correlation
convergence do not imply energy convergence. Section 4 constructs witnesses that
additionally vanish on the entire logarithmic grid; those zeros are proved from
support, never assumed as an analytic interface. This is a sharpness result for
the origin-energy criterion, not a prime-weight or polar coercivity theorem.

## 1. Uniform control by a small source [PAPER PROOF]

For compact continuous real f,q and t>0, Young's inequality gives

    2|ab| <= t a² + b²/t.

Integrate it for a=f(u), b=q(u+x) and then for a=f(u+x), b=q(u).
Translation invariance gives, for every real x,

    |integral f(u)q(u+x)du + integral q(u)f(u+x)du|
        <= t R_f + R_q/t.

All products are integrable because the sources are continuous and compact. Expanding
the actual autocorrelation and using |h_q(x)|<=R_q therefore proves

    |h_(f+q)(x)-h_f(x)| <= R_q + t R_f + R_q/t.

Suppose additionally f(u)q(u)=0 for every u, so R_(f+q)=R_f+R_q. Put R=R_f>0,
r=R_q. Division and the correlation envelope |h_f|<=R yield

    |h_(f+q)(x)/(R+r) - h_f(x)/R|
        <= (2r+tR+r/t)/(R+r).

If 0<t<=1 and r<=t², this is at most t(R+3)/R, uniformly in x. Indeed r>=0,
r/t<=t, r<=t, and R+r>=R. The same assertions apply after changing q's sign.

## 2. Unit energy with arbitrarily small mass [PAPER PROOF]

For every b>0 and eta>0 there is a real smooth compact q supported in [-b,b],
with 0<R_q<eta and J(q)=1.

Construct a concrete smooth bump p with inner radius b/2 and outer radius b,
equal to one at zero. Thus R_p>0 and p vanishes whenever |u|>=b. A source supported
in [-b,b] has h_p(x)=0 for |x|>2b: if p(u) and p(u+x) were both nonzero, the
triangle inequality would give |x|<=2b.

Let c=exp(-1/2)>0. Choose T=4(1/eta+1)/c+1>0, delta=exp(-T), and
L=(2b+1)exp(T)>=1. For p_L(u)=p(Lu), its mass is L^{-1}R_p>0, its support stays
inside [-b,b], and h_pL(delta)=L^{-1}h_p(2b+1)=0. Also 0<delta<=1. The existing
logarithmic increment inequality gives

    c T R_pL <= 4 J(p_L), hence E(p_L)>=cT/4>1/eta.

In particular J(p_L)>0. Set q=p_L/sqrt(J(p_L)). The exact amplitude-scaling laws
give J(q)=1 and R_q=R_pL/J(p_L)=1/E(p_L), which is positive and less than eta.
Smoothness, compactness and support are preserved. This constructs every analytic
ingredient from an actual bump, with no energy-existence premise.

## 3. A sign retaining the energy gain [PAPER PROOF]

For compact C² sources the already certified parallelogram is

    J(f+q)+J(f-q)=2(J(f)+J(q)).

Both summands are nonnegative. Therefore one of the two signs s in {1,-1} satisfies

    J(f)+J(q) <= J(f+s q) <= 2(J(f)+J(q)).

This chooses a genuine scalar source, without estimates on a mixed energy integral.
When J(q)=1, it retains at least one extra raw energy unit.

## 4. Full sequence with common support and a fixed gap [PAPER PROOF]

Set b=log(2)/16>0 and choose the smooth positive-mass bump f of radius b above.
Put R=R_f>0, A=J(f)>=0, d=1/(2R)>0, and K=2(A+1)/R. For n>=0 put
t_n=1/(n+1), and choose the unit-energy bump q_n from section 2 with mass

    0<r_n<min(t_n², R/(2A+1)).

Translate q_n by 4b. Its source support lies in [3b,5b], disjoint from f's
support [-b,b]. Choose s_n by section 3 and define

    g_n(u)=f(u)+s_n q_n(u-4b).

All g_n are smooth, compact, and supported in [-5b,5b]. Their masses are exactly
R+r_n>0. Since 10b<log(2)<=log(k) for every k>=2, support separation gives
h_gn(log k)=0 for every grid node; the same holds for f. Section 3 gives

    (A+1)/(R+r_n) <= E(g_n) <= 2(A+1)/(R+r_n) <= K.

The choice r_n<R/(2A+1) implies

    (A+1)/(R+r_n) >= A/R + 1/(2R) = E(f)+d.

This follows on multiplying positive denominators: it is precisely
R/2 >= r_n(A+1/2). Thus the energy gap holds for every n. Section 1 gives

    sup_x |h_gn(x)/(R+r_n)-h_f(x)/R| <= t_n(R+3)/R -> 0.

The actual sources also converge in squared L² distance:

    integral |g_n(u)-f(u)|² du = s_n² R_qn = r_n <= t_n² -> 0.

The identity follows directly from g_n-f=s_n q_n(.-4b), s_n²=1, and translation
invariance. Nonnegativity and the upper bound give the limit by squeezing.

We have constructed uniform correlation convergence to an actual smooth all-grid
source while the normalized energies stay a fixed positive distance above its energy.
In particular the energies do not converge to the limit kernel's energy.

## 5. Positive survivor and boundary [PAPER PROOF]

Uniform correlation convergence does not preserve energy even for actual smooth
sources with a single common compact source support. Package 9 supplies the exact
positive replacement: uniform smallness of the origin energy is necessary and
sufficient. The present sequence violates that property. Extract a convergent energy
subsequence in [0,K]; its defect D is at least d>0, and package 9 places that entire
defect in every fixed origin interval. Source support escape, grid defects, and
source-realization failure are therefore unnecessary for strict loss. Even strong
L² convergence of the actual sources does not by itself make this singular energy
continuous; the missing control remains precisely the origin-energy criterion.

For the unrestricted signed-source statement, forget the proved grid-zero
property of these same witnesses. Retain their smoothness, positive masses,
common support, common upper energy bound, both convergences and fixed positive
energy gap. This is a dependency-closed proof in the concrete C_c(ℝ,ℝ) domain.
Future tail estimates should retain signed node values; the all-grid family here
tests sharpness and does not replace that general formulation.

Young's inequality, bump functions and the parallelogram identity are reused, not
claimed as new. The connected contribution is the unconditional actual all-grid
construction showing that the certified origin obstruction is sharp within the
field's source domain. No claim of exhaustive external priority is made.

## Formal status

Certified package 10. Four direct `lake --old env lean` leaf checks pass without
diagnostics: `SmallSourceCorrelationStability.lean` (4 theorems),
`UnitEnergySmallSources.lean` (4), `ShortSupportEnergyInjection.lean` (1), and
`InfiniteGridStrictEnergyLoss.lean` (3). All 12 declarations were independently
audited from `/tmp/infinite_grid_strict_loss_axioms.lean`; dependencies use only
`propext`, `Classical.choice`, and `Quot.sound`. Every umbrella import and exact
theorem/module API pair was verified; index refresh passed. No umbrella build ran.

Formal lint reports only two concurrent foreign modules missing umbrella reachability:
`HyperbolicGaugeChebyshevEnergyRepresentation` and `OptimizedHyperbolicRayReceiver`.
No owned leaf has a lint error; repository-wide green is not claimed.

Logs: `/tmp/infinite-grid-small-source-leaf.log`,
`/tmp/infinite-grid-unit-energy-leaf.log`, `/tmp/infinite-grid-energy-injection-leaf.log`,
and `/tmp/infinite-grid-strict-loss-{leaf,axioms,index,lint}.log`.
The read-only field README was read fully at its relocated path; its SHA256 remained
`80c91d482d9dfcfeb86508edcf5551d34d34a5ef333d3fab64be78e75dd67507`.
