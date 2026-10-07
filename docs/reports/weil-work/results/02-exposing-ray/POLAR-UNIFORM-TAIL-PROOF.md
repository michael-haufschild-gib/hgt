# Uniform small-shift polar tail: paper construction

Status: formalized in `WeilWorkExposingRayUniformPolarTail.lean`, including the uniform quartic lower bound. Final installed leaf and seven-capstone axiom audits pass without warnings, using only the standard three axioms. The main WP02 lower inequality remains open.

## Target and positive survivor

Let Phi be the actual Riemann kernel, K=Phi*Phi (the existing real autocorrelation), D=d/dx, and F=(D^2-1/4)Phi. Let G=F*F. Prove G strictly positive on a common distant tail, then prove a single Y works for all 0<c<=1 in P_c^2 K(y)>0 for y>=Y. Here P_c h(y)=h(y)-(h(y-c)+h(y+c))/(2cosh(c/2)), exactly the corpus polarShift.

The positive result is stronger than an exact-blindness exclusion: it gives the sign of every far integer coefficient uniformly in the polar shift, including shifts tending to zero. It does not apply to arbitrary coherent mixtures or prove the WP02 lower bound. Carlson already excludes exact blindness for the corresponding finite tempered multiplier class; do not count that exclusion again.

## Actual differential source, with all theta terms retained

The existing cusp-series representation expresses F on x>=0 as S_R(x), where
R=cuspDeriv(cuspDeriv(riemannCuspPoly))-(1/4)riemannCuspPoly.
Its degree is four and leading coefficient is 16*pi^4>0. Hence R(v)>=1 for all sufficiently large v. Each theta term is nonnegative there, and the n=1 term gives

F(x)>=exp(-pi exp(2|x|)) for |x|>=R0.

Evenness follows from the actual even derivative and kernel identities. The existing cusp-series estimate absorbs its fixed polynomial factor into half of the theta exponential and gives a global constant B>0 with

|F(x)|<=B exp(-(pi/2)exp(2|x|)) exp(-|x|).

This is an analytic bound on the full infinite series, not a numerical truncation. F is continuous and every shifted product is integrable.

## Signed autocorrelation: positive middle beats every negative tail

Choose y>=2(R0+1). On I=[y/2-1,y/2+1], both arguments t and t-y are beyond R0 and have absolute value <=y/2+1. Thus

F(t)F(t-y)>=exp(-2*pi*exp(2)*exp(y))=:L(y).

Outside I the integrand need not be positive. If its product is negative, at least one factor has |argument|<R0, hence the other has |argument|>=y-R0. The full envelope then gives, for EVERY t,

F(t)F(t-y)>=-B^2 exp(-(pi/2)exp(2(y-R0))) exp(-|t|)=:-J_y(t).

The integrable function F(t)F(t-y)+J_y(t) is nonnegative everywhere and >=L(y) on I. Integrating gives

G(y)>=2L(y)-2B^2 exp(-(pi/2)exp(2(y-R0))).

Since exp(2y) dominates exp(y), the last term is eventually <=L(y). Therefore, for all sufficiently large y,

G(y)>=exp(-2*pi*exp(2)*exp(y))>0.

This retains all negative parts. It is invalid to infer positive correlation merely from eventual positivity of F without paying those parts.

## Positive Green transfer to every small polar shift

For c>0 let J_c(v)=2*sinh((c-|v|)/2) on |v|<=c and zero outside. Distributionally (D^2-1/4)J_c=delta_{-c}+delta_c-2cosh(c/2)delta_0. Ordinary integration by parts, with compact J_c and the smooth rapidly decreasing actual source, gives

P_c Phi=-(2cosh(c/2))^(-1) J_c*F,
P_c^2 K=(2cosh(c/2))^(-2)(J_c*J_c)*G.

All interchanges are absolutely integrable by the displayed decay and compact supports. J_c is nonnegative, supported in [-c,c], strictly positive inside, and has positive integral. If y>=Y+2 and 0<c<=1, every translated G argument lies beyond Y, where G is strictly positive. The last convolution is therefore strictly positive. This proves the uniform-tail target on paper. A quantitative quartic c^4 lower bound follows by restricting each Green variable to [-c/2,c/2] and using sinh(v)>=v. Lean formalizes the equivalent normalized-average proof below, including a quartic lower bound.

## Attack and scope

The fixed-c outermost-shift argument alone fails to prove this uniform statement as c->0. The actual differential kernel and compact positive Green representation remove that gap. Positivity of a tail kernel does not prove Fourier positivity, arithmetic matched-cone positivity, or RH. For truncated Phi_L the far cutoff region also matters; transferring this sign uniformly at the moving cutoff needs the existing truncation error and an explicit comparison, not pointwise convergence.

Classical parents: theta derivative leading terms, Laplace-type saddle separation, and Green kernels. External scientific novelty is not established. The source-specific uniform polar sign must be compared with current corpus before claiming an advance.

## Equivalent transfer used in Lean

To avoid a triple-convolution regularity detour, normalize the exact one-step Green identity. Put I(c)=integral_0^c 2 sinh((c-t)/2) dt and kappa(c)=2 p(c) I(c)>0 for c>0. Then f_c=-P_c Phi/kappa(c) is the positive weighted average of F(x+t) and F(x-t), with total weight one. For 0<c<=1, the preceding bounds imply, uniformly in c,

- |f_c(x)| <= B exp(1) exp(-(pi/2) exp(-2) exp(2|x|)) exp(-|x|);
- for |x|>=R+1, f_c(x) >= exp(-pi exp(2) exp(2|x|)).

These follow from |x|-1<=|x±t|<=|x|+1; no division estimate deteriorates with c because the same positive I(c) cancels exactly. The signed-correlation argument above uses only continuity and these envelopes, so its threshold is common to this entire family. Its conclusion gives a positive common tail for f_c autocorrelation. Multiplication by kappa(c)^2>0 and the exact translated-integral identity identify this with P_c^2 K. Thus the full uniform target has the same dependency-closed paper proof without differentiating a convolution or discarding a negative contribution.

The normalized proof also makes the quartic constant explicit: sinh(v)>=v for v>=0 gives I(c)>=c^2/2. Since p(c)>=p(1)>0 for 0<c<=1, kappa(c)>=p(1)c^2. The common signed-correlation lower envelope is exp(-C exp(y)) with C=2*pi*exp(4). Therefore P_c^2 K(y)>=p(1)^2 c^4 exp(-C exp(y)) beyond one common threshold. The Lean capstone may existentially package these positive constants without evaluating them.
