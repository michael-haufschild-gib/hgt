# Mass-shifted parabolic degree horizon

- **ID:** `mass-shifted-parabolic-degree-horizon`
- **Stage:** 2-fully-proven / needs specialist audit
- **Route:** U, mass-shifted reciprocal-Hankel propagation
- **Scientific status:** `[PAPER PROOF COMPLETE] [NOVELTY UNVERIFIED] [LEAN NOT STARTED]`
- **Depends on:** `mass-xi-finite-true-prime-cone`, especially C43-Y and C43-BA

## Result

Put

\[
 \lambda_{y,q}=(y+w_q)^{-1},\qquad
 m_k(y)=\Re\sum_q\lambda_{y,q}^{k+1},
\]

and let

\[
 H_N(y)=(m_{i+j}(y))_{0\le i,j<N}.
\]

There is a universal constant `K>0` such that

\[
 \boxed{\qquad y\ge K N^2\quad\Longrightarrow\quad H_N(y)\succ0.\qquad} \tag{PDH.1}
\]

No zero-location hypothesis enters. Consequently, any Route U first-contact block at shift `y`
has order

\[
 N>\sqrt{y/K}.                                             \tag{PDH.2}
\]

This is the first quantitative cofinal exclusion in Route U: defect degree cannot merely tend to
infinity; it must enter the parabolic regime `N^2/y` bounded away from zero.

## 1. Filter before averaging

Let `p(X)=sum_(i=0)^d c_i X^i`, `d=N-1`, and define the reversed shifted polynomial

\[
 Q_{p,d,y}(W)=(W+y)^d p((W+y)^{-1}).                       \tag{PDH.3}
\]

It is a nonzero real polynomial of degree at most `d` whenever `p` is nonzero. The exact filtered
Gamma identity C43-BA gives

\[
 \begin{aligned}
 c^T H_N(y)c
 &=\Re\sum_q\lambda_{y,q}p(\lambda_{y,q})^2\\
 &=\frac1{(2d)!}\int_0^\infty t^{2d}e^{-yt}
       \Re\mathcal H_{Q_{p,d,y}}(t)\,dt,                 \tag{PDH.4}
 \end{aligned}
\]

where

\[
 \mathcal H_Q(t)=\sum_q Q(w_q)^2e^{-tw_q}.
\]

The order in (PDH.4) matters. Expanding against the unfiltered trace produces the indefinite
divided-factorial kernel of C43-BB and cannot prove (PDH.1).

## 2. Quantitative ultraviolet wedge

For a real polynomial `Q` of degree at most `d`, set

\[
 M_Q(t)=\int_{\mathbb R}Q(x^2)^2e^{-tx^2}\,dx>0.           \tag{PDH.5}
\]

The proof of C43-Y is quantitative before its final strict-sign statement: there are universal
constants `a,eta>0` such that

\[
 0<t,\qquad t(d+1)\le\eta
 \quad\Longrightarrow\quad
 \Re\mathcal H_Q(t)\ge aM_Q(t).                           \tag{PDH.6}
\]

Indeed, its Gamma term is at least
`(c_0-C_0 sqrt(t(d+1)))M_Q(t)`, its complete prime term is at most
`C exp(-(log 2)^2/(16t))M_Q(t)`, and its polar term is nonnegative. Shrinking `eta` once leaves a
fixed positive fraction of `c_0`. This proves (PDH.6), uniformly in coefficients and degree.

Also, `M_Q(t)` is nonincreasing in `t`.

## 3. Coefficient-free global lower envelope

There is a universal `A>0` such that, whenever

\[
 t\ge \frac{\eta}{d+1},
\]

one has

\[
 \Re\mathcal H_Q(t)
 \ge -A\exp(A(d+1+t))M_Q(t).                              \tag{PDH.7}
\]

To prove this, use the exact completed-source formula

\[
 \Re\mathcal H_Q(t)
 =2e^{t/4}Q(-1/4)^2
 +\frac1\pi\int_{\mathbb R}Q(x^2)^2e^{-tx^2}
       \vartheta_\infty(x)\,dx
 -\frac1\pi\sum_{n\ge2}\frac{\Lambda(n)}{\sqrt n}
       \widehat F_{Q,t}(\log n).                          \tag{PDH.8}
\]

The first term is nonnegative and `vartheta_infinity` is bounded below. For the prime term, the
coefficient-free Hermite translation estimate from C43-Y is

\[
 \frac{|\widehat F_{Q,t}(\xi)|}{M_Q(t)}
 \le \exp\!\left(-\frac{\xi^2}{4t}
          +2\sqrt d\frac{|\xi|}{\sqrt t}\right).         \tag{PDH.9}
\]

Group integers by `k<=log n<k+1`, use `Lambda(n)<=log n`, and bound the number in that shell by
`e^(k+1)`. After the factor `n^(-1/2)`, the shell is bounded by a constant times

\[
 (k+1)\exp\!\left(-\frac{k^2}{4t}
       +\left(\frac12+\frac{2\sqrt d}{\sqrt t}\right)k
       +\frac{2\sqrt d}{\sqrt t}\right).                 \tag{PDH.10}
\]

Completing the square gives exponent maximum

\[
 4d+2\sqrt{dt}+t/4+2\sqrt d/\sqrt t.
\]

On `t>=eta/(d+1)`, the last term is `O_eta(d+1)`; the Gaussian shell sum contributes only another
`exp(O(d+1+t))` factor. Equations (PDH.8)--(PDH.10) prove (PDH.7).

## 4. Gamma clock misses the negative region below the quadratic horizon

Put

\[
 T=\frac{\eta}{d+1}.
\]

Split (PDH.4) at `T`. By (PDH.6) and monotonicity of `M_Q`,

\[
 \int_0^T t^{2d}e^{-yt}\Re\mathcal H_Q(t)\,dt
 \ge aM_Q(T)\int_0^Tt^{2d}e^{-yt}\,dt.                  \tag{PDH.11}
\]

By (PDH.7), for `y>A`,

\[
 \int_T^\infty t^{2d}e^{-yt}\Re\mathcal H_Q(t)\,dt
 \ge -Ae^{A(d+1)}M_Q(T)
       \int_T^\infty t^{2d}e^{-(y-A)t}\,dt.             \tag{PDH.12}
\]

It remains only to compare two scalar Gamma tails. Write `r=2d`,

\[
 Y=yT,\qquad Z=(y-A)T.
\]

For integer `r`,

\[
 \begin{aligned}
 \int_0^Tt^re^{-yt}\,dt
 &=\frac{r!}{y^{r+1}}
   \left(1-e^{-Y}\sum_{j=0}^r\frac{Y^j}{j!}\right),\\
 \int_T^\infty t^re^{-(y-A)t}\,dt
 &=\frac{r!}{(y-A)^{r+1}}
   e^{-Z}\sum_{j=0}^r\frac{Z^j}{j!}.                    \tag{PDH.13}
 \end{aligned}
\]

If `y>=K(d+1)^2`, then `Y,Z` are at least a fixed multiple of `K(d+1)`, whereas
`r<=2(d+1)`. For sufficiently large universal `K`, the lower Poisson tail obeys

\[
 e^{-Z}\sum_{j=0}^r\frac{Z^j}{j!}\le e^{-Z/8},           \tag{PDH.14}
\]

the parenthesis in the first line of (PDH.13) is at least `1/2`, and
`(y/(y-A))^(r+1)` is bounded universally. Increase `K` once more so that the decay in (PDH.14)
dominates `Ae^(A(d+1))` and leaves less than `a/2` of (PDH.11). Then (PDH.11) plus (PDH.12) is
strictly positive. Since `M_Q(T)>0`, (PDH.4) proves (PDH.1).

## 5. Route U consequence and exact limit

At a first contact of `H_N(y)`, the block is singular and every preceding leading block is
positive definite. Equation (PDH.1) rules this out whenever `y>=KN^2`, proving (PDH.2).

This does **not** orient the terminal anti-Stieltjes flux of C43-BI. It removes the whole
subcritical region

\[
 \frac{N^2}{y}\longrightarrow0,                           \tag{PDH.15}
\]

and leaves only critical or supercritical double scaling. The positive-carrier no-go does not
apply to the proof: (PDH.4) filters by the actual test polynomial before averaging, while the
no-go concerns an unfiltered factorial carrier.

## Higher universal principle

Two previously separate Route U scales compose. A degree-`d` heat test remains in the
unconditional source cone while `td=O(1)`. The exact Gamma transform of a degree-`d` reciprocal
test concentrates at `t` of order `d/y`. Their composition is the invariant

\[
 \boxed{\text{heat action}\times\text{Gamma clock}=d^2/y.}
\]

The moving-degree obstruction is therefore not arbitrary loss of compactness. It is a parabolic
phase transition created by filtering and averaging in sequence. Earlier fixed-degree recession,
degree--time heat positivity, and factorial-carrier failures are three shadows of this one
double-scaling law.

## Novelty audit

Corpus searches found no `N^2/y` shifted-Xi positivity horizon. C43-Y contains the heat wedge and
C43-BA contains the filtered Gamma identity, but neither composes them or states (PDH.1)--(PDH.2).
Searches through current literature found generic double-scaling Hankel asymptotics for varying
complex weights and orthogonal-polynomial expansions of Xi, but no source-completed Xi theorem
coupling reciprocal-Hankel shift, polynomial degree, and filtered Gamma time in this form. No
priority claim is made without specialist audit.

## Lean status

No Lean declaration is claimed. Formalization must include the exact completed-source formula,
coefficient-uniform Hermite translation bound, shell estimate, filtered Gamma transmutation, and
Gamma-tail comparison for the literal Xi objects. An abstract theorem taking (PDH.6) or (PDH.7)
as hypotheses would violate the route's unconditional-proof requirement and is intentionally not
being added.
