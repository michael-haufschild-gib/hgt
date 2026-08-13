# Mass-shifted parabolic degree horizon

- **ID:** `mass-shifted-parabolic-degree-horizon`
- **Stage:** 3-formalized / needs specialist novelty audit
- **Route:** U, mass-shifted reciprocal-Hankel propagation
- **Scientific status:** `[PAPER PROOF COMPLETE] [NOVELTY UNVERIFIED] [LEAN COMPLETE]`
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

The original Poisson-tail wording hid the constants needed by Lean. The following equivalent
entropy-tail proof is explicit and avoids incomplete-Gamma recurrences.

Write `n=d+1`, `r=2d`, and use the scale `u=yt/n`. Let `a>0` be the wedge coefficient and let
`D>0` satisfy the global bound

\[
 \Re\mathcal H_Q(t)\ge-D e^{8(d+t)}M_Q(t).               \tag{PDH.13}
\]

One may take

\[
 a=\frac{\vartheta_\infty(R_*)}{2\pi},\qquad
 D=\frac{|\vartheta_\infty(0)|+C_\Lambda+1}{\pi}.
\]

Put `s=n/y`. If `y eta/n^2>=256`, then `[s,2s]` lies inside `[0,T]`. On this interval,
`t^r>=s^r` and `exp(-yt)>=exp(-2n)`, so the positive part is at least

\[
 aM_Q(T)s^{r+1}e^{-2n}.                                 \tag{PDH.14}
\]

For the tail `t>=T`, put `u=yt/n`. Then `u>=256`. The elementary inequality

\[
 \log u\le 2\sqrt u\le u/8\qquad(u\ge256)
\]

gives

\[
 u^{2d}\le e^{nu/4}.
\]

If also `y>=16`, then `y-8>=y/2`, hence

\[
 t^r e^{-(y-8)t}
 \le s^r e^{-yt/4}.
\]

Therefore the magnitude of the negative tail is at most

\[
 4D e^{8d}M_Q(T)s^{r+1}n^{-1}e^{-yT/4}.                 \tag{PDH.15}
\]

Set

\[
 R=4D/a,\qquad L=\log(R+1)+1,
\]

and choose

\[
 K=\max\!\left(16,\frac{256}{\eta},
                   \frac{4(10+L)}{\eta}\right).         \tag{PDH.16}
\]

For `y>=Kn^2`, the ratio of (PDH.15) to (PDH.14) is at most

\[
 \frac{R}{n}\exp\!\left(8d+2n-\frac{y\eta}{4n}\right)
 \le R e^{-Ln}<1.
\]

The last strict inequality follows from `n>=1` and
`e^{-L}<1/(R+1)`. Thus positive interval strictly dominates the whole negative tail. Since
`M_Q(T)>0`, the filtered integral in (PDH.4) is strictly positive, proving (PDH.1). Every constant
in this proof is now a literal expression in already-formal positive Route U constants.

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
unconditional source cone while `td=O(1)`. The scalar domination used in the filtered Gamma
transform has shape `2d+1` and therefore places its worst-case tail at `t` of order `d/y`. The
literal coefficient-dependent integrand can concentrate earlier; no coefficient-independent
clock identity is claimed. The worst-case composition is the invariant

\[
 \boxed{\text{heat action}\times\text{Gamma clock}=d^2/y.}
\]

The moving-degree obstruction is therefore not arbitrary loss of compactness. It is a parabolic
phase transition created by filtering and worst-case tail domination in sequence. Earlier
fixed-degree recession, degree--time heat positivity, and factorial-carrier failures are three
shadows of this one double-scaling law. The successor
`mass-shifted-hard-edge-paley-wiener-compactification` proves that this worst-case scale is sharp
for the least defective block under RH failure.

## Novelty audit

Corpus searches found no `N^2/y` shifted-Xi positivity horizon. C43-Y contains the heat wedge and
C43-BA contains the filtered Gamma identity, but neither composes them or states (PDH.1)--(PDH.2).
Searches through current literature found generic double-scaling Hankel asymptotics for varying
complex weights and orthogonal-polynomial expansions of Xi, but no source-completed Xi theorem
coupling reciprocal-Hankel shift, polynomial degree, and filtered Gamma time in this form. No
priority claim is made without specialist audit.

## Lean status

Fully formalized unconditionally in
`GaloisForLFunctions/RHTower/XiShiftedParabolicDegreeHorizon.lean`, umbrella-reachable from
`GaloisForLFunctions/RHTower.lean`.

The module proves, rather than assumes:

1. polynomial-Gaussian mass monotonicity;
2. quantitative completed ultraviolet-wedge lower bound;
3. arbitrary-time coefficient-free global lower envelope;
4. shifted reversed-polynomial degree control and nonvanishing for nonzero coefficient vectors;
5. elementary entropy/power tail domination and exact exponential-tail integrals;
6. strict positivity of the literal filtered Gamma integral above the explicit quadratic horizon;
7. strict positivity of the shifted-Xi reciprocal Hankel quadratic form:
   `xiShiftedReciprocalHankelQuadratic_pos_of_parabolic`.

Verification:

- `lake env lean GaloisForLFunctions/RHTower/XiShiftedParabolicDegreeHorizon.lean` passed;
- `lake build GaloisForLFunctions.RHTower.XiShiftedParabolicDegreeHorizon` passed (`9892/9892`);
- both capstones depend only on standard Lean axioms `propext`, `Classical.choice`, and
  `Quot.sound`;
- new module contains no `sorry`, `admit`, `axiom`, `opaque`, or `unsafe` declaration.
