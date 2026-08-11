# Mass-shifted completed-source hard-edge compactness

- **ID:** `mass-shifted-completed-source-hard-edge-compactness`
- **Stage:** 2-fully-proven / needs specialist audit
- **Route:** U, compactified first-contact source
- **Scientific status:** `[PAPER PROOF COMPLETE] [NOVELTY UNVERIFIED] [LEAN NOT STARTED]`
- **Depends on:** `mass-shifted-hard-edge-paley-wiener-compactification` and the completed Weil
  source formula

## Result

Put `y=a^2`, and for a real polynomial `p` define the literal rational hard-edge test

\[
 g_{a,p}(x)={a\over\sqrt{a^2+x^2}}
 p\!\left((a^2+x^2)^{-1}\right).                              \tag{CSHC.1}
\]

Its completed Xi divisor form is exactly

\[
 \mathcal W(g_{a,p})
 :=\Re\sum_q g_{a,p}(\alpha_q)^2
 =a^2\Phi_{a^2}[p].                                           \tag{CSHC.2}
\]

Fix `C>0`. There are constants `b_C,B_C>0` and `a_C` such that every nonzero `p` with
`deg p<=Ca`, `a>=a_C`, and `mathcal W(g_(a,p))<=0` satisfies

\[
 \boxed{\quad
 {\displaystyle\int_{\mathbb R}\log(2+|x|)|g_{a,p}(x)|^2dx
  \over \|g_{a,p}\|_2^2}
 \le B_C.
 \quad}                                                       \tag{CSHC.3}
\]

Moreover,

\[
 \boxed{\quad
 \|g_{a,p}'\|_2
 \le {2(\deg p+1)\over a}\|g_{a,p}\|_2.
 \quad}                                                       \tag{CSHC.4}
\]

Consequently every normalized family

\[
 a_j\to\infty,\qquad \deg p_j\le Ca_j,\qquad
 \|g_{a_j,p_j}\|_2=1,\qquad \mathcal W(g_{a_j,p_j})\le0       \tag{CSHC.5}
\]

has a strongly convergent `L^2(R)` subsequence. Every limit is a nonzero real Paley--Wiener
function of exponential type at most `2C`.

Thus the `Theta(sqrt(y))` theorem does more than bound degree. Completed prime--Gamma incidence
prevents the bounded-type packet from translating to height infinity. Route U's cofinal first
contacts have genuine nonzero finite-type subsequential limits.

## 1. Exact completed source

For a real even test `g` of the present rational class, the explicit formula is

\[
 \begin{aligned}
 \mathcal W(g)
 ={}&2g(i/2)^2
 +{1\over\pi}\int_{\mathbb R}g(x)^2\vartheta_\infty(x)dx\\
 &-{1\over\pi}\sum_{n\ge2}{\Lambda(n)\over\sqrt n}
      \widehat{g^2}(\log n).                                  \tag{CSHC.6}
 \end{aligned}
\]

The polar term is nonnegative. The archimedean rate obeys universal constants `b,B>0` with

\[
 \vartheta_\infty(x)\ge b\log(2+|x|)-B.                       \tag{CSHC.7}
\]

The only issue is a coefficient-uniform bound for the complete prime term when degree moves with
`a`.

## 2. Rational prime information cone

Use

\[
 x=a\tan(\theta/2),\qquad -\pi<\theta<\pi,
\]

and set

\[
 q_{a,p}(\theta)=p\!\left(a^{-2}\cos^2(\theta/2)\right).
\]

Then `q_(a,p)` is a real trigonometric polynomial of degree at most `deg p`, and cancellation of
the half-density Jacobian gives

\[
 \|g_{a,p}\|_2^2={a\over2}\int_{-\pi}^{\pi}q_{a,p}(\theta)^2d\theta, \tag{CSHC.8}
\]

\[
 \widehat{g_{a,p}^2}(L)
 ={a\over2}\int_{-\pi}^{\pi}q_{a,p}(\theta)^2
 e^{-iaL\tan(\theta/2)}d\theta.                              \tag{CSHC.9}
\]

Shift the periodic contour to `theta-i sigma`, `sigma>0`. The pole at the endpoint is bypassed in
the lower half-plane, where the Fourier exponential decays; no rational pole is crossed. Since

\[
 \Im\tan((\theta-i\sigma)/2)
 =-{\sinh\sigma\over\cos\theta+\cosh\sigma}
 \le-\tanh(\sigma/2),                                      \tag{CSHC.10}
\]

and vertical translation on trigonometric polynomials of degree `N` has `L^2` norm at most
`e^(N sigma)`, Cauchy--Schwarz gives

\[
 \boxed{\quad
 { |\widehat{g_{a,p}^2}(L)|\over\|g_{a,p}\|_2^2}
 \le \exp\!\left(2N\sigma-aL\tanh(\sigma/2)\right).
 \quad}                                                       \tag{CSHC.11}
\]

If `N<=Ca`, every `L>4C` admits a sufficiently small fixed `sigma` for which the exponent in
(CSHC.11) is `<=-c_(C,L)a`. Fix one `L_C>4C`. For `log n<=L_C`, the trivial Fourier bound is

\[
 |\widehat{g^2}(\log n)|\le\|g\|_2^2.                         \tag{CSHC.12}
\]

For `log n>L_C`, (CSHC.11), `Lambda(n)<=log n`, and grouping by unit logarithmic shells give an
exponentially small tail after increasing `a_C`. Hence

\[
 \boxed{\quad
 \sum_{n\ge2}{\Lambda(n)\over\sqrt n}
 |\widehat{g_{a,p}^2}(\log n)|
 \le B_C\|g_{a,p}\|_2^2.
 \quad}                                                       \tag{CSHC.13}
\]

This is the rational hard-edge information cone: scaled degree `N/a<=C` permits only a bounded
prime-log aperture, uniformly over every coefficient vector.

## 3. Gamma growth forces height tightness

Insert (CSHC.7) and (CSHC.13) into (CSHC.6), discard the nonnegative polar term, and use
`mathcal W(g)<=0`. This gives

\[
 {b\over\pi}\int\log(2+|x|)g(x)^2dx
 \le \left({B\over\pi}+{B_C\over\pi}\right)\|g\|_2^2,        \tag{CSHC.14}
\]

which is (CSHC.3). In particular, normalized null or negative packets are uniformly tight:

\[
 \sup_{a,p}\int_{|x|>R}|g_{a,p}(x)|^2dx
 \le {B_C\over\log(2+R)}\longrightarrow0.                     \tag{CSHC.15}
\]

This uses the completed source essentially. Degree control alone permits translation to arbitrary
height; Gamma growth is the confining potential, while finite prime-log aperture makes arithmetic
forcing bounded at fixed scaled degree.

## 4. Uniform translation control

In the same coordinate,

\[
 g_{a,p}(a\tan(\theta/2))=\cos(\theta/2)q_{a,p}(\theta),
 \qquad {d\theta\over dx}={2\over a}\cos^2(\theta/2).          \tag{CSHC.16}
\]

Bernstein's inequality for a degree-`N` trigonometric polynomial and (CSHC.8) give

\[
 \begin{aligned}
 \|g_{a,p}'\|_2^2
 &\le {2\over a}\left\|
 {d\over d\theta}(\cos(\theta/2)q_{a,p}(\theta))
 \right\|_2^2\\
 &\le {4(N+1)^2\over a^2}\|g_{a,p}\|_2^2,                    \tag{CSHC.17}
 \end{aligned}
\]

proving (CSHC.4). Thus normalized bounded-scaled-degree packets have a uniform translation modulus
in `L^2`.

Equations (CSHC.15) and (CSHC.17) are the two Kolmogorov--Riesz conditions, so (CSHC.5) is strongly
precompact in `L^2(R)`. Norm one makes every strong limit nonzero.

Finally, expand `q_(a,p)` into modes `|k|<=N`. On compact `x`-sets,

\[
 e^{2ik\arctan(x/a)}\longrightarrow e^{2i(k/a)x}.
\]

The frequency parameters `2k/a` remain in `[-2C,2C]`. Weak compactness of the mode measures,
combined with strong `L^2` convergence, shows that every limit has Fourier support in that
interval. This proves the Paley--Wiener assertion.

## 5. Canonical first-contact consequence

Take any cofinal Route U sequence of singular first-contact blocks with

\[
 N_j/a_j\le C.
\]

Let `p_j` be the terminal-normalized null polynomial and normalize `g_(a_j,p_j)` in `L^2`.
Null incidence gives `mathcal W(g_(a_j,p_j))=0`, so the theorem supplies a nonzero strong
Paley--Wiener limit after a subsequence. If also `N_j/a_j->tau`, the complete null row passes to
the limit against every hard-edge packet of type strictly below `2tau`. The limit is therefore a
finite-type Weil-null vector orthogonal to the lower-type test flag, not an arbitrary negative
Weil witness.

The polynomial null vectors remain real-rooted in their rational coordinate. Determining the exact
closed constraint this imposes on the Paley--Wiener limit is the next source problem; it is not
being replaced by an unsupported Laguerre--Polya claim.

## Conjecture--failure--pivot audit

1. **Bounded scaled degree automatically gives a nonzero limit.** **Failed.** Packets can translate
   to height infinity; type compactness alone permits weak convergence to zero.
2. **Completed-source height coercivity.** **Proved.** Rational prime information is bounded at
   fixed `N/a`, while Gamma rate grows logarithmically.
3. **Canonical first-contact limit.** **Proved.** Source tightness plus rational Bernstein control
   gives strong, nonzero Paley--Wiener compactness and retains the lower null flag.

## Higher universal principle

Route U had two independent-looking noncompact variables: polynomial degree and spectral height.
They are controlled by the two halves of the completed source.

\[
 \text{degree}/a\quad\longleftrightarrow\quad\text{finite prime-log aperture},
\]

\[
 \text{height}\quad\longleftrightarrow\quad\text{Gamma confining potential}.
\]

Prime information controls frequency; Gamma growth controls position. Together they give phase-
space compactness. Earlier degree recession, first-prime horizon, and Gamma far-right positivity
were shadows of this completed uncertainty law.

## Novelty audit

Corpus search found the heat prime-information cone and several Gamma coercivity statements, but
no rational hard-edge contour estimate (CSHC.11), no completed-source logarithmic tightness at
moving degree, and no strong compactness theorem for Route U first-contact null packets. Literature
search found classical Paley--Wiener, Mehler--Heine, and semiclassical Weil frameworks, but no
matching shifted-Xi reciprocal-Hankel phase-space compactness theorem. No priority claim is made
without specialist audit.

## Lean status

No Lean declaration is claimed. Faithful formalization requires the literal rational test,
trigonometric Cayley substitution, contour shift with endpoint indentation, coefficient-uniform
prime tail, Gamma lower coercivity, rational Bernstein estimate, Kolmogorov--Riesz compactness, and
the canonical Xi null-row limit. An abstract compactness theorem supplied with source estimates as
hypotheses would not meet the route's unconditional Lean requirement.
