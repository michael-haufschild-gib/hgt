# Route E critical dissipation saturation: antiscale resonance no-go

- **ID:** `ROUTE-E-CRITICAL-DISSIPATION-ANTISCALE-NOGO-001`
- **Stage:** 5-failed, with positive survivor
- **Type:** `[THEOREM — PAPER]` / `[NO-GO]` / `[BRIDGE]`
- **Parent:** `route-e-cofinal-parity-energy-covariance-accumulation.md`
- **RH used:** no
- **Computation used:** no
- **External audit:** intentionally omitted under current instruction; no priority claim permitted
- **Scientific status:** `[PROVED HERE] [CANDIDATE NEW FORMULATION] [NOVELTY NOT CERTIFIED]`

## Proposed statement and verdict

For a finite prime aperture `S`, put

\[
 \mathcal Q_S(x)=\frac{J_S(x)^2}{Z_S(x)},\qquad
 \mathscr E_r(S)=\int_0^\infty x^{r-1}\mathcal Q_S(x)\,dx,
\]

and let `\mathscr D_r(S,p)` be the same-sign dissipation from the parent card. The exact insertion
balance is

\[
 \mathscr E_r(S\cup\{p\})+\mathscr D_r(S,p)
 =(1+p^{-r})\mathscr E_r(S).                              \tag{1}
\]

Proposed **critical dissipation saturation** said that, along natural prime apertures, accumulated
positive losses in (1) cancel divergent Euler baseline to bounded remainder for every
`0<r\le1`.

This statement is **false for every fixed `0<r<1`**. If

\[
 S_Y=\{p\text{ prime}:p\le Y\},
\]

then

\[
 \boxed{\mathscr E_r(S_Y)\longrightarrow+\infty\qquad(0<r<1).} \tag{2}
\]

Thus dissipation deficit itself diverges below `r=1`. Falsifier is exactly proposed escape mode:
terminal primes share asymptotic antiscale Mellin phase at

\[
 t_Y=\frac{\pi}{\log Y}.                                  \tag{3}
\]

Endpoint `r=1` is not refuted by this theorem and becomes sharp surviving boundary of this no-go.

## Exact Mellin reporter lower bound

For `r>0`, define positive baseline mass

\[
 \mathscr B_r(S)=\int_0^\infty x^{r-1}Z_S(x)\,dx
 =\Gamma(r)\prod_{p\in S}(1+p^{-r}).                     \tag{4}
\]

For every real `t`, finite gas expansion and Euler's Gamma integral give

\[
 \mathscr M_{r,S}(t)
 :=\int_0^\infty x^{r+it-1}J_S(x)\,dx
 =\Gamma(r+it)\prod_{p\in S}(1-p^{-r-it}).               \tag{5}
\]

Cauchy--Schwarz is applied before any primewise absolute value:

\[
\begin{aligned}
 |\mathscr M_{r,S}(t)|^2
 &=\left|\int_0^\infty x^{r-1}
     \frac{J_S(x)}{\sqrt{Z_S(x)}}\sqrt{Z_S(x)}x^{it}\,dx\right|^2\\
 &\le \mathscr E_r(S)\mathscr B_r(S).
\end{aligned}                                             \tag{6}
\]

Combining (4)--(6) yields exact source-derived reporter bound

\[
 \boxed{
 \mathscr E_r(S)\ge
 \frac{|\Gamma(r+it)|^2}{\Gamma(r)}
 \prod_{p\in S}
 \frac{|1-p^{-r-it}|^2}{1+p^{-r}}.}                     \tag{7}
\]

This is not desired upper bound re-encoded. It is unconditional lower bound on remaining energy,
obtained from one explicit Mellin character.

## Terminal antiscale factor

Write

\[
 u=p^{-r},\qquad \theta=t\log p,\qquad
 R_{r,t}(p)=\frac{|1-u e^{-i\theta}|^2}{1+u}
 =\frac{1+u^2-2u\cos\theta}{1+u}.                        \tag{8}
\]

If `3\pi/4\le\theta\le\pi`, then `\cos\theta\le-2/3`. Since `0<u<1`,

\[
 1+u^2-2u\cos\theta
 \ge 1+u^2+\frac43u
 \ge (1+u)\left(1+\frac u6\right),
\]

and hence

\[
 \boxed{R_{r,t}(p)\ge1+\frac{p^{-r}}6.}                 \tag{9}
\]

At `t=t_Y`, every prime `Y^{3/4}<p\le Y` lies in this chamber. For `Y\ge81`, corpus terminal
window

\[
 W_Y=\{p:Y/3<p\le Y\}
\]

is contained in that chamber, and (9) gives

\[
 \prod_{p\in W_Y}R_{r,t_Y}(p)
 \ge\left(1+\frac{Y^{-r}}6\right)^{\#W_Y}.              \tag{10}
\]

Exact Chebyshev window theorem already formalized in
`MobiusCriticalPrimeBlockResonance.lean` gives, for some absolute `c>0` and all large `Y`,

\[
 \#W_Y\ge c\frac{Y}{\log Y}.                             \tag{11}
\]

Since `\log(1+v)\ge v/(1+v)`, (10)--(11) contribute at least

\[
 c'\frac{Y^{1-r}}{\log Y}                                \tag{12}
\]

to logarithm of product in (7).

## Earlier-prime loss is lower order

For every phase,

\[
 R_{r,t}(p)\ge\frac{(1-p^{-r})^2}{1+p^{-r}}.             \tag{13}
\]

Put `u_0=2^{-r}<1` and

\[
 C_r=1+\frac{2}{1-u_0}.
\]

Elementary bounds

\[
 \log(1-u)\ge-\frac{u}{1-u},\qquad \log(1+u)\le u
\]

show, uniformly for primes,

\[
 \log R_{r,t}(p)\ge-C_r p^{-r}.                          \tag{14}
\]

For only primes not covered by positive chamber, `p\le Y^{3/4}`, crude integer sum is enough:

\[
 \sum_{p\le Y^{3/4}}p^{-r}
 \le 1+\frac{Y^{3(1-r)/4}}{1-r}.                        \tag{15}
\]

All intermediate primes `Y^{3/4}<p\le Y` have `R_{r,t_Y}(p)\ge1`; retaining only `W_Y` and using
(10), (14), and (15) therefore gives

\[
\begin{aligned}
 \log\prod_{p\le Y}R_{r,t_Y}(p)
 &\ge \#W_Y\log\left(1+\frac{Y^{-r}}6\right)
   -C_r\left(1+\frac{Y^{3(1-r)/4}}{1-r}\right)\\
 &\ge c'\frac{Y^{1-r}}{\log Y}
   -C_r\left(1+\frac{Y^{3(1-r)/4}}{1-r}\right)
 \longrightarrow+\infty.                               \tag{16}
\end{aligned}
\]

Last limit is strict because

\[
 \frac{Y^{1-r}/\log Y}{Y^{3(1-r)/4}}
 =\frac{Y^{(1-r)/4}}{\log Y}\longrightarrow+\infty.
\]

Finally `t_Y\to0` and continuity of Gamma give
`|\Gamma(r+it_Y)|^2/\Gamma(r)\to\Gamma(r)>0`. Equation (7) and (16) prove (2).

## Exact escape-mode classification

Pointwise dissipation coefficient is strictly positive, so

\[
 \boxed{
 \mathcal D_{S,p}(x)=0
 \quad\Longleftrightarrow\quad
 \psi_S(px)=-\psi_S(x).}                                \tag{17}
\]

Thus antiscale coherence is exactly null space of one insertion loss. Equations (3), (8), and (9)
prove more: below `r=1`, natural terminal prime block realizes this null direction coherently
enough that one Mellin reporter forces residual energy to diverge. Escape mode is physical in
finite source, not generic-function countermodel.

## No-go closure and positive survivor

- **Killed statement:** bounded critical dissipation deficit for every `0<r\le1` along natural
  prime apertures.
- **Exact falsifier:** terminal-prime antiscale Mellin character `t_Y=\pi/\log Y`.
- **Sharp range:** divergence is proved for every fixed `0<r<1`; argument is neutral at `r=1`.
- **Positive survivor:** Mellin reporter inequality (7), exact null-space law (17), and critical
  boundary `r=1`.
- **Route consequence:** no Route E proof can demand cofinal boundedness of
  `\mathscr E_r(S_Y)` below `r=1`. Viable replacement must project out moving antiscale reporter,
  renormalize terminal shell before positive norm, or return to signed source statistic retaining
  cross-shell cancellation.
- **No RH claim:** (2) refutes overstrong sufficient condition. It does not refute RH or original
  pointwise normalized-current target.

## Formalization target

Formalize without new axioms:

1. exact dissipation-zero iff antiscale coherence (17);
2. exact Mellin mass/reporter identities (4)--(5);
3. Cauchy reporter lower bound (7);
4. normalized local factor law (8), terminal gain (9), and natural-window product bound (10);
5. early-prime penalty (14)--(15) and cofinal divergence (16).

## Formalization status

Finite source infrastructure is formalized and umbrella-wired in
`RHTower/GibbsCriticalDissipationAntiscaleResonance.lean`: exact null-space law (17), general
finite Gibbs Mellin--Euler factorization (hence (5)), exact parity reporter product, local factor
identity (8), universal early-factor lower bound (13), strict terminal gain (9), and natural-window
product bound (10). Direct Lean check and targeted module build pass; axiom audit reports only
`propext`, `Classical.choice`, and `Quot.sound`.

Paper steps still awaiting Lean encoding are Cauchy reporter inequality (6)--(7), logarithmic
conversion (14), integer-sum bound (15), and final cofinal limit (16). Formalized positive-survivor
card: `../3-formalized/new_scientific_knowledge/route-e-gibbs-antiscale-mellin-resonance-law.md`.
