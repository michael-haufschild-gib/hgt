# Quadratic law-discriminant, Bockstein, and controlled horizon

- **ID:** `quadratic-law-discriminant-bockstein-controlled-horizon`
- **Stage:** 3-formalized
- **Type:** THEOREM / EXACT MODEL / RH-ROUTE BRIDGE (paper)
- **Status:** `[PAPER PROOF COMPLETE] [UNCONDITIONAL] [BRIDGE]`
  `[NEW RH-ROUTE LEVERAGE] [NO RH CLAIM] [FORMALIZED IN LEAN]`
- **Role:** smallest non-Morita law horizon with exact punctured observer descent, Tor recovery of
  lost law direction, and sharp discriminant conditioning exponent.

## Setup

Let

\[
 B=\mathbb C[h],
 \qquad
 A=B[\eta]/(\eta(\eta-h)).
 \tag{1}
\]

As `B`-module, `A` is free with basis `1,eta`. Define two-character observer

\[
 J:A\longrightarrow B^2,
 \qquad
 J(a+b\eta)=(a,a+bh),
 \tag{2}
\]

and collision reporter

\[
 r:B^2\longrightarrow B/(h),
 \qquad
 r(x,y)=y-x\pmod h.
 \tag{3}
\]

## Theorem 1: exact global descent sequence

Sequence

\[
 0\longrightarrow A\xrightarrow{J}B^2
 \xrightarrow{r}B/(h)\longrightarrow0
 \tag{4}
\]

is exact.

### Proof

If `J(a+b eta)=0`, first coordinate gives `a=0`, second gives `bh=0`. Since `B=C[h]` is domain,
`b=0`; hence `J` injective. Clearly `rJ=0`. Conversely `r(x,y)=0` means `y-x` is divisible by
`h`, uniquely `y-x=bh`; then `(x,y)=J(x+b eta)`. Reporter is surjective because `(0,1)` maps to
`1 mod h`. QED.

## Theorem 2: non-Morita law collision

For fibre `h=c`,

\[
 A_c=\mathbb C[\eta]/(\eta(\eta-c)).
\]

If `c!=0`,

\[
 A_c\cong\mathbb C\times\mathbb C
 \tag{5}
\]

and `J_c` records two distinct characters. At `c=0`,

\[
 A_0\cong\mathbb C[\varepsilon]/(\varepsilon^2),
 \qquad
 J_0(a+b\varepsilon)=(a,a),
 \tag{6}
\]

so nilpotent line `C epsilon` is erased by ordinary specialized observer.

### Proof

For `c!=0`, ideals `(eta)` and `(eta-c)` are comaximal; Chinese remainder proves `(5)`. At zero,
relation becomes `eta^2=0`, proving `(6)`. Two algebras are not Morita equivalent because centers
and semisimplicity differ. QED.

This is a genuine law horizon: punctured fibres are split semisimple, collision fibre is
nonsplit infinitesimal extension.

## Theorem 3: lost law direction is Tor/Bockstein class

Let `k=B/(h)`. Tensor `(4)` with `k`. Resulting exact sequence contains

\[
 0\longrightarrow
 \operatorname{Tor}_1^B(k,k)
 \longrightarrow A_0\xrightarrow{J_0}k^2
 \longrightarrow k\longrightarrow0.
 \tag{7}
\]

Moreover

\[
 \operatorname{Tor}_1^B(k,k)\cong k,
 \qquad
 \operatorname{im}\bigl(\operatorname{Tor}_1^B(k,k)\to A_0\bigr)
 =k\varepsilon.
 \tag{8}
\]

### Proof

Use free resolution

\[
 0\longrightarrow B\xrightarrow{\cdot h}B\longrightarrow k\longrightarrow0.
\]

After tensoring with `k`, multiplication by `h` is zero, so `Tor_1^B(k,k)=k`. Exactness of
derived tensor sequence gives its image as `ker J_0`. Equation `(6)` shows
`ker J_0=k epsilon`. QED.

Thus ordinary base change erases law direction while derived base change retains it exactly as
Bockstein/Tor conormal.

## Theorem 4: sharp discriminant conditioning law

For `c!=0`, hidden coefficient `b` is recovered from observer values by

\[
 D_c(u,v)=\frac{v-u}{c}.
 \tag{9}
\]

With Euclidean norm on `C^2`,

\[
 \|D_c\|=\frac{\sqrt2}{|c|}.
 \tag{10}
\]

Polynomial `eta(eta-h)` in chosen family basis `(1,eta)` has discriminant `h^2`; hence framed
fibre discriminant is `c^2`, and

\[
 \boxed{
 \sqrt{|\operatorname{Disc}(\eta(\eta-c);1,\eta)|}\,\|D_c\|=\sqrt2.}
 \tag{11}
\]

### Proof

Linear functional `(u,v) mapsto (v-u)/c` has coefficient vector `(-1/c,1/c)` and norm
`sqrt(2)/|c|`, proving `(10)`. Root difference is `c`, so discriminant is `c^2`; substitute. QED.

Exact descent holds at every punctured fibre yet raw uniform inverse conditioning diverges exactly
as inverse square root discriminant.

## Theorem 5: universal finite-dimensional decoder blow-up

Let `J_t:E->F` be continuous family of linear maps between finite-dimensional normed spaces,
injective for `t!=0`, with `ker J_0!=0`. Every family of left inverses `D_tJ_t=id_E` satisfies

\[
 \|D_t\|\longrightarrow\infty
 \qquad(t\to0).
 \tag{12}
\]

### Proof

Choose unit `x in ker J_0`. Continuity gives `||J_t x||->0`. For `t!=0`,

\[
 1=\|x\|=\|D_tJ_tx\|
 \le\|D_t\|\,\|J_tx\|,
\]

forcing `(12)`. QED.

Therefore bounded uniform descent is structurally incompatible with continuously approached law
horizon losing direction. Correct notion is source-renormalized controlled singularity.

## Theorem 6: relative cotangent equals nonreduced discriminant shadow

For quadratic family `(1)`, relative Kähler differential module satisfies

\[
 \boxed{
 \Omega_{A/B}
 \cong B/(h^2)\,d\eta.}
 \tag{13}
\]

Consequently

\[
 \operatorname{Fitt}_0^B(\Omega_{A/B})
 =(h^2)
 =\operatorname{Disc}(A/B),
 \tag{14}
\]

up to conventional unit in discriminant.

### Proof

For presentation

\[
 A=B[\eta]/(\eta^2-h\eta),
\]

conormal sequence gives

\[
 \Omega_{A/B}
 \cong A\,d\eta/\bigl((2\eta-h)d\eta\bigr).
\]

Impose `2eta-h=0`, so `eta=h/2`. Original relation becomes

\[
 \eta(\eta-h)=-h^2/4=0.
\]

Since `4` is unit in `C`, quotient is `B/(h^2)`, proving `(13)`. Cyclic presentation gives
zeroth Fitting ideal `(h^2)`. Discriminant of monic polynomial with roots `0,h` is squared root
difference `h^2`, proving `(14)`. QED.

This one relative-law object casts four exact shadows:

\[
 \begin{array}{c|c}
 \text{shadow}&\text{quadratic coordinate}\\ \hline
 \text{oriented family defect}&h\\
 \text{positive/Fitting energy}&h^2\\
 \text{topological support wall}&V(h)\\
 \text{hidden decoder conditioning}&|h|^{-1}
 \end{array}
 \tag{15}
\]

Derived observer specialization recovers reduced conormal `B/(h)` through Tor, while cotangent
retains nonreduced order-two thickening `B/(h^2)`. Positivity squares away orientation; support
forgets multiplicity; ordinary fibre forgets nilpotent direction; inverse conditioning remembers
distance but not source sign. This is exact prototype of heterogeneous shadow uncertainty.

## Arithmetic specialization and precise prediction

Set formally

\[
 h=\delta_n(\rho)-1,
 \qquad
 \delta_n(\rho)=n^{2\Re\rho-1},
 \tag{16}
\]

or use algebra

\[
 A_\delta=\mathbb C[u]/((u-1)(u-\delta)).
 \tag{17}
\]

Critical equality is collision of source-inverse and analytic-adjoint character sheets. Ordinary
two-leg observer becomes diagonal and loses nilpotent conormal, while derived specialization
retains it by Tor.

Conditional simple-quadratic prediction:

\[
 K_{\mathrm{hidden}}
 \asymp|\operatorname{Disc}|^{-1/2}.
 \tag{18}
\]

Different exponent, higher Jordan order, or absent Tor class falsifies this universality class.
Substitution `(16)` does not force `h=0` and does not prove RH. Live theorem is to construct actual
arithmetic Bockstein landing in Tor-generated conormal from source before divisor specialization.

## Physics prediction

If two independently calibrated boundary reconstruction sheets coalesce while bulk/interior law
tangent survives as nilpotent extension, optimal hidden decoder must diverge with exponent
`Disc^(-1/2)` in quadratic class. This is falsifiable scaling statement, not evidence that black
holes realize model.

## Hostile audit

1. Quadratic degeneration, Tor sequence, and conditioning are classical ingredients.
2. New corpus leverage is exact identification of what source-normal Bockstein must retain and a
   quantitative exponent distinguishing true law collision from ordinary recurrence.
3. Defining `h=delta-1` is representation, not selector.
4. Source construction of nonzero Tor landing is open and RH-bearing.
5. Higher-rank arithmetic defect may require higher discriminant/Jordan universality class.
6. Framed discriminant and conditioning use chosen family generator, basis, and Euclidean norm;
   abstract nonzero fibre `C times C` alone does not determine `c^2` or decoder norm.

## Lean-return note

Formalized; see `quadratic-law-discriminant-bockstein-controlled-horizon-formalized.md`.  The note below was written before that work and is kept for the record: it is no longer a restriction.

> No Lean work authorized. If later requested, formalize algebraic exact sequence, fibre
> classification, Tor computation, and finite-dimensional blow-up separately. Existing Cartier
> torsion modules should be audited before naming new files.

## Log

- 2026-08-08 — hostile foundation audit; proof promoted.

## Formalized companion

`quadratic-law-discriminant-bockstein-controlled-horizon-formalized.md` (same directory).
