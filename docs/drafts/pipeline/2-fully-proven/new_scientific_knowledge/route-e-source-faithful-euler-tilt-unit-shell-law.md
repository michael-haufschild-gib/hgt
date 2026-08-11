# Route E source-faithful Euler tilt and unit-shell law

- **ID:** `ROUTE-E-SOURCE-FAITHFUL-EULER-TILT-UNIT-SHELL-001`
- **Stage:** 2-fully-proven
- **Type:** `[PAPER-PROVED] [EXACT FINITE SOURCE IDENTITY] [COFINAL SADDLE CLASSIFICATION]`
- **Parent:** `../../1-in-progress/route-e-cofinal-parity-energy-covariance-accumulation.md`
- **Companions:** `route-e-physical-shell-conditioned-parity-energy-regression-law.md`,
  `route-e-product-truncated-reservoir-harmonic-mass-law.md`,
  `../../3-formalized/new_scientific_knowledge/route-e-moving-euler-tilt-chi-square-contiguity-law.md`
- **RH used:** no
- **Computation used:** no
- **Lean status:** exact finite source identity and unit-shell profile are formalized in
  `RouteESourceFaithfulEulerTiltUnitShell.lean`; the moving-to-critical chi-square bridge is
  formalized in `RouteEMovingEulerTiltChiSquareContiguity.lean`. The PNT asymptotics `(9)`--`(14)`
  remain paper-only, so this full card remains stage 2.
- **Scientific status:** project-local new synthesis; external priority unclaimed

## 1. Result

The literal squarefree exponential Gibbs source has an exact Euler--Bernoulli representation.
That representation also proves a sharp obstruction: its physical localization has bounded width
in logarithmic energy.  The broad Gaussian shell theorem therefore does not descend to the Gibbs
current by a harmless change of weight.

Let (S) be a nonempty finite prime set, (x>0), and (sigma>0).  Under independent Bernoulli
variables

\[
 \mathbb P_sigma(B_p=1)=q_{p,sigma}
 =\frac{p^{-\sigma}}{1+p^{-\sigma}},
 \qquad
 N=\sum_{p\in S}B_p,
 \qquad
 E=\sum_{p\in S}B_p\log p,
\tag{1}
\]

put

\[
 \mathcal P_{\sigma,S}=\prod_{p\in S}(1+p^{-\sigma}),
 \qquad
 W_{\sigma,x}(E)=\exp(\sigma E-xe^E).
\tag{2}
\]

Then the literal finite Gibbs partition and current satisfy

\[
 \boxed{
 Z_S(x)=\mathcal P_{\sigma,S}\,
        \mathbb E_\sigma W_{\sigma,x}(E),
 \qquad
 J_S(x)=\mathcal P_{\sigma,S}\,
        \mathbb E_\sigma[(-1)^N W_{\sigma,x}(E)].}
\tag{3}
\]

Consequently

\[
 \boxed{
 \psi_S(x)=\frac{J_S(x)}{Z_S(x)}
 =\frac{\mathbb E_\sigma[(-1)^N W_{\sigma,x}(E)]}
        {\mathbb E_\sigma W_{\sigma,x}(E)}.}
\tag{4}
\]

The weight in `(2)` has unique maximum

\[
 E^*_{\sigma,x}=\log(\sigma/x),
\tag{5}
\]

and its complete centered profile is exact:

\[
 \boxed{
 \frac{W_{\sigma,x}(E^*_{\sigma,x}+u)}
      {W_{\sigma,x}(E^*_{\sigma,x})}
 =\exp\{\sigma(u+1-e^u)\}.}
\tag{6}
\]

For (sigma) in any compact subinterval of ((0,\infty)), equation `(6)` is an (O(1))-width
log-energy shell: it has Gaussian curvature (-\sigma) at zero, exponential left tail, and
superexponential right tail.  This width is independent of aperture.

Now take the canonical cofinal aperture

\[
 L=\log(1/x),
 \qquad
 Y=\frac{2L}{x}(1+o(1)),
 \qquad
 \ell=\log Y=L+\log L+O(1).
\tag{7}
\]

There is a unique moving tilt (sigma_x) near (1) for which the Bernoulli mean energy is the
physical saddle:

\[
 \mu_{\sigma_x,Y}:=
 \sum_{p\le Y}\frac{p^{-\sigma_x}}{1+p^{-\sigma_x}}\log p
 =E^*_{\sigma_x,x}.
\tag{8}
\]

It obeys

\[
 \boxed{
 \sigma_x
 =1+\frac{2\log\ell}{\ell^2}
   +O\!\left(\frac1{\ell^2}
       +\frac{(\log\ell)^2}{\ell^3}\right).}
\tag{9}
\]

Thus source-faithful central tilt is slightly on the (sigma>1) side and converges to the
critical Euler edge.  It is not any fixed (sigma<1), including the half-density
(sigma=1/2).

At this tilt, with

\[
 A=\operatorname{Var}N,
 \quad B=\operatorname{Cov}(N,E),
 \quad C=\operatorname{Var}E,
 \quad t^*=\pi B/C,
 \quad D=\pi^2(A-B^2/C),
\tag{10}
\]

one has

\[
 \boxed{
 A=\log\ell+O(1),\qquad
 B=\ell-\log\ell+O(1),\qquad
 C=\frac{\ell^2}{2}+O(\ell\log\ell),}
\tag{11}
\]

and hence

\[
 \boxed{
 t^*=\frac{2\pi}{\ell}
      +O\!\left(\frac{\log\ell}{\ell^2}\right),
 \qquad
 D=\pi^2\log\ell+O(1).}
\tag{12}
\]

The physical shell is resonant with this escape frequency:

\[
 \boxed{
 t^*E^*_{\sigma_x,x}
 =2\pi+O\!\left(\frac{\log\ell}{\ell}\right).}
\tag{13}
\]

The unconditioned exact Bernoulli characteristic at that frequency is only logarithmically
small:

\[
 \boxed{
 \left|
 \mathbb E_{\sigma_x}
   e^{i(\pi N-t^*E)}
 \right|
 =\ell^{-2}e^{O(1)}.}
\tag{14}
\]

Equations `(6)`, `(9)`, and `(13)` locate the true descent wall.  Literal Gibbs current is a
unit-log-shell, all-prime-scale, Euler-edge problem in which raw parity is phase-compatible with
the antiscale escape.  Fixed-(sigma<1) terminal Gaussian regression and positive shell averaging
cannot supply its missing physical power.

## 2. Proof of the exact source identity

For a subset (T\subseteq S), write

\[
 m_T=\prod_{p\in T}p,
 \qquad N(T)=|T|,
 \qquad E(T)=\log m_T.
\tag{15}
\]

Its Bernoulli probability in `(1)` is

\[
 \mathbb P_\sigma(T)
 =\frac{m_T^{-\sigma}}{\mathcal P_{\sigma,S}}.
\tag{16}
\]

Multiplying `(16)` by `(2)` gives

\[
 \mathcal P_{\sigma,S}\,
 \mathbb P_\sigma(T)W_{\sigma,x}(E(T))
 =m_T^{-\sigma}m_T^\sigma e^{-xm_T}
 =e^{-xm_T}.
\tag{17}
\]

Summing `(17)` with sign (1), then with sign ((-1)^{N(T)}), proves `(3)` and `(4)`.
This is exact at every finite aperture; no independent-prime approximation is made.

Differentiating (log W_{\sigma,x}(E)=\sigma E-xe^E) gives unique critical point `(5)` and
negative second derivative (-xe^E).  Substituting (E=E^*+u) proves `(6)`.

## 3. Forced cofinal tilt

Write (sigma=1+\delta), where eventually
(delta=O(\log\ell/\ell^2)).  Uniformly in that range, PNT partial summation and the absolutely
summable denominator correction give

\[
 \begin{aligned}
 \mu_{1+\delta,Y}
 &=\sum_{p\le Y}p^{-1-\delta}\log p+O(1)\\
 &=\frac{1-e^{-\delta\ell}}{\delta}+O(1)\\
 &=\ell-\frac{\delta\ell^2}{2}
   +O(\delta^2\ell^3+1).
 \end{aligned}
\tag{18}
\]

Meanwhile

\[
 E^*_{1+\delta,x}
 =L+\log(1+\delta)=\ell-\log\ell+O(1+\delta).
\tag{19}
\]

Equating `(18)` and `(19)` yields `(9)`.  Existence follows by evaluating the difference on
the two sides of the displayed asymptotic interval.  Uniqueness is exact: (mu_{\sigma,Y}) is
strictly decreasing in (sigma), while (log(\sigma/x)) is strictly increasing.

For comparison, if (sigma\le1-\eta) for fixed (eta>0), then

\[
 \mu_{\sigma,Y}\asymp Y^{1-\sigma},
 \qquad
 \sqrt{\operatorname{Var}_\sigma E}
 \asymp Y^{(1-\sigma)/2}\sqrt{\ell},
\tag{20}
\]

so physical energy (L) lies a diverging number of standard deviations below mean.  The
fixed-(sigma<1) Gaussian shell theorem is therefore a genuine finite Euler source theorem but
not a central model for full cofinal Gibbs aperture `(7)`.

## 4. Euler-edge covariance and phase wrapping

Let

\[
 w_{p,\sigma}=q_{p,\sigma}(1-q_{p,\sigma})
 =\frac{p^{-\sigma}}{(1+p^{-\sigma})^2}.
\tag{21}
\]

Because ((\sigma_x-1)\ell=o(1)), PNT partial summation gives

\[
 \begin{aligned}
 \sum_{p\le Y}w_{p,\sigma_x}
 &=\log\ell+O(1),\\
 \sum_{p\le Y}w_{p,\sigma_x}\log p
 &=\ell-\log\ell+O(1),\\
 \sum_{p\le Y}w_{p,\sigma_x}(\log p)^2
 &=\frac{\ell^2}{2}+O(\ell\log\ell).
 \end{aligned}
\tag{22}
\]

These are `(11)`.  The quotient (B^2/C=2+o(1)), proving `(12)`.  Combining `(9)`, `(12)`,
and (E^*=L+o(1)=\ell-\log\ell+O(1)) proves `(13)`.

This regime is not a limiting case of the terminal proof used at fixed (sigma<1).  For each
fixed (K>0), terminal band (Y/\ell^K<p\le Y) contributes

\[
 \sum_{Y/\ell^K<p\le Y}\frac1p
 =O\!\left(\frac{\log\ell}{\ell}\right)=o(1),
\tag{23}
\]

while (D\asymp\log\ell).  Escape variance is carried across all logarithmic prime scales, not
by terminal primes with uniformly small residual phase.  Higher cumulants are therefore of the
same order as quadratic term; a Gaussian extrapolation to parity phase (pi) is invalid.

## 5. Exact all-cumulant antiscale amplitude

Independence gives

\[
 \Phi_Y(t)
 :=\mathbb E_{\sigma_x}e^{i(\pi N-tE)}
 =\prod_{p\le Y}
   \frac{1-p^{-\sigma_x-it}}{1+p^{-\sigma_x}}.
\tag{24}
\]

Since (sum_pp^{-2\sigma_x}=O(1)), local logarithmic expansion yields

\[
 \log|\Phi_Y(t)|
 =-\sum_{p\le Y}p^{-\sigma_x}
      (1+\cos(t\log p))+O(1).
\tag{25}
\]

At (t=t^*), `(12)` and PNT partial summation imply

\[
 \sum_{p\le Y}p^{-\sigma_x}=\log\ell+O(1),
 \qquad
 \sum_{p\le Y}p^{-\sigma_x}\cos(t^*\log p)
 =\log\ell+O(1).
\tag{26}
\]

For second estimate, subtract (1) inside cosine and use

\[
 \int_0^1\frac{\cos(2\pi u)-1}{u}\,du> -\infty;
\tag{27}
\]

errors from `(9)` and `(12)` are (o(1)) after prime-harmonic summation.  Equations
`(25)`--`(26)` prove `(14)`.

This (ell^{-2}) is complete all-cumulant Euler-edge amplitude.  Covariance alone would attach
Gaussian amplitude (e^{-D/2}=\ell^{-\pi^2/2+o(1)}), which is false here because `(23)` destroys
small-phase Lindeberg regime.  Equation `(14)` is a source correction, not desired Gibbs bound:
the unit-shell weight in `(4)` can still change parity by arithmetic correlations invisible to
unconditioned product `(24)`.

## 6. Heavy conjecture--proof--failure loop

### Loop A: broad shell descends by positive Laplace averaging

`[CONJECTURE]` Average broad Gaussian shell theorem over positive physical scales.

`[FALSIFIED]` Positive Laplace mixtures are decreasing, whereas centered shell rises below its
center.  Exact tilt `(3)` shows correct descent does not average shells at all; it multiplies by
bounded-width profile `(6)`.

### Loop B: fixed half-density is source-faithful at cofinal aperture

`[CONJECTURE]` Use (sigma=1/2) shell theorem with full (Y\asymp L/x).

`[FALSIFIED]` Equation `(20)` puts physical energy a diverging number of deviations into lower
tail.  Exact centering forces moving tilt `(9)`.

### Loop C: fixed-(sigma) terminal regression extends continuously to Euler edge

`[CONJECTURE]` Insert (sigma_x\to1) into fixed-(sigma) Schur-complement saddle proof.

`[FALSIFIED]` Equation `(23)` shows terminal band carries (o(1)), while total escape variance is
(asymp\log\ell).  Small terminal phases no longer dominate and higher cumulants remain leading.

### Loop D: raw parity is transverse to regression escape on physical shell

`[CONJECTURE]` Missing compensating phase (e^{-it^*E}) destroys antiscale coherence.

`[FALSIFIED]` Phase-wrap law `(13)` makes (e^{-it^*E}=1+o(1)) throughout every bounded-width
physical shell.  Raw parity is asymptotically phase-compatible with escape.

### Loop E: unconditioned Euler edge supplies physical power

`[CONJECTURE]` Accumulate all-prime characteristic before unit-shell localization.

`[FALSIFIED]` Exact all-cumulant law `(14)` gives only ((\log Y)^{-2}), the harmonic ceiling
already known from first-trace analysis.

## 7. Revised Route E frontier

Analytic and physical branches are not independent alternatives at source-faithful scale.
Equations `(3)` and `(6)` force them to meet in one unit-log-energy window.  Product-truncated
reservoir theorem supplies harmonic row mass inside subpower product budget, while exact tilt
theorem shows missing Gibbs descent needs fine physical incidence inside bounded log-product
shell.

The next non-circular source premise is therefore

**`UNIT-LOG-SHELL-E3-PARITY-CARLESON-AND-RECURRENCE-SEAM`**:

construct source-predeclared local (E_3)/reservoir relation inside every bounded physical
log-product shell; prove unit column Carleson load and signed seam flux there; then push those same
weights through exact prime-dilation recurrence.  The premise must be stated as local incidence
and flux inequalities before endpoint current is formed.  Merely bounding ratio `(4)` is the
Route E endpoint and remains circular.

This hybrid target strictly refines both previous survivors:

1. `PRODUCT-TRUNCATED-E3-LOCAL-LAYER-UNIT-CARLESON-AND-SEAM` supplies required physical
   microcanonical incidence but lacked exact Gibbs tilt;
2. `RECURRENCE-WEIGHTED-SHELL-COVARIANCE-ACCUMULATION` supplied exact descent shape but did not
   identify forced shell width or Euler-edge phase wrap.

Route E and RH remain open.

## 8. Novelty and anti-theatre audit

New project-local content is combined exact source law `(3)`, cofinal forced-tilt asymptotic
`(9)`, Euler-edge covariance transition `(11)`--`(13)`, all-cumulant amplitude `(14)`, and proof
that broad fixed-(sigma) shell mechanism cannot model literal cofinal Gibbs source.  Finite
Mellin--Euler factorization and prime-sum asymptotics separately existed in corpus; their
source-faithful unit-shell splice and resulting hybrid frontier did not.

No endpoint estimate is claimed.  No literature search was used under current instruction.  No
Lean file was written or built.
