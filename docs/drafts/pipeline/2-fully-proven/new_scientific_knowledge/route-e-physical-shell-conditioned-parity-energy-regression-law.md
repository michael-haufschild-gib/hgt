# Route E physical-shell-conditioned parity--energy regression law

- **ID:** `ROUTE-E-PHYSICAL-SHELL-PARITY-ENERGY-REGRESSION-001`
- **Stage:** 2-fully-proven
- **Type:** `[PAPER-PROVED] [EXACT CONDITIONED ODD-CUBE OPERATOR] [NEW FRONTIER REDUCTION]`
- **Parent:** `route-e-physical-saddle-antiscale-coercivity-barrier.md`
- **Source:** `OPEN-SOURCE-001`
- **RH used:** no
- **Computation used:** no
- **Lean status:** not started; Lean corpus was read only during active refactor
- **Scientific status:** project-local new synthesis; external priority unclaimed

## 1. Result

Physical-shell conditioning does not destroy the growing parity cube.  At critical moving
aperture it turns the squarefree Euler law into a joint Bernoulli regression problem whose exact
escape variance is the Schur complement of energy covariance.

Fix

\[
 \frac12\le \sigma<1,\qquad a=1-\sigma,\qquad
 P_Y=\{p:p\le Y\},\qquad \ell=\log Y.
\tag{1}
\]

Put

\[
 r_p=p^{-\sigma},\qquad q_p=\frac{r_p}{1+r_p},
\tag{2}
\]

and let \((B_p)_{p\le Y}\) be independent Bernoulli variables with
\(\mathbb P(B_p=1)=q_p\).  Define occupancy and logarithmic energy

\[
 N_Y=\sum_{p\le Y}B_p,
 \qquad E_Y=\sum_{p\le Y}B_p\log p.
\tag{3}
\]

Write

\[
 A_Y=\operatorname{Var}N_Y,qquad
 B_Y=\operatorname{Cov}(N_Y,E_Y),\qquad
 C_Y=\operatorname{Var}E_Y,
\tag{4}
\]

and set

\[
 t_Y^*=\pi\frac{B_Y}{C_Y},
 \qquad
 D_Y=\pi^2\left(A_Y-\frac{B_Y^2}{C_Y}\right).
\tag{5}
\]

Then \(D_Y>0\), and

\[
 \boxed{
 D_Y=\frac{\pi^2}{a^3}\frac{Y^a}{\ell^3}(1+o(1)),
 \qquad
 t_Y^*=\frac\pi\ell+\frac\pi{a\ell^2}+O(\ell^{-3}).}
\tag{6}
\]

Let

\[
 \mu_Y=\mathbb E E_Y=\sum_{p\le Y}q_p\log p,
 \qquad X_Y=e^{\mu_Y},
 \qquad \Delta_Y^2=\lambda C_Y
\tag{7}
\]

for any fixed \(\lambda>0\), and use positive Gaussian physical-shell weight

\[
 K_Y(u)=\exp\!\left(-\frac{u^2}{2\Delta_Y^2}\right).
\tag{8}
\]

For \(T\subseteq P_Y\), put \(m_T=\prod_{p\in T}p\), and define shell-conditioned positive and
alternating Euler fields

\[
 \begin{aligned}
 Z_Y^{\rm sh}(t)
 &=\sum_{T\subseteq P_Y}m_T^{-\sigma}
   K_Y(\log m_T-\log X_Y)e^{-it\log m_T},\\
 M_Y^{\rm sh}(t)
 &=\sum_{T\subseteq P_Y}(-1)^{|T|}m_T^{-\sigma}
   K_Y(\log m_T-\log X_Y)e^{-it\log m_T},\\
 P_Y^{\rm sh}
 &=\sum_{T\subseteq P_Y}m_T^{-\sigma}
   K_Y(\log m_T-\log X_Y).
 \end{aligned}
\tag{9}
\]

The normalized shell-conditioned parity determinant is

\[
 \mathfrak D_Y^{\rm sh}(t)
 =\frac{|Z_Y^{\rm sh}(t)|^2-|M_Y^{\rm sh}(t)|^2}
 {(P_Y^{\rm sh})^2}.
\tag{10}
\]

At exact regression frequency \(t_Y^*\),

\[
 \boxed{
 \log\frac{|M_Y^{\rm sh}(t_Y^*)|^2}{(P_Y^{\rm sh})^2}
 =-D_Y(1+o(1)),}
\tag{11}
\]

whereas for one constant \(c_{a,\lambda}>0\),

\[
 \boxed{
 \frac{|Z_Y^{\rm sh}(t_Y^*)|^2}{(P_Y^{\rm sh})^2}
 \le \exp\!\left(-c_{a,\lambda}\frac{Y^a}{\ell}\right).}
\tag{12}
\]

Consequently

\[
 \boxed{
 \mathfrak D_Y^{\rm sh}(t_Y^*)
 =-\exp\!\left(-\frac{\pi^2}{a^3}
                  \frac{Y^a}{\ell^3}(1+o(1))\right).}
\tag{13}
\]

Since

\[
 \log X_Y=\frac{Y^a}{a}(1+o(1)),
\tag{14}
\]

equation `(13)` is equivalently

\[
 \boxed{
 |\mathfrak D_Y^{\rm sh}(t_Y^*)|
 =X_Y^{-\pi^2/(a^2\ell^3)+o(\ell^{-3})}
 =X_Y^{-o(1)}.}
\tag{15}
\]

Thus literal positive physical-shell conditioning retains a subpower-full transverse parity
determinant.  It does not integrate away the antiscale mode.  Instead, physical centering and
antiscale frequency are the two regression equations selecting the same saddle.

## 2. Exact Euler-to-probability identity

Let

\[
 \mathcal P_Y=\prod_{p\le Y}(1+r_p).
\tag{16}
\]

For every function \(F\) of \((N_Y,E_Y)\), independence gives exact finite identity

\[
 \frac1{\mathcal P_Y}
 \sum_{T\subseteq P_Y}m_T^{-\sigma}F(|T|,\log m_T)
 =\mathbb E F(N_Y,E_Y).
\tag{17}
\]

In particular,

\[
 \begin{aligned}
 \frac{P_Y^{\rm sh}}{\mathcal P_Y}
 &=\mathbb E K_Y(E_Y-\mu_Y),\\
 \frac{Z_Y^{\rm sh}(t)}{\mathcal P_Y}
 &=\mathbb E\left[K_Y(E_Y-\mu_Y)e^{-itE_Y}\right],\\
 \frac{M_Y^{\rm sh}(t)}{\mathcal P_Y}
 &=\mathbb E\left[K_Y(E_Y-\mu_Y)e^{i(\pi N_Y-tE_Y)}\right].
 \end{aligned}
\tag{18}
\]

The alternating finite-volume sign has not been replaced: it is exactly
\((-1)^{N_Y}=e^{i\pi N_Y}\).  Shell conditioning has not been applied after scalarization: it is
the positive factor \(K_Y(E_Y-\mu_Y)\) inside the literal subset sum.

Equation `(18)` identifies missing Route E object as conditional characteristic function of
signed parity against physical energy.

## 3. Exact covariance minimax

For arbitrary real \(t\),

\[
 \operatorname{Var}(\pi N_Y-tE_Y)
 =\pi^2A_Y-2\pi tB_Y+t^2C_Y.
\tag{19}
\]

Completing square gives

\[
 \boxed{
 \operatorname{Var}(\pi N_Y-tE_Y)
 =D_Y+C_Y(t-t_Y^*)^2.}
\tag{20}
\]

This proves unique minimizer `(5)`.  Strict positivity follows because equality in
Cauchy--Schwarz would force \(1=c\log p\) on every prime with \(0<q_p<1\), impossible for two
distinct primes.

The same minimizer and residual survive Gaussian shell conditioning at quadratic order.  Indeed,
for a centered Gaussian pair \((N,E)\) with covariance matrix

\[
 \Sigma=\begin{pmatrix}A&B\\B&C\end{pmatrix},
\tag{21}
\]

multiplication by \(e^{-E^2/(2\Delta^2)}\) changes covariance to

\[
 \Sigma_\Delta
 =\Sigma-\frac1{C+\Delta^2}
   \begin{pmatrix}B\\C\end{pmatrix}
   \begin{pmatrix}B&C\end{pmatrix}.
\tag{22}
\]

Hence

\[
 \frac{(\Sigma_\Delta)_{12}}{(\Sigma_\Delta)_{22}}=\frac BC,
 \qquad
 \min_t\operatorname{Var}_\Delta(\pi N-tE)
 =\pi^2\left(A-\frac{B^2}{C}\right).
\tag{23}
\]

This is exact linear algebra.  Positive energy conditioning removes only component parallel to
energy; antiscale coherence \(\pi N\approx tE\) is exact orthogonal escape mode.  Residual
\(D_Y\) is parity--energy Schur complement.

## 4. Prime asymptotics and exact critical scale

From `(2)` and \(q_p(1-q_p)=r_p/(1+r_p)^2\),

\[
 \begin{aligned}
 A_Y&=\sum_{p\le Y}\frac{p^{-\sigma}}{(1+p^{-\sigma})^2},\\
 B_Y&=\sum_{p\le Y}\frac{p^{-\sigma}\log p}{(1+p^{-\sigma})^2},\\
 C_Y&=\sum_{p\le Y}\frac{p^{-\sigma}(\log p)^2}{(1+p^{-\sigma})^2}.
 \end{aligned}
\tag{24}
\]

Terms created by denominators beyond first order are lower order for \(\sigma\ge1/2\).  Put
\(\log p=\ell-v\).  PNT partial summation gives terminal measure

\[
 \frac{Y^a}{\ell}e^{-av}\,dv
\tag{25}
\]

on every fixed \(v\)-window, with exponentially negligible tail after
\(v>C\log\ell\).  Its first three moments give

\[
 \frac{B_Y}{C_Y}
 =\frac1\ell+\frac1{a\ell^2}+O(\ell^{-3})
\tag{26}
\]

and

\[
 A_Y-\frac{B_Y^2}{C_Y}
 =\frac1{a^3}\frac{Y^a}{\ell^3}(1+o(1)).
\tag{27}
\]

Equations `(26)`--`(27)` prove `(6)`.  They are same weighted terminal variance computed in
`route-e-critical-half-density-terminal-frame-minimax-law.md`, now identified as literal
parity--energy regression residual.

Also

\[
 \mu_Y=\sum_{p\le Y}\frac{p^{-\sigma}}{1+p^{-\sigma}}\log p
 =\frac{Y^a}{a}(1+o(1)),
\tag{28}
\]

which proves `(14)`.  The pair-product center is \(2\mu_Y=2\log X_Y\), exactly physical-saddle
condition of parent barrier.

## 5. Gaussian-shell saddle lemma

We record analytic step used in `(11)`.

**Lemma.**  Let independent Bernoulli triangular array have energies \(e_j>0\), probabilities
\(q_j\to0\), and let \(N=\sum B_j\), \(E=\sum e_jB_j\).  Suppose:

1. \(C=\operatorname{Var}E\to\infty\) and \(\max e_j=o(\sqrt C)\);
2. for \(t_* =\pi\operatorname{Cov}(N,E)/C\),
   \(D=\operatorname{Var}(\pi N-t_*E)\to\infty\);
3. outside a set where \(\max|\pi-t_*e_j|=o(1)\), contribution to every second and third
   cumulant of \(\pi N-t_*E\) is \(o(D)\);
4. on that set,
   \(\sum q_j|\pi-t_*e_j|^3=o(D)\).

Put \(\Delta^2=\lambda C\), \(\mu=\mathbb EE\), and
\(K(u)=e^{-u^2/(2\Delta^2)}\).  Then

\[
 \log\left|
 \frac{\mathbb E[K(E-\mu)e^{i(\pi N-t_*E)}]}
      {\mathbb E K(E-\mu)}\right|^2
 =-D(1+o(1)).
\tag{29}
\]

**Proof.**  Fourier inversion gives

\[
 K(E-\mu)
 =\frac\Delta{\sqrt{2\pi}}
  \int_{\mathbb R}e^{-\Delta^2\tau^2/2}e^{i\tau(E-\mu)}\,d\tau.
\tag{30}
\]

After expectation, integrand is finite Bernoulli product

\[
 e^{-\Delta^2\tau^2/2-i\tau\mu}
 \prod_j\left(1-q_j+q_je^{i(\pi-t_*e_j+\tau e_j)}\right).
\tag{31}
\]

On central saddle range \(|\tau|=O(C^{-1/2}\log C)\), Taylor expansion of logarithm in
small terminal phases gives quadratic form `(22)`.  Linear \(\tau\)-term vanishes because
\(t_*C=\pi\operatorname{Cov}(N,E)\).  Constant real term is \(-D/2\), and assumptions 3--4
make complete third-and-higher remainder \(o(D)\), uniformly after harmless saddle displacement
caused by imaginary cumulants.  Gaussian Hessian differs from unphased denominator Hessian by
relative \(o(1)\), so its logarithm contributes \(o(D)\).  Outside central range, Gaussian factor
together with \(\max e_j=o(\sqrt C)\) gives an exponentially smaller integral.  Dividing by same
calculation with zero parity phase proves `(29)`.

This is Laplace's method for explicit finite product `(31)`; no local limit theorem is assumed.

For prime array `(2)`, take terminal set \(Y/\ell^C<p\le Y\) with fixed \(C>4/a\).  Equations
`(25)`--`(27)` verify assumptions.  On terminal set,

\[
 \pi-t_Y^*\log p
 =\frac\pi\ell\left(v-\frac1a\right)
  +O\left(\frac{1+v}{\ell^2}\right),
\tag{32}
\]

and omitted primes contribute \(o(Y^a/\ell^3)=o(D_Y)\).  Thus lemma proves `(11)`.

## 6. Positive branch is exponentially smaller

For \(Z_Y^{\rm sh}\), phase in `(18)` is \(-t_Y^*E_Y\), with no parity counterphase.  Fourier
representation is

\[
 \frac{Z_Y^{\rm sh}(t_Y^*)}{\mathcal P_Y}
 =\frac{\Delta_Y}{\sqrt{2\pi}}
  \int e^{-\Delta_Y^2\tau^2/2-i\tau\mu_Y}
  \prod_{p\le Y}
  \left(1-q_p+q_pe^{-i(t_Y^*-\tau)\log p}\right)d\tau.
\tag{33}
\]

On terminal chamber \(Y/e<p\le Y\), \(t_Y^*\log p=\pi+O(1/\ell)\), and

\[
 \sum_{Y/e<p\le Y}q_p\asymp\frac{Y^a}{\ell}.
\tag{34}
\]

Use

\[
 |1-q+qe^{i\theta}|^2
 =1-2q(1-q)(1-\cos\theta)
 \le e^{-2q(1-q)(1-\cos\theta)}.
\tag{35}
\]

If \(|\tau|\ell\le1\), `(35)` and `(34)` give modulus at most
\(e^{-cY^a/\ell}\).  If \(|\tau|\ell>1\), either terminal phases remain bounded away from
\(0\pmod{2\pi}\), giving same product bound, or \(\tau\ell\) approaches an odd multiple of
\(\pi\); then Gaussian factor costs

\[
 \Delta_Y^2\tau^2\gg C_Y/\ell^2\asymp Y^a/\ell.
\tag{36}
\]

Splitting real line into these alternatives proves numerator bound
\(e^{-cY^a/\ell}\mathcal P_Y\).  Denominator saddle at zero satisfies

\[
 \frac{P_Y^{\rm sh}}{\mathcal P_Y}
 \longrightarrow\sqrt{\frac\lambda{1+\lambda}}>0
\tag{37}
\]

by same quadratic expansion with zero phase.  Equations `(33)`--`(37)` prove `(12)`.

Since \(Y^a/\ell\gg D_Y\), `(11)` and `(12)` prove `(13)`.

## 7. Exact Fourier odd-cube preservation

For completeness, conditioning can also be seen before probabilistic normalization.  For
pair-product Gaussian shell

\[
 K_Y(\log(m_Tm_U)-2\log X_Y),
\tag{38}
\]

Fourier inversion gives exact finite identity

\[
 \begin{aligned}
 &\sum_{T,U}\bigl(1-(-1)^{|T|+|U|}\bigr)(m_Tm_U)^{-\sigma}
 e^{-it(\log m_T-\log m_U)}K_Y(\log(m_Tm_U)-2\log X_Y)\\
 &=\frac{\Delta_Y}{\sqrt{2\pi}}\int_{\mathbb R}
 e^{-\Delta_Y^2\tau^2/2-2i\tau\log X_Y}
 \left[
 \prod_{p\le Y}(B_p(\tau)+U_p(\tau,t))
 -\prod_{p\le Y}(B_p(\tau)-U_p(\tau,t))
 \right]d\tau,
 \end{aligned}
\tag{39}
\]

where

\[
 B_p(\tau)=1+p^{-2\sigma+2i\tau\log p},
 \qquad
 U_p(\tau,t)=2p^{-\sigma+i\tau\log p}\cos(t\log p).
\tag{40}
\]

Therefore

\[
 \prod(B_p+U_p)-\prod(B_p-U_p)
 =2\sum_{\substack{R\subseteq P_Y\\|R|\text{ odd}}}
   \prod_{p\in R}U_p\prod_{p\notin R}B_p.
\tag{41}
\]

Every even grade still cancels exactly.  Physical shell adds one common energy frequency \(\tau\);
it does not collapse growing odd cube to scalar first grade.

At exact monochromatic antiscale \(t\log p=\pi\), dominant minus branch satisfies

\[
 B_p(\tau)-U_p(\tau,t)
 =(1+p^{-\sigma+i\tau\log p})^2.
\tag{42}
\]

Its logarithmic phase derivative at \(\tau=0\) is

\[
 2i\frac{p^{-\sigma}}{1+p^{-\sigma}}\log p.
\tag{43}
\]

Summing `(43)` gives \(2i\mu_Y\), which cancels external derivative
\(-2i\log X_Y\) in `(39)` exactly.  This is saddle-lock identity:

\[
 \boxed{\text{physical Euler centering}=\text{stationarity of sign-corrected antiscale branch}.}
\tag{44}
\]

Equation `(20)` and asymptotic `(27)` measure only failure of real prime logs to be exactly
monochromatic.

## 8. Conjecture--proof--failure loops

### Loop A: project physical shell before replicas

`[CONJECTURE]` Apply one-copy orthogonal shell projection and then use existing replica incidence
law to condition growing odd cube.

`[FAILED AS A ROUTE E IDENTIFICATION]` Product shell constrains sum of prime log-energies and is a
global microcanonical projection.  A tensor product of one-copy shell projectors imposes each
coordinate separately and is a different operator.  Existing
`HTGeometry/ReplicaProjectionIncidenceLaw.lean` proves exact defect control for genuine replica
projection, but supplies no identification with Route E product shell.  Using it directly would
be theatre.

### Loop B: shell conditioning destroys odd cube

`[FALSIFIED]` Equations `(39)`--`(41)` retain every odd grade exactly.  Conditioning introduces
one common Fourier energy coordinate, not exponential new combinatorics.

### Loop C: physical saddle and antiscale lobe are incompatible

`[FALSIFIED]` Exact derivative identity `(44)` shows physical center is stationary point of
sign-corrected antiscale branch.  Regression minimizer `(5)` is its non-monochromatic correction.

### Loop D: conditioning adds new dissipation

`[FALSIFIED AT SHARP EXPONENT]` Gaussian regression law `(23)` leaves Schur-complement residual
unchanged.  Equations `(11)` and `(15)` recover same sharp exponent as unconditioned physical
saddle barrier, now inside literal positive physical shell.

### Loop E: conditioned transversality closes Route E

`[FAILED AS A CLAIM]` The theorem constructs exact shell-conditioned operator and proves its
subpower-full determinant, but does not yet descend that operator to existing ordinary-integer
kernel, normalized coarse denominator, or co-moving friable/one-large-prime flux.  Calling RH
proved would be false.

## 9. New exact frontier

Named premise

`PHYSICAL-SHELL-CONDITIONED-GROWING-ODD-CUBE-TRANSVERSALITY`

is now discharged for positive Gaussian log-product shell `(8)`--`(10)`: determinant has exact
asymptotic `(13)` and retains alternating finite-volume signs, physical energy, every odd grade,
and critical recurrence frequency.

Remaining analytic Route E bridge is strictly narrower:

`SHELL-CONDITIONED-DETERMINANT-SOURCE-FAITHFUL-DESCENT`:

1. identify `(9)` with, or dominate it by, literal co-moving ordinary-integer Gibbs relation at
   \(x\asymp X_Y^{-1}\);
2. preserve normalized denominator of coarse defect rather than only \((P_Y^{\rm sh})^2\);
3. retain zero/one-large-prime seam charge under same descent;
4. prove resulting uncovered physical Gibbs mass is \(X^{1/2+o(1)}\).

No further unconditioned Euler capacity, generic frame mass, or coordinatewise replica projection
addresses these four tasks.

## 10. Novelty and anti-theatre audit

- Exact identities `(17)`--`(23)` are finite probability and linear algebra.
- PNT terminal moments are existing unconditional corpus inputs.
- New knowledge is synthesis: parity--energy Schur complement, invariance under positive Gaussian
  shell conditioning, exact Fourier preservation of growing odd cube, saddle-lock identity, and
  conditioned determinant asymptotic `(13)`.
- Result is not a repackaged RH equivalence.  It proves explicit asymptotic for finite prime Euler
  object without RH.
- It removes one previously open analytic premise and names remaining descent theorem without
  weakening it.
- No literature search, computation, Lean edit, or Lean build was performed.

## 11. Positive-Laplace descent wall and exact covariance survivor

A final hostile loop rules out simplest descent.

Let \(\nu\) be a nonnegative measure on \((0,\infty)\) for which

\[
 K_\nu(m)=\int_0^\infty e^{-mx}\,d\nu(x)
\tag{45}
\]

is finite.  If \(0<m_1\le m_2\), then \(e^{-m_2x}\le e^{-m_1x}\) pointwise, hence

\[
 \boxed{K_\nu(m_2)\le K_\nu(m_1).}
\tag{46}
\]

Thus every positive Laplace mixture is decreasing.  Centered Gaussian log shell

\[
 G_{X,\Delta}(m)
 =\exp\!\left(-\frac{(\log m-\log X)^2}{2\Delta^2}\right)
\tag{47}
\]

is strictly increasing on \(0<m<X\) and strictly decreasing on \(m>X\).  Therefore no nonzero
positive measure \(\nu\) satisfies \(K_\nu=G_{X,\Delta}\), even on any interval crossing \(X\).
More generally, no positive Laplace mixture can suppress low-product prefix while retaining
interior physical shell.

Consequently source-faithful descent from equation (9) cannot be a positivity-only Tauberian
averaging of raw kernels \(e^{-mx}\).  It must use signed scale differences, logarithmic
derivatives, or exact recurrence weights.

This creates unavoidable cross-shell problem.  For any signed shell decomposition

\[
 Z=\int Z_y\,d\alpha(y),\qquad M=\int M_y\,d\alpha(y),
\tag{48}
\]

one has exact polarization

\[
 |Z|^2-|M|^2
 =\iint\left(Z_y\overline{Z_z}-M_y\overline{M_z}\right)
       d\alpha(y)d\overline{\alpha}(z).
\tag{49}
\]

Diagonal estimates \(y=z\), including equation (13), do not bound off-diagonal integral.
Two-shell choice with opposite phases already cancels diagonal mass.  Required survivor is
therefore exact:

**RECURRENCE-WEIGHTED-SHELL-COVARIANCE-ACCUMULATION**:

prove a cofinal lower frame bound for kernel in equation (49) under literal recurrence weights and
prime-dilation intervals, while preserving alternating finite-volume signs and normalized Gibbs
denominator.  This is source-faithful content of
**SHELL-CONDITIONED-DETERMINANT-SOURCE-FAITHFUL-DESCENT**.

### Loop F: positive shell averaging descends to Laplace current

[CONJECTURE] Express Gaussian shell as positive mixture of raw Laplace scales and integrate
conditioned determinant.

[FALSIFIED] Monotonicity (46) excludes representation.  Even a signed representation leaves
off-diagonal covariance (49), so shellwise lower bounds cannot be summed independently.

Positive survivor (49) is not a restatement of RH: it is exact finite polarization identity
specifying additional cross-scale theorem required before any Mertens conclusion.
