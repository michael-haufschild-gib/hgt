# Formation cumulant chirality and involutive-selection law

- **ID:** ULF-FCRM-1
- **Stage:** 2-fully-proven
- **Type:** POSITIVE-JUMP FORMATION / INFORMATION-ARROW / INVOLUTIVE-SELECTION THEOREM
- **Source:** universal-law-field formation/properness and time-reversal likelihood mechanisms
- **Statement:** Every nontrivial positive-jump compound-Poisson Esscher family carries a strict
  information chronology: the sign of directed relative-entropy asymmetry reconstructs the order
  of every two formation parameters. The exchange-generated abelian-zeta-gas formation is an exact
  realization. Hence no two distinct source formations can be exchanged by an involution, and every
  finite-order law symmetry acting on the full formation family fixes its formation parameter.
- **Status:** `[PAPER-PROVED] [DEPENDENCY-CLOSED] [HOSTILE REVIEW PASSED]
  [INTERNAL FRONTIER AUDITED] [EXTERNAL PARENTS AUDITED] [MECHANISM FIRST]
  [POSITIVE-JUMP LEVY FORMATION] [INFORMATION CHRONOLOGY] [FINITE-SYMMETRY RIGIDITY]
  [CENTERED REVERSAL SELECTION]
  [BRIDGE] [NOVELTY UNVERIFIED] [NO LEAN YET] [NOT RH]`

## 1. Goal and higher pivot

The preceding global formation-properness theorem proves that a finite uniform bound on full source
Jeffreys work selects neutral formation. It does not produce that bound. The first conjecture for
this lane was therefore:

> source reversal or conservation automatically bounds the exchange-generated work.

This is false. The source work was proved proper precisely because every positive scale orbit has
unbounded work. A trace or conservation law cannot bound it without an additional compatibility
mechanism.

The stronger replacement retains the orientation discarded by Jeffreys symmetrization. For two
source laws \(P,Q\), define the directed information commutator

\[
 \chi(P,Q)=D(P\Vert Q)-D(Q\Vert P).
 \tag{FCRM.1}
\]

An involution exchanging \(P\) and \(Q\) forces \(\chi(P,Q)=0\). The live question is whether the
literal source-generated formation has a fixed nonzero sign. If so, reversal compatibility itself,
not an assumed energy bound, selects the neutral formation.

## 2. Internal frontier

`AbelianZetaGas.LawCommutator` proves that the source-marked schedule commutator generates the
fugacity translation

\[
 [S,H_u]=V_u:(\sigma,\tau)\longmapsto(\sigma,\tau+u).
 \tag{FCRM.2}
\]

The class law is

\[
 P_t(A)=Z(t)^{-1}\exp\bigl(-\sigma\log|A|-(\tau+t)Q(A)\bigr),
 \qquad Q(A)=\log|\operatorname{soc}A|,
 \tag{FCRM.3}
\]

with

\[
 Z(t)=\prod_{j\ge1}\zeta(j\sigma+\tau+t),
 \qquad \sigma>0,\quad \tau\ge0,\quad \sigma+\tau>1,\quad t\ge0.
 \tag{FCRM.4}
\]

The corpus already proves mutual absolute continuity, Radon--Nikodym and log-likelihood formulas,
integrability of \(Q\), the exact symmetric work

\[
 D(P_0\Vert P_u)+D(P_u\Vert P_0)
 =u\bigl(\mathbb E_0Q-\mathbb E_uQ\bigr),
 \tag{FCRM.5}
\]

and source-scale properness. `ConstitutiveTimeReversalLikelihoodCocycle` proves KL invariance under
measurable embeddings and the exact likelihood law of a measurable involution. No existing card
computes the antisymmetric directed difference for this source.

## 3. External parent boundary

- `[LITERATURE]` Relative entropy of an exponential family is the Bregman divergence of its log
  partition function. This is standard information geometry.
- `[LITERATURE]` Time-reversal entropy production is relative entropy between forward and reversed
  path laws: Maes--Netocny, *Time-Reversal and Entropy*, arXiv:cond-mat/0202501; Parrondo--van den
  Broeck--Kawai, *Entropy production and the arrow of time*, arXiv:0904.1573; Lopes--Mengue,
  *On information gain, Kullback-Leibler divergence, entropy production and the involution kernel*,
  arXiv:2003.02030.
- `[LITERATURE]` The Bregman commutator
  \(\frac12(D_F(x,y)-D_F(y,x))\) and its vanishing for quadratic generators are explicit in the
  supplementary material of *Alternating Mirror Descent* (NeurIPS 2022). Global symmetry of a
  Bregman divergence characterizes quadratic generators under standard regularity hypotheses.
- `[LITERATURE]` Compound-Poisson laws, their Lévy measures, cumulant formulas, and Esscher
  transforms are classical. Dello Schiavo, *Moments and Cumulants in Infinite Dimensions with
  Applications to Poisson, Gamma and Dirichlet--Ferguson Random Measures* (arXiv:1611.02208)
  develops the compound-Poisson cumulant parent; Qiu--Koor--Rebentrost, *The Quantum Esscher
  Transform* (arXiv:2401.07561), recalls the classical Esscher transform as the minimum-relative-
  entropy tilt before extending it.
- `[LITERATURE]` Choi, *Information geometry of Lévy processes and financial models*
  (arXiv:2507.23646), computes directed and dual Kullback--Leibler divergences for equivalent Lévy
  laws from their Lévy triplets. It occupies the general Lévy information-geometry receiver. The
  order reconstruction and finite-order symmetry consequences below are obtained here from the
  source's one-sided jump law; no priority claim is made for the surrounding machinery.

These parents occupy the abstract machinery. The source-specific residue is the exact sign and
cumulant formula forced by the abelian-group formation, and its incompatibility with involutive
realization of the generated central law.

## 4. General exponential-formation identities

Let \((\Omega,\mu)\) be a measure space, let \(Q\ge0\), and suppose

\[
 Z(t)=\int e^{-tQ}\,d\mu
 \tag{FCRM.6}
\]

is strictly positive and finite on \([0,u]\), with differentiation under the integral valid
through order three. Put

\[
 dP_t=Z(t)^{-1}e^{-tQ}\,d\mu,
 \quad F(t)=\log Z(t),
 \quad m(t)=\mathbb E_tQ,
 \quad V(t)=\operatorname{Var}_t(Q),
 \quad \kappa_3(t)=\mathbb E_t[(Q-m(t))^3].
 \tag{FCRM.7}
\]

Then standard differentiation gives

\[
 F'=-m,\qquad m'=-V,\qquad V'=-\kappa_3.
 \tag{FCRM.8}
\]

The two directed works are

\[
\begin{aligned}
 D(P_0\Vert P_u)&=F(u)-F(0)+u m(0),\\
 D(P_u\Vert P_0)&=F(0)-F(u)-u m(u).
\end{aligned}
\tag{FCRM.9}
\]

Consequently their sum and difference obey

\[
 \boxed{J(u)=u\int_0^u V(t)\,dt,}
 \tag{FCRM.10}
\]

and

\[
\begin{aligned}
 \chi(u)
 &=u(m(0)+m(u))-2\int_0^u m(t)\,dt\\
 &=\int_0^u(u-2t)V(t)\,dt\\
 &=\boxed{\int_0^u t(u-t)\kappa_3(t)\,dt.}
\end{aligned}
\tag{FCRM.11}
\]

Thus Jeffreys work is integrated second response, while its directed orientation is integrated
third response. Together they reconstruct both directed costs:

\[
 D(P_0\Vert P_u)=\frac{J(u)+\chi(u)}2,
 \qquad
 D(P_u\Vert P_0)=\frac{J(u)-\chi(u)}2.
 \tag{FCRM.12}
\]

#### Proof

Differentiating \(Z\) gives

\[
 Z'=-Z\mathbb E_tQ,qquad
 Z''=Z\mathbb E_tQ^2,qquad
 Z'''=-Z\mathbb E_tQ^3.
\]

The quotient rule therefore gives \(F'=Z'/Z=-m\) and
\(F''=\mathbb E_tQ^2-m^2=V\). Differentiating once more and expanding the centered cube gives

\[
 F'''=-\mathbb E_tQ^3+3m\mathbb E_tQ^2-2m^3=-\kappa_3.
\]

Hence \(m'=-V\) and \(V'=-\kappa_3\), proving (FCRM.8). The density ratio is

\[
 \log\frac{dP_0}{dP_u}=uQ+F(u)-F(0),
\]

and its negative is \(\log(dP_u/dP_0)\). Integrating under the appropriate laws gives
(FCRM.9). Their sum is

\[
 u(m(0)-m(u))=u\int_0^uV(t)\,dt,
\]

which proves (FCRM.10). Their difference is

\[
 2(F(u)-F(0))+u(m(0)+m(u))
 =u(m(0)+m(u))-2\int_0^um(t)\,dt.
\]

Substitute \(m(t)=m(0)-\int_0^tV(s)\,ds\) and apply Fubini to obtain
\(\int_0^u(u-2t)V(t)\,dt\). Finally set \(g(t)=t(u-t)\). Since
\(g'(t)=u-2t\), \(g(0)=g(u)=0\), and \(V'=-\kappa_3\), integration by parts gives

\[
 \int_0^u(u-2t)V(t)\,dt
 =-\int_0^ug(t)V'(t)\,dt
 =\int_0^ut(u-t)\kappa_3(t)\,dt.
\]

This proves (FCRM.11); solving the two linear equations for the directed divergences proves
(FCRM.12). QED.

## 5. Positive-jump formation chirality

The mechanism does not depend on primes or finite groups. It is a one-sided Lévy law.

### Theorem 5.1 -- positive-jump formation law

Let \(\nu\) be a nonzero finite positive Borel measure on \((0,\infty)\) satisfying
\(\int x^3\,d\nu(x)<\infty\). Let \(P_0\) be its compound-Poisson law, characterized by

\[
 \log\mathbb E_0e^{-tQ}
 =\int_{(0,\infty)}(e^{-tx}-1)\,d\nu(x),
 \qquad t\ge0,
 \tag{FCRM.13}
\]

and let \(P_t\) be its Esscher tilt by \(e^{-tQ}\). Then

\[
 \boxed{\kappa_3(t)=\int x^3e^{-tx}\,d\nu(x)>0,}
 \tag{FCRM.14}
\]

and for every \(u>0\),

\[
 \boxed{
 D(P_0\Vert P_u)-D(P_u\Vert P_0)
 =\int K(ux)\,d\nu(x)>0,}
 \tag{FCRM.15}
\]

where the universal formation kernel is

\[
 \boxed{K(a)=a-2+(a+2)e^{-a}.}
 \tag{FCRM.16}
\]

#### Proof

The log Laplace transform in (FCRM.13) is three times differentiable by dominated convergence:
for \(t\ge0\), its third differentiated integrand is \(-x^3e^{-tx}\), dominated by \(x^3\).
The general identities of Section 4 give (FCRM.14). Tonelli's theorem and (FCRM.11) give

\[
 \chi(u)=\int\!\left(\int_0^u t(u-t)x^3e^{-tx}\,dt\right)d\nu(x).
\]

After the change of variables \(y=tx\), the inner integral is

\[
 \int_0^{ux}y(ux-y)e^{-y}\,dy=ux-2+(ux+2)e^{-ux}=K(ux).
\]

Now \(K(0)=0\) and

\[
 K'(a)=1-(a+1)e^{-a}>0\qquad(a>0),
\]

because \(e^a>1+a\) for \(a>0\). Thus \(K(a)>0\) on \((0,\infty)\). Since \(u>0\) and
\(\nu\) is nonzero and supported on \((0,\infty)\), the integral in (FCRM.15) is strictly
positive. QED.

This is the higher law: a positive-jump formation has an intrinsic information arrow. Gaussian
and other quadratic formations fail because their Lévy carrier has no positive-jump third response,
not because positivity alone is insufficiently strong.

### Theorem 5.2 -- pairwise information chronology

The third-moment hypothesis of Theorem 5.1 is unnecessary for pairwise orientation. Assume only
that \(\nu\) is a nonzero finite positive Borel measure on \((0,\infty)\) with finite first moment,
and define its admitted Esscher domain

\[
 I_\nu=\left\{t\in\mathbb R:
 \int (1+x)e^{-tx}\,d\nu(x)<\infty\right\}.
 \tag{FCRM.16a}
\]

For every \(t\in I_\nu\), let \(P_t\) be the Esscher formation of the compound-Poisson law with
Lévy measure \(\nu\). For any \(s,t\in I_\nu\),

\[
 \boxed{
 \chi(s,t):=D(P_s\Vert P_t)-D(P_t\Vert P_s)
 =\int e^{-sx}K((t-s)x)\,d\nu(x).}
 \tag{FCRM.16b}
\]

Consequently,

\[
 \boxed{
 s<t\quad\Longleftrightarrow\quad
 D(P_s\Vert P_t)>D(P_t\Vert P_s).}
 \tag{FCRM.16c}
\]

Thus directed relative entropy reconstructs the complete order of the formation parameter. It is
not merely a nonzero local tensor at the neutral law.

#### Proof

Write

\[
 F(t)=\log\mathbb E_0e^{-tQ}
 =\int(e^{-tx}-1)\,d\nu(x),
 \qquad
 m(t)=\mathbb E_tQ=\int xe^{-tx}\,d\nu(x).
\]

The definition of \(I_\nu\) makes both quantities finite. The strictly positive Esscher density
gives mutual absolute continuity, and direct integration of its log likelihood gives

\[
 D(P_s\Vert P_t)=F(t)-F(s)+(t-s)m(s),
\]

\[
 D(P_t\Vert P_s)=F(s)-F(t)-(t-s)m(t).
\]

Subtracting and then integrating coefficientwise yields

\[
\begin{aligned}
 \chi(s,t)
 &=2(F(t)-F(s))+(t-s)(m(s)+m(t))\\
 &=\int e^{-sx}
 \bigl[(t-s)x-2+((t-s)x+2)e^{-(t-s)x}\bigr]\,d\nu(x)\\
 &=\int e^{-sx}K((t-s)x)\,d\nu(x).
\end{aligned}
\]

If \(s<t\), every factor \(e^{-sx}\) is positive and Theorem 5.1 proved
\(K((t-s)x)>0\) for every \(x>0\). Since \(\nu\ne0\), the integral is strictly positive. If
\(s=t\), it is zero. If \(s>t\), antisymmetry
\(\chi(s,t)=-\chi(t,s)\) makes it strictly negative. This proves (FCRM.16c). QED.

## 6. Abelian-zeta-gas realization

### Theorem 6.1 -- source Lévy measure and strict chirality

The socle observable under \(P_0\) is compound Poisson with the discrete Lévy measure

\[
 \boxed{
 \nu_{\sigma,\tau}
 =\sum_p\sum_{j\ge1}\sum_{k\ge1}
 \frac{p^{-k(j\sigma+\tau)}}{k}\,\delta_{k\log p}.}
 \tag{FCRM.17}
\]

This measure is finite, nonzero, and has finite moments of every fixed order. In particular, the
third cumulant exists and has the absolutely convergent expansion

\[
 \boxed{
 \kappa_3(t)=
 \sum_{p}\sum_{j\ge1}(\log p)^3
 \frac{r_{p,j}(t)(1+r_{p,j}(t))}{(1-r_{p,j}(t))^3}>0,}
 \tag{FCRM.18}
\]

where

\[
 r_{p,j}(t)=p^{-(j\sigma+\tau+t)}.
 \tag{FCRM.19}
\]

The series and the first three differentiated log-partition series converge locally uniformly for
\(t\ge0\). Consequently,

\[
 \boxed{u>0\Longrightarrow
 D(P_0\Vert P_u)>D(P_u\Vert P_0).}
 \tag{FCRM.20}
\]

#### Proof

For a fixed prime-depth mode \((p,j)\), put \(\lambda_p=\log p\) and
\(r=r_{p,j}(t)\). Its occupation number \(N_{p,j}\) has geometric law

\[
 \Pr(N_{p,j}=n)=(1-r)r^n,\qquad n\ge0.
\]

The mode contribution to the log partition function is

\[
 \phi_{p,j}(t)=-\log(1-r_{p,j}(t)).
\]

Since \(r'=-\lambda_pr\), direct differentiation gives

\[
 \phi'=-\lambda_p\frac r{1-r},\qquad
 \phi''=\lambda_p^2\frac r{(1-r)^2},\qquad
 \phi'''=-\lambda_p^3\frac{r(1+r)}{(1-r)^3}.
 \tag{FCRM.21}
\]

These are respectively minus the mean, the variance, and minus the third cumulant of
\(\lambda_pN_{p,j}\).

It remains to justify summation and differentiation. Put \(s=\sigma+\tau>1\). For every
\(p,j,t\) in the stated range,

\[
 0<r_{p,j}(t)\le p^{-(j\sigma+\tau)}\le2^{-s}<\frac12.
\]

Thus all factors \((1-r)^{-k}\), \(k\le3\), and \(1+r\) are uniformly bounded. Moreover,

\[
 \sum_{j\ge1}p^{-(j\sigma+\tau)}
 =\frac{p^{-s}}{1-p^{-\sigma}}
 \le\frac{p^{-s}}{1-2^{-\sigma}}.
 \tag{FCRM.22}
\]

For \(k=0,1,2,3\), the absolute values of the \(k\)-th differentiated summands are therefore
bounded by a constant depending only on \(\sigma,\tau,k\), times
\((\log p)^k p^{-(j\sigma+\tau)}\). The prime sum

\[
 \sum_p(\log p)^k p^{-s}
\]

converges: choose \(0<\varepsilon<s-1\), use \((\log n)^k\le C_{k,\varepsilon}n^\varepsilon\),
and dominate by \(\sum_{n\ge2}n^{-(s-\varepsilon)}\). The Weierstrass test gives local uniform
convergence through order three. Hence

\[
 F(t)=\sum_{p,j}\phi_{p,j}(t),\qquad
 -F'''(t)=\sum_{p,j}\lambda_p^3\frac{r_{p,j}(t)(1+r_{p,j}(t))}{(1-r_{p,j}(t))^3}.
\]

Every summand is strictly positive and there is at least one mode, proving (FCRM.18). The
class-space observable \(Q=\log|\operatorname{soc}A|\) is the almost-sure finite sum
\(\sum_{p,j}\lambda_pN_{p,j}\); the canonical classification of finite abelian groups identifies
the class law with the pushforward of the product mode law. Thus \(-F'''(t)\) is precisely its
third cumulant. Moreover, \(dP_t/dP_0\) is a function of \(Q\) alone. Hence \(Q\) is sufficient
for the entire one-parameter formation: the conditional law given \(Q\) is independent of \(t\),
and the full class-law directed KL divergences equal those of the \(Q\)-marginals. The calculation
therefore proves strict chirality for the full source laws, not merely for a reporter.

For completeness, the geometric Laplace transform also identifies the claimed Lévy measure:

\[
 \log\mathbb E_0e^{-t\lambda_pN_{p,j}}
 =\log\frac{1-r_{p,j}(0)}{1-r_{p,j}(0)e^{-t\lambda_p}}
 =\sum_{k\ge1}\frac{r_{p,j}(0)^k}{k}(e^{-tk\lambda_p}-1).
\]

Summing over modes gives (FCRM.17). Finiteness of its mass follows from convergence of
\(\sum_{p,j}-\log(1-r_{p,j}(0))\), already supplied by the same majorant; its third moment is
exactly (FCRM.18) at \(t=0\). Thus Theorem 5.1 applies directly. Equivalently, substitution into
(FCRM.11) yields

\[
 \chi(u)=\int_0^u t(u-t)\kappa_3(t)\,dt>0
\]

for \(u>0\), because the integrand is continuous and strictly positive on \((0,u)\). QED.

### Corollary 6.2 -- exact source chronology on the full convergence chamber

For fixed \(\sigma>0\) and \(\tau\ge0\) with \(\sigma+\tau>1\), the complete admitted source
coefficient-defined convergence interval and the literal nonnegative-chemical-potential source
interval are respectively

\[
 J_{\sigma,\tau}=(1-\sigma-\tau,\infty),
 \qquad
 I_{\sigma,\tau}=J_{\sigma,\tau}\cap[-\tau,\infty).
 \tag{FCRM.22a}
\]

For every \(s<t\) in \(J_{\sigma,\tau}\), the coefficient-defined abelian-group class laws satisfy

\[
\boxed{
 D(P_s\Vert P_t)-D(P_t\Vert P_s)
 =\sum_p\sum_{j\ge1}\sum_{k\ge1}
 \frac{p^{-k(j\sigma+\tau+s)}}{k}
 K\bigl((t-s)k\log p\bigr)>0.}
 \tag{FCRM.22b}
\]

#### Proof

Multiplying the atom of (FCRM.17) at \(k\log p\) by its Esscher factor
\(e^{-sk\log p}\) gives the displayed coefficient. For \(s>1-\sigma-\tau\), the least exponent
\(\sigma+\tau+s\) exceeds one. The same prime-Dirichlet majorant used in Theorem 6.1 therefore
proves convergence of the mass and first-moment series, so \(s,t\in I_{\nu_{\sigma,\tau}}\).
Theorem 5.2 gives the equality and strict sign. Conversely, at or left of the boundary of
\(J_{\sigma,\tau}\), the least-depth zeta factor is outside the absolute convergence chamber, so
this coefficient-defined probability formation is not admitted. Intersecting with
\(\tau+t\ge0\) gives the literal source interval \(I_{\sigma,\tau}\) used by the existing source
parameter type. QED.

## 7. Involutive-selection theorem

### Theorem 7.1 -- pairwise involutive selection

Let \(s,t\in I_{\sigma,\tau}\), and let \(\Theta\) be a measurable involution of the
finite-abelian-group class space. If

\[
 \Theta_*P_s=P_t,
 \tag{FCRM.23}
\]

then \(s=t\). Conversely, at \(s=t\), the identity involution works. Therefore

\[
 \boxed{
 \exists\Theta,\ \Theta^2=1,\ \Theta_*P_s=P_t
 \quad\Longleftrightarrow\quad s=t.}
 \tag{FCRM.24}
\]

In particular, if \(c-a,c+a\in I_{\sigma,\tau}\) and \(a\ge0\), then

\[
 \boxed{
 \Theta_*P_{c-a}=P_{c+a},\quad \Theta^2=1
 \quad\Longrightarrow\quad a=0.}
 \tag{FCRM.25}
\]

This is the centered-reversal statement missing from the earlier neutral-to-displaced formulation.

#### Proof

Involutivity gives \(\Theta_*P_t=P_s\). Invariance of relative entropy under a measurable
bijection gives

\[
 D(P_s\Vert P_t)
 =D(\Theta_*P_s\Vert\Theta_*P_t)
 =D(P_t\Vert P_s).
\]

Corollary 6.2 says this equality is impossible when \(s\ne t\). Hence \(s=t\). The identity map
supplies the converse. Substituting \(s=c-a\), \(t=c+a\) gives \(a=0\). QED.

### Theorem 7.2 -- finite-order formation-symmetry rigidity

Let \(I\subseteq I_{\sigma,\tau}\) be an interval. Suppose a measurable bijection \(\Theta\) of
the class space and a map \(\varphi:I\to I\) satisfy

\[
 \Theta_*P_t=P_{\varphi(t)}\qquad(t\in I).
 \tag{FCRM.26}
\]

Then \(\varphi\) is strictly increasing. If \(\Theta^N=1\) for some integer \(N\ge1\), then

\[
 \boxed{\varphi=\operatorname{id}_I.}
 \tag{FCRM.27}
\]

Thus a finite-order source symmetry cannot reverse, permute, or translate positive-jump formation
time. It fixes every admitted formation law.

#### Proof

For \(s<t\), Corollary 6.2 gives \(\chi(s,t)>0\). KL invariance under \(\Theta\) gives

\[
 \chi(s,t)=\chi(\varphi(s),\varphi(t)).
\]

The order reconstruction (FCRM.16c) therefore implies \(\varphi(s)<\varphi(t)\), so \(\varphi\)
is strictly increasing. If \(\Theta^N=1\), iteration of (FCRM.26) gives
\(P_{\varphi^N(t)}=P_t\). The source family is injective because Corollary 6.2 separates every
two distinct parameters. Hence \(\varphi^N(t)=t\).

If \(\varphi(t)>t\), strict monotonicity yields
\(t<\varphi(t)<\cdots<\varphi^N(t)=t\), a contradiction. The case \(\varphi(t)<t\) is identical
with reversed inequalities. Therefore \(\varphi(t)=t\) for every \(t\in I\). QED.

## 8. Hostile conjecture loops

### Loop A -- bounded conservation

**Conjecture.** Source conservation automatically bounds \(J(d^nu)\).

**Verdict:** `[FALSIFIED]`. The Lean-certified formation-properness theorem proves the opposite:
for \(u>0\), reporter work and full source work cannot have a finite uniform scale bound.

**Stronger survivor.** Retain the directed pair rather than its symmetric sum. Reversal predicts
equality of directions, while source skewness may force a strict orientation.

### Loop B -- universal positive chirality

**Conjecture.** Every nontrivial exponential formation has \(\chi(u)>0\).

**Verdict:** `[FALSIFIED]`. A Gaussian location family has quadratic log partition, zero third
cumulant, and symmetric KL at distinct parameters. Other exponential families can have changing
third-cumulant sign.

**Stronger survivor.** Chirality is not a generic positivity axiom. It is a source-generated
orientation determined by the sign of the third response. The abelian zeta gas must prove its sign
from literal geometric modes.

### Loop C -- Jeffreys work alone

**Conjecture.** Symmetric work detects reversal compatibility.

**Verdict:** `[FALSIFIED]`. Jeffreys work is invariant under exchange of its arguments and therefore
forgets the arrow required to obstruct a reversal. It proves properness but not chirality.

**Stronger survivor.** The pair \((J,\chi)\), equivalently the two directed works, is the minimal
information packet. Its second/third-cumulant hierarchy is reconstruction, not another scalar
observer.

### Loop D -- source star already closes selection

**Conjecture.** The existing gas adjoint automatically exchanges \(P_0,P_u\).

**Verdict:** `[FALSIFIED]`. `GasStar` reverses algebra words while preserving the fixed real Gibbs
weights. It does not push one chemical-potential law to another. A parameter-changing involution is
additional constitutive data.

**Positive survivor.** The theorem is an exact falsifier: any future source-reflection proposal
that claims to exchange a nonzero generated formation must either fail involutivity, fail law
transport, or erase the source chirality under a non-sufficient observer.

### Loop E -- arbitrary infinitely divisible formation

**Conjecture.** Infinite divisibility alone fixes the information arrow.

**Verdict:** `[FALSIFIED]`. A Gaussian infinitely divisible law has quadratic log Laplace transform
and zero commutator. A two-sided jump measure can have cancelling or sign-changing odd cumulants.

**Stronger survivor.** The load-bearing structure is the source-derived positive-jump cone:
\(\nu\ne0\) and \(\operatorname{supp}\nu\subset(0,\infty)\). This condition is not added to rescue
the source; (FCRM.17) derives it coefficientwise from the Euler product.

### Loop F -- observer reversal

**Conjecture.** An involution after an arbitrary observer still selects neutrality.

**Verdict:** `[FALSIFIED]`. Data processing may erase directed KL asymmetry. A constant observer is
reversible for every \(u\).

**Positive survivor.** Theorem 7.1 is native to the full source law. A receiver inherits it only
through an information-sufficient comparison, making loss of selection an exact observer defect.

### Loop G -- neutral-to-displaced reversal

**Conjecture.** It is enough to obstruct an involution exchanging \(P_0\) and \(P_u\).

**Verdict:** `[FALSIFIED AS RH TYPING]`. Functional-equation reflection should exchange two
centered endpoints, not the center with one displaced endpoint. The earlier theorem was correct but
its proposed RH interface was misaligned.

**Stronger survivor.** The pairwise kernel formula (FCRM.16b) orients every admitted pair, so the
centered exchange \(P_{c-a}\leftrightarrow P_{c+a}\) forces \(a=0\). The same order reconstruction
proves the stronger finite-order rigidity theorem. This is a representation change, not an added
route hypothesis.

### Loop H -- arbitrary symmetry order

**Conjecture.** Every source symmetry acts trivially on formation time.

**Verdict:** `[FALSIFIED]`. KL invariance forces the induced parameter map only to be increasing;
infinite-order increasing maps need not be the identity.

**Positive survivor.** Finite order is load-bearing and source-natural for reflection. An increasing
finite-order self-map of an interval is exactly the identity, yielding Theorem 7.2.

## 9. Fourth-organ prediction

The real Esscher, Fisher, and time-reversal organs cannot all be represented by a nontrivially
reversible positive-jump formation interval. If a fourth KMS, modular, or reflected-path
realization transports the same source laws and their directed relative entropies faithfully, its
parameter action must preserve the chronology (FCRM.16c). Any finite-order realization must act
trivially by Theorem 7.2; a centered involution therefore selects zero displacement.

This predicts a concrete audit test for any proposed reflected arithmetic completion: compute its
two directed formation costs. Equality off neutrality proves that the realization has forgotten
the literal source formation or is not information-faithful.

## 10. RH boundary

No RH statement follows from (FCRM.25) alone. An RH application would still need a pre-zero,
coefficient-faithful comparison which:

1. sends reflection-paired physical displacements to a generated gas-formation pair;
2. realizes functional-equation reflection as an involution exchanging their source laws;
3. preserves the directed information packet before divisor specialization.

Unlike bilateral summability or a postulated uniform work bound, these requirements are
transformation laws and can be attacked before asking where zeros lie. They are not constructed in
this card.

## 11. Gates

- [x] 0 -> 1: exact source, exact conjecture, internal audit, external parents, hostile loops.
- [x] 1 -> 2: positive-jump kernel, pairwise chronology, source Lévy realization, centered
  involutive selection, and finite-order symmetry rigidity closed under hostile review.
- [ ] 2 -> 3: formalize the exact paper theorem with no additional hypothesis or project axiom.
- [ ] 3 -> 4: publication/priority audit and standalone exposition.

## 12. Log

- 2026-08-11 -- automatic bounded conservation falsified by source properness; pivoted to directed
  formation chirality.
- 2026-08-11 -- extracted exact second/third-cumulant reconstruction identities and the proposed
  involutive-selection theorem.
- 2026-08-11 -- closed the geometric-mode third-cumulant expansion by a uniform Dirichlet majorant;
  obtained strict source chirality and the involutive-selection equivalence.
- 2026-08-11 -- hostile RH-typing audit killed the neutral-to-displaced reflection interface.
  Replaced it by the first-moment pairwise kernel law, full source-parameter chronology, centered
  reversal selection, and finite-order formation-symmetry rigidity.
