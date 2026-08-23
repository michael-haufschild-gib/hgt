# Route U: Cayley–Chebyshev positive-root criterion

**Status:** `[FORMALIZED] [BRIDGE] [UNCONDITIONAL] [NO COMPUTATION] [NOT RH]`

**Hostile verdict:** `REDISCOVERED/BRIDGE`. The detecting sequence is a new local reduction in
Route U, but its Cayley mechanism and source arithmetic lie inside generalized
Bombieri--Lagarias/Li theory. It is not candidate-new scientific knowledge.

## Result

Let \(q\) range over the actual nontrivial divisor of the completed Riemann \(\xi\)-function, with divisor multiplicity, and put
\[
  u_q:=\operatorname{xiResolventPoint}(1,q)
      =\frac{1}{1+\operatorname{xiSpectralPoint}(q)^2}.
\]
For \(n\ge 0\), define
\[
  p_n(X):=T_n(2X-1),
  \qquad
  C_n:=\Re\sum_q u_q\,p_n(u_q)^2,
\]
where \(T_n\) is the degree-\(n\) Chebyshev polynomial of the first kind.

Then
\[
  \boxed{\quad \mathrm{RH}\quad\Longleftrightarrow\quad
  (\forall n\ge0)\; C_n\ge0.\quad}
\]

This is not a proof of RH. It replaces Route U's quantification over all real polynomial squares by one explicit polynomial square in each degree. Those polynomials have an explicit positive-root source transform.

## Exact generalized-Li collision

Put \(\alpha_q=\operatorname{xiSpectralPoint}(q)\) and
\[
 y_q=\frac{1+i\alpha_q}{1-i\alpha_q}.
\]
Functional-equation reflection sends \(\alpha_q\) to \(-\alpha_q\) and hence \(y_q\) to
\(y_q^{-1}\). Let \(\ell_m\) be the multiplicity-exact, reflection-paired generalized Li sum
\[
 \ell_m=\sum_q\bigl(1-(-y_q)^m\bigr).
\]
This is the \(\tau=2\) Li coordinate after translating the zero variable by \(1/2\): if
\(z=\rho+1/2=1+i\alpha\), then
\[
 \frac{z}{z-2}=-\frac{1+i\alpha}{1-i\alpha}=-y.
\]

For every reflected pair \(y,y^{-1}\), algebra gives
\[
 u=\frac{2+y+y^{-1}}4,
 \qquad
 T_n(2u-1)^2=\frac{2+y^{2n}+y^{-2n}}4.
\]
Consequently
\[
 \boxed{\quad C_0=\frac{\ell_1}{2},\qquad
 C_n=\frac{\ell_{2n+1}-2\ell_{2n}+\ell_{2n-1}+2\ell_1}{8}
 \quad(n\ge1).\quad}
\]
Thus the criterion is an exact positive trigonometric stencil in the generalized Li chart. Its
maximal-shell converse is the Bombieri--Lagarias exterior-Cayley mechanism with a different
positive detecting kernel, not a source proof beyond that parent theory.

## Inputs already established in the corpus

For the actual shift-one \(\xi\)-resolvent divisor:

1. \(u_q\ne0\), \(\sum_q|u_q|<\infty\), \(|u_q|\le1\), and \(\Re u_q>0\).
2. For each \(r>0\), only finitely many \(q\) satisfy \(|u_q|\ge r\).
3. Divisor conjugation sends \(u_q\) to \(\overline{u_q}\), preserving multiplicity.
4. An off-critical divisor point gives \(\Im u_q\ne0\).
5. RH is equivalent to every \(u_q\) being real; with the preceding bounds, every such real node lies in \((0,1]\).

Absolute convergence of every \(C_n\) follows because \(p_n\) is a fixed polynomial and the nodes lie in the closed unit disk.

## Forward implication

Assume RH. Every \(u_q\in(0,1]\), and \(p_n(u_q)\in\mathbb R\). Hence
\[
  u_qp_n(u_q)^2\ge0
\]
term by term. Absolute convergence gives \(C_n\ge0\) for every \(n\).

## Converse: maximal Green shell

Assume an off-critical divisor point exists. Then some \(u_q\notin[0,1]\).

On \(\mathbb C\setminus[0,1]\), choose the exterior Joukowski coordinate
\[
  \Phi(z):=2z-1+\sqrt{(2z-1)^2-1}
          =2z-1+2\sqrt{z(z-1)},
\]
with the branch characterized by \(|\Phi(z)|>1\). It satisfies
\[
  T_n(2z-1)=\frac{\Phi(z)^n+\Phi(z)^{-n}}2.
\]
On \([0,1]\), \(|T_n(2x-1)|\le1\).

As \(z\to0\) through \(\mathbb C\setminus[0,1]\), \(|\Phi(z)|\to1\). Since the \(u_q\) tend cofinitely to \(0\), the set of values \(|\Phi(u_q)|>1+\varepsilon\) is finite for every \(\varepsilon>0\). Therefore
\[
  R:=\max_{q:\,u_q\notin[0,1]}|\Phi(u_q)|>1
\]
exists. Let \(M\) be the finite maximal shell where \(|\Phi(u_q)|=R\), counted with divisor multiplicity.

For a shell node,
\[
  u_qp_n(u_q)^2
  =\frac{u_q}{4}
    \left(\Phi(u_q)^{2n}+2+\Phi(u_q)^{-2n}\right).
\]
Finite separation from the next exterior shell, absolute summability of the nodes, and the bound on \([0,1]\) give
\[
  R^{-2n}C_n
  =\frac14 b_n+o(1),
\]
where
\[
  b_n:=\Re\sum_{q\in M}
  u_q\left(\frac{\Phi(u_q)}R\right)^{2n}.
\]

Thus \(b_n\) is a finite real trigonometric sequence.

### Mean zero

No maximal-shell phase equals \(1\). Indeed,
\[
  \left(\frac{\Phi(u_q)}R\right)^2=1
\]
would make \(\Phi(u_q)\) real, hence \(u_q\) real and outside \([0,1]\). This is impossible because \(\Re u_q>0\) and \(|u_q|\le1\) force every real \(u_q\) into \((0,1]\). Consequently every exponential in \(b_n\) has Cesàro mean zero, so \(b_n\) has Cesàro mean zero.

### The leading sequence cannot vanish identically

The only possible collision of squared phases is
\[
  \Phi(v)^2=\Phi(u)^2
  \quad\Longrightarrow\quad
  v=u\ \text{ or }\ v=1-u.
\]
The first case follows from injectivity of the exterior Joukowski coordinate. In the second, \(\Phi(v)=-\Phi(u)\), and inversion of the Joukowski map gives \(2v-1=-(2u-1)\).

After grouping an \(u\)-node of multiplicity \(m>0\) with a possible \((1-u)\)-node of multiplicity \(m'\ge0\), its phase coefficient is
\[
  mu+m'(1-u)=(m-m')u+m'.
\]
It cannot vanish for nonreal \(u\): if \(m=m'\), it equals \(m\); if \(m\ne m'\), vanishing would force \(u=-m'/(m-m')\in\mathbb R\). Conjugation symmetry pairs the remaining frequencies and coefficients, so taking the real part cannot erase a nonzero group. Hence \(b_n\) is not identically zero.

### Sign recurrence

Let \(K\) be the compact orbit closure of the finitely many shell phases in their product torus. The sequence \(b_n\) is the restriction to a dense cyclic orbit of a continuous real function \(b\) on \(K\). Haar integration on \(K\) gives \(\int_K b=0\). Since \(b\) is not identically zero, it cannot be nonnegative on \(K\); therefore \(b<-\delta\) on some nonempty open subset of \(K\), for some \(\delta>0\). Recurrence of the cyclic rotation visits that subset infinitely often. Along that subsequence,
\[
  b_n<-\delta.
\]
Since \(R^{-2n}C_n=\frac14b_n+o(1)\), this forces \(C_n<0\) for infinitely many \(n\), contradicting \(C_n\ge0\) for all \(n\).

Therefore no off-critical divisor point exists, proving RH.

## Exact Route U source handoff

Define the degree-\(n\) source polynomial
\[
  Q_n(W):=(1+W)^nT_n\!\left(\frac{1-W}{1+W}\right).
\]
It obeys
\[
  \frac{Q_n(W)}{(1+W)^n}
  =p_n\!\left(\frac1{1+W}\right).
\]
Its roots are all positive and explicit:
\[
  W_{n,k}=\tan^2\!\left(\frac{(2k-1)\pi}{4n}\right),
  \qquad 1\le k\le n.
\]
Indeed, the roots of \(T_n\) are \(\cos((2k-1)\pi/(2n))\), and solving
\[
  \frac{1-W}{1+W}=\cos\theta
\]
gives \(W=\tan^2(\theta/2)>0\).

The established C43 Gamma transmutation therefore specializes to
\[
  C_n
  =\Re\frac1{(2n)!}
   \int_0^\infty t^{2n}e^{-t}\,\mathcal H_{Q_n}(t)\,dt.
\]
Consequently RH is equivalent to the single explicit source inequality
\[
  \Re\int_0^\infty t^{2n}e^{-t}\,\mathcal H_{Q_n}(t)\,dt\ge0
\]
for every \(n\ge0\).

On the real spectral line, the corresponding rational square is
\[
  \frac{Q_n(x^2)^2}{(1+x^2)^{2n+1}}
  =\frac1{1+x^2}
   T_n\!\left(\frac{1-x^2}{1+x^2}\right)^2
  =\frac{\cos^2(2n\arctan x)}{1+x^2}.
\]

For the Fourier convention
\(\widehat f(\xi)=\int_{\mathbb R}f(x)e^{-i\xi x}\,dx\), its transform is, for \(n\ge1\),
\[
 \boxed{\quad
 \widehat F_n(\xi)=\frac{\pi}{4}e^{-|\xi|}
 \left(2+L_{2n}^{(-1)}(2|\xi|)\right),
 \qquad
 F_n(x)=\frac{\cos^2(2n\arctan x)}{1+x^2}.
 \quad}
\]
Indeed, with \(Y=(1+ix)/(1-ix)\),
\(F_n=(2+Y^{2n}+Y^{-2n})/[4(1+x^2)]\). For \(m\ge1\), residue evaluation or the Gamma integral
for \((1-ix)^{-k}\) gives
\[
 \widehat{\frac{Y^m}{1+x^2}}(\xi)
 =\begin{cases}
 \pi(-1)^m e^{-\xi}L_m^{(-1)}(2\xi),&\xi>0,\\
 0,&\xi<0,
 \end{cases}
\]
and the inverse power supplies the reflected half-line. This is the associated-Laguerre prime
kernel already characteristic of arithmetic formulas for generalized Li coefficients.

The kernel is not coefficientwise positive. At the first nontrivial hostile test,
\[
 2+L_4^{(-1)}(6)=-4.
\]
Therefore von-Mangoldt positivity cannot orient the source term prime by prime. Any closure must
retain valuation-summed prime--Gamma compensation.

## Full valuation towers still have both signs

The first failure does not disappear after summing every prime-power depth. For a prime \(p\), put

\[
 S_2(p):=\sum_{e\ge1}p^{-3e/2}
 \left(2+L_4^{(-1)}(2e\log p)\right).
\]

This is, up to the fixed positive factor \((\log p)/4\), the complete \(p\)-tower occurring in
the prime face of the explicit formula for \(F_2\). The source formula itself carries the opposite
overall sign. The exact local towers satisfy

\[
 \boxed{S_2(7)>0,\qquad S_2(19)<0.}
\]

Hence neither sign convention makes all completed local prime towers positive.

### Proof

Set

\[
 f(t):=2+L_4^{(-1)}(2t)
 =2-2t+6t^2-4t^3+\frac23t^4
 =\frac23t^2(t-3)^2-2t+2.                         \tag{1}
\]

We first record elementary logarithmic bounds without decimal or numerical evaluation. The
exponential series gives

\[
 e<1+1+\frac12+\frac16+\frac1{24}\sum_{j\ge0}4^{-j}
 =\frac{49}{18}<\frac{11}{4},
 \qquad e^{1/10}>1+\frac1{10}=\frac{11}{10}.       \tag{2}
\]

Consequently

\[
 e^{19/10}<\frac{(11/4)^2}{11/10}=\frac{55}{8}<7,
 \qquad
 e^{29/10}<\frac{(11/4)^3}{11/10}=\frac{605}{32}<19. \tag{3}
\]

Also \(e^2>7\), because its exponential series through degree four equals \(7\) and the tail is
strictly positive, while

\[
 e^3>\sum_{k=0}^{6}\frac{3^k}{k!}=\frac{1553}{80}>19. \tag{4}
\]

Thus

\[
 \frac{19}{10}<\log7<2,
 \qquad
 \frac{29}{10}<\log19<3.                              \tag{5}
\]

On \([19/10,2]\), equation (1) gives \(f'<0\), so

\[
 f(\log7)>f(2)=\frac23>0.                              \tag{6}
\]

For \(t\ge19/5\),

\[
 f'(t)=\frac43t(t-3)(2t-3)-2>0,
 \qquad
 f(19/5)=\frac{1052}{1875}>0.                          \tag{7}
\]

Every depth \(e\ge2\) has \(e\log7>19/5\). Equations (6)--(7) make every summand of
\(S_2(7)\) strictly positive, proving the first sign.

For the second sign, write \(\ell=\log19\) and \(q=19^{-3/2}\). From (1) and (5),

\[
 f(\ell)
 <\frac23\cdot9\cdot\frac1{100}-\frac{29}{5}+2
 =-\frac{187}{50}.                                     \tag{8}
\]

The rational square bounds

\[
 \frac{87}{20}<\sqrt{19}<\frac{22}{5}
\]

give

\[
 \frac5{418}<q<\frac{20}{1653}<\frac1{82}.             \tag{9}
\]

Thus the first depth is bounded above by

\[
 qf(\ell)<-\frac{935}{20900}<-\frac1{23}.              \tag{10}
\]

For every \(e\ge2\), one has \(e\ell>29/5\). The monotonicity in (7), now used on the
larger interval, and \(\ell<3\) imply

\[
 f(e\ell)<f(3e),qquad f(6)=206,qquad
 f(3e)<54e^4\quad(e\ge3).                              \tag{11}
\]

For \(a_e=e^4/82^e\) and \(e\ge3\),

\[
 \frac{a_{e+1}}{a_e}
 \le\frac{(4/3)^4}{82}<\frac1{25}.
\]

Using (9)--(11), the complete tail therefore satisfies

\[
 \begin{aligned}
 \sum_{e\ge2}q^ef(e\ell)
 &<\frac{206}{82^2}
   +54\frac{3^4}{82^3}\frac{25}{24}\\
 &<\frac{31}{1000}+\frac9{1000}
 =\frac1{25}.                                           \tag{12}
 \end{aligned}
\]

Combining (10) and (12) yields

\[
 S_2(19)<-\frac1{23}+\frac1{25}=-\frac2{575}<0.
\]

This proves both signs. No prime cutoff was used: each \(S_2(p)\) contains its entire valuation
tower.

### Conjecture verdict and positive survivor

The conjecture that cofinal valuation summation repairs the Laguerre sign defect locally is
\([FALSIFIED]\). The surviving source requirement is sharper: a successful proof must retain the
polar and Gamma counterterms and any cross-prime covariance through completion, and only then
take the scalar Cayley coefficient. Arithmetic Schur cofinal exhaustion by itself supplies a
positive kernel, but this theorem shows that the linear Cayley readout is not a positive local
prime functional on that kernel.

This is coefficient-faithful: it preserves phase through the full degree sequence, unlike a single norm-amplifying polynomial.

## Recurrences and resolvent generating function

The source polynomials satisfy
\[
  Q_{n+1}(W)
  =2(1-W)Q_n(W)-(1+W)^2Q_{n-1}(W),
\]
with \(Q_0=1\) and \(Q_1=1-W\).

Put
\[
  a_k:=\sum_q u_qT_k(2u_q-1),
  \qquad
  R(y):=\sum_q\frac1{\operatorname{xiSpectralPoint}(q)^2+y}.
\]
The identity \(T_n(x)^2=(1+T_{2n}(x))/2\) gives
\[
  C_n=\frac12\Re(a_0+a_{2n}).
\]
For \(|r|<1/3\), set \(t=(1-r)/(1+r)\). The Chebyshev generating function and absolute
summability yield the exact resolvent relation
\[
  \sum_{k\ge0}a_kr^k
  =\frac12\left(R(1)+tR(t^2)\right).
\]
Per divisor atom, with \(u=(1+w)^{-1}\), this is
\[
  \sum_{k\ge0}uT_k(2u-1)r^k
  =\frac12\left(\frac1{w+1}+\frac{t}{w+t^2}\right).
\]
The formerly asserted unit disk was too broad unconditionally: off-critical Cayley modes have only
the proved uniform bound \(|y_q|\le3\), so the closed double-series argument requires
\(3|r|<1\).  The displayed disk is the exact unconditional domain proved here.  These identities
expose a concrete next source attack: derive the even-coefficient lower bounds from the unit-shift
source recurrence or a source-side property of \(R(t^2)\).

## What this corrects

The earlier compactification audit correctly ruled out one fixed Chebyshev amplifier: norm growth alone loses complex phase and cannot certify sign. The obstruction does not apply to the complete sequence \((p_n)_{n\ge0}\). Maximal-shell asymptotics retains the squared phase, while torus recurrence forces a negative value. The new criterion therefore does not revive the failed single-amplifier argument; it identifies the phase-complete replacement.

## Remaining open core

Prove, from the prime/Gamma source alone and without importing an equivalent \(\xi\)-positivity statement, that
\[
  \Re\int_0^\infty t^{2n}e^{-t}\,\mathcal H_{Q_n}(t)\,dt\ge0
  \qquad(n\ge0).
\]
This burden is still equivalent to RH. The gain is an exact collapse from all polynomial tests to one explicit positive-root Cayley–Chebyshev test per degree, together with a recurrence and a resolvent generating function that are absent for an arbitrary test polynomial.

## Parent-theory audit

Internal collision searches found the Cayley rational identity, general polynomial trace-Hankel criteria, positive-root Schur packets, effective Turán detection windows, and an existing Li reciprocal-Chebyshev atlas. The exact one-test-per-degree reduction was not found internally, but the identity above places its mechanism in generalized Li theory. It remains a useful Route U bridge, not a novelty claim.

Primary parent literature:

- Bombieri and Lagarias, *Complements to Li's Criterion for the Riemann Hypothesis*, Journal of Number Theory 77 (1999), 274--287.
- Sekatskii, *Generalized Bombieri--Lagarias' theorem and generalized Li's criterion*, Ukrainian Mathematical Journal 64 (2014), 371--383; arXiv:1304.7895.
- Ernvall-Hytönen, Odžak, Smajlović, and Sušić, *On generalized Li criterion for a certain class of L-functions*, arXiv:1410.4384, especially the associated-Laguerre arithmetic formula.
- Lagarias, *Li coefficients for automorphic L-functions*, Annales de l'Institut Fourier 57 (2007), 1689--1740.

No scientific-priority claim is made. Exact novelty of the reduced stencil itself is unverified and immaterial to its Route U use.

## Formal status

Formalization is complete and unconditional.

- `CesaroSignRecurrence.lean` proves the reusable mean-zero/positive-square sign recurrence, finite
  exponential-pencil recurrence, and dominant-packet theorem.
- `CayleyChebyshevSource.lean` constructs `Q_n`, proves its recurrence, explicit positive roots,
  rational-square identity, and exact Hankel/Gamma source formula.
- `CayleyLaguerreFourier.lean` proves the pole-power Gamma transform, finite Cayley decomposition,
  associated-Laguerre half-line formulas, and the exact all-frequency transform of
  `cos^2(2n arctan x)/(1+x^2)`.
- `XiCayleyChebyshevPositiveRootCriterion.lean` proves the maximal-shell converse, the closed RH
  equivalence, generalized-Li stencil, normalized Gamma equivalence, corrected Abel--resolvent
  identity on `norm r < 1/3`, hostile Laguerre value, and both complete valuation-tower signs.

All four modules are imported by `GaloisForLFunctions.RHTower`. Direct `lake env lean` checks and
targeted leaf builds pass. Batched `#print axioms` checks for the public capstones report only
`propext`, `Classical.choice`, and `Quot.sound`. No `sorry`, `admit`, project `axiom`, `opaque`, or
`unsafe` declaration occurs in the new modules. The repository-wide lint invocation found no
Route U violation; its nonzero exit was solely five unrelated concurrently added `HTGeometry`
modules not yet imported by their umbrella.
