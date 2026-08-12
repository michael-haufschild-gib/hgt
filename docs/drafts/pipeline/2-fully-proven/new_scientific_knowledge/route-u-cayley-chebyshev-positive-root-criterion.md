# Route U: Cayley–Chebyshev positive-root criterion

**Status:** `[PAPER-PROVED] [UNCONDITIONAL] [NO COMPUTATION] [LEAN NOT STARTED] [NOT RH] [CANDIDATE NEW]`

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
For \(|r|<1\), set \(t=(1-r)/(1+r)\). The Chebyshev generating function yields the exact resolvent relation
\[
  \sum_{k\ge0}a_kr^k
  =\frac12\left(R(1)+tR(t^2)\right).
\]
Per divisor atom, with \(u=(1+w)^{-1}\), this is
\[
  \sum_{k\ge0}uT_k(2u-1)r^k
  =\frac12\left(\frac1{w+1}+\frac{t}{w+t^2}\right).
\]
These identities expose a concrete next source attack: derive the even-coefficient lower bounds from the unit-shift source recurrence or a source-side property of \(R(t^2)\).

## What this corrects

The earlier compactification audit correctly ruled out one fixed Chebyshev amplifier: norm growth alone loses complex phase and cannot certify sign. The obstruction does not apply to the complete sequence \((p_n)_{n\ge0}\). Maximal-shell asymptotics retains the squared phase, while torus recurrence forces a negative value. The new criterion therefore does not revive the failed single-amplifier argument; it identifies the phase-complete replacement.

## Remaining open core

Prove, from the prime/Gamma source alone and without importing an equivalent \(\xi\)-positivity statement, that
\[
  \Re\int_0^\infty t^{2n}e^{-t}\,\mathcal H_{Q_n}(t)\,dt\ge0
  \qquad(n\ge0).
\]
This burden is still equivalent to RH. The gain is an exact collapse from all polynomial tests to one explicit positive-root Cayley–Chebyshev test per degree, together with a recurrence and a resolvent generating function that are absent for an arbitrary test polynomial.

## Novelty audit

Internal collision searches found the Cayley rational identity, general polynomial trace-Hankel criteria, positive-root Schur packets, and effective Turán detection windows, but not this complete-sequence criterion or its maximal-Green-shell proof. It is compatible with, and strictly refines, the recorded failure of a single Chebyshev amplifier.

Nearby external literature includes Faber/Faber–Walsh asymptotics, extremal polynomial growth off a compact interval, and Jensen-polynomial criteria for \(\xi\), but the exact shift-one resolvent criterion and positive-root source handoff were not found:

- Sète and Liesen, *Properties and Examples of Faber–Walsh Polynomials* (arXiv:1306.1347).
- O'Sullivan, *Zeros of Jensen polynomials and asymptotics for the Riemann xi function* (arXiv:2007.13582).
- Christiansen, Simon, and Zinchenko, *Asymptotics of Chebyshev Polynomials, I* (Constructive Approximation, 2021).

No external priority claim is made.

## Formal status

No Lean file was started. Formalization should begin only when the analytic maximal-shell lemma, Joukowski branch interface, and torus-recurrence sign lemma can be implemented as closed reusable mathematics. No theorem wrapper or premise-carrying surrogate is acceptable.
