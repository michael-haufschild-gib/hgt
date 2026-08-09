# q-Gamma positive recurrent hypertranscendental process and open-history law

- **ID:** ULF-QGPRH-1
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper) / INFINITE CROSS-DOCTRINE PROCESS
- **Source:** infinite common-process gate for Constitutive Process Mathematics
- **Statement:** Jackson's \(q\)-Gamma function is one explicit process with positive atomic, GNS/operator, recurrent-history, entropy-tilt, and hypertranscendental differential realizations.
- **Status:** [PAPER-PROVED] [ONE SOURCE PROCESS] [POSITIVE] [PURE-POINT RECURRENT] [OPEN LIFT] [HYPERTRANSCENDENTAL] [WITHHELD TILT RESPONSE] [CLASSICAL INGREDIENTS] [NOT RH] [NO LEAN]

## 1. q-Gamma probability law

Fix \(0<q<1\). Write

\[
(q;q)_0=1,
\qquad
(q;q)_n=\prod_{k=1}^n(1-q^k),
\qquad
(q;q)_\infty=\prod_{k=1}^\infty(1-q^k).
\tag{1}
\]

Define

\[
w_n=(q;q)_\infty\frac{q^n}{(q;q)_n},
\qquad
x_n=n\log q-\log(1-q)
\qquad(n\ge0).
\tag{2}
\]

### Theorem 1.1

The numbers \(w_n\) are strictly positive and sum to one. For \(\operatorname{Re}s>-1\),

\[
\boxed{
F_q(s):=\Gamma_q(1+s)=\sum_{n=0}^\infty w_ne^{s x_n}.}
\tag{3}
\]

Thus \(F_q\) is the moment-generating/Mellin response of the discrete probability law

\[
\mu_q=\sum_{n=0}^\infty w_n\delta_{x_n}.
\tag{4}
\]

### Proof

Jackson's \(q\)-Gamma function is

\[
\Gamma_q(z)
=(1-q)^{1-z}\frac{(q;q)_\infty}{(q^z;q)_\infty}.
\tag{5}
\]

The \(q\)-binomial theorem gives

\[
\frac1{(a;q)_\infty}
=\sum_{n=0}^\infty\frac{a^n}{(q;q)_n}
\qquad(|a|<1).
\tag{6}
\]

Put \(a=q^{1+s}\). Then

\[
\begin{aligned}
\Gamma_q(1+s)
&=(1-q)^{-s}(q;q)_\infty
  \sum_{n\ge0}\frac{q^{n(1+s)}}{(q;q)_n}\\
&=\sum_{n\ge0}
  \left((q;q)_\infty\frac{q^n}{(q;q)_n}\right)
  \exp\!\left(s[n\log q-\log(1-q)]\right).
\end{aligned}
\]

At \(s=0\), \(\Gamma_q(1)=1\), so the positive coefficients sum to one. QED.

Since \((q;q)_n\ge(q;q)_\infty\), one has \(0<w_n\le q^n\). Because \(x_n\) grows
linearly, every polynomial moment of \(\mu_q\) is finite.

## 2. Positive kernel and GNS realization

Put

\[
C_q(t)=F_q(it)=\Gamma_q(1+it).
\tag{7}
\]

### Theorem 2.1

The translation kernel

\[
K_q(s,t)=C_q(t-s)
\tag{8}
\]

is positive definite. More precisely, let

\[
\mathcal H_q=\ell^2(\mathbb N_0,w),
\qquad
\langle \xi,\eta\rangle
=\sum_{n\ge0}w_n\overline{\xi_n}\eta_n,
\qquad
\Omega=(1,1,\ldots).
\tag{9}
\]

Let \(X\) be multiplication by \(x_n\) on its maximal domain and put \(U_t=e^{itX}\). Then

\[
\boxed{
C_q(t)=\langle\Omega,U_t\Omega\rangle.}
\tag{10}
\]

The operator \(X\) is self-adjoint with compact resolvent, and
\(\Omega\in\operatorname{Dom}X^k\) for every \(k\ge0\).

### Proof

For finite \(c_j\in\mathbb C\) and \(t_j\in\mathbb R\),

\[
\sum_{i,j}\overline{c_i}c_jC_q(t_j-t_i)
=\sum_{n\ge0}w_n
  \left|\sum_jc_je^{it_jx_n}\right|^2
\ge0.
\tag{11}
\]

Equation (10) is (3) at \(s=it\). Under the unitary identification
\(\ell^2(w)\to\ell^2\), \(\xi_n\mapsto\sqrt{w_n}\xi_n\), \(X\) is the real diagonal
operator with distinct eigenvalues \(x_n\), and \(|x_n|\to\infty\). Hence its resolvent is compact.
The geometric bound \(w_n\le q^n\) gives
\(\sum_nw_n|x_n|^{2k}<\infty\), proving the domain assertion. QED.

Every finite moment matrix

\[
M_N=\bigl(F_q^{(i+j)}(0)\bigr)_{0\le i,j\le N}
=\left(\int x^{i+j}\,d\mu_q(x)\right)_{i,j}
\tag{12}
\]

is positive definite. Indeed,

\[
c^*M_Nc=\int\left|\sum_{j=0}^Nc_jx^j\right|^2d\mu_q(x)>0
\tag{13}
\]

for \(c\ne0\), because a nonzero polynomial cannot vanish on the infinite distinct support
\(\{x_n:n\ge0\}\).

## 3. Recurrent observation and open marked history

The phase coordinates factor as

\[
e^{itx_n}
=e^{-it\log(1-q)}\bigl(e^{it\log q}\bigr)^n.
\tag{14}
\]

### Theorem 3.1

The orbit \(\{U_t\Omega:t\in\mathbb R\}\) has compact norm closure. There are unbounded
\(t_j\to+\infty\) such that

\[
\boxed{\|U_{t_j}\Omega-\Omega\|_{\mathcal H_q}\longrightarrow0.}
\tag{15}
\]

Yet the marked logarithmic lift

\[
h(t)=tX\Omega=(t x_n)_{n\ge0}
\tag{16}
\]

satisfies

\[
\boxed{
\|h(t_j)\|
=t_j\left(\sum_{n\ge0}w_nx_n^2\right)^{1/2}
\longrightarrow\infty.}
\tag{17}
\]

### Proof

Define

\[
\Phi:\mathbb T^2\longrightarrow\mathcal H_q,
\qquad
\Phi(\alpha,\beta)_n=e^{i\alpha}e^{in\beta}.
\tag{18}
\]

Finite-coordinate continuity plus the uniform tail bound
\(\sum_{n>N}w_n\to0\) makes \(\Phi\) norm-continuous. Equation (14) places the orbit in the compact
set \(\Phi(\mathbb T^2)\). Compact-group recurrence, equivalently simultaneous Dirichlet
approximation of

\[
\frac{-\log(1-q)}{2\pi},
\qquad
\frac{\log q}{2\pi},
\]

gives unbounded return times satisfying (15). Equation (17) is immediate from (16). Its coefficient
is finite by the moment bound and nonzero because the support is not concentrated at \(0\). QED.

Thus one process has a closed recurrent observer shadow and an open lifted history. The latter is
not inferred from recurrence alone; it is retained by the marked logarithmic spectral
realization.

## 4. Hypertranscendental analytic memory

### Theorem 4.1

The response \(F_q(s)=\Gamma_q(1+s)\) is hypertranscendental over \(\mathbb C(s)\). Consequently,

\[
\boxed{
\operatorname{trdeg}_{\mathbb C(s)}
\mathbb C(s)\bigl(F_q,F_q',\ldots,F_q^{(N)}\bigr)=N+1
\quad(N\ge0).}
\tag{19}
\]

### Proof

P. I. Pastro's \(q\)-analogue of Hölder's theorem proves that \(\Gamma_q(z)\) satisfies no
algebraic differential equation even over the larger differential field
\(\mathbb C(z,q^z)\). In particular it is hypertranscendental over \(\mathbb C(z)\).
The affine substitution \(z=1+s\) preserves differential algebraicity and its negation, proving
the first assertion. Equation (19) is the finite-jet characterization of hypertranscendence. QED.

Combining (12), (13), and (19), the same response has both maximal positive Hankel rank and maximal
algebraic intervention rank. Positivity does not create the HT statement; Pastro's theorem does.
Their coexistence is nevertheless intrinsic to the same \(\mu_q\)-process.

## 5. Exact intervention tilt and entropy law

Jackson's functional equation is

\[
\Gamma_q(z+1)=\frac{1-q^z}{1-q}\Gamma_q(z).
\tag{20}
\]

Since \(F_q(1)=\Gamma_q(2)=1\), the exponentially tilted weights

\[
\widetilde w_n=e^{x_n}w_n
\tag{21}
\]

again form a probability law. Their characteristic response is

\[
\widetilde C_q(t)
=\sum_n\widetilde w_ne^{itx_n}
=F_q(1+it).
\tag{22}
\]

### Theorem 5.1

The response to this unmeasured tilt is forced by the original response:

\[
\boxed{
\widetilde C_q(t)
=\frac{1-q^{1+it}}{1-q}\,C_q(t).}
\tag{23}
\]

Moreover \(X\) is the log-likelihood ratio:

\[
\log\frac{\widetilde w_n}{w_n}=x_n,
\tag{24}
\]

and

\[
\boxed{
D(\widetilde w\|w)=F_q'(1),
\qquad
D(w\|\widetilde w)=-F_q'(0).}
\tag{25}
\]

### Proof

Equation (23) is (20) with \(z=1+it\). Equation (24) follows from (21). Both measures have full
support, so direct summation gives

\[
D(\widetilde w\|w)=\sum_n\widetilde w_nx_n=F_q'(1)
\]

and

\[
D(w\|\widetilde w)=-\sum_nw_nx_n=-F_q'(0).
\]

All sums converge by the exponential tail. QED.

This is a cross-doctrine withheld prediction: the analytic \(q\)-difference law predicts an
unmeasured probabilistic intervention, its characteristic response, and both directed information
costs.

## 6. One-process synthesis

The single constitutive response \(F_q\) has the exact chart:

\[
\boxed{
\begin{array}{c}
\text{positive discrete law }\mu_q\\
\Updownarrow\\
\text{positive kernel }K_q\\
\Updownarrow\\
\text{GNS pair }(\mathcal H_q,X,\Omega)\\
\Updownarrow\\
\text{recurrent observer }U_t\Omega
\text{ with open lift }tX\Omega\\
\Updownarrow\\
\text{hypertranscendental analytic process }\Gamma_q(1+s)\\
\Updownarrow\\
\text{exponential tilt and entropy response}
\end{array}}
\tag{26}
\]

The vertical arrows are explicit equations (3), (10), (14), (19), and (23), not analogies.

This passes the infinite common-process gate of Constitutive Process Mathematics:

- positivity, recurrence, open history, and HT occur in one source-normalized process;
- observed compactness and maximal differential intervention memory coexist without being
  identified;
- one functional equation predicts a response in another intervention doctrine.

## 7. Hostile boundaries

1. The ingredients are classical: \(q\)-binomial theorem, Jackson \(q\)-Gamma, GNS/Bochner,
   compact pure-point dynamics, relative entropy, and Pastro's \(q\)-Hölder theorem.
2. Atomicity is load-bearing for norm-precompact recurrence. A continuous spectral law can be
   positive and HT without recurrent vector orbit.
3. The marked lift (16) is extra information erased by the phase observer.
4. Hypertranscendence does not follow from positive Hankel rank; many DA measures have infinite
   support and full moment rank.
5. Recurrence does not imply HT; finite atomic laws are recurrent and exponential-polynomial.
6. The functional equation supplies the tilt but no physical clock, Hamiltonian cost, or
   Brown--Susskind complexity.
7. No Morita/presentation invariance theorem, higher-slot intervention process, RH statement, or
   arithmetic zero theorem follows.

## Primary parents

- P. I. Pastro, *The q-analogue of Hölder's theorem for the gamma function*, Rendiconti del
  Seminario Matematico della Università di Padova **70** (1983), 47--53,
  <https://www.numdam.org/item/RSMUP_1983__70__47_0/>.
- Jackson's \(q\)-Gamma definition and the \(q\)-binomial theorem, summarized in NIST DLMF,
  Chapter 17, <https://dlmf.nist.gov/17>.

## Log

- 2026-08-09 — positive atomic representation, GNS recurrence, open lift, Pastro
  hypertranscendence, and exact entropy tilt closed as one infinite CPM process.
