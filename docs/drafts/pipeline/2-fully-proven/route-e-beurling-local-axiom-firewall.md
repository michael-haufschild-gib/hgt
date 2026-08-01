# Route E Beurling local-axiom firewall

- **ID:** `ROUTE-E-BEURLING-FIREWALL-001`
- **Stage:** 2-fully-proven
- **Type:** THEOREM / SOURCE-CLASSIFICATION FIREWALL
- **Scientific status:** `[LITERATURE] [PAPER-PROVED] [BRIDGE] [NOVELTY UNVERIFIED]`
- **Parent:** `../1-in-progress/route-e-squarefree-exponential-gibbs-parity.md`
- **RH used:** no
- **Computation used:** no
- **Lean status:** abstract finite identities already have ordinary-integer instances in the
  corpus; generalized-system formalization not started

## Exact claim

There is a discrete Beurling prime system \(\mathcal P\), with free commutative generalized-integer
monoid \(\mathcal G_{\mathcal P}\), multiplicative norm \(|\cdot|\), generalized Möbius function
\(\mu_{\mathcal P}\), and zeta function \(\zeta_{\mathcal P}\), for which all of the following hold.

1. For some \(1/2<\theta<1\) and \(\kappa>0\),

   \[
   N_{\mathcal P}(X)=\#\{g\in\mathcal G_{\mathcal P}:|g|\le X\}
   =\kappa X+O(X^\theta),
   \tag{BF1}
   \]

   and the generalized primes obey a PNT with a de la Vallée Poussin-scale remainder.

2. \(\zeta_{\mathcal P}\) has infinitely many zeros \(\rho\) with
   \(\Re\rho>1/2\).

3. Every finite squarefree exponential-Gibbs table

   \[
   w_x(S)=\exp\!\left(-x\prod_{p\in S}|p|\right)
   \tag{BF2}
   \]

   is strictly log-submodular in every genuinely transverse pair of set directions.  In
   particular every conditional two-prime table is strictly Rayleigh.

4. With

   \[
   \Phi_{\mathcal P}(x)
    =\sum_{g\in\mathcal G_{\mathcal P}}\mu_{\mathcal P}(g)e^{-x|g|},
   \qquad
   A_{\mathcal P,z}(x)
    =\sum_{\substack{g\in\mathcal G_{\mathcal P}\\p\mid g\Rightarrow |p|\le z}}
       \mu_{\mathcal P}(g)e^{-x|g|},
   \tag{BF3}
   \]

   unique factorization gives the exact zero/one-large-prime decomposition

   \[
   \Phi_{\mathcal P}(x)
   =A_{\mathcal P,z}(x)
    -\sum_{|p|>z}A_{\mathcal P,z}(|p|x)
    +R_{\mathcal P,\ge2,z}(x).
   \tag{BF4}
   \]

   If \(0<x\le x_0\) and

   \[
   xz^2\ge \tfrac12\log(1/x),
   \tag{BF5}
   \]

   then

   \[
   |R_{\mathcal P,\ge2,z}(x)|=O(x^{-1/2}).
   \tag{BF6}
   \]

5. The one-large-prime kernel

   \[
   K_{\mathcal P,z}(t)
   =e^{-t}\left(1-\sum_{|p|>z}e^{-(|p|-1)t}\right)
   \tag{BF7}
   \]

   has exactly one sign transition \(\tau_{\mathcal P,z}\), and

   \[
   \frac{z\tau_{\mathcal P,z}}{\log z}\longrightarrow1.
   \tag{BF8}
   \]

   For fixed \(1<u<2\), \(Y=X^{1/u}\), its positive scalar renewal norm has the same barrier

   \[
   \sum_{Y<|p|\le X}|p|^{-\alpha}
   \sim\frac{X^{1-\alpha}}{(1-\alpha)\log X}\quad(0\le\alpha<1),
   \qquad
   \sum_{Y<|p|\le X}|p|^{-1}=\log u+o(1).
   \tag{BF9}
   \]

6. The divided-log prime-power completion is still exact:

   \[
   \frac{\Lambda_{\mathcal P}(p^k)}{\log|p^k|}=\frac1k,
   \tag{BF10}
   \]

   and its critical depth-zero Gamma gauge is

   \[
   \frac1{1-|p|^{-1}}.
   \tag{BF11}
   \]

   After deleting finitely many initial generalized primes, without changing any zero or
   asymptotic assertion, this gauge lies in \([1,2]\).

7. Nevertheless, for every zero \(\rho\) from item 2 and every
   \(a\) with

   \[
   \max(\theta,\tfrac12)<a<\Re\rho,
   \tag{BF12}
   \]

   neither

   \[
   \Phi_{\mathcal P}(x)=O(x^{-a})
   \tag{BF13}
   \]

   nor

   \[
   A_{\mathcal P,z(x)}(x)
   -\sum_{|p|>z(x)}A_{\mathcal P,z(x)}(|p|x)=O(x^{-a})
   \tag{BF14}
   \]

   can hold as \(x\downarrow0\) on any schedule satisfying `(BF5)`.

Consequently strict Rayleigh/log-submodular finite Gibbs geometry, generalized unique
factorization, PNT-quality prime distribution, the critical zero/one seam, the scalar-renewal
barrier, the divided-log Gamma/co-Poisson completion, and bounded depth-zero Gamma recovery do
**not** imply the Route E source estimate.  Any universal proof from only those inputs is false.

## External existence input

Diamond--Montgomery--Vorhauer prove that, for every \(1/2<\theta<1\) and suitable \(a>0\), there
is a **discrete** Beurling prime system satisfying `(BF1)`, with \(\zeta_{\mathcal P}\) analytic
on \(\Re s\ge\theta\) apart from its simple pole at \(1\), and with infinitely many zeros on

\[
\Re s=1-\frac{a}{\log|\Im s|}.
\]

They also prove

\[
\psi_{\mathcal P}(X)
=X+O\!\left(Xe^{-2\sqrt{a\log X}}\right).
\]

Thus the system supplies items 1--2, with strict-right zeros arbitrarily close to \(1\).

Primary source:

- H. G. Diamond, H. L. Montgomery, and U. M. A. Vorhauer,
  *Beurling primes with large oscillation*, Math. Ann. **334** (2006), 1--36,
  Theorem 1, DOI `10.1007/s00208-005-0638-2`.

The source explicitly notes that additive structure of the ordinary integers is what permits
zero-free information beyond the Beurling axioms used in its construction.

## Critical-normalization sharpening

`[PAPER-PROVED BRIDGE; NOVELTY UNVERIFIED]` The preceding firewall can be made strictly sharper
at the generalized-integer counting boundary.  For every prescribed integer cutoff \(R\), there
is a discrete Beurling system \(\mathcal P_R\) such that

\[
\mathcal P_R\cap[1,R]
=\{p\le R:p\text{ is an ordinary rational prime}\},
\tag{BF17}
\]

\[
N_{\mathcal P_R}(X)
=X+O\!\left(
 X^{1/2}\exp\{c(\log X)^{2/3}\}
\right),
\tag{BF18}
\]

and \(\zeta_{\mathcal P_R}\) is analytic on \(\Re s>1/2\), apart from its simple pole at \(1\),
but has infinitely many zeros on

\[
\Re s=1-\frac1{\log|\Im s|}.
\tag{BF19}
\]

Moreover every generalized prime belongs to the dyadic rational mesh

\[
\left\{n+\frac{\ell}{2^n}:n\ge0,\ 0\le\ell<2^n\right\}.
\tag{BF20}
\]

These are Wen-Bin Zhang's Theorem 2.  Theorem 2 states that its system has properties
(i)--(iii) of Theorem 1 and then replaces the RH conclusion by `(BF19)` and the sharp
de la Vallée Poussin oscillation law.  In particular `(BF17)` is available with \(R\) chosen
arbitrarily large before the system is constructed.

Primary source:

- W.-B. Zhang, *Normalization of Beurling generalized primes with Riemann hypothesis*,
  Ann. Univ. Sci. Budapest. Sect. Comput. **39** (2013), 459--469, Theorem 2,
  DOI `10.71352/ac.39.459`.

This system satisfies every conclusion `(BF2)`--`(BF11)`.  Indeed, for each fixed
\(\delta>0\),

\[
\exp\{c(\log X)^{2/3}\}=O_\delta(X^\delta),
\]

so `(BF18)` implies `(BF1)` with \(\kappa=1\) and any
\(\theta=1/2+\delta<1\).  The already-proved higher-large-prime estimate therefore applies
unchanged.  Zhang's prime error gives the PNT inputs used in `(BF8)`--`(BF9)`, while the free
prime-label monoid gives the finite Gibbs, zero/one-sector, and divided-log identities.

The strict-half failure is now stronger than item 7.  If \(\rho\) is a zero in `(BF19)`, then
for **every**

\[
\frac12<a<\Re\rho,
\tag{BF21}
\]

neither `(BF13)` nor `(BF14)` can hold.  The proof of `(BF13)` from `(BF16)` uses only the
assumed \(O(x^{-a})\) behavior at zero and exponential decay at infinity; it does not require
\(a>\theta\).  The deduction from `(BF14)` uses `(BF6)` and \(a>1/2\).  Thus `(BF21)` follows.

Consequently Route E cannot be obtained from the earlier local package even after adjoining all
three of the following:

```text
near-critical generalized-integer rigidity
  N_P(X)=X+X^(1/2+o(1));
analytic continuation of zeta_P through the full strict right half-plane;
agreement with ordinary rational primes below an arbitrarily prescribed finite aperture.
```

This is a genuine strengthening of the source classification.  A successful ordinary-integer
source must be discontinuously sensitive to the exact infinite additive lattice (or an equivalent
all-scale self-duality); no finite prime prefix, \(X^{1/2+o(1)}\) counting error, or strict-half
analytic continuation can supply the missing Wold-breadth orientation.

## Paper proof

### Finite Gibbs geometry

Let \(A,B\) be finite prime-label sets.  Write

\[
c=\prod_{p\in A\cap B}|p|,\qquad
r=\prod_{p\in A\setminus B}|p|,\qquad
s=\prod_{p\in B\setminus A}|p|.
\]

Every generalized prime norm is \(>1\), so

\[
rs+1-r-s=(r-1)(s-1)\ge0.
\]

Therefore

\[
w_x(A\cup B)w_x(A\cap B)
=e^{-xc(rs+1)}
\le e^{-xc(r+s)}
=w_x(A)w_x(B).
\]

The inequality is strict when both set differences are nonempty.  Taking each difference to be
one prime gives the conditional two-prime Rayleigh law.  No discreteness, additive structure, or
zero-free input occurs.

### Exact zero/one decomposition

The Beurling generalized integers are the free commutative monoid on the generalized-prime
labels.  Every squarefree \(g\) therefore contains exactly zero, one, or at least two labels with
norm \(>z\).  The zero sector is \(A_{\mathcal P,z}(x)\).  In the one sector write uniquely
\(g=pm\), where \(|p|>z\) and every prime label of \(m\) has norm at most \(z\).  Then
\(\mu_{\mathcal P}(pm)=-\mu_{\mathcal P}(m)\), giving the second term of `(BF4)`.  The remaining
sector is \(R_{\mathcal P,\ge2,z}\).  Absolute convergence follows from `(BF1)`.

### Critical higher-large-prime remainder

Every generalized integer in the remainder has norm \(>z^2\).  Put

\[
S_{\mathcal P}(T,x)=\sum_{|g|>T}e^{-x|g|}.
\]

Partition \((T,\infty)\) into intervals of length \(1/x\).  From `(BF1)`, for a constant \(C\),

\[
\begin{aligned}
N_{\mathcal P}(T+(j+1)/x)-N_{\mathcal P}(T+j/x)
\le{}&\kappa/x\\
&+C\bigl((T+(j+1)/x)^\theta+(T+j/x)^\theta\bigr).
\end{aligned}
\]

Multiplying by \(e^{-xT-j}\), summing over \(j\ge0\), and using
\((r+s)^\theta\le r^\theta+s^\theta\) for \(0<\theta<1\), gives

\[
S_{\mathcal P}(T,x)
\ll e^{-xT}\bigl(x^{-1}+T^\theta+x^{-\theta}\bigr).
\tag{BF15}
\]

Take \(T=z^2\).  Under `(BF5)`, \(e^{-xT}\le x^{1/2}\).  The first term in `(BF15)` is
\(x^{-1/2}\).  Put \(y=xT\).  Once \(x\) is small, `(BF5)` gives
\(y\ge\frac12\log(1/x)>\theta\), and \(y^\theta e^{-y}\) is decreasing there.  Hence, since
\(\theta<1\),

\[
e^{-xT}T^\theta
=x^{-\theta}e^{-y}y^\theta
\ll x^{1/2-\theta}\log(1/x)^\theta
=O(x^{-1/2}),
\qquad
e^{-xT}x^{-\theta}\le x^{1/2-\theta}=O(x^{-1/2}).
\]

This proves `(BF6)`.

### Transition and scalar-renewal laws

For fixed \(z\), the prime sum in `(BF7)` converges for every \(t>0\), strictly decreases from
\(+\infty\) to \(0\), and hence crosses \(1\) exactly once.  PNT partial summation gives, uniformly
for fixed \(c>0\),

\[
\sum_{|p|>z}e^{-(|p|-1)c\log z/z}
=z^{1-c+o(1)}.
\]

For every \(c<1\) this tends to \(+\infty\); for every \(c>1\) it tends to \(0\).  Monotonicity
then proves `(BF8)`.  The same PNT and ordinary partial summation give `(BF9)`.

### Gamma completion

The generalized von Mangoldt function has value \(\log|p|\) on \(p^k\), while
\(\log|p^k|=k\log|p|\).  This proves `(BF10)`.  Formula `(BF11)` is the same depth-zero
half-density/Gamma quotient as for rational primes.  Removing finitely many labels only
multiplies the zeta function by a finite nonvanishing Euler factor on \(\Re s>0\), so it preserves
all strict-right zeros and asymptotic conclusions; after doing so every remaining norm is at least
\(2\), and `(BF11)` lies in \([1,2]\).

### Strict-half failure

For \(\Re s>1\), absolute convergence and termwise Mellin transformation give

\[
\int_0^\infty\Phi_{\mathcal P}(x)x^{s-1}\,dx
=\Gamma(s)\sum_g\frac{\mu_{\mathcal P}(g)}{|g|^s}
=\frac{\Gamma(s)}{\zeta_{\mathcal P}(s)}.
\tag{BF16}
\]

Fix a zero \(\rho\) and \(a\) as in `(BF12)`.  If `(BF13)` held, the left side of `(BF16)` would
define a holomorphic function on \(\Re s>a\): the assumed bound handles \(x\downarrow0\), while
`(BF1)` gives exponential decay at \(+\infty\).  On \(\Re s>1\) it equals
\(\Gamma/\zeta_{\mathcal P}\), so analytic continuation would make that quotient holomorphic at
\(\rho\).  This is impossible because Gamma has no zeros and \(\zeta_{\mathcal P}(\rho)=0\).
Thus `(BF13)` fails.

By `(BF4)` and `(BF6)`, `(BF14)` would imply `(BF13)`, because \(a>1/2\).  Therefore `(BF14)`
also fails.

This closes all seven items.

## Hostile audit

1. **Not an RH proof.**  The theorem constructs a countermodel to a source axiom set.
2. **Not a new Beurling construction.**  Discrete system and its zeros are exactly
   Diamond--Montgomery--Vorhauer's theorem.
3. **Not merely “Beurling systems differ.”**  Items 3--6 verify, one by one, that the exact local,
   critical-aperture, renewal, and Gamma mechanisms currently retained by Route E survive in the
   countermodel.
4. **No functional-equation claim.**  The countermodel is not asserted to carry the Riemann
   functional equation.  That absence is the point: functional-equation/archimedean data remain a
   possible ordinary-integer-specific source.
5. **No additive-lattice claim.**  Generalized norms are real and need not form the ordinary
   additive lattice.  Therefore additive Fourier structure also remains a possible discriminator.
6. **No overclaim of novelty.**  The local-axiom firewall appears absent from the searched
   literature, but it is an elementary synthesis over a known Beurling construction.  It remains
   `[BRIDGE] [NOVELTY UNVERIFIED]`, not candidate new scientific knowledge.

## Exact representation lesson

The surviving depth-zero source cannot be a theorem of:

```text
free prime-factor monoid
+ PNT-quality prime counting
+ finite Gibbs log-submodularity/Rayleigh geometry
+ zero/one critical aperture
+ scalar prime renewal
+ divided-log Gamma prime-power completion
+ bounded depth-zero Gamma gauge.
```

That package has a strict-right-zero model.  A successful Route E source must use at least one
structure not preserved by this firewall.  Current exact candidates are:

1. ordinary additive lattice and its distinguished character \(n\mapsto e^{int}\);
2. archimedean functional equation/co-Poisson reflection tied to that lattice;
3. an equivalent global invariant that rules out the Diamond--Montgomery--Vorhauer system before
   the desired Möbius estimate is invoked.

Merely naming “integer-specific arithmetic” is not a source theorem.  Next conjecture must exhibit
one exact discriminator and derive a quantitative orientation from it.

## Local-prefix nonrobustness theorem

`[PAPER-PROVED BRIDGE; NOVELTY UNVERIFIED]`  The Zhang sharpening has a topology-free
formulation which removes a remaining ambiguity in “cofinal continuity.”  Let \(\mathscr B\) be
any class of discrete Beurling systems containing the ordinary primes \(\mathcal P_0\) and all
systems supplied by `(BF17)`--`(BF20)`.  Give \(\mathscr B\) the finite-prefix topology: a basic
neighborhood of \(\mathcal P_0\) prescribes agreement with the rational primes below one finite
cutoff.

Let \(\mathcal C\subseteq\mathscr B\) be any certificate class with the soundness property

\[
\mathcal P\in\mathcal C
\quad\Longrightarrow\quad
\Phi_{\mathcal P}(x)=O_{\mathcal P,\varepsilon}
  (x^{-1/2-\varepsilon})
\quad\text{for every }\varepsilon>0.
\tag{BF22}
\]

Then \(\mathcal C\) cannot both contain \(\mathcal P_0\) and be a neighborhood of
\(\mathcal P_0\).  Equivalently, no sound Route E certificate which is stable under sufficiently
long finite-prime-prefix agreement can certify the ordinary primes.

The proof is one line but the quantifiers matter.  If \(\mathcal C\) contained a basic
neighborhood of \(\mathcal P_0\), choose its cutoff \(R\).  Zhang's system
\(\mathcal P_R\) lies in that neighborhood by `(BF17)`, hence in \(\mathcal C\).  Soundness
would give `(BF13)` for every \(a=1/2+\varepsilon\), contradicting `(BF21)` at any zero
\(\rho\) with \(1/2<a<\Re\rho\).

This does **not** say that pointwise finite-aperture formulas are useless, nor does it assume RH
for \(\mathcal P_0\).  It says that a successful certificate at \(\mathcal P_0\) cannot have an
open, uniform margin in finite-prefix topology.  Its admission step must be tail-singular:
exact all-scale additive lattice structure, exact co-Poisson self-duality, or another
non-open invariant must enter before the strict-half estimate.  Pointwise convergence at each
fixed physical scale is insufficient; required nonuniformity is in the joint
prime-aperture/critical-scale limit.

Hostile novelty audit found literature on Beurling zero distributions and on Zhang's
normalization theorem, but no statement of `(BF22)` as a source-certificate nonrobustness law.
The construction is external and the deduction elementary, so status remains
`[BRIDGE] [NOVELTY UNVERIFIED]`, not independent new construction.
