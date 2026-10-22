# Two-prime Kummer precision horizon and compact-repair no-go

- **ID:** `two-prime-kummer-precision-horizon-and-compact-repair-no-go`
- **Stage:** 3-formalized
- **Type:** THEOREM (paper proof; live Route-L application)
- **Program:** `noncommuting-exactification-geometry`
- **Parent:**
  `../../3-formalized/new_scientific_knowledge/deninger-two-prime-kummer-dense-nonclosed-range.md`
- **Scientific status:** `[UNCONDITIONAL] [NEW ROUTE LEVERAGE]`
- **RH status:** no RH premise and no RH conclusion; strictly narrows the surviving Route-L repair
- **Novelty discipline:** diagonal-operator spectrum, compact singular-sequence arguments, and
  Dirichlet approximation are classical. New payload is the exact arithmetic precision spectrum,
  finite-section conditioning law, and proof that every compact cross-sector repair fails for the
  actual two-prime Kummer source.

## 1. Source operator

Let

\[
a=\log2,
\qquad
b=\log3,
\qquad
L=\mathbb Za+\mathbb Zb.
\]

Unique factorization implies \(a/b\notin\mathbb Q\), so every \(\mu\in L\) has a unique
integer pair \((m,n)\) with \(\mu=ma+nb\). Let

\[
\mathcal H=\ell^2(L\setminus\{0\}).
\]

Define the bounded Kummer phase transform

\[
(Bf)(\mu)=\beta(\mu)f(\mu),
\qquad
\beta(\mu)=\frac{\mu}{1+|\mu|}.                               \tag{1.1}
\]

The parent card proves that \(B\) is an injective contraction with dense nonclosed range, while
every finite modal truncation is invertible. This paper determines the geometry of that failure and
tests the surviving repair class.

## 2. Exact finite precision spectrum

For \(N\geq1\), define the rectangular source modes

\[
S_N=\{ma+nb:(m,n)\in\mathbb Z^2,\ |m|,|n|\leq N\}
\setminus\{0\},                                               \tag{2.1}
\]

and the arithmetic clock-separation scale

\[
d_N=\min_{\mu\in S_N}|\mu|.                                  \tag{2.2}
\]

Let \(B_N\) be the restriction of \(B\) to \(\ell^2(S_N)\), and let

\[
\Delta_N=B_N^*B_N.                                            \tag{2.3}
\]

### Theorem 2.1 — exact Kummer precision law

The smallest singular value, constraint-Laplacian gap, and inverse capacity are

\[
\sigma_{\min}(B_N)=\frac{d_N}{1+d_N},                         \tag{2.4}
\]

\[
\lambda_{\min}(\Delta_N)
=\left(\frac{d_N}{1+d_N}\right)^2,                            \tag{2.5}
\]

\[
\|B_N^{-1}\|=\frac{1+d_N}{d_N}=1+\frac1{d_N}.                \tag{2.6}
\]

In particular, the finite-section precision horizon is exactly the Diophantine approximation
profile of the two arithmetic clocks \(\log2\) and \(\log3\).

#### Proof

In the coordinate basis, \(B_N\) is diagonal with nonzero entries \(\beta(\mu)\),
\(\mu\in S_N\). The function

\[
t\longmapsto\frac{t}{1+t}
\]

is strictly increasing for \(t\geq0\). Hence the least absolute diagonal entry occurs at a mode
with \(|\mu|=d_N\), giving (2.4). The eigenvalues of \(B_N^*B_N\) are
\(|\beta(\mu)|^2\), proving (2.5). The inverse is diagonal with entries
\(1/\beta(\mu)\); its operator norm is the reciprocal of the least singular value, proving
(2.6). ∎

## 3. Unconditional quantitative bounds

### Theorem 3.1 — elementary horizon window

For every \(N\geq2\), with \(M=\lfloor N/2\rfloor\),

\[
3^{-N}\leq d_N\leq\frac{\log2}{M}.                            \tag{3.1}
\]

Consequently,

\[
\left(\frac{3^{-N}}{1+3^{-N}}\right)^2
\leq\lambda_{\min}(\Delta_N)
\leq
\left(\frac{(\log2)/M}{1+(\log2)/M}\right)^2,                \tag{3.2}
\]

and

\[
1+\frac{M}{\log2}
\leq\|B_N^{-1}\|
\leq1+3^N.                                                     \tag{3.3}
\]

In particular,

\[
d_N\to0,
\qquad
\lambda_{\min}(\Delta_N)\to0,
\qquad
\|B_N^{-1}\|\to\infty.                                      \tag{3.4}
\]

#### Proof

For the lower bound, take \(\mu=ma+nb\in S_N\). If \(m,n\) have the same sign, or one is
zero, then \(|\mu|\geq\log2>3^{-N}\). Otherwise, after changing the overall sign if needed,
write

\[
\mu=\log(2^p/3^q),
\qquad
1\leq p,q\leq N.
\]

The integers \(2^p\) and \(3^q\) are distinct by unique factorization. If \(A>B\) are these
two integers, then

\[
|\log(A/B)|
=\int_B^A\frac{dt}{t}
\geq\frac{A-B}{A}
\geq\frac1A
\geq3^{-N}.
\]

The case \(B>A\) is identical. Taking the minimum proves the lower bound.

For the upper bound, put \(\alpha=b/a\). Since \(1<\alpha<2\), Dirichlet's pigeonhole
argument applied to

\[
0,\alpha,2\alpha,\ldots,M\alpha\pmod1
\]

gives integers \(1\leq q\leq M\) and \(p\) with

\[
|q\alpha-p|\leq\frac1M.
\]

Because \(q\leq M\) and \(\alpha<2\), the nearest such integer satisfies
\(1\leq p\leq N\). Here is the endpoint check. If \(M=1\), then
\(N\in\{2,3\}\) and a nearest integer to \(\alpha\in(1,2)\) is either `1` or `2`. If
\(M\geq2\), then

\[
p<q\alpha+\frac1M<2M+1,
\]

so integrality gives \(p\leq2M\leq N\); positivity follows from
\(q\alpha-1/M>0\). Thus \((-p,q)\) is allowed in (2.1), and

\[
d_N\leq|-pa+qb|
=a|q\alpha-p|
\leq\frac{\log2}{M}.
\]

This proves (3.1). Equations (3.2)--(3.3) follow from Theorem 2.1 and monotonicity. Since
\(M\to\infty\), (3.4) follows. ∎

### Remark 3.2 — sharper imported bounds

Baker's theory of nonzero linear forms in logarithms gives effective constants \(C,A>0\) with

\[
d_N\geq C N^{-A}.
\]

That improves the elementary exponential lower bound but is not needed for any theorem below. The
paper keeps (3.1) so its core is dependency-light.

## 4. Approximate Green contractions also blow up

Exact inverse norms are not the only obstruction. Uniformly accurate approximate inverses inherit
the same arithmetic cost.

### Theorem 4.1 — approximate inverse uncertainty law

Let \(0\leq\varepsilon<1\), and let
\(G_N:\ell^2(S_N)\to\ell^2(S_N)\) satisfy

\[
\|G_NB_N-I\|\leq\varepsilon.                                 \tag{4.1}
\]

Then

\[
\|G_N\|
\geq(1-\varepsilon)\frac{1+d_N}{d_N}
\geq(1-\varepsilon)\left(1+\frac{\lfloor N/2\rfloor}{\log2}\right).
                                                                    \tag{4.2}
\]

The analogous lower bound holds for right approximate inverses satisfying
\(\|B_NG_N-I\|\leq\varepsilon\).

#### Proof

Choose \(\mu_N\in S_N\) with \(|\mu_N|=d_N\). Applying (4.1) to the unit coordinate
vector \(e_{\mu_N}\) gives

\[
1-\varepsilon
\leq\|G_NB_Ne_{\mu_N}\|
\leq\|G_N\|\,|\beta(\mu_N)|.
\]

Use (2.4) and rearrange. The second inequality in (4.2) follows from (3.1).

For a right approximate inverse, take adjoints. Since \(B_N=B_N^*\),

\[
\|B_NG_N-I\|\leq\varepsilon
\quad\Longrightarrow\quad
\|G_N^*B_N-I\|\leq\varepsilon.
\]

Apply the proved left-inverse bound to \(G_N^*\) and use
\(\|G_N^*\|=\|G_N\|\). ∎

### Consequence

No cofinal family of uniformly bounded exact or fixed-accuracy Green contractions exists, even
though every finite problem is algebraically invertible. Making the finite spectral equation exact
forces arithmetic amplification at least linear in rectangular depth.

## 5. Full essential spectrum

### Theorem 5.1 — interval essential spectrum from two clocks

The spectrum and essential spectrum of \(B\) are both

\[
\sigma(B)=\sigma_{\mathrm{ess}}(B)=[-1,1].                    \tag{5.1}
\]

The point spectrum is the countable dense set

\[
\sigma_{\mathrm p}(B)
=\left\{\frac{\mu}{1+|\mu|}:\mu\in L\setminus\{0\}\right\}.
                                                                    \tag{5.2}
\]

Thus \(B\) has a coordinate eigenbasis but a full interval of essential spectral obstruction.

#### Proof

The additive subgroup \(L=\mathbb Za+\mathbb Zb\) is nondiscrete because \(a/b\) is
irrational. Every nondiscrete additive subgroup of \(\mathbb R\) is dense, so \(L\) is dense in
\(\mathbb R\). The map

\[
\phi(t)=\frac{t}{1+|t|}
\]

is a homeomorphism from \(\mathbb R\) onto \((-1,1)\). Therefore the diagonal values of \(B\)
are dense in \((-1,1)\), and their closure is \([-1,1]\). The spectrum of a bounded diagonal
operator is the closure of its diagonal values, proving the first equality in (5.1). Every diagonal
value is an eigenvalue with coordinate eigenvector, proving (5.2).

Fix \(\lambda\in[-1,1]\). Choose distinct \(\mu_n\in L\setminus\{0\}\) with
\(\phi(\mu_n)\to\lambda\). The coordinate vectors \(e_{\mu_n}\) form an orthonormal sequence,
hence converge weakly to zero, while

\[
\|(B-\lambda I)e_{\mu_n}\|
=|\phi(\mu_n)-\lambda|\to0.
\]

This is a singular Weyl sequence, so every \(\lambda\in[-1,1]\) belongs to the essential
spectrum. The reverse inclusion follows from \(\sigma_{\mathrm{ess}}(B)\subseteq\sigma(B)\).
∎

## 6. Compact-repair no-go

### Theorem 6.1 — compact corrections cannot close the Kummer horizon

Let \(K:\mathcal H\to\mathcal H\) be compact. Then \(B+K\) is not bounded below. Therefore:

1. \(B+K\) has no bounded inverse;
2. if \(B+K\) is injective, its range is not closed;
3. no finite-rank, Hilbert--Schmidt, trace-class, or other compact cross-sector correction produces
   an injective closed-range Kummer Green operator;
4. in Fredholm language, zero remains in the essential spectrum under compact perturbation.

#### Proof

Choose distinct nonzero \(\mu_n\in L\) with \(\mu_n\to0\), possible because \(L\) is dense.
Then \(e_{\mu_n}\) is an orthonormal sequence and hence converges weakly to zero. Compact operators
map weakly convergent bounded sequences to norm-convergent sequences, so

\[
\|Ke_{\mu_n}\|\to0.
\]

Also

\[
\|Be_{\mu_n}\|
=\frac{|\mu_n|}{1+|\mu_n|}\to0.
\]

Therefore

\[
\|(B+K)e_{\mu_n}\|\to0
\]

along unit vectors. Thus \(B+K\) is not bounded below. A boundedly invertible operator is bounded
below, proving item 1. An injective bounded operator with closed range is bounded below, proving item
2. The operator classes in item 3 are compact. Item 4 is also an immediate consequence of invariance
of Fredholm essential spectrum under compact perturbations, or of the singular sequence just built.
∎

### Corollary 6.2 — necessary form of any viable Route-L repair

Any successful repair of the two-prime Kummer phase complex must do at least one of the following:

1. change the domain or graph norm;
2. impose a relative boundary condition that removes or reweights the resonant sequence;
3. add genuinely noncompact cross-sector incidence acting nontrivially on every small-divisor mode;
4. abandon scalar Hilbert completion for a topology that retains a separated source quotient.

A compact correction on the existing Hilbert carrier is impossible.

This does not prove that any listed repair exists or yields RH. It removes a broad and natural class
from the live conjectural debt.

## 7. Noncommuting-exactification interpretation

The exactification geometry is now source-computed:

- arithmetic clocks: \(m\log2+n\log3\);
- precision metric: \(\Delta_N=B_N^*B_N\);
- horizon coordinate: \(d_N\), the shortest clock mismatch;
- finite sharpness: \(\lambda_N>0\);
- cofinal horizon: \(\lambda_N\downarrow0\);
- capacity blow-up: \(\|B_N^{-1}\|\uparrow\infty\);
- stable obstruction: \(0\in\sigma_{\mathrm{ess}}(B)\);
- repair law: compact observer coupling cannot move the essential horizon.

This is a literal phase geometry of two arithmetic times. The phase ratio
\(\log3/\log2\) determines where finite observer charts become nearly resonant. No black-hole or
wormhole claim is needed.

## 8. Hostile review

### Attack A — the law only restates that the diagonal has small entries

The parent card already proved small entries and nonclosed range. New content here is the exact
finite gap, quantitative inverse/approximate-inverse cost, full essential spectrum, and stability
under **every** compact repair.

### Attack B — a clever finite-rank correction can target the bad modes

It can target finitely many. The resonant coordinate vectors form an infinite orthonormal sequence;
compactness forces the correction to vanish along a subsequence. Theorem 6.1 is uniform over all
compact choices.

### Attack C — essential spectrum depends on self-adjoint compact perturbations

The direct not-bounded-below proof allows arbitrary compact \(K\), not necessarily self-adjoint.
The Fredholm phrasing is supplementary.

### Attack D — rectangular truncation is arbitrary

The exact formulas (2.4)--(2.6) hold for any finite mode set after replacing \(d_N\) by its least
absolute frequency. Rectangles provide a canonical arithmetic exhaustion and elementary rates.

### Attack E — this creates nonzero reduced cohomology

It does not. It proves the opposite for a wide repair class. The positive survivor is a necessary
design law: relative-domain or genuinely noncompact incidence is unavoidable.

## 9. Novelty and significance verdict

- **New unconditional route theorem:** compact perturbations cannot repair the actual two-prime
  Kummer dense-range obstruction.
- **New quantitative law:** finite inverse and fixed-accuracy approximate-inverse norms grow at least
  linearly with rectangular arithmetic depth.
- **New spectral classification:** pure coordinate eigenvectors coexist with essential spectrum
  \([-1,1]\).
- **Route effect:** eliminates finite-rank, Hilbert--Schmidt, trace-class, and compact cross-sector
  Green repairs from the surviving Route-L conjecture.
- **RH ceiling:** no nonzero separated Hodge space is constructed; goal remains open.

## 10. Lean return notes

Do not write Lean now. Existing parent formalization already contains the arithmetic small-divisor
sequence and dense/nonclosed diagonal range. Later formalization can extend

`formal/GaloisForLFunctions/RHTower/Deninger/DeningerTwoPrimeKummerDenseNonclosedRange.lean`

with separately reviewed theorems for:

1. finite diagonal minimum/inverse norm;
2. elementary rectangular Dirichlet upper and integer-separation lower bounds;
3. approximate-inverse norm lower bound;
4. compact operators on orthonormal sequences;
5. diagonal spectrum and Weyl sequences.

This path is a note for later; no Lean file is edited or built in this phase.
