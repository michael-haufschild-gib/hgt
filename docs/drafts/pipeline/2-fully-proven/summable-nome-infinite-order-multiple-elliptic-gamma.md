# Universal Hadamard--Schatten renormalization law for infinite-order multiple elliptic gamma functions

Status: Stage 2 — [PAPER-PROVED], exact strengthened theorem ready for formalization

## Research question

For which arbitrary infinite nome families does the finite-order multiple
elliptic gamma hierarchy possess a symmetric, nontrivial canonical limit?
What is the exact minimal Hadamard renormalization, and which functional,
parity, scaling, and infinitesimal laws survive?

## Active claim

**[CONJECTURE — Universal Hadamard--Schatten renormalization law.]** Let \(A\) be an
arbitrary infinite index set and let \(p:A\to\mathbb C\) satisfy
\[
0<|p_a|<1.
\]
For an arbitrary integer \(g\ge0\), put
\[
E_g(w)=(1-w)\exp\left(\sum_{m=1}^{g}\frac{w^m}{m}\right).
\]
For each finite \(S\subset A\), replace every \(q\)-Pochhammer factor
\(1-w\) in the standard product by \(E_g(w)\), obtaining the canonical
genus-\(g\) finite product \(G_{S,g}\), and set
\[
H_{S,g}=G_{S,g}^{(-1)^{|S|+1}}.
\]
Then the following three statements are equivalent:
\[
\sum_{a\in A}|p_a|^{g+1}<\infty;
\qquad
\sum_{\nu\in\mathbb N^{(A)}\setminus\{0\}}
 |p^\nu|^{g+1}<\infty;
\]
\[
\mathcal G_{A,g}(x)
 =\prod_{\nu\in\mathbb N^{(A)}}E_g(xp^\nu)
\quad\text{converges normally on }\mathbb C;
\]
whenever they hold,
\[
H_{S,g}\longrightarrow\mathcal G_{A,g}
\quad\text{locally uniformly on }\mathbb C^\times.
\]
More fundamentally, for every real exponent \(\sigma>0\),
\[
\sum_{\nu\in\mathbb N^{(A)}}|p^\nu|^\sigma
=\sup_{S\in\operatorname{Fin}(A)}
  \prod_{a\in S}(1-|p_a|^\sigma)^{-1}, \tag{C1}
\]
and this quantity is finite exactly when
\(\sum_a|p_a|^\sigma<\infty\). Hence the one-particle and full bosonic
occupation spectra have the same critical exponent
\[
\rho(p):=\inf\left\{\sigma>0:\sum_a|p_a|^\sigma<\infty\right\}
=\inf\left\{\sigma>0:
  \sum_{\nu\ne0}|p^\nu|^\sigma<\infty\right\}. \tag{C2}
\]
The real convergence set is empty or an upper interval, with its critical
endpoint included exactly when the critical power sum converges.
Consequently every infinite nome family has an exact convergence spectrum
\[
\mathfrak S(p)=
\left\{g\in\mathbb N:
\sum_{a\in A}|p_a|^{g+1}<\infty\right\},
\]
which is either empty or an upper ray. This decides, for every family and
every finite genus, whether the canonical Weierstrass-primary-factor
completion is normally convergent. Genus zero is exactly the unmodified standard
hierarchy and occurs precisely when \(\sum_a|p_a|<\infty\).

For every \(a\in A\) and every convergent genus,
\[
\mathcal G_{A,g}(x)
 =\mathcal G_{A\setminus\{a\},g}(x)
  \mathcal G_{A,g}(p_a x).
\]
Parity normalization is necessary at every convergent genus:
unnormalized even and odd finite sections have reciprocal cluster limits
\(\mathcal G_{A,g}^{-1}\) and \(\mathcal G_{A,g}\).

At every convergent genus, if \(d=g+1\),
\(Q_S=\prod_{a\in S}p_a\), and \(F_{S,g}\) is the forward factor, the
collapsed contribution has a complete counterterm jet. For every integer
\(N\ge d\),
\[
\frac{\displaystyle
 \log F_{S,g}(x)+
 \sum_{m=d}^{N-1}\frac{Q_S^m x^{-m}}{m}M_{S,m}}
 {Q_S^N}
\longrightarrow
-\frac{x^{-N}}{N}M_{A,N}, \tag{C3}
\]
locally uniformly on \(\mathbb C^\times\), using the logarithm branch
selected by \(F_{S,g}\to1\), where
\[
M_{S,m}=\prod_{a\in S}(1-p_a^m)^{-1},\qquad
M_{A,m}=\prod_{a\in A}(1-p_a^m)^{-1}.
\]
The former tangent law is the case \(N=d\).

For finite \(S\), the genus-\(g\) product differs from the standard
multiple elliptic gamma by an explicit exponential Laurent-polynomial
gauge:
\[
\prod_{\nu\in\mathbb N^S}E_g(tp^\nu)
=\prod_{\nu\in\mathbb N^S}(1-tp^\nu)
 \exp\left(
 \sum_{m=1}^{g}\frac{t^m}{m}
 \prod_{a\in S}(1-p_a^m)^{-1}\right).
\]
This gauge is differentially algebraic, so the exact finite-section
rational-rank differential phase law is unchanged at every genus.
For any two convergent genera \(h>g\), the infinite completions themselves
obey the exact scheme-change law
\[
\frac{\mathcal G_{A,h}(x)}{\mathcal G_{A,g}(x)}
=\exp\left(
  \sum_{m=g+1}^{h}\frac{x^m}{m}M_{A,m}\right). \tag{C4}
\]
Thus all admissible schemes have exactly the same divisor and differ only
by an explicit finite local counterterm. The critical exponent, divisor,
coface system, parity obstruction, and finite differential phase are
scheme-independent.

Finally, for any moving coordinate \(x_S\) such that
\[
x_S\to x,\qquad Q_S/x_S\to y,
\]
one has \(xy=0\). Every finite two-coordinate scaling limit is obtained by
substituting \(x\) and \(y\) into \(\mathcal G_{A,g}\); no scaling retains
two nonzero gamma halves.

This is one capstone claim: real critical exponent, existence, sharpness,
complete genus spectrum, exact scheme changes, finite-section limit, coface
law, parity obstruction, all counterterm jets, and two-axis scaling
classification form one universal boundary theorem.

## Fock-space representation

Interpret \(p_a\) as one-particle eigenvalues of a strict diagonal
contraction \(P\). The bosonic occupation basis is indexed by
\(\nu\in\mathbb N^{(A)}\), and the multiplicative second quantization
\(\Gamma_s(P)\) has eigenvalues \(p^\nu\). For every real
\(\sigma>0\), the sharp mass identity becomes
\[
\Gamma_s(P)\in S_\sigma
\quad\Longleftrightarrow\quad
P\in S_\sigma,
\]
and, in the positive diagonal case,
\[
\operatorname{Tr}|\Gamma_s(P)|^\sigma
=\prod_{a\in A}(1-|p_a|^\sigma)^{-1}. \tag{F1}
\]
Thus multiplicative bosonic second quantization preserves the entire
Schatten spectrum and its critical exponent, not merely one integer ideal.
For \(d=g+1\), moreover,
\[
\mathcal G_{A,g}(x)
=\det_d\!\left(I-x\Gamma_s(P)\right).
\]
Thus genus is the minimal regularized Fredholm-determinant order forced by
the one-particle Schatten spectrum. The coface law is the exact
vacuum/excited-sector decomposition for any selected mode. This
representation is part of the theorem only in the diagonal occupation
model actually proved; no unsupported extension to arbitrary nonnormal
operators is allowed.

## Intended proof representation

Write the finite genus-\(g\) product as a backward factor \(B_{S,g}\) and
a forward factor \(F_{S,g}\). Parity normalization gives
\[
H_{S,g}=B_{S,g}F_{S,g} \quad (|S|\ \text{odd}),\qquad
H_{S,g}=B_{S,g}/F_{S,g} \quad (|S|\ \text{even}).
\]
The backward factors exhaust the finitely supported multi-indices and
should converge to \(\mathcal G_{A,g}\). Power summability forces
\(\prod_{a\in S}|p_a|\to0\), so both \(F_{S,g}\) and \(F_{S,g}^{-1}\)
should converge locally uniformly to \(1\). Coface follows by partitioning
finitely supported multi-indices according to whether \(\nu_a=0\).

## Sharp mass identity

For \(r_a=|p_a|\) and \(d=g+1\),
\[
\sum_{\nu\in\mathbb N^{(A)}}r^{d\nu}
=\sup_{S\subset A,\ S\text{ finite}}
\prod_{a\in S}(1-r_a^d)^{-1}.
\]
Necessity of \(\sum_a r_a^d<\infty\) follows from the singleton
multi-indices. Sufficiency follows from convergence of the infinite product,
using \(-\log(1-r_a^d)\le 2r_a^d\) outside a finite set.

## Dependency-complete paper proof

Put \(d=g+1\), let
\(\mathcal N_A=\mathbb N^{(A)}\) be the finitely supported occupation
multi-indices, and write
\[
p^\nu=\prod_{a\in A}p_a^{\nu_a},\qquad
r^\nu=\prod_{a\in A}|p_a|^{\nu_a}.
\]
All sums over arbitrary sets mean unordered sums, and all finite-section
limits are nets over \(\operatorname{Fin}(A)\), directed by inclusion.

### Lemma 1: exact occupation mass at every real exponent

Fix any real \(\sigma>0\). For every finite \(S\subset A\),
\[
\sum_{\operatorname{supp}\nu\subset S}(r^\nu)^\sigma
=\prod_{a\in S}\sum_{n\ge0}r_a^{\sigma n}
=\prod_{a\in S}(1-r_a^\sigma)^{-1}. \tag{1}
\]
Every finite set of occupations is contained in the occupations supported
on one finite \(S\). Hence nonnegative unordered summation gives
\[
\sum_{\nu\in\mathcal N_A}(r^\nu)^\sigma
=\sup_{S\in\operatorname{Fin}(A)}
\prod_{a\in S}(1-r_a^\sigma)^{-1}. \tag{2}
\]
If the left side is finite, its singleton occupations imply
\(\sum_a r_a^\sigma<\infty\). Conversely, assume this last sum is finite.
Then \(r_a^\sigma\to0\) in the unordered sense. Outside a finite set,
\(r_a^\sigma\le1/2\), and
\[
0\le-\log(1-r_a^\sigma)\le2r_a^\sigma.
\]
Thus the finite products in (2) are uniformly bounded, so the occupation
mass is finite. This proves
\[
\sum_{\nu\ne0}(r^\nu)^\sigma<\infty
\quad\Longleftrightarrow\quad
\sum_a r_a^\sigma<\infty. \tag{3}
\]
It also proves that a convergent family is countable: for every \(n\), only
finitely many \(a\) can satisfy \(r_a^\sigma\ge1/n\), and their countable union
contains \(A\).

Since \(0<r_a<1\), convergence at \(\sigma\) implies convergence at every
larger exponent. If the real convergence set is nonempty and has infimum
\(\rho\), then every exponent larger than \(\rho\) belongs to it; the
endpoint belongs exactly when its power sum converges. Applying (3) for
every \(\sigma>0\) proves (C1)--(C2), including \(\rho=\infty\) when the
set is empty. The integer genus spectrum is precisely the intersection of
this real interval with \(\{g+1:g\in\mathbb N\}\).

### Lemma 2: exact normal-convergence threshold

The entire function \(E_g(w)-1\) has a zero of exact order \(d\) at zero,
because
\[
\log E_g(w)=-\sum_{m=d}^{\infty}\frac{w^m}{m},
\qquad |w|<1. \tag{4}
\]
For every \(R>0\), removal of that zero gives a finite constant \(C_R\)
such that
\[
|E_g(w)-1|\le C_R|w|^d,\qquad |w|\le R. \tag{5}
\]
If (3) holds, then on \(|x|\le R\),
\[
\sum_{\nu\in\mathcal N_A}|E_g(xp^\nu)-1|
\le C_RR^d\sum_{\nu\in\mathcal N_A}r^{d\nu}<\infty. \tag{6}
\]
The Weierstrass product therefore converges normally and defines an entire
function \(\mathcal G_{A,g}\).

Conversely, suppose the product is normal on a disk \(|x|\le R\).
The singleton occupations form a subfamily. If
\[
M_a=\sup_{|x|\le R}|E_g(xp_a)-1|,
\]
Cauchy's coefficient estimate applied to the coefficient
\(-p_a^d/d\) of \(x^d\) gives
\[
M_a\ge \frac{R^d}{d}|p_a|^d. \tag{7}
\]
Normal convergence forces \(\sum_aM_a<\infty\), hence
\(\sum_a|p_a|^d<\infty\). This proves exact necessity, not merely a
sufficient majorant.

The factor \(\nu=0\) gives \(E_g(x)\), so
\(\mathcal G_{A,g}(0)=1\) and \(\mathcal G_{A,g}(1)=0\).
The limit is nonconstant. For \(|x|<1\), absolute rearrangement of (4)
gives the exact regularized free energy
\[
\log\mathcal G_{A,g}(x)
=-\sum_{m=d}^{\infty}\frac{x^m}{m}M_{A,m},
\qquad
M_{A,m}:=\prod_{a\in A}(1-p_a^m)^{-1}. \tag{8}
\]
Indeed \(\sum_a|p_a|^m<\infty\) for every \(m\ge d\), and
\[
|M_{A,m}|
\le\prod_a(1-r_a^m)^{-1}
\le\prod_a(1-r_a^d)^{-1}. \tag{9}
\]

### Lemma 3: finite-section exhaustion

Let
\[
\Phi_{S,g}(t)
=\prod_{\nu\in\mathbb N^S}E_g(tp^\nu).
\]
After extending \(\nu\) by zero outside \(S\), this is the subproduct over
occupations supported on \(S\). The support sets exhaust
\(\mathcal N_A\). Given a compact disk and \(\varepsilon>0\), normal
convergence supplies a finite set of occupations whose complementary
factor tail is \(<\varepsilon\); the union of their supports is one finite
\(S_0\). Therefore
\[
\Phi_{S,g}\longrightarrow\mathcal G_{A,g}
\quad\text{locally uniformly on }\mathbb C. \tag{10}
\]
This is a net statement and uses no enumeration of \(A\).

### Lemma 4: forward collapse and the infinite gamma limit

Define \(Q_S=\prod_{a\in S}p_a\). Since \(A\) is infinite and
\(\sum_a r_a^d<\infty\), for every \(\varepsilon>0\) there is an
\(a\in A\) with \(r_a<\varepsilon\). For every \(S\supset\{a\}\),
\[
|Q_S|\le r_a<\varepsilon,
\]
so \(Q_S\to0\). The finite backward and forward factors are
\[
B_{S,g}(x)=\Phi_{S,g}(x),\qquad
F_{S,g}(x)=\Phi_{S,g}(Q_S/x). \tag{11}
\]
Equation (10), uniformity on a fixed disk, and \(Q_S/x\to0\) uniformly on
compact subsets of \(\mathbb C^\times\) give
\[
B_{S,g}\to\mathcal G_{A,g},\qquad F_{S,g}\to1. \tag{12}
\]
The second convergence is eventually within \(1/2\) of \(1\), so
\(F_{S,g}\) is then zero-free on the compact and
\(F_{S,g}^{-1}\to1\).

By the parity definition,
\[
G_{S,g}=
\begin{cases}
F_{S,g}/B_{S,g},&|S|\text{ even},\\
F_{S,g}B_{S,g},&|S|\text{ odd}.
\end{cases}
\]
Consequently
\[
H_{S,g}:=G_{S,g}^{(-1)^{|S|+1}}
=
\begin{cases}
B_{S,g}/F_{S,g},&|S|\text{ even},\\
F_{S,g}B_{S,g},&|S|\text{ odd}
\end{cases}
\longrightarrow\mathcal G_{A,g}. \tag{13}
\]

Both parity subposets of \(\operatorname{Fin}(A)\) are cofinal and
directed: enlarge any finite union by at most one fresh element to obtain
the requested parity. Along odd sections the raw \(G_{S,g}\) tends to
\(\mathcal G_{A,g}\); along even sections it tends meromorphically to
\(\mathcal G_{A,g}^{-1}\). These limits differ because one has a zero at
\(x=1\) and the other a pole. Hence the raw net does not converge, and
parity normalization is necessary.

### Lemma 5: coface and dependence on every nome

Fix \(a\in A\). Partition occupations into \(\nu_a=0\) and
\(\nu_a\ge1\). The first part is \(\mathcal N_{A\setminus\{a\}}\);
subtracting one from \(\nu_a\) identifies the second part with
\(\mathcal N_A\) and changes \(p^\nu\) to \(p_ap^\nu\). Normal convergence
permits the partition:
\[
\mathcal G_{A,g}(x)
=\mathcal G_{A\setminus\{a\},g}(x)
 \mathcal G_{A,g}(p_ax). \tag{14}
\]
The second factor is nonconstant: it equals \(1\) at \(x=0\) and vanishes
at \(x=p_a^{-1}\). Thus every nome contributes nontrivially.

### Lemma 6: complete finite two-coordinate scaling boundary

Let \(x_S\ne0\), \(x_S\to x\), and \(Q_S/x_S\to y\). Since
\[
x_S(Q_S/x_S)=Q_S\to0,
\]
continuity gives \(xy=0\). Equation (10) at moving points gives
\[
B_{S,g}(x_S)\to\mathcal G_{A,g}(x),\qquad
F_{S,g}(x_S)\to\mathcal G_{A,g}(y). \tag{15}
\]
Therefore every finite two-coordinate scaling limit is
\[
\begin{array}{c|c|c}
&|S|\text{ even}&|S|\text{ odd}\\ \hline
G_{S,g}&
\mathcal G_{A,g}(y)/\mathcal G_{A,g}(x)&
\mathcal G_{A,g}(y)\mathcal G_{A,g}(x)
\end{array} \tag{16}
\]
with quotients understood meromorphically. Because \(xy=0\) and
\(\mathcal G_{A,g}(0)=1\), the boundary consists exactly of the forward
axis, the backward axis, and their common origin. Two nonzero gamma halves
cannot survive any finite scaling.

### Lemma 7: complete counterterm jet of the collapsed half

For a compact \(K\subset\mathbb C^\times\), let
\(\delta=\min_{x\in K}|x|>0\). For large \(S\),
\(|Q_S|/\delta<1\), and (4) selects a canonical logarithm:
\[
\log F_{S,g}(x)
=-\sum_{m=d}^{\infty}
\frac{Q_S^m x^{-m}}{m}M_{S,m},
\qquad
M_{S,m}=\prod_{a\in S}(1-p_a^m)^{-1}. \tag{17}
\]
Absolute product convergence gives
\(M_{S,m}\to M_{A,m}\) for each \(m\ge d\). From (9), uniformly in \(S\)
and \(m\ge d\),
\(|M_{S,m}|\le C_d:=\prod_a(1-r_a^d)^{-1}\). After division by
\(Q_S^d\), the terms \(m>d\) have uniform bound
\[
C_d\delta^{-d}
\frac{|Q_S|/\delta}{1-|Q_S|/\delta}\longrightarrow0. \tag{18}
\]
More generally, fix any \(N\ge d\). Truncating (17) after \(m=N\) gives
\[
\sup_{x\in K}\left|
\log F_{S,g}(x)+
\sum_{m=d}^{N}\frac{Q_S^m x^{-m}}mM_{S,m}
\right|
\le C_{K,N}|Q_S|^{N+1}, \tag{19}
\]
because the remaining geometric tail is bounded by
\[
C_d\sum_{m=N+1}^{\infty}\frac{|Q_S|^m\delta^{-m}}m.
\]
Divide (19), with the \(m=N\) term restored, by \(Q_S^N\).
The remainder tends uniformly to zero and \(M_{S,N}\to M_{A,N}\).
Therefore
\[
\frac{\displaystyle
\log F_{S,g}(x)+
\sum_{m=d}^{N-1}\frac{Q_S^m x^{-m}}mM_{S,m}}
{Q_S^N}
\longrightarrow
-\frac{x^{-N}}N M_{A,N} \tag{20}
\]
locally uniformly on \(\mathbb C^\times\). This proves (C3) simultaneously
for every counterterm order. The finite-section coefficients \(M_{S,m}\)
are essential: replacing them prematurely by \(M_{A,m}\) would require a
rate of convergence not implied by the theorem's sharp hypotheses.

### Lemma 8: exact scheme-change law and finite differential phase

For finite \(S\), absolute summation of the exponent in \(E_g\) gives
\[
\Phi_{S,g}(t)
=\Phi_{S,0}(t)
\exp\left(
\sum_{m=1}^{g}\frac{t^m}{m}
\prod_{a\in S}(1-p_a^m)^{-1}\right). \tag{21}
\]
Substitution \(t=x\) and \(t=Q_S/x\), with the parity product or quotient,
shows that \(G_{S,g}/G_{S,0}\) is the exponential of a finite Laurent
polynomial in \(x=e^{2\pi iz}\). The functions \(x\) and \(x^{-1}\)
satisfy first-order linear differential equations; a finite Laurent
polynomial in them is differentially algebraic, and adjoining its
exponential is a differential-algebraic extension. Hence the gauge and
its logarithmic derivative are differentially algebraic over
\(\mathbb C(z)\).

Multiplication or division by a nonzero differentially algebraic function
preserves both differential algebraicity and hypertranscendence. Addition
of its logarithmic derivative does the same. Therefore the already proved
finite rational-rank classification for \(G_{S,0}\) and \(G'_{S,0}/G_{S,0}\)
holds unchanged for \(G_{S,g}\) and \(G'_{S,g}/G_{S,g}\), for every finite
\(S\) and every genus \(g\).

For \(h>g\), the primary factors satisfy identically
\[
E_h(w)=E_g(w)
\exp\left(\sum_{m=g+1}^{h}\frac{w^m}{m}\right).
\]
If genus \(g\) converges, Lemma 1 gives absolute summability of
\((p^\nu)^m\) for every \(m\ge g+1\). Multiplying over all occupations and
using
\[
\sum_{\nu\in\mathcal N_A}(p^\nu)^m
=\prod_{a\in A}(1-p_a^m)^{-1}=M_{A,m}
\]
proves (C4). Its quotient is a nowhere-zero exponential polynomial.
Therefore every admissible genus has the same zero divisor, and the
scheme-independent content is exactly separated from the finite local
counterterm.

### Lemma 9: exact diagonal bosonic Fock spectrum and determinant

Under (3), \(A\) is countable. On the occupation Hilbert space with
orthonormal basis \((e_\nu)_{\nu\in\mathcal N_A}\), define the diagonal
multiplicative second quantization by
\[
\Gamma_s(P)e_\nu=p^\nu e_\nu,
\]
where \(Pe_a=p_ae_a\) on the one-particle space. Its singular values are
\(r^\nu\). Equations (2)--(3), now for every \(\sigma>0\), give
\[
\Gamma_s(P)\in S_\sigma
\Longleftrightarrow P\in S_\sigma,\qquad
\operatorname{Tr}|\Gamma_s(P)|^\sigma
=\prod_{a\in A}(1-r_a^\sigma)^{-1}. \tag{22}
\]
This proves equality of the complete real Schatten spectra and their
critical exponents. This identity is a standard parent Fock trace
mechanism and is classified here as **[BRIDGE]**, not as the paper's
standalone novelty.

For the integer \(d=g+1\), by the eigenvalue definition of the order-\(d\)
regularized Fredholm
determinant,
\[
\det_d(I-x\Gamma_s(P))
=\prod_{\nu\in\mathcal N_A}E_{d-1}(xp^\nu)
=\mathcal G_{A,g}(x). \tag{23}
\]
Equation (8) is equivalently the convergent trace expansion
\[
\log\det_d(I-x\Gamma_s(P))
=-\sum_{m=d}^{\infty}\frac{x^m}{m}
\operatorname{Tr}\Gamma_s(P)^m,\qquad |x|<1. \tag{24}
\]
This proves the operator interpretation rather than adding it by analogy.

### Conclusion

Lemmas 1--9 prove every component of the strengthened active claim.
Lemma 1 classifies every real exponent, not only determinant orders.
Its intersection with the positive integers gives the empty-or-upper-ray
genus spectrum. If the spectrum is empty, Lemma 2 proves that no
finite-genus symmetric normal completion exists. Lemma 8 classifies every
change between admissible schemes, and Lemma 7 recovers every asymptotic
counterterm coefficient of the collapsed half. This exhausts every nome
family, every positive real spectral exponent, every finite Hadamard genus,
every pair of admissible genera, and every finite counterterm order.

## Hostile threats

1. Genus zero may be dismissed as merely an infinite-variable
   \(q\)-Pochhammer symbol. Required answer: prove it is exactly the
   parity-renormalized standard hierarchy limit and prove the full sharp
   genus spectrum, rather than merely naming one product.
2. The forward half collapses to \(1\). Required answer: state this as a
   rigidity theorem and show that the remaining product is nonconstant,
   genuinely depends on every nome, and retains every coface equation.
   Recover and prove the universal tangent law of the collapsed half.
3. Raw finite sections do not converge because order parity oscillates.
   Required answer: prove reciprocal cluster limits and the necessity of the
   normalization.
4. “Infinite” could hide a sequential enumeration. Required answer: formulate
   all limits as nets over finite subsets of an arbitrary index set.
5. A convergence assumption could be stronger than needed. Required answer:
   prove the equivalence at every genus and the empty-or-upper-ray
   classification. Distinguish symmetric normal convergence from
   order-dependent conditional regularizations.
6. Differential-algebraic classification need not survive locally uniform
   limits. Do not claim such a phase law for \(\mathcal G_A\) without a
   separate proof. Prove only that every finite genus renormalization is a
   differential-algebraic gauge and therefore preserves the already proved
   finite-section phase law.
7. Novelty could fail if countably-nome multiple \(q\)-products already occur
   in the literature. Complete an external state-of-the-art audit before
   promotion.
8. The Fock-space language could be decorative. Required answer: prove the
   exact occupation-spectrum/Schatten/determinant identities and use them to
   identify genus as a forced operator-ideal threshold, not an analogy.
9. Integer genera could conceal the real invariant. Required answer: classify
   every real power exponent first and recover the genus spectrum as its
   integer shadow.
10. Higher genera could be unrelated regularizations. Required answer: prove
    the exact quotient (C4), show that it is a finite local counterterm, and
    identify the resulting scheme-independent divisor.
11. One tangent coefficient could conceal uncontrolled higher corrections.
    Required answer: prove the locally uniform jet (C3) at every order. Keep
    the finite-section coefficients \(M_{S,m}\); limiting coefficients cannot
    be substituted without an unavailable convergence rate.

## Internal frontier

- Existing corpus proves products and logarithmic convergence for every
  finite order.
- Existing publication-ready paper proves a universal finite-section
  rational-rank phase law but explicitly excludes an actual infinite-order
  product.
- No internal theorem currently supplies a countably infinite nome product,
  its sharp convergence criterion, or a finite-section limit theorem.

## External frontier

Narukawa's multiple elliptic gamma functions, Winding's cone
generalizations, and current supersymmetric-partition-function uses all
retain a fixed finite number of nomes. Standard bosonic Fock theory already
contains the trace identity
\(\operatorname{Tr}\Gamma_s(T)=\det(I-T)^{-1}\); regularized Fredholm
determinants already contain the primary-factor mechanism. These are parent
theories and make the isolated real-Schatten equivalence and isolated
scheme-change formula **[BRIDGE]** results. Focused searches through July
2026 found no source stating a countably-nome, parity-normalized exhaustion
with its exact real critical exponent, complete genus spectrum, two-axis
boundary, and all-order collapsed-half jet. This supports
**[NOVELTY UNVERIFIED]**, not a priority claim: independent expert search is
still required before **[CANDIDATE NEW SCIENTIFIC KNOWLEDGE]**.

## Hostile proof-audit verdict

**[PAPER-PROVED].** Lemmas 1--9 close the strengthened theorem without a
conditional step. Attacks applied:

- unordered rather than sequential convergence;
- necessity, not only sufficiency, of the power-summability threshold;
- zeros and poles in parity limits;
- moving-coordinate limits at both boundary axes;
- uniform control of every counterterm-jet remainder;
- exact rather than metaphorical Fock/Schatten identification;
- all positive real Schatten exponents rather than integer determinant
  orders alone;
- exact finite counterterm relating every pair of admissible genera;
- necessity of moving finite-section coefficients in the all-order jet;
- preservation of functions and logarithmic derivatives under the finite
  DA gauge;
- nontrivial dependence on every nome;
- empty convergence spectrum and impossibility of any finite canonical
  genus in that case.

Two scope restrictions are binding. “Minimal genus” always means the
canonical primary factors \(E_g\), not every conceivable order-dependent or
zeta regularization. The operator theorem concerns the diagonal normal
occupation model actually defined in Lemma 9, not arbitrary nonnormal
operators.

Mathematical proof is closed. Novelty and general-journal significance remain
separate gates: standard Fock trace and regularized-determinant identities
must be cited as parents, while novelty is claimed only for their exact
synthesis with the infinite-nome elliptic-gamma limit, parity obstruction,
real critical exponent, full genus spectrum, scheme-change torsor, scaling
boundary, complete counterterm jet, and finite differential-phase
invariance.

## Formalization ledger

Namespace `HTGeometry`, area umbrella `GaloisForLFunctions.HTGeometry`.  All entries below have a
clean `#print axioms` (`propext`, `Classical.choice`, `Quot.sound` only).

### Closed in Lean

| Card item | Lean |
|---|---|
| Lemma 1, (C1) at integer genus | `nomeOccupationMass_eq_iSup_finset` |
| Lemma 1, (C1) at every real exponent | `nomeOccupationMass_rpow_eq_iSup_finset` |
| Lemma 1, (3) at integer genus | `summable_nomeMonomial_pow_iff` |
| Lemma 1, (3) at every real exponent | `summable_nomeMonomial_rpow_iff` |
| Lemma 1, (C2) | `nomeOccupationSummabilitySpectrum_eq` |
| Lemma 1, upper-ray classification | `summable_nome_rpow_mono`, `summable_nomeMonomial_rpow_mono` |
| Lemma 2, sufficiency (6) | `infiniteMultipleEllipticGamma_hasProdLocallyUniformlyOn`, `infiniteMultipleEllipticGamma_analytic` |
| Lemma 2, (4) — the exact primary-factor logarithm | `primaryFactor_eq_exp_neg_primaryLogTail` |
| Lemma 2, (5)/(7) — necessity of the genus | `primaryFactor_sub_one_norm_ge`, `summable_pow_of_normal_majorant`, `summable_nome_pow_of_normal_majorant` |
| Lemma 2, the exact criterion | `summable_nome_pow_iff_exists_normal_majorant` |
| Lemma 3, (10) | `finiteNomeSection`, `tendsto_finiteNomeSection` |
| Lemma 5, (14) | `infiniteMultipleEllipticGamma_tower_hasProd`, `infiniteMultipleEllipticGamma_coface` |
| Lemma 2, values and nonconstancy | `infiniteMultipleEllipticGamma_at_zero`, `infiniteMultipleEllipticGamma_at_one`, `infiniteMultipleEllipticGamma_nonconstant` |
| Lemma 5, second half — every nome contributes | `infiniteMultipleEllipticGamma_shift_nonconstant` |
| Lemma 4, `Q_S → 0` | `tendsto_nomeProduct_atTop_zero` |
| Lemma 4, uniform smallness of the sections near 0 | `norm_finiteNomeSection_sub_one_le` |
| Lemma 4, (12) forward collapse `F_{S,g} → 1` | `tendsto_forwardNomeFactor_one` |
| Lemma 4, (13) `H_{S,g} → 𝒢_{A,g}` | `tendsto_parityNormalizedSection` |
| Lemma 4, reciprocal cluster limits | `tendsto_rawSection_odd`, `tendsto_rawSection_even`, `evenCard_neBot`, `oddCard_neBot` |
| Lemma 4, necessity of parity normalization | `sq_eq_one_of_tendsto_rawSection`, `exists_point_of_half`, `exists_rawSection_not_convergent` |
| Lemma 6, moving-point collapse | `tendsto_finiteNomeSection_one_of_tendsto_zero` |
| Lemma 6, the boundary `xy = 0` | `scalingBoundary_mul_eq_zero` |
| Lemma 6, no scaling keeps two gamma halves | `scalingBoundary_half_collapses` |
| Lemma 6, moving-coordinate convergence | `exists_primaryFactor_sub_one_bound`, `tendsto_finiteNomeSection_moving` |
| Lemma 6, the full table (15)/(16) | `tendsto_scalingTable` |
| finite-index geometric identity over ℂ | `hasSum_pi_geometric`, `summable_norm_pi_geometric` |
| occupation moments are nome Euler products | `nomeMonomial_pow`, `summable_norm_pow_of_le`, `tsum_nomeMonomial_pow` |
| occupation Euler product over ℂ | `hasSum_supported_nomeMonomial`, `hasProd_inv_one_sub_nome`, `tsum_nomeMonomial_eq_tprod` |
| Lemma 2, (8) in summed-tail form | `norm_primaryLogTail_le`, `hasProd_cexp`, `infiniteMultipleEllipticGamma_eq_exp_neg_tsum` |
| Lemma 2, (8) in moment form | `norm_logTail_term_le`, `summable_logTail_family`, `tsum_logTail_family_occupation`, `infiniteMultipleEllipticGamma_eq_exp_neg_moments` |
| Lemma 7, (17) — the finite-section free energy | `finiteNomeSection_eq_restricted`, `finiteNomeSection_eq_exp_neg_moments` |
| Lemma 8, (C4) and scheme-independent divisor | `infiniteMultipleEllipticGamma_scheme_change`, `infiniteMultipleEllipticGamma_scheme_change_eq_zero_iff` |

New modules: `HTGeometry/PrimaryFactorLogExpansion.lean`,
`HTGeometry/InfiniteMultipleEllipticGammaSharpness.lean`,
`HTGeometry/InfiniteMultipleEllipticGammaValues.lean`,
`HTGeometry/InfiniteMultipleEllipticGammaCollapse.lean`,
`HTGeometry/InfiniteMultipleEllipticGammaScaling.lean`,
`HTGeometry/InfiniteMultipleEllipticGammaMovingPoint.lean`,
`HTGeometry/InfiniteMultipleEllipticGammaFreeEnergy.lean`,
`HTGeometry/PiGeometricSeries.lean`,
`HTGeometry/OccupationEulerProduct.lean`,
`HTGeometry/InfiniteMultipleEllipticGammaMoments.lean`,
`HTGeometry/InfiniteMultipleEllipticGammaMomentForm.lean`,
`HTGeometry/FiniteNomeSectionRestriction.lean`.

### Open in Lean

1. Lemma 7, the jet (C3)/(20).  Its input (17) is closed: a finite section is the infinite product
   of the restricted nome family (`finiteNomeSection_eq_restricted`), so its free energy is the
   moment series with the finite Euler products `M_{S,m} = ∏_{a∈S}(1-p_a^m)^{-1}` as coefficients.
   What remains: write `log F_{S,g}(x) = -∑_{m≥d} (Q_S/x)^m M_{S,m}/m` from that, subtract the
   counterterms through order `N-1`, divide by `Q_S^N`, and show the remaining tail tends to zero
   uniformly on a compact of `ℂ^×` while `M_{S,N} → M_{A,N}`.  The last convergence is already
   available: `hasProd_inv_one_sub_nome` applied at `p^N` *is* the statement that the finite Euler
   products converge to `M_{A,N}`.
2. Lemma 9: the diagonal bosonic Fock model — (F1), the Schatten equivalence (22), and the
   order-`d` regularized determinant identity (23)/(24).

The uniform-in-`S` route worked as predicted: `norm_finiteNomeSection_sub_one_le` bounds every
finite section by `exp(e^g ‖t‖^{g+1} · ∑_ν ‖p^ν‖^{g+1}) - 1`, with no dependence on `S`, because the
centred factors of every section are dominated by one fixed summable family.  Lemma 3 did not need
upgrading.  Two hypotheses turned out to be unnecessary and were dropped: `tendsto_forwardNomeFactor_one`
and `tendsto_parityNormalizedSection` hold at every `x`, including `x = 0`.

Lemmas 2, 4 and 6 are now closed.  Local uniformity was never needed: the moving-coordinate limit
follows from dominated convergence for infinite products, once the centred primary factor is bounded
on an arbitrary disc rather than only the unit disc.  That radius-general bound
(`exists_primaryFactor_sub_one_bound`) combines the vanishing order at the origin with plain
compactness outside the unit disc, and holds at every radius with no hypothesis at all.

The moment form of (8) needed one reassembly: written as a single theorem it would not elaborate,
while the same argument split into a per-term majorant, a summability lemma, an occupation-sum
lemma and a four-line assembly compiles in seconds.  Avoiding `field_simp` on the
`Nat.cast (m + (g+1))` denominators — `div_le_div₀` and `ring` suffice — was the other half of the
fix.

Lemma 4 is closed including the obstruction.  The witness point for genuine non-convergence of
the raw net is elementary rather than Picard-theoretic: `Re 𝒢` runs continuously from `1` at the
origin to `0` at one, so by the intermediate value theorem it equals `1/2` somewhere, and there
`𝒢` is neither zero nor a square root of one.
