# Projective-prime Weyl leakage realizes the squarefree Fock normal cone

- **ID:** `projective-prime-weyl-leakage-fock-normal-cone`
- **Stage:** 3-formalized / complete theorem surface Lean-proved, external novelty audit preliminary
- **Type:** EXACT FINITE PRODUCER--REPORTER COMPARISON / ALL-PRIME NORMAL-CONE LIMIT
- **Scientific status:** `[PAPER PROOF COMPLETE] [SOURCE-PURE] [NOT RH]`
  `[CANDIDATE NEW SCIENTIFIC KNOWLEDGE] [SIGNIFICANCE PASS]`
- **Parents:**
  - `prime-valuation-dyadic-fermion-normal-cone-law.md`;
  - `../not_new_scientific_knowledge/poisson-euler-sobolev-natural-cone-bipolarity.md`;
  - `squarefree-euler-modular-corona-curvature-colligation.md`;
  - `../../1-in-progress/squarefree-fourier-torsion-counterface-completion.md`;
  - `../../1-in-progress/source-effective-boundary-complexity-conservation-law.md`.

## The missing finite comparison

The squarefree Euler factor is usually represented by a two-state space.  That representation
retains “prime absent / prime present” but has no room for an additive Weyl transform.  The
smallest arithmetic enlargement is forced by the critical odds.

For a prime \(p\), let
\[
 X_p=\mathbb P^1(\mathbb F_p),\qquad |X_p|=p+1,
 \qquad {\cal K}_p=\ell^2(X_p).
 \tag{1}
\]
For \(a\in X_p\), put
\[
 e_a=\mathbf 1_{\{a\}},\qquad
 b_a=\frac1{\sqrt p}\sum_{x\ne a}e_x,\qquad
 E_a=\operatorname{span}\{b_a,e_a\}.                    \tag{2}
\]
The two-dimensional subspace \(E_a\) is the point/complement compression at the marked
projective point \(a\).

For real \(z\), define the positive natural-cone vector
\[
 u_a(z)
 =
 \frac{\sqrt p\,b_a+e^z e_a}
 {\sqrt{p+e^{2z}}}
 =
 \frac{\sum_{x\ne a}e_x+e^z e_a}
 {\sqrt{p+e^{2z}}}.                                     \tag{3}
\]
Its marked-point odds are
\[
 \frac{\Pr(a)}{\Pr(X_p\setminus\{a\})}
 =
 \frac{e^{2z}}p.                                        \tag{4}
\]
With \(z=c\log p\), `(4)` is exactly the critical squarefree prime odds
\[
 p^{-1+2c}.
 \tag{5}
\]
At \(c=0\),
\[
 u_a(0)=\frac1{\sqrt{p+1}}\sum_{x\in X_p}e_x=:u_p^0,    \tag{6}
\]
independent of the marked point.  The critical squarefree state is therefore the uniform
projective vector, not an arbitrarily calibrated Bernoulli line.

## 1. Local polarization-intersection theorem

> **[THEOREM -- PROJECTIVE PRIME POLARIZATION INTERSECTION.]**
> If \(a\ne b\) in \(X_p\), then
> \[
> E_a\cap E_b=\mathbb C u_p^0.                           \tag{7}
> \]

### Proof

A vector in \(E_a\) has one coefficient at \(a\) and a common coefficient at every point
different from \(a\).  A vector in \(E_b\) has the analogous property with \(b\).  Choose a point
different from both \(a\) and \(b\), which exists because \(p+1\ge3\).  Comparing its coefficient
with those at \(a\) and \(b\) forces all coefficients to be equal.  The common line is `(6)`.
`QED`

Every \(w\in\operatorname{PGL}_2(\mathbb F_p)\) acts on \({\cal K}_p\) by a permutation unitary,
and
\[
 wE_a=E_{wa},\qquad wu_a(z)=u_{wa}(z),\qquad wu_p^0=u_p^0.       \tag{8}
\]
Choose the Weyl inversion \(w_p:x\mapsto-1/x\), so \(w_p\infty=0\).  Equations `(7)`--`(8)` give
an exact finite producer--reporter double:

```text
producer polarization: E_infinity;
reporter polarization: E_0 = w_p E_infinity;
common source line:     C u_p^0;
reflection:             permutation unitary w_p.
```

No zeta zero, analytic continuation, target metric, or fitted divisor enters this double.

### Transverse line, safe determinant, Fisher tangent, and Möbius phase

The unit transverse vector in \(E_a\ominus\mathbb C u_p^0\) is
\[
 v_a
 =
 \sqrt{\frac p{p+1}}e_a
 -
 \frac1{\sqrt{p(p+1)}}\sum_{x\ne a}e_x.                 \tag{8a}
\]
For distinct \(a,b\),
\[
 \boxed{\langle v_a,v_b\rangle=-\frac1p.}               \tag{8b}
\]
Indeed the two marked coordinates contribute \(-2/(p+1)\), while the other \(p-1\)
coordinates contribute \((p-1)/(p(p+1))\).  Consequently
\[
 \det
 \begin{pmatrix}
  1&\langle v_a,v_b\rangle\\
  \langle v_b,v_a\rangle&1
 \end{pmatrix}
 =
 1-p^{-2}.                                              \tag{8c}
\]
Thus the critical numerator \(1-p^{-2}\) in the safe squarefree correction is the Gram determinant
of the producer and reporter transverse projective lines.  The coefficient \(-1/p\) is its
unsquared first-trace seam; its prime sum diverges while its square sum converges.
Globally,
\[
 \prod_p
 \det\operatorname{Gram}(v_{\infty,p},v_{0,p})
 =
 \prod_p(1-p^{-2})
 =
 \frac1{\zeta(2)}.                                      \tag{8c1}
\]
This is exactly one chiral half of the critical squarefree Sobolev residue
\[
 \lim_{r\downarrow1/2}
 (2r-1)\|W_{\rm sf}\|_{\dot H^{-r}}^2
 =
 \frac2{\zeta(2)}.
 \tag{8c2}
\]
The critical residue is therefore the two-sided projective transverse Gram determinant, not an
unrelated Euler constant.

The marked-weight derivative is exactly the squarefree Fisher direction:
\[
 \left.\frac d{dz}u_a(z)\right|_{z=0}
 =
 \frac{\sqrt p}{p+1}v_a,
 \qquad
 \left\|
 \left.\frac d{dz}u_a(z)\right|_{z=0}
 \right\|^2
 =
 \frac p{(p+1)^2}
 =
 \frac{p^{-1}}{(1+p^{-1})^2}.                           \tag{8d}
\]
Hence projective transversality, the safe determinant, and the squarefree Fisher capacity are one
finite metric object.

The Möbius phase is also source-internal at the critical point.  Let
\[
 S_a=1-2|e_a\rangle\langle e_a|                         \tag{8e}
\]
be the marked-point sign reflection.  Then
\[
 \langle u_p^0,S_au_p^0\rangle
 =
 \frac{p-1}{p+1}
 =
 \frac{1-p^{-1}}{1+p^{-1}},                             \tag{8f}
\]
the critical local signed Pluecker/Loschmidt factor.  Weyl transport moves the entire phase
package:
\[
 wS_aw^{-1}=S_{wa}.                                     \tag{8g}
\]
Thus the projective clock carries the critical Möbius determinant sign as well as its positive
natural-cone metric.  Extending `(8e)`--`(8g)` to the full complex reciprocal section remains
open.

## 2. Exact Weyl leakage

Let \(Q_a\) be the orthogonal projection onto \(E_a\).  For \(a\ne b\),
\[
 L_p(z)
 :=
 \|(1-Q_a)u_b(z)\|^2
 =
 \frac{p-1}{p}\,
 \frac{(e^z-1)^2}{p+e^{2z}}.                            \tag{9}
\]

### Proof

Inside the \(p\)-point complement of \(a\), the vector \(u_b(z)\) has coefficient \(e^z\) at
\(b\) and coefficient one at the other \(p-1\) points, before the common normalization in
`(3)`.  Its mean coefficient is
\[
 m=1+\frac{e^z-1}{p}.
\]
The squared mean-zero residual is
\[
 (e^z-m)^2+(p-1)(1-m)^2
 =
 \frac{p-1}{p}(e^z-1)^2.
\]
Division by \(p+e^{2z}\) proves `(9)`. `QED`

Therefore
\[
 \|Q_\infty w_pu_\infty(z)\|^2=1-L_p(z).                \tag{10}
\]
The critical state has zero leakage.  Every noncritical real radial state leaks a nonzero
polarization into the projective modes erased by the two-state Euler compression.

The same-polarization Gram coefficient is
\[
 \langle u_a(z),u_a(y)\rangle
 =
 \frac{p+e^{z+y}}
 {\sqrt{(p+e^{2z})(p+e^{2y})}}.                         \tag{11}
\]
This is exactly the Hellinger affinity of the Bernoulli laws with odds \(e^{2z}/p\) and
\(e^{2y}/p\).  Thus the Hellinger geometry is already the projective-source Gram geometry at
finite \(p\).

## 3. Prime-profile all-prime theorem

Let
\[
 {\cal F}_0=\{f\in C^1([0,1],\mathbb R):f(0)=0\},
 \qquad t_{p,x}=\frac{\log p}{\log x}.
 \tag{12}
\]
For \(p\le x\), use \(z_{p,x}=f(t_{p,x})\), and define
\[
 U_x(f)=\bigotimes_{p\le x}u_{\infty,p}(z_{p,x}),\qquad
 W_x=\bigotimes_{p\le x}w_p,\qquad
 Q_x=\bigotimes_{p\le x}Q_{\infty,p}.                   \tag{13}
\]

> **[THEOREM -- PROJECTIVE WEYL-LEAKAGE NORMAL CONE.]**
> For every \(f\in{\cal F}_0\),
> \[
> \|Q_xW_xU_x(f)\|
> \longrightarrow
> \exp\!\left[
> -\frac12\int_0^1(e^{f(t)}-1)^2\,\frac{dt}{t}
> \right].                                              \tag{14}
> \]
> This is exactly the squarefree Hellinger/Fock kernel
> \({\cal K}(f,0)\).

### Proof

Equations `(9)`--`(10)` give
\[
 \|Q_xW_xU_x(f)\|
 =
 \prod_{p\le x}\sqrt{1-L_p(f(t_{p,x}))}.                 \tag{15}
\]
Uniformly on the bounded range of \(f\),
\[
 L_p(f(t_{p,x}))
 =
 \frac{(e^{f(t_{p,x})}-1)^2}{p}+R_{p,x},
 \qquad |R_{p,x}|\le C_fp^{-2}.                          \tag{16}
\]
For every fixed \(p\), both sides of `(16)` tend to zero, since \(t_{p,x}\to0\) and \(f(0)=0\);
therefore dominated convergence gives
\[
 \sum_{p\le x}R_{p,x}\longrightarrow0.                  \tag{17}
\]
Prime-number-theorem partial summation gives
\[
 \sum_{p\le x}\frac{(e^{f(t_{p,x})}-1)^2}{p}
 \longrightarrow
 \int_0^1(e^{f(t)}-1)^2\,\frac{dt}{t}.                  \tag{18}
\]
Moreover \(L_p^2\) has a summable \(O_f(p^{-2})\) majorant and tends coordinatewise to zero, so
\[
 \sum_{p\le x}
 \bigl(\log(1-L_p)+L_p\bigr)\longrightarrow0.            \tag{19}
\]
Taking logarithms in `(15)` and using `(16)`--`(19)` proves `(14)`. `QED`

For the radial profile \(f(t)=ut\), `(14)` is \(e^{-\Phi(u)}\).  Hence the previously
measure-theoretic defect
\[
 d\kappa_{f,0}(t)
 =
 \frac12(e^{f(t)}-1)^2\,\frac{dt}{t}                    \tag{20}
\]
has an exact geometric meaning: it is the continuum density of projective Weyl leakage from the
reporter polarization back through the producer compression.

There is also a finite intersection statement at every prime aperture.  Tensoring `(7)` gives
\[
 \left(\bigotimes_{p\le x}E_{\infty,p}\right)
 \cap
 \left(\bigotimes_{p\le x}E_{0,p}\right)
 =
 \mathbb C\bigotimes_{p\le x}u_p^0.                     \tag{21}
\]
Thus the only finite product line simultaneously carried by both complete point/complement
polarizations is the critical uniform source line.

## 4. Infinite completion already supplied by the source

Form the von Neumann incomplete tensor product
\[
 {\cal K}_{\rm proj}
 =
 \widehat\bigotimes_p({\cal K}_p,u_p^0).                 \tag{22}
\]
Because every \(w_p\) fixes \(u_p^0\), the infinite tensor
\[
 W=\widehat\bigotimes_pw_p                              \tag{23}
\]
exists as an honest unitary on `(22)`.  This is the first explicit Hausdorff infinite completion
in the route on which the full primewise Weyl comparison survives without finite-aperture
leakage.  The leakage appears only after compressing `(23)` to the moving two-state Euler
polarizations.

The critical profile normal cone of those compressions is the coherent Fock space constructed in
the first parent.  Equation `(14)` proves that this Fock kernel is the asymptotic compression
coefficient of the exact unitary `(23)`.  In particular, the completion curvature is no longer a
formal cone name: its positive metric face is the accumulated orthogonal complement
\[
 (1-Q_{\infty,p})\,w_pE_{\infty,p}
 \tag{24}
\]
over the ordinary primes.

## 5. Global cross-Gram theorem and the projective Möbius operator

The infinite completion contains more than the reference line and the compressed leakage.
For a squarefree integer \(n\), let \(S(n)\) be its prime support and put
\[
 \xi_a(n)
 =
 \bigotimes_{p\mid n}v_{a,p}
 \quad\text{with }u_p^0\text{ in every coordinate }p\nmid n.
 \tag{25}
\]
For \(a=\infty,0\), the vectors \(\{\xi_a(n):\mu^2(n)=1\}\) form an orthonormal basis of the
incomplete tensor-product polarization
\[
 {\cal P}_a
 =
 \widehat\bigotimes_p(E_{a,p},u_p^0)
 \subset{\cal K}_{\rm proj}.
 \tag{26}
\]
Write
\[
 J_a:\ell^2(\{n:\mu^2(n)=1\})\longrightarrow{\cal P}_a,
 \qquad J_ae_n=\xi_a(n).
 \tag{27}
\]

> **[THEOREM -- PROJECTIVE MÖBIUS CROSS-GRAM.]**
> The producer--reporter cross-Gram operator is
> \[
> {\cal A}:=J_\infty^*J_0,
> \qquad
> {\cal A}e_n=\frac{\mu(n)}n e_n
> \quad(\mu^2(n)=1).
> \tag{28}
> \]
> Consequently:
>
> 1. \({\cal P}_\infty\cap{\cal P}_0=\mathbb C\xi_\infty(1)\);
> 2. on the vacuum-orthogonal parts, the polarization angle is uniformly strict:
>    \[
>    |\langle x,y\rangle|
>    \le\frac12\|x\|\,\|y\|,
>    \qquad
>    x\in{\cal P}_\infty^\circ,\ y\in{\cal P}_0^\circ;
>    \tag{29}
>    \]
> 3. the transverse cross-Gram \({\cal A}^\circ\) is compact, injective, Hilbert--Schmidt,
>    has dense nonclosed range, and is not trace class;
> 4. its closed inverse graph has exact domain
>    \[
>    \operatorname{Dom}(({\cal A}^\circ)^{-1})
>    =
>    \left\{y:\sum_{\substack{n>1\\\mu^2(n)=1}}n^2|y_n|^2<\infty\right\},
>    \qquad
>    ({\cal A}^\circ)^{-1}e_n=\mu(n)n\,e_n.
>    \tag{30}
>    \]

### Proof

If \(m\ne n\), some prime coordinate of \(\xi_\infty(m)\) is \(v_{\infty,p}\) while the
corresponding coordinate of \(\xi_0(n)\) is \(u_p^0\), or conversely.  That local inner product
is zero.  If \(m=n\), equation `(8b)` gives
\[
 \langle\xi_\infty(n),\xi_0(n)\rangle
 =
 \prod_{p\mid n}\left(-\frac1p\right)
 =
 \frac{\mu(n)}n,
 \tag{31}
\]
which proves `(28)`.

If \(J_\infty a=J_0b\), projection to the two polarizations gives
\[
 a={\cal A}b,\qquad b={\cal A}a,
\]
so \(b={\cal A}^2b\).  Since the diagonal of \({\cal A}^2\) is \(n^{-2}\), only the
\(n=1\) coefficient can survive.  This proves the intersection statement.

On the transverse squarefree basis,
\[
 \|{\cal A}^\circ\|=\sup_{n>1,\ \mu^2(n)=1}\frac1n=\frac12,
\]
which proves `(29)` and in particular makes
\({\cal P}_\infty^\circ+{\cal P}_0^\circ\) closed.  The nonzero diagonal entries tend to zero,
so \({\cal A}^\circ\) is compact and injective with dense range; the range is not closed because
the diagonal is not bounded below.  Finally
\[
 \|{\cal A}^\circ\|_{\mathcal S_2}^2
 =
 \sum_{\substack{n>1\\\mu^2(n)=1}}\frac1{n^2}
 =
 \frac{\zeta(2)}{\zeta(4)}-1<\infty,
 \tag{32}
\]
whereas
\[
 \sum_{\substack{n>1\\\mu^2(n)=1}}\frac1n=\infty.
 \tag{33}
\]
Thus it is Hilbert--Schmidt but not trace class.  Coordinatewise inversion of `(28)` gives
`(30)`, and the weighted \(\ell^2\) domain proves that inverse graph is closed. `QED`

The operator has two exact spectral Dirichlet traces.  For \(\Re s>1\),
\[
 \boxed{\operatorname{Tr}|{\cal A}|^s
 =\sum_{\mu^2(n)=1}n^{-s}
 =\frac{\zeta(s)}{\zeta(2s)}
 =Z_{\rm sq}(s),}
 \tag{34}
\]
while, with \(\operatorname{sgn}{\cal A}\,e_n=\mu(n)e_n\),
\[
 \boxed{\operatorname{Tr}\bigl(\operatorname{sgn}{\cal A}\,|{\cal A}|^s\bigr)
 =\sum_{n\ge1}\frac{\mu(n)}{n^s}
 =\frac1{\zeta(s)}.}
 \tag{35}
\]
Thus the positive squarefree Euler partition and the reciprocal-zeta Möbius reporter are the
unsigned and signed spectral zeta traces of one source-built cross-polarization operator.  The
failure of \({\cal A}\) to be trace class at \(s=1\) is the same first-trace wall already seen by
the Wold/BV and determinant-line constructions.

The trace realization itself is not new.  Greenfield--Marcolli--Teh construct the squarefree
Riemann-gas Hilbert space with
\[
 |\widetilde D|e_n=n e_n,\qquad Fe_n=\mu(n)e_n
\]
and prove exactly `(34)`--`(35)` for
\(|\widetilde D|^{-1}\) and its Möbius grading.  Equation `(28)` identifies
\[
 {\cal A}=F|\widetilde D|^{-1}
 \tag{35a}
\]
after the canonical squarefree-basis identification.  The candidate-new content is therefore not
the spectral triple or its eta function; it is the derivation of `(35a)` as the cross-Gram of two
ordinary-prime projective Weyl polarizations, together with the leakage, angle, and fixed-source
boundary laws surrounding it.

Equations `(28)`--`(35)` also sharpen the candidate third completion.  It is not an arbitrary
intermediate norm: the source supplies the closed graph scale of the unbounded Möbius inverse
\({\cal A}^{-1}\).  That scale is Hausdorff, retains every squarefree occupation coordinate, and
keeps the producer--reporter comparison strict despite its dense nonclosed Hilbert range.
What is not yet proved is that the Gamma/Poisson continuation preserves this graph or lands every
\(\Xi\)-conormal in it.

## 6. Full \(p\)-adic clock and the half-density law

The residue clock is the depth-one shadow of a canonical complete local clock.  Let
\({\cal T}_p\) be the Bruhat--Tits tree of \(\operatorname{PGL}_2(\mathbb Q_p)\), let \(o\) be
the standard vertex, and identify
\[
 \partial{\cal T}_p=\mathbb P^1(\mathbb Q_p).
 \tag{36}
\]
Let \(\nu_o\) be the visual probability measure at \(o\).  The \(p+1\) first shadows
\(\{C_a:a\in\mathbb P^1(\mathbb F_p)\}\) all have mass \(1/(p+1)\).  Hence
\[
 \iota_p:\ell^2(\mathbb P^1(\mathbb F_p))
 \longrightarrow L^2(\mathbb P^1(\mathbb Q_p),\nu_o),
 \qquad
 \iota_pe_a=\sqrt{p+1}\,\mathbf1_{C_a}
 \tag{37}
\]
is an isometry, sends \(u_p^0\) to the constant function \(1\), and intertwines the
\(\operatorname{PGL}_2(\mathbb Z_p)\) action with reduction modulo \(p\).  Thus every formula
`(7)`--`(11)` is an exact depth-one cylinder formula in the full boundary space.

More generally, primitive-coordinate reduction gives
\[
 \mathbb P^1(\mathbb Q_p)
 \longrightarrow
 \mathbb P^1(\mathbb Z/p^n\mathbb Z),
 \qquad
 \left|\mathbb P^1(\mathbb Z/p^n\mathbb Z)\right|
 =p^{n-1}(p+1).
 \tag{38}
\]
The corresponding cylinder functions are dense in the boundary \(L^2\) space.  Therefore `(37)`
does not replace the full prime-power clock by its residue quotient; it embeds the singular
squarefree digit as its first martingale shell.

The noncompact radial direction supplies the missing half-density meaning.  If \(g o\) is adjacent
to \(o\), let
\[
 J_g=\frac{d\nu_{go}}{d\nu_o}.
 \]
If \(C_g\) is the first shadow pointing from \(o\) toward \(go\), then
\[
 J_g(\xi)
 =
 \begin{cases}
 p,&\xi\in C_g,\\
 p^{-1},&\xi\notin C_g.
 \end{cases}
 \tag{39}
\]
Indeed, moving the base vertex toward \(C_g\) changes the visual mass of every cylinder inside
that shadow by \(p\), and changes every cylinder in its complement by \(p^{-1}\).

For \(s\in\mathbb C\), define the weighted boundary transport
\[
 (\Pi_s(g)f)(\xi)
 =
 J_g(\xi)^s f(g^{-1}\xi).
 \tag{40}
\]
The Radon--Nikodym cocycle makes \(\Pi_s\) a representation on the common cylinder core.
Writing \(s=\tfrac12+c+it\), one has
\[
 \Pi_s(g)
 =
 M_{J_g^{\,c+it}}\Pi_{1/2}(g),
 \qquad
 \|\Pi_s(g)\|=p^{|c|}
 \tag{41}
\]
for a one-edge translation.  In particular,
\[
 \Pi_s(g)\text{ is contractive in the fixed source }L^2(\nu_o)\text{ norm}
 \quad\Longleftrightarrow\quad
 \Re s=\frac12.
 \tag{42}
\]
The imaginary parameter is a harmless unitary Radon--Nikodym phase.  The real displacement is
exactly norm leakage from the source half-density.

The constant-vector coefficient is
\[
 m_p(s)
 :=
 \langle1,\Pi_s(g)1\rangle
 =
 \int J_g^s\,d\nu_o
 =
 \frac{p^s+p^{1-s}}{p+1}.
 \tag{43}
\]
Therefore
\[
 m_p(s)=m_p(1-s),\qquad
 \frac{m_p(s)}{m_p(1/2)}
 =
 \cosh\bigl((s-\tfrac12)\log p\bigr).
 \tag{44}
\]
The Riemann reflection, the exact Tate prime-dilation character in the adelic
purity-or-escape theorem, critical half-density unitarity, and the \(p+1\)-point projective clock
are thus four shadows of one visual-boundary Jacobian law.

This local lift is parent rank-one boundary representation theory.  Its role here is diagnostic:
it shows exactly why complementary-series unitarizations do not answer the source problem.  Such
unitarizations change the metric with \(s\); `(42)` uses one parameter-independent visual measure
fixed by the arithmetic source.  What remains open is the restricted adelic half-density
groupoid/rigged completion in which the radial spectral characters are retained as moderate point
conormals rather than lost in an \(L^2\) direct integral.

## 7. Meaning and next lift

The local source has three layers:

```text
full projective clock K_p        retains every residue-point polarization;
Euler producer E_infinity       remembers point at infinity versus affine bulk;
Weyl reporter E_0               remembers point zero versus its complement.
```

The two-state Euler model did not fail because it was finite.  It failed because it compressed
before applying the additive/projective Weyl comparison.  At finite aperture this creates
leakage; at all-prime aperture the leakage becomes the Hellinger--Fock normal field.

This is the boundary-building shadow of the desired arithmetic Calderon comparison.  The residue
clock has now been lifted to the full \(p\)-adic boundary, and its radial coefficient has been
identified with the exact Tate \(\cosh\) character.  The next theorem must compare the resulting
restricted adelic half-density groupoid with the already-constructed additive
Schwartz--Bruhat/Tate carrier, identifying its normalized global Weyl relation with the actual
Poisson intertwiner and Gamma factor.  Only after that identification may the source Mellin
conormal or \(X_{\rm sq}^{-1}\) be landed in the projective graph completion.

## 8. Hostile audit

1. **This is the positive natural cone, not the Möbius phase line.**  The signed Pluecker vector
   has a distinguished minus sign.  Equations `(8e)`--`(8g)` now attach that sign at the critical
   source and transport it under Weyl reflection, but they do not construct the full
   complex-parameter determinant torsor or reciprocal section.
2. **Finite-field inversion is not Poisson summation.**  The permutation \(w_p\) is the
   residue-field Weyl shadow.  No equality with the local Tate Fourier transform, global
   intertwiner, or completed-zeta functional equation is claimed.
3. **The infinite unitary does not prove RH.**  It exists because it fixes the critical reference
   vector.  No theorem yet says that every Xi conormal lands in its common polarization.
4. **Product intersections do not classify entangled boundary cohomology.**  Equation `(21)` is a
   finite tensor-subspace statement.  The global Milnor/Steinberg incidence and full Cauchy
   boundary classification remain independent.
5. **Complementary-series representations are a warning.**  Unitarity of a larger
   \(\operatorname{PGL}_2\) representation off the unitary principal axis can occur.  The
   RH-bearing claim must be strict source-polarization intersection, not bare representation
   unitarity.
6. **Higher prime powers remain regular but necessary.**  The theorem realizes only the singular
   squarefree digit.  The dyadic Gamma/determinant tower must be restored in the global
   intertwiner.
7. **Multiplicity jets remain absent.**  Conormal conservativity is not implied by line
   intersection.
8. **The spectral trace formulas hold only on their Euler half-plane.**  Equations `(34)`--`(35)`
   do not continue the operator trace through \(\Re s=1\), and poles of the continued signed trace
   are not eigenvalues of \({\cal A}\).  The strict Fourier--Mellin graph remains essential.
9. **The local boundary law is not the global source connector.**  Equations `(39)`--`(44)` are
   rank-one principal-series parent mathematics.  They do not identify the adelic boundary
   relation with Poisson summation or prove that a zeta resonance is a moderate boundary class.

## 9. Novelty and significance gate

Parent mathematics includes \(\mathbb P^1(\mathbb F_p)\), permutation representations of
\(\operatorname{PGL}_2(\mathbb F_p)\), point/complement association schemes, Bernoulli Hellinger
geometry, tensor products, prime-number-theorem partial summation, and the
Greenfield--Marcolli--Teh squarefree twisted spectral triple.  The latter already contains the
unsigned \(Z_{\rm sq}\) and signed \(1/\zeta\) trace formulas, so no novelty is claimed for
`(34)`--`(35)`.  Targeted searches found none of the narrower source-geometric joint statement:
\[
 \text{critical squarefree Euler natural cone}
 =
 \text{uniform projective residue vector},
 \quad
 \text{Hellinger normal cone}
 =
 \text{all-prime Weyl-compression leakage},
 \quad
 F|\widetilde D|^{-1}
 =
 \text{projective producer--reporter cross-Gram}.        \tag{45}
\]
This is provisional search noncollision, not a priority certificate.

- `[ANTI-THEATRE -- PASS]` The theorem constructs the finite producer--reporter comparison maps
  and their nonzero all-prime curvature that the universal-law card had left abstract.
- `[SIGNIFICANCE -- PASS]` It replaces a demanded comparison with an exact arithmetic
  projective-line model, identifies its transverse overlap with the first trace, its Gram
  determinant with the safe squarefree correction and critical Sobolev residue, its tangent with
  Fisher capacity, derives the known Möbius Riemann-gas spectral triple as the inverse
  projective cross-Gram rather than postulating its diagonal, attaches the critical Möbius phase,
  produces the full prime-profile defect measure, and identifies the next non-parent lift.
- `[FIELDS VERDICT]` Not yet.  The adelic Bruhat/Tate lift with source-first Xi conormal
  conservativity would be Fields-scale and would imply RH.
- `[RH BOUNDARY]` No divisor landing, global Poisson identification, phase transport, or
  multiplicity theorem is proved.

## Gates

- [x] lift critical Bernoulli odds to uniform projective residue vector
- [x] prove exact producer/reporter polarization intersection
- [x] construct finite Weyl comparison
- [x] identify transverse overlap and safe Gram determinant
- [x] identify horizontal tangent with squarefree Fisher capacity
- [x] attach and Weyl-transport critical Möbius phase
- [x] compute exact compression leakage
- [x] prove all-prime prime-profile leakage limit
- [x] identify limit with Hellinger--Fock kernel
- [x] construct infinite projective comparison unitary
- [x] compute the full producer/reporter cross-Gram operator
- [x] classify the infinite polarization intersection and strict transverse angle
- [x] prove Hilbert--Schmidt/non-trace-class Möbius boundary
- [x] construct the closed inverse graph and its exact domain
- [x] identify the unsigned and signed spectral traces with \(Z_{\rm sq}\) and \(1/\zeta\)
- [x] lift the residue clock to the full \(p\)-adic boundary cylinder filtration
- [x] derive the exact visual-boundary Jacobian and half-density norm law
- [x] recover Riemann reflection and the Tate \(\cosh\) character as one spherical moment
- [x] hostile complementary-series and phase audit
- [x] preliminary corpus and external collision search
- [x] spectral-triple collision found and novelty claim narrowed
- [ ] independent finite-group representation audit
- [ ] construct restricted-product half-density groupoid with moderate point conormals
- [ ] identify its normalized Weyl relation with the additive Poisson/Tate comparison
- [ ] attach Möbius determinant torsor and regular dyadic tower
- [ ] land Xi conormal and multiplicity jets source-first
- [ ] RH

Primary collision:

- M. Greenfield, M. Marcolli, K. Teh, *Twisted Spectral Triples and Quantum Statistical
  Mechanical Systems*, \(p\)-Adic Numbers, Ultrametric Analysis and Applications 6 (2014),
  81--104, DOI `10.1134/S2070046614020010`, Proposition 4.8.

## Lean formalization (complete)

Modules (all wired into `GaloisForLFunctions.RHTower`, all built green, all capstones depend only
on `propext`, `Classical.choice`, `Quot.sound`).  Core modules:

- `formal/GaloisForLFunctions/RHTower/ProjectivePrimeWeylPolarization.lean` — the finite projective
  clock on an abstract point set of cardinality `p + 1`;
- `formal/GaloisForLFunctions/RHTower/ProjectivePrimeWeylModel.lean` — the concrete
  `P¹(F_p) = Option (ZMod p)` model, the residue Weyl inversion, and the global Gram product;
- `formal/GaloisForLFunctions/RHTower/SquarefreeMoebiusCrossGram.lean` — the producer/reporter
  cross-Gram diagonal and its operator;
- `formal/GaloisForLFunctions/RHTower/ProjectiveTensorAperture.lean` — the finite tensor aperture,
  its Hilbert norm, and the aperture polarization intersection;
- `formal/GaloisForLFunctions/RHTower/Sieve/ApertureWeylCompressionLimit.lean` — the aperture Weyl
  compression coefficient and its all-prime limit.

| Card item | Lean theorem |
|---|---|
| `(6)` critical state is the uniform projective vector | `projNatural_zero` |
| `(7)` polarization intersection is the source line | `projPolarization_inf`, `weylProducer_inf_weylReporter` |
| `(8)` Weyl transport of the whole package | `projPermute_projUniform`, `projPermute_projNatural`, `projPermute_projTransverse`, `mem_projPolarization_permute`, `mem_weylReporter_iff` |
| `(8b)` transverse seam `-1/p` | `inner_projTransverse`, `inner_weylTransverse` |
| `(8c)` safe Gram determinant `1 - p⁻²` | `det_projTransverseGram`, `det_weylTransverseGram` |
| `(8c1)` global product is `1/ζ(2) = 6/π²` | `tprod_weylGramDet`, `tprod_weylGramDet_eq` |
| `(8d)` marked tangent is the Fisher direction, capacity `p/(p+1)²` | `hasDerivAt_projNatural_zero`, `projNatural_deriv_eq_transverse`, `norm_sq_projNatural_deriv` |
| `(8e)`–`(8f)` critical Möbius phase `(p-1)/(p+1)` | `inner_projUniform_signReflect` |
| `(8g)` Weyl transport of the sign reflection | `projPermute_signReflect` |
| `(9)` exact compression leakage | `projWeylLeakage` (with `starProjection_projPolarization` identifying the compression with the orthogonal projection) |
| `(10)` complementary compressed norm; zero leakage exactly at the critical state | `projWeylCompressionNorm`, `projLeakageValue_zero`, `projLeakageValue_pos` |
| `(11)` Hellinger affinity Gram coefficient | `inner_projNatural_same` |
| `(31)` tensored seam is the Möbius cross-Gram | `prod_transverseSeam_eq_crossGram` |
| `(28)`, `(29)` cross-Gram operator, norm exactly `1/2` | `crossGramOperator`, `norm_crossGramOperator`, `norm_inner_crossGram_le` |
| injectivity of the transverse cross-Gram | `crossGramOperator_injective` |
| `(32)` Hilbert–Schmidt | `summable_squarefreeTransverseWeight_two` |
| `(33)` not trace class — the first-trace wall | `not_summable_squarefreeTransverseWeight_one` |
| `(30)` closed inverse graph domain | `mem_range_crossGramOperator_iff`, `crossGramDiagonal_mul_inverse` |
| `(34)` unsigned spectral trace `ζ(s)/ζ(2s)` | `tsum_crossGram_unsigned_trace` |
| `(35)` signed spectral trace `1/ζ(s)` | `LSeries_crossGram_signed_trace` |

Fourth module: `formal/GaloisForLFunctions/RHTower/ProjectiveVisualBoundaryCosh.lean` — the
two-atom visual shadow model of the `p`-adic boundary.

| Card item | Lean theorem |
|---|---|
| `(39)` visual Radon–Nikodym Jacobian, probability normalization | `visualJacobian`, `visualShadowMeasure_univ` |
| `(43)` spherical moment `(p^s + p^{1-s})/(p+1)` as a visual integral | `integral_visualJacobian_cpow` |
| `(44)` Riemann reflection `m_p(s) = m_p(1-s)` | `visualSphericalMoment_reflection` |
| `(44)` Tate character `m_p(s)/m_p(1/2) = cosh((s-1/2) log p)` | `visualSphericalMoment_div_half` |
| `(41)`–`(42)` half-density norm `p^{|c|}`; contractive iff `Re s = 1/2` | `visualJacobian_rpow_sup`, `visualJacobian_rpow_sup_eq_one_iff` |

`(16)`, the leading prime-density expansion of the leakage with its `O(p⁻²)` remainder, is
`abs_projLeakageValue_sub_le`.

The all-prime limit `(14)` and its inputs:

- `(16)` is `abs_projLeakageValue_sub_le`, above.  The
  number-theoretic input `(18)` needs is **already corpus-owned** — not, as first recorded here,
  missing:

  | statement | Lean theorem |
  |---|---|
  | `\|mertensS N − logLog N − meisselMertensConst\| ≤ C/log N` | `RHTower.Sieve.abs_mertensS_sub_logLog_sub_const_le` |
  | `\|Σ_{z<p≤b} 1/p − (logLog b − logLog z)\| ≤ C/log b + C/log z` | `RHTower.Sieve.abs_sum_inv_bigPrimeSet_sub_le` |
  | defect tail `≤ 1/(N log N)` | `RHTower.Sieve.tsum_logLogDefect_add_le` |

  (in `Sieve/MertensSecondSharp.lean`, `Sieve/MertensWindowSharp.lean`,
  `Sieve/MertensDefectTail.lean`).  The old two-sided `mertensS_le` / `le_mertensS` are superseded.

  The transfer layer is now partly built, in
  `formal/GaloisForLFunctions/RHTower/Sieve/PrimeWindowExponentLimit.lean` and
  `formal/GaloisForLFunctions/RHTower/Sieve/PrimeProfileExponentTransfer.lean`:

  | statement | Lean theorem |
  |---|---|
  | `log ⌊N^c⌋ = c log N + O(1)` | `abs_log_exponentCutoff_sub_le` |
  | `log ⌊N^c⌋ / log N → c` | `tendsto_log_exponentCutoff_div` |
  | `logLog ⌊N^c⌋ − logLog N → log c` | `tendsto_logLog_exponentCutoff_sub` |
  | **`Σ_{N^a<p≤N^b} 1/p → log b − log a`** (the step case of `(18)`) | `tendsto_sum_inv_exponentWindow` |
  | primes of `(⌊N^a⌋, ⌊N^b⌋]` have exponent exactly in `(a,b]` — no floor slop | `exponent_mem_Ioc_of_mem_bigPrimeSet` |
  | window approximation by the left endpoint value | `abs_primeProfileWindowSum_sub_le` |
  | small-prime head `≤ C·c + O(1/log N)` for `\|g t\| ≤ C t` | `abs_primeProfileSum_head_le'` |

  The partition and the integral comparison are now built too, in
  `Sieve/PrimeProfilePartitionSum.lean` and `Sieve/ProfileStepIntegralComparison.lean`:

  | statement | Lean theorem |
  |---|---|
  | exact partition of the profile sum at the exponents `j/m` | `primeProfileSum_partition` |
  | each window is a step of the profile up to `L/m` | `abs_primeProfileWindowSum_sub_step_le` |
  | **profile sum = head + step sum, up to `(L/m)·Σ_j W_j`** | `abs_primeProfileSum_sub_stepSum_le` |
  | cell weight `∫_{j/m}^{(j+1)/m} dt/t = log(j+1) − log j` | `integral_one_div_cell` |
  | cellwise step-vs-integral comparison | `abs_integral_cell_sub_step_le` |
  | **step sum = `∫_{1/m}^1 g(t) dt/t`, up to `(L/m)·log m`** | `abs_stepSum_sub_integral_le` |

  **`(18)` is now proved.**  `Sieve/PrimeProfileIntegralBound.lean` assembles the pieces into one
  explicit finite inequality, and `Sieve/PrimeProfileTransferLimit.lean` takes the two limits:

  | statement | Lean theorem |
  |---|---|
  | `t ↦ g t / t` is integrable through the origin when `\|g t\| ≤ C t` | `intervalIntegrable_profile_div` |
  | integral head `\|∫₀^r g/t\| ≤ C·r` | `abs_integral_profile_head_le` |
  | **explicit master bound**, all five error sources displayed | `abs_primeProfileSum_sub_integral_le` |
  | window mass `W_j → log(j+1) − log j` | `tendsto_exponentWindowMass` |
  | fixed-`m` error `→ 2L·log m/m + 2C/m` | `tendsto_profileErrorBound` |
  | **`Σ_{p≤N} g(log p/log N)/p → ∫₀¹ g(t) dt/t`** | `tendsto_primeProfileSum` |

  Hypotheses: `g` continuous, `L`-Lipschitz, and `\|g t\| ≤ C t` for `t ≥ 0` — exactly the card's
  class, since `g = (e^f − 1)²` with `f ∈ C¹([0,1])`, `f(0) = 0` satisfies all three.  No prime
  number theorem is used anywhere: only Mertens' first theorem and the corpus's sharp Mertens.

  The leakage layer on top of `(18)` is now started, in
  `Sieve/PrimeSumDominatedVanishing.lean` and `Sieve/PrimeLeakageEstimates.lean`:

  | statement | Lean theorem |
  |---|---|
  | dominated vanishing of `Σ_{p≤N} a N p` (moving range **and** moving summands) | `tendsto_sum_primesLE_of_dominated` |
  | `L_p` as a function of the prime; identified with the projective-clock leakage | `primeLeakage`, `primeLeakage_eq_projLeakageValue` |
  | `0 ≤ L_p ≤ (e^z−1)²/p` | `primeLeakage_nonneg`, `primeLeakage_le_div` |
  | `L_p ≤ (E²+1)/(2+E²) < 1` uniformly when `e^z ≤ E` | `primeLeakage_le_theta`, `theta_lt_one` |
  | `\|L_p − (e^z−1)²/p\| ≤ (e^z−1)²(1+e^{2z})/p²` | `abs_primeLeakage_sub_div_le` |
  | `\|log(1−u) + u\| ≤ u²/(1−θ)` for `0 ≤ u ≤ θ < 1` | `abs_log_one_sub_add_le` |

  The uniform bound `L_p ≤ θ < 1` is what makes `(19)` work: it keeps `1 − L_p` away from zero for
  *every* prime, including the small ones, so the quadratic logarithmic defect is dominated by
  `C/p²` with no exceptional set.

  **`(17)` and `(19)` are now proved**, in `Sieve/PrimeLeakageProfileVanishing.lean`, together with
  the profile regularity they feed, in `Sieve/ExpProfileRegularity.lean`:

  | statement | Lean theorem |
  |---|---|
  | `(17)` `Σ_{p≤N} (L_p(f(t_p)) − (e^{f(t_p)}−1)²/p) → 0` | `tendsto_sum_leakageExpansion` |
  | `(19)` `Σ_{p≤N} (log(1−L_p) + L_p) → 0` | `tendsto_sum_leakageLogDefect` |
  | uniform bounds `(e^z−1)² ≤ (e^F−1)²`, `e^{2z} ≤ e^{2F}` | `sq_exp_sub_one_le`, `exp_sq_le` |
  | `exp` is `e^F`-Lipschitz on `[−F,F]` | `abs_exp_sub_exp_le` |
  | the profile `g = (e^f−1)²` is globally Lipschitz | `expProfile_lipschitz` |
  | the profile vanishes linearly at the origin, `\|g t\| ≤ C t` | `expProfile_le_linear` |

  Hypotheses on the weight: `f` continuous, bounded (`\|f t\| ≤ F`), globally Lipschitz, `f(0)=0` —
  the class obtained by truncating a `C¹([0,1])` weight, which is exactly the card's `𝓕₀` after
  restriction to the exponent range `(0,1]`.

  **`(14)` is now proved**, in `Sieve/PrimeLeakageProductLimit.lean`:

  | statement | Lean theorem |
  |---|---|
  | `1 − L_p > 0` for every prime | `one_sub_primeLeakage_pos` |
  | `∏_{p≤N} √(1−L_p) = exp(½ Σ log(1−L_p))` | `prod_sqrt_one_sub_primeLeakage` |
  | `Σ log(1−L_p) = Σ logDefect − Σ expansion − primeProfileSum g N` | `sum_log_one_sub_primeLeakage` |
  | **`∏_{p≤N} √(1 − L_p(f(log p/log N))) → exp(−½ ∫₀¹ (e^{f t}−1)² dt/t)`** | `tendsto_prod_sqrt_one_sub_primeLeakage` |

  This is the card's all-prime Weyl-leakage normal-cone limit: the compression coefficient of the
  exact projective comparison converges to the squarefree Hellinger–Fock kernel `𝓚(f,0)`.

  The tensor layer `(13)`, the exact finite identity `(15)`, and the aperture intersection `(21)`
  are proved in `ProjectiveTensorAperture.lean` and `Sieve/ApertureWeylCompressionLimit.lean`:

  | statement | Lean theorem |
  |---|---|
  | product coordinates of the aperture tensor product; tensors are determined by them | `apertureBasis`, `apertureCoord_tprod`, `apertureTensor_ext` |
  | the one-slot exchange walk | `apertureCoord_congr_of_step` |
  | `⨂ᵢ E_{a i}` is exactly slotwise constancy off the marked points | `tensorSubspace_projPolarization` |
  | **`(21)` `(⨂_{p≤x} E_{∞,p}) ∩ (⨂_{p≤x} E_{0,p}) = ℂ·⨂_{p≤x} u_p⁰`** | `tensorSubspace_projPolarization_inf`, `tensorSubspace_weylProducer_inf_weylReporter` |
  | the Hilbert tensor norm: `‖⨂ᵢ v_i‖ = ∏ᵢ ‖v_i‖` | `apertureModel`, `apertureNorm`, `apertureNorm_tprod` |
  | `(13)` the aperture operators `Q_x`, `W_x`, `U_x(f)` | `apertureCompress`, `aperturePermute`, `apertureNatural` |
  | **`(15)` `‖Q_x W_x U_x(f)‖ = ∏_{p≤x} √(1−L_p)`** | `apertureNorm_compress_permute_natural`, `apertureNorm_weylCompression` |
  | **`(14)` in operator form: `‖Q_N W_N U_N(f)‖ → exp(−½∫₀¹(e^{f t}−1)² dt/t)`** | `tendsto_apertureNorm_weylCompression` |

  The aperture tensor product is mathlib's `PiTensorProduct`; its Hilbert norm is defined through
  the product coordinate basis `apertureBasis`, and `apertureNorm_tprod` — `‖⨂ v_i‖ = ∏ ‖v_i‖` — is
  precisely the defining property of the Hilbert tensor norm, so at finite aperture no separate
  metric completion is needed.  `(21)` needs `p + 1 ≥ 3` in every slot, exactly as `(7)` does: the
  proof exchanges one slot through a third point that is invisible to both polarizations at once,
  which forces the coordinate function of a common tensor to be constant.

  Nothing on this card is left unformalized.
