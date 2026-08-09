# Rank-one polarized exchange-geometrizability

- **ID:** `rank-one-polarized-exchange-geometrizability`
- **Stage:** 3-formalized
- **Type:** THEOREM (paper) / UNIVERSAL EXCHANGE OBSTRUCTION
- **Scientific status:** `[LEAN-FORMALIZED] [PAPER-PROVED] [DEPENDENCY-CLOSED] [STRICT SHADOW ONLY]`
  `[CORPUS-SYNTHESIS] [NOT RH]`
- **Source:** `../../1-in-progress/polarized-exchange-horizon-geometry/`
  `polarized-exchange-horizon-geometry-program.md`
- **Statement:** The one-sided polarized top-conormal family is fully composition-coherent exactly
  at zero modular weight; off weight zero its maximal coherent subspace is the permanent conormal
  line, so purity requires transverse framed landing rather than bare nonvanishing.

## Goal

Give a closed, zero-free theorem joining:

1. arithmetic power composition;
2. ramified top-conormal geometry; and
3. the spectral/Hilbert modular character.

The theorem does not construct an arithmetic exchange functor or admit Xi conormals.  It proves
the exact obstruction that any such functor must annihilate.

## Theorem

Let \(M=(\mathbb N_{>0},\cdot)\).  Fix \(\theta\in\mathbb R\) and define, for \(n\in M\),

\[
 \chi_\theta(n)=n^\theta,
 \qquad
 A_n=
 \begin{pmatrix}
 n&n-1\\
 0&1
 \end{pmatrix},
 \qquad
 T_\theta(n)=
 \begin{pmatrix}
 \chi_\theta(n)&0\\
 0&1
 \end{pmatrix}A_n.
\tag{1}
\]

Then:

1. \(A_mA_n=A_{mn}\) for all \(m,n\in M\).
2. The polarized composition defect is

   \[
   T_\theta(m)T_\theta(n)-T_\theta(mn)
   =
   \begin{pmatrix}
   0&\chi_\theta(m)(m-1)(1-\chi_\theta(n))\\
   0&0
   \end{pmatrix}.
   \tag{2}
   \]

3. The following are equivalent:

   - \(T_\theta:M\to\operatorname{End}(\mathbb R^2)\) is a monoid representation;
   - \(T_\theta(2)^2=T_\theta(4)\);
   - \(\chi_\theta(2)=1\);
   - \(\theta=0\).

4. Regard \(M\) as the one-object category \(BM\), and let
   \(B\operatorname{End}(\mathbb R^2)\) be the one-object category of linear endomorphisms.  Let
   \(\mathcal U\) be any category with functors
   \(F:BM\to\mathcal U\) and
   \(R:\mathcal U\to B\operatorname{End}(\mathbb R^2)\) such that
   \(R(F(n))=T_\theta(n)\) for every \(n\).  Then \(\theta=0\).
   In particular, this conclusion applies when \(\mathcal U\) is a partial-\(K\)-labelled
   universal exchange category and the stated matrices are the restriction of one of its
   realization functors.

5. If \(\theta=0\), this rank-one composition obstruction vanishes and \(T_0=A\).  This converse
   asserts only a representation of \(M\), not existence of a full exchange/base-change
   formalism.

6. If spectral parameters \(s,t\in\mathbb C\) are inserted through
   \(\theta_s=2\operatorname{Re}s-w\) for fixed \(w\in\mathbb R\), then
   \(T_{\theta_s}=T_{\theta_t}\) whenever \(\operatorname{Re}s=\operatorname{Re}t\).  Hence the
   framed exchange family detects spectral weight but is blind to imaginary height.

7. Let

   \[
   H_\theta
   =\bigcap_{m,n\ge1}
     \ker\bigl(T_\theta(m)T_\theta(n)-T_\theta(mn)\bigr).
   \tag{6}
   \]

   Then

   \[
   H_\theta=
   \begin{cases}
   \mathbb R^2,&\theta=0,\\
   \mathbb R e_1,&\theta\ne0.
   \end{cases}
   \tag{7}
   \]

   In both cases \(H_\theta\) is \(T_\theta\)-invariant, and the restrictions form a monoid
   representation.  Hence the maximal coherent framed dimension jumps from one to two exactly at
   \(\theta=0\).

8. Put

   \[
   J_\theta(n)=
   \begin{pmatrix}
   0&1\\
   \chi_\theta(n)&0
   \end{pmatrix},
   \qquad
   E_{12}=
   \begin{pmatrix}
   0&1\\0&0
   \end{pmatrix}.
   \tag{8}
   \]

   Then \(J_\theta(n)^2=\chi_\theta(n)I\), and the exchange curvature is the calibrated
   paracyclic monodromy defect

   \[
   T_\theta(m)T_\theta(n)-T_\theta(mn)
   =-\chi_\theta(m)(m-1)E_{12}\bigl(J_\theta(n)^2-I\bigr).
   \tag{9}
   \]

   For any \(m\ge2\), its vanishing is therefore equivalent to trivial paracyclic monodromy
   \(J_\theta(n)^2=I\).  The exchange-coherence and retained-cyclicity selectors have the same
   zero locus because they are two representations of one defect.

9. Order \(\operatorname{Sub}(\mathbb R^2)\) by inclusion and give it the Scott topology.  Let

   \[
   \kappa_{\rm ex}:\mathbb R\longrightarrow\operatorname{Sub}(\mathbb R^2),
   \qquad
   \kappa_{\rm ex}(\theta)=H_\theta,
   \tag{10}
   \]

   and give \(\mathbb R\) the initial topology \(\tau_{\rm ex}\) of \(\kappa_{\rm ex}\).  Then

   \[
   \boxed{
   \tau_{\rm ex}=\{\varnothing,\{0\},\mathbb R\}.
   }
   \tag{11}
   \]

   Its \(T_0\) quotient has two points: full framed coherence and permanent-line-only coherence.
   All nonzero modular weights are topologically indistinguishable.

10. Define the common kernel of every ordinary higher-word defect by

    \[
    H_\theta^{\rm word}
    =\bigcap_{q\ge2}\ \bigcap_{n_1,\ldots,n_q\in M}
      \ker\!\left(
        T_\theta(n_1)\cdots T_\theta(n_q)
        -T_\theta(n_1\cdots n_q)
      \right).
    \tag{17}
    \]

    Then \(H_\theta^{\rm word}=H_\theta\).  Hence the pairwise coherence-rank jump controls every
    strict matrix reassociation defect.  This does not construct higher oriented interchange
    cells.

11. Let

    \[
    D_\theta
    =T_\theta(2)^2-T_\theta(4)
    =2^\theta(1-2^\theta)E_{12}.
    \tag{18}
    \]

    Then \(D_\theta^2=0\).  Its exchange homology is

    \[
    \mathsf{EH}_\theta
    :=\ker D_\theta/\operatorname{im}D_\theta
    \cong
    \begin{cases}
    \mathbb R^2,&\theta=0,\\
    0,&\theta\ne0.
    \end{cases}
    \tag{19}
    \]

    If \(\theta\ne0\), then
    \(\ker D_\theta=\operatorname{im}D_\theta=\mathbb Re_1\), and \(D_\theta\) induces an
    isomorphism

    \[
    \overline D_\theta:
    \mathbb R^2/\mathbb Re_1\xrightarrow{\ \sim\ }\mathbb Re_1.
    \tag{20}
    \]

    Thus the off-horizon transverse framed direction is not merely detected; it is contracted
    exactly onto the conormal error line.

12. Put \(L=\mathbb Re_1\), \(Q=\mathbb R^2/L\), and regard

    \[
    \mathcal E_\theta=
    \left[Q\xrightarrow{\ \overline D_\theta\ }L\right]
    \tag{21}
    \]

    as a two-term chain complex, with \(Q\) in degree one.  If a chain map from any chain complex
    \(B\) to \(\mathcal E_\theta\) has nonzero induced map on homology, then \(\theta=0\).
    Equivalently, a homology-conservative landing in the exchange complex forces the horizon.
    The assertion is one-way: \(\theta=0\) does not construct such a chain map.

## Universal modular-character corollary

Let \(k\) be a field of characteristic zero and let
\(\chi:M\to k^\times\) be any multiplicative character.  Define

\[
 T_\chi(n)=
 \begin{pmatrix}\chi(n)&0\\0&1\end{pmatrix}A_n
 \in\operatorname{End}_k(k^2).
\]

Here the integer entries of \(A_n\) are read through the canonical map \(\mathbb Z\to k\), and
\(H_\chi\) denotes the common kernel of all curvature operators in `(12)`.

Then

\[
 T_\chi(m)T_\chi(n)-T_\chi(mn)
 =\chi(m)(m-1)(1-\chi(n))E_{12}.
\tag{12}
\]

Consequently:

\[
 T_\chi\text{ is a monoid representation}
 \quad\Longleftrightarrow\quad
 \chi=1,
 \qquad
 H_\chi=
 \begin{cases}
 k^2,&\chi=1,\\
 ke_1,&\chi\ne1.
 \end{cases}
\tag{13}
\]

On the full character set \(X=\operatorname{Hom}(M,k^\times)\), the initial Scott topology of
\(\chi\mapsto H_\chi\) is
\(\{\varnothing,\{1\},X\}\).  Thus the rank-one horizon detects triviality of a modular
character, not the special analytic form \(n^\theta\).  The corresponding common kernel of every
ordinary higher-word defect is also \(H_\chi\).  If \(\chi\ne1\), choose \(n\) with
\(\chi(n)\ne1\).  Then the defect at \((2,n)\) is square-zero and exact, with kernel and image
\(ke_1\), and induces \(k^2/ke_1\cong ke_1\).  If \(\chi=1\), every defect vanishes and the
exchange homology is \(k^2\).

For the generic character, write

\[
 \mathcal E_{\chi,n}
 =\left[k^2/ke_1
   \xrightarrow{\ \overline{\mathfrak C_\chi(2,n)}\ }ke_1\right].
\tag{22}
\]

Let \(S\subseteq M\) be any multiplicative generating set.  If, for every \(n\in S\), some chain
map into \(\mathcal E_{\chi,n}\) has nonzero induced map on homology, then \(\chi=1\).  In
particular, prime-indexed source landings suffice.

## Hermitian exchange-transgression corollary

Let \(\lambda:M\to\mathbb C^\times\) be a multiplicative character and define its Hermitian
torsion and anomaly by

\[
 \tau(n)=\lambda(n)\overline{\lambda(n)}=|\lambda(n)|^2,
 \qquad
 a(n)=1-\tau(n).
\tag{23}
\]

Then \(\tau:M\to\mathbb R_{>0}\) is multiplicative and \(a\) obeys the crossed-cocycle law

\[
 a(mn)=a(m)+\tau(m)a(n).
\tag{24}
\]

The one-sided framed curvature associated to \(\tau\) is exactly its affine Hermitian
transgression:

\[
 \mathfrak C_\lambda(m,n)
 =\tau(m)(m-1)a(n)E_{12}.
\tag{25}
\]

For every \(n\),

\[
 \lambda(n)^{-1}=\overline{\lambda(n)}
 \quad\Longleftrightarrow\quad
 \tau(n)=1
 \quad\Longleftrightarrow\quad
 a(n)=0.
\tag{26}
\]

Thus reciprocal flatness, inverse-versus-adjoint mismatch, and exchange curvature are not three
independent defects at rank one: the first supplies \(\lambda\), the second is the Hermitian
torsion anomaly, and the affine different transgresses that anomaly to the third.

## Proof

Multiplication gives

\[
 A_mA_n
 =
 \begin{pmatrix}
 m&m-1\\0&1
 \end{pmatrix}
 \begin{pmatrix}
 n&n-1\\0&1
 \end{pmatrix}
 =
 \begin{pmatrix}
 mn&m(n-1)+(m-1)\\0&1
 \end{pmatrix}.
\]

Since \(m(n-1)+(m-1)=mn-1\), this is \(A_{mn}\), proving item 1.

Because \(\chi_\theta\) is multiplicative,

\[
 T_\theta(n)
 =
 \begin{pmatrix}
 \chi_\theta(n)n&\chi_\theta(n)(n-1)\\
 0&1
 \end{pmatrix}.
\tag{3}
\]

The upper-left entry of \(T_\theta(m)T_\theta(n)\) is
\(\chi_\theta(m)\chi_\theta(n)mn=\chi_\theta(mn)mn\), equal to the upper-left entry of
\(T_\theta(mn)\).  Its upper-right entry is

\[
 \chi_\theta(m)m\chi_\theta(n)(n-1)
 +\chi_\theta(m)(m-1).
\]

Subtracting \(\chi_\theta(mn)(mn-1)\) and factoring gives

\[
\begin{aligned}
 &\chi_\theta(m)
 \left[m\chi_\theta(n)(n-1)+(m-1)-\chi_\theta(n)(mn-1)\right]\\
 &\qquad=\chi_\theta(m)(m-1)(1-\chi_\theta(n)).
\end{aligned}
\]

The lower row is unchanged, proving `(2)`.

If \(T_\theta\) is a representation, use `(2)` with \(m=n=2\).  Its upper-right entry is

\[
 \chi_\theta(2)(1-\chi_\theta(2)).
\]

The first factor is positive, so it vanishes exactly when \(\chi_\theta(2)=1\).  Since
\(\chi_\theta(2)=2^\theta\), this is equivalent to \(\theta=0\).  Conversely, if \(\theta=0\),
then \(\chi_0(n)=1\) for every \(n\), so \(T_0(n)=A_n\), and item 1 proves functoriality.  This
proves item 3 and item 5.

For item 4, functoriality of \(F\) and \(R\) sends multiplication of degree morphisms to
composition of their matrices.  Therefore the restricted family \(T_\theta\) is a monoid
representation.  Item 3 gives \(\theta=0\).

Item 6 follows because every entry of `(1)` depends on a spectral parameter only through the real
scalar \(\theta_s\).

Every curvature matrix in `(2)` kills \(e_1\), so \(\mathbb Re_1\subseteq H_\theta\).  If
\(\theta=0\), item 3 makes every curvature matrix zero and gives \(H_0=\mathbb R^2\).  If
\(\theta\ne0\), then \(\chi_\theta(2)\ne1\), and the curvature at \((m,n)=(2,2)\) is

\[
 \begin{pmatrix}
 0&\chi_\theta(2)(1-\chi_\theta(2))\\
 0&0
 \end{pmatrix},
\]

whose kernel is exactly \(\mathbb Re_1\).  Therefore the intersection `(6)` is
\(\mathbb Re_1\).  Upper triangularity makes this line invariant, and the restricted scalar is
\(\chi_\theta(n)n=n^{\theta+1}\), which is multiplicative.  This proves item 7.

Direct multiplication gives \(J_\theta(n)^2=\chi_\theta(n)I\).  Hence

\[
 -\chi_\theta(m)(m-1)E_{12}\bigl(J_\theta(n)^2-I\bigr)
 =\chi_\theta(m)(m-1)(1-\chi_\theta(n))E_{12},
\]

which is `(2)`.  If \(m\ge2\), the calibration \(\chi_\theta(m)(m-1)\) is nonzero, so the two
defects vanish simultaneously.  This proves item 8.

By item 7, the image of \(\kappa_{\rm ex}\) is the two-element chain

\[
 \mathbb Re_1\subsetneq\mathbb R^2.
\]

Let \(U\) be Scott-open in the full lattice \(\operatorname{Sub}(\mathbb R^2)\).  If
\(\mathbb Re_1\in U\), upward closure gives \(\mathbb R^2\in U\), so the pullback is
\(\mathbb R\).  If \(U\) contains \(\mathbb R^2\) but not \(\mathbb Re_1\), its pullback is
\(\{0\}\); otherwise the pullback is empty.  All three cases occur.  In particular,
\(\{\mathbb R^2\}\) is Scott-open: if a directed family of subspaces has supremum
\(\mathbb R^2\), finite dimensionality puts a basis in finitely many family members, and
directedness gives one member containing that basis, hence equal to \(\mathbb R^2\).  Therefore
the initial topology is exactly `(11)`, proving item 9.

Every binary defect occurs among the intersections in `(17)`, so
\(H_\theta^{\rm word}\subseteq H_\theta\).  Conversely, item 7 proves that \(H_\theta\) is invariant
under every \(T_\theta(n)\) and that the restrictions form a monoid representation.  Induction on
\(q\) therefore gives, for every \(v\in H_\theta\),

\[
 T_\theta(n_1)\cdots T_\theta(n_q)v
 =T_\theta(n_1\cdots n_q)v.
\]

Thus \(H_\theta\subseteq H_\theta^{\rm word}\), proving item 10.

Because \(E_{12}^2=0\), equation `(18)` gives \(D_\theta^2=0\).  If \(\theta=0\), its coefficient
is zero, so its kernel is \(\mathbb R^2\), its image is zero, and its homology is \(\mathbb R^2\).
If \(\theta\ne0\), the coefficient \(2^\theta(1-2^\theta)\) is nonzero.  Therefore
\(D_\theta(xe_1+ye_2)=2^\theta(1-2^\theta)y e_1\), whence both its kernel and image are
\(\mathbb Re_1\).  The first isomorphism theorem gives `(20)` and the homology is zero.  This
proves item 11.

The complex `(21)` is acyclic when \(\theta\ne0\), because `(20)` is an isomorphism.  Hence every
map into it induces the zero map on homology.  The contrapositive proves item 12.  This does not
prove the converse construction.

For the corollary, the calculation proving `(2)` used only multiplicativity of the character, so
it gives `(12)`.  If \(T_\chi\) is a representation, take \(m=2\) in `(12)`.  Since
\(\chi(2)\ne0\) and a characteristic-zero field has \(2-1\ne0\), vanishing for every \(n\)
forces \(\chi(n)=1\) for every \(n\).  The converse is immediate.  If \(\chi\ne1\), choose \(n\)
with \(\chi(n)\ne1\) and take \(m=2\); the resulting nonzero multiple of \(E_{12}\) has kernel
exactly \(ke_1\).  The common-kernel and topology arguments above now prove `(13)` and the stated
initial topology.  Invariance of \(ke_1\), followed by the same induction used for item 10, proves
the higher-word assertion.  For nontrivial \(\chi\), choose \(n\) with \(\chi(n)\ne1\).  Equation
`(12)` at \((2,n)\) has nonzero coefficient because \(\chi(2)\in k^\times\).  The preceding
square-zero, kernel, image, quotient, and homology argument works over \(k\) verbatim.  For trivial
\(\chi\), every defect is zero.  Finally, nonzero induced homology for
\(\mathcal E_{\chi,n}\) prevents its differential from being an isomorphism, so the preceding
classification forces \(\chi(n)=1\).  If this holds on a multiplicative generating set, the
multiplicative character is trivial on all of \(M\), proving the generic landing criterion.

For the Hermitian corollary, multiplicativity of \(\lambda\) and of complex conjugation gives
multiplicativity of \(\tau\).  Directly,

\[
 1-\tau(m)\tau(n)
 =(1-\tau(m))+\tau(m)(1-\tau(n)),
\]

which is `(24)`.  Substituting \(\chi=\tau\) in `(12)` gives `(25)`.  Since \(\lambda(n)\ne0\),
multiplying the first equality in `(26)` by \(\lambda(n)\) shows that it is equivalent to
\(1=\lambda(n)\overline{\lambda(n)}=\tau(n)\); the last equivalence is the definition of \(a\).
\(\square\)

## Spectral specialization

For a complex spectral parameter \(s\), the one-sided Hilbert gain in the actual top-conormal
block is

\[
 \chi_s(n)
 =\left\lVert n^{1/2-s}\right\rVert^{-2}
 =n^{2\operatorname{Re}s-1}.
\tag{4}
\]

Thus \(\theta=2\operatorname{Re}s-1\), and the theorem gives

\[
 \boxed{
 T_s\text{ is composition-coherent}
 \quad\Longleftrightarrow\quad
 \operatorname{Re}s=\frac12.
 }
\tag{5}
\]

This is an exchange-geometrizability criterion for an already-admitted rank-one block.  It is not
an RH criterion until one independently proves that every reduced Xi conormal is a conservative
image of the same pre-divisor exchange functor.

More generally, if the centered modular gain of a self-dual source of weight \(w\) is

\[
 \chi_{s,w}(n)=n^{2\operatorname{Re}s-w},
\tag{14}
\]

the theorem gives

\[
 T_{s,w}\text{ is composition-coherent}
 \quad\Longleftrightarrow\quad
 \operatorname{Re}s=\frac w2.
\tag{15}
\]

This is a universal rank-one purity template.  It does not prove that a given completed
\(L\)-function has the source category, tangent label, polarized realization, or conservative
Cartier packets required to apply it.

Item 7 sharpens the required Cartier hypothesis.  Off the purity line, a nonzero packet may still
land in the always-coherent line \(\mathbb Re_1\); nonvanishing alone then detects nothing.  A
purity argument must retain a nonzero class in the transverse quotient

\[
 \mathbb R^2/\mathbb Re_1.
\tag{16}
\]

Thus “conservative Xi landing” must mean framed transversality, not merely survival of one scalar
conormal.

## Meaning of the theorem

The entries of `(1)` belong to different sides of the proposed meta-theory:

```text
n                 arithmetic degree;
n-1               ramified different / top-conormal shift;
A_m A_n=A_mn      geometric composition;
n^theta           Fourier/Hilbert modular gain;
equation (2)       obstruction to one polarized exchange realization.
```

Unpolarized top-conormal transport is flat for every degree.  The spectral modular gain is also
multiplicative.  Their one-sided combination nevertheless fails to compose because the gain does
not act on the affine different term in the same way as arithmetic composition.  The critical
half-density is exactly the unique weight at which this mismatch disappears.

## Hostile audit

1. **Raw identity already exists.**  The matrix curvature formula and its critical-line
   specialization are already formalized in
   `DeningerOneSidedFramedMateCurvatureTransgression.lean`.  No new priority is claimed for the
   calculation.
2. **New statement is a typed synthesis.**  The additional conclusion is that the same curvature
   is the exact obstruction to factoring the framed family through any functorial exchange
   realization on the power-correspondence subcategory.
3. **No converse overreach.**  Vanishing proves only finite power-semigroup coherence.  It does
   not produce pullbacks, base change, Thom labels, a dagger, a source-normal completion, or Xi
   Cartier survival.
4. **No zero input.**  The theorem is uniform in \(s\) and contains no zeta, Xi, or divisor.
5. **No positivity proof.**  Positivity is used only to identify the scalar gain `(4)`.  The
   theorem does not prove that the actual arithmetic source has this polarized realization.
6. **No generic three-face claim.**  The result uses the actual ramified different \(n-1\).
   Replacing it by an arbitrary affine term changes the obstruction.
7. **No spectral-location claim.**  Item 6 proves that this exchange geometry cannot determine
   imaginary parts of zeros.  Those must come from the arithmetic source and its Cartier support.
8. **Nonzero is too weak.**  Item 7 exhibits a nonzero coherent line at every off-critical
   parameter.  Any RH application must prove nonzero projection to the transverse framed quotient
   `(16)` before using curvature vanishing.
9. **Cyclic collision acknowledged.**  The existing source--dagger cyclic-monodromy card already
   proves that a nonzero vector need not survive the minimal stable defect boundary.  Item 8 does
   not replace that work; it identifies its monodromy-minus-identity scalar with the framed
   exchange curvature through an exact calibration.
10. **Topology parentage.**  Scott topology and initial topology are standard, and interfinity
    geometry already uses solvability-subspace profiles.  Candidate new content is the specific
    polarized-exchange profile `(10)` and its exact coherence-rank jump, not the ambient topology.
11. **Strict-shadow limitation.**  The matrix identity proves a strict composition obstruction.
    It does not construct the bioriented lax/oplax comparison cells or their higher interchange
    coherences.  Those are required in the Stage-1 geometry and remain open.
12. **Power law not essential.**  The universal character corollary shows that the object detects
    triviality of a modular character.  The specialization \(\chi(n)=n^{2\operatorname{Re}s-w}\)
    supplies a purity line only because the analytic realization independently has that form.
13. **Modular-selector collision.**  The generic character curvature formula is already formalized
    in `DeningerOneSidedFramedMateCurvatureTransgression.lean`, and the centered-flow capacity card
    already identifies triviality of the actual Xi modular cocycle as the RH-equivalent debt.  New
    content claimed here is only the exchange-factorization reading, common-kernel/transverse
    classification, calibrated paracyclic bridge, and their strict-shadow topology.
14. **Higher-word closure, not higher-category closure.**  Item 10 proves that no new ordinary
    matrix reassociation defect appears after arity two.  It does not identify or fill higher
    oriented cubes in a Gray-enriched realization.
15. **Homology is a selector, not source admission.**  Exchange homology jumps at the trivial
    modular character, but an RH argument still must place a transverse Xi Cartier class in the
    actual source-derived complex.  Declaring that class to exist would restate the missing
    theorem.
16. **Landing criterion is noncircular only source-first.**  Item 12 is useful only if \(B\), its
    class, and the chain map are constructed before divisor location is used.  Choosing them from
    the desired target homology would encode \(\theta=0\) by definition.
17. **Scalar transgression is not the exact-couple lift.**  Equations `(23)`--`(26)` construct the
    rank-one shadow of the dagger-sensitive transgression.  They do not lift it through the
    first-trace and Gamma/co-Poisson/Sonin source-normal exact couples.
18. **Hermitian-transgression collision.**  The corpus already computes
    \(\tau=|\lambda|^2\), reduced defect \(1-\chi\), source/dual mate polarization, and its finite
    Gamma calibration.  Equations `(23)`--`(26)` are a dependency-closed repackaging that exposes
    the crossed-cocycle and exchange-factorization roles; no priority is claimed for their scalar
    ingredients.
19. **Landing criterion is formal after acyclicity.**  Item 12 is the contrapositive of “maps into
    an acyclic complex vanish on homology.”  Its value is typing the required arithmetic producer;
    it is not claimed as a deep independent theorem.

## Literature boundary

- Universal exchange and partial-\(K\) labels are parent mathematics from William Fisher,
  *Exchange theorems and coherent duality in six functors*,
  <https://arxiv.org/abs/2607.12123>.
- Six-functor and cohomological-correspondence formalism is parent mathematics; see Peter Scholze,
  *Six-Functor Formalisms*, <https://arxiv.org/abs/2510.26269>.
- Lax/oplax orientation and their bioriented combination are parent mathematics from David Gepner
  and Hadrian Heine, *Oriented Category Theory*, <https://arxiv.org/abs/2510.10504>.
- Ramified top-conormal coherence and formula `(2)` are prior HGT corpus results.
- Retained-cyclicity rigidity and the nonzero-quotient correction are prior HGT corpus results in
  `source-dagger-cyclic-monodromy-rigidity-law.md`.

Candidate-new knowledge is restricted to the exact universal-exchange interpretation, the maximal
coherent-subspace classification `(6)`--`(7)` and `(13)`, the calibrated bridge `(9)` from exchange
curvature to paracyclic monodromy, the exchange-horizon profile/topology `(10)`--`(11)`, and strict
higher-word stabilization `(17)`.  Equations `(18)`--`(20)` sharpen the permanent-line warning to
an exact off-horizon contraction from the transverse quotient onto the conormal error line.
The two-term landing criterion `(21)`--`(22)` isolates the exact source-comparison theorem an
arithmetic application must supply.
The Hermitian transgression `(23)`--`(26)` records the prior corpus scalar value any such lift must
recover.
Their use is to
replace the vague request “find a geometry making prime transfer unitary” by a falsifiable
construction problem: build the actual pre-divisor unpolarized exchange realization, its curved
polarization, and transverse Cartier horizon landing.

## Lean note

Every numbered item and every corollary is now an unconditional Lean theorem:

```text
formal/GaloisForLFunctions/RHTower/
  RankOnePolarizedExchangeCurvature.lean
  RankOnePolarizedExchangeModularGain.lean
  RankOnePolarizedExchangeCoherentKernel.lean
  RankOnePolarizedExchangeHorizon.lean
  RankOnePolarizedExchangeHorizonTopology.lean
```

The existing curvature file is imported rather than duplicated, and the identification with it is
itself proved (`spectralGain_one_apply`, `exchangeTransport_spectralGain_one_eq`).  The universal
character corollary is proved over every field, not only in characteristic zero, because the
calibration actually used is `2 - 1 = 1`.

## Gates

- [x] exact theorem stated without Xi or RH assumptions
- [x] complete paper proof
- [x] converse limited to the rank-one multiplication category
- [x] raw-calculation rediscovery boundary explicit
- [x] source-admission and Cartier-conservativity debts explicit
- [x] arbitrary multiplicative modular character classified
- [x] all ordinary higher-word defects classified by pairwise coherent kernel
- [x] off-horizon curvature complex and transverse quotient isomorphism classified
- [x] abstract homology-conservative landing criterion paper-proved
- [x] rank-one Hermitian torsion-to-exchange transgression paper-proved
- [x] unconditional Lean theorems for every item and corollary
  (`rank-one-polarized-exchange-geometrizability-formalized.md`)
- [ ] external specialist audit of exchange-geometrizability interpretation

## Log

- 2026-08-09 — Formalized in Lean 4 without hypotheses: flatness, exact curvature, the
  representation/factorization criterion through `SingleObj`, the coherent-kernel classification and
  its restricted representation, the paracyclic calibration, higher-word stabilization, the two
  horizon topologies, the off-horizon acyclic complex with its transverse contraction, the
  homology-conservative landing criterion with its generating-set and prime forms, and the Hermitian
  transgression.
- 2026-08-08 — Extracted from the one-sided framed curvature after Fisher's universal exchange
  theorem supplied the correct parent category.  Proved the exact representation/factorization
  criterion and separated it from the still-open actual-source exchange realization.
