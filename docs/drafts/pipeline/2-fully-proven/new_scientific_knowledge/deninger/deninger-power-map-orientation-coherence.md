# Deninger power-map orientation coherence

- **ID:** `deninger-power-map-orientation-coherence`
- **Stage:** 2-fully-proven
- **Type:** SOURCE CONSTRUCTION LEMMA
- **Parent:** `deninger-mw-gamma-brst-complex`
- **Lean status:** direct check passes in `DeningerArithmeticPowerOrientation.lean`

## Statement

Let \(R\) be a commutative ring and let
\[
 f_n:\mathbb A^1_R\longrightarrow\mathbb A^1_R,\qquad x\longmapsto x^n
\]
for \(n\geq 1\).  Give \(f_n\) the complete-intersection orientation determined by the monic
presentation
\[
 R[y]\longrightarrow R[y,x]/(x^n-y)
\]
and the ordered bases \(x^n-y\) of the conormal line and \(dx\) of the relative differential
line.

For \(m,n\geq 1\), the orientation induced on \(f_m\circ f_n=f_{mn}\) by composition agrees
with the direct monic orientation of \(x^{mn}-z\).  More precisely, the iterated presentation
\[
 R[z,x,y]/(x^n-y,\ y^m-z)
\]
has relative cotangent differential, in the ordered relation basis
\((x^n-y,y^m-z)\) and coordinate basis \((dx,dy)\),
\[
 A(a,b)=
 \begin{pmatrix}
 a&0\\
 -1&b
 \end{pmatrix},
 \qquad
 a=nx^{n-1},\quad b=my^{m-1}.
\]
There are elementary matrices \(L(a),R(b)\in \operatorname{SL}_2\) such that
\[
 L(a)A(a,b)R(b)=
 \begin{pmatrix}
 1&0\\
 0&ab
 \end{pmatrix}.                                                   \tag{1}
\]
After imposing \(y=x^n\), the second differential is
\[
 ab=mnx^{mn-1},                                                    \tag{2}
\]
the derivative of \(x^{mn}-z\).  Cancelling the displayed contractible identity summand in
`(1)` therefore preserves the determinant orientation and leaves exactly the direct monic
orientation of \(f_{mn}\).

## Proof

Put
\[
 E(a)=\begin{pmatrix}1&a\\0&1\end{pmatrix},\quad
 S=\begin{pmatrix}0&1\\1&0\end{pmatrix},\quad
 D=\begin{pmatrix}-1&0\\0&1\end{pmatrix},\quad
 F(b)=\begin{pmatrix}1&b\\0&1\end{pmatrix}.
\]
Direct multiplication gives
\[
 E(a)A(a,b)=
 \begin{pmatrix}0&ab\\-1&b\end{pmatrix},
\]
\[
 SE(a)A(a,b)=
 \begin{pmatrix}-1&b\\0&ab\end{pmatrix},
\]
and hence
\[
 DSE(a)A(a,b)F(b)=
 \begin{pmatrix}1&0\\0&ab\end{pmatrix}.
\]
Thus take \(L(a)=DSE(a)\) and \(R(b)=F(b)\).  Since
\[
 \det D=-1,\qquad \det S=-1,\qquad \det E(a)=\det F(b)=1,
\]
both \(L(a)\) and \(R(b)\) have determinant \(1\).  This proves `(1)` without changing the
orientation line.

For `(2)`, use \(y=x^n\) and \(m,n\geq1\):
\[
\begin{aligned}
ab
 &=nx^{n-1}\,m(x^n)^{m-1}\\
 &=mnx^{(n-1)+n(m-1)}\\
 &=mnx^{mn-1}.
\end{aligned}
\]
The first diagonal entry of `(1)` is the differential of a contractible rank-one complex.
Removing it leaves the rank-one complex for \(x^{mn}-z\), with the same determinant
orientation.  This is the claimed composition law.

## Scope and non-claim

This proves the orientation needed by Milnor--Witt/Gysin transfers and removes any possible
sign or unit discrepancy in the power semigroup.  A tangential framing is a path
\(\mathcal L_f\simeq0\) in the full algebraic \(K\)-theory space, not only a determinant-line
orientation.  The theorem does not by itself construct the coherent higher homotopies among all
such paths.  Those homotopies are supplied only if the chosen monic presentations are lifted to
the framed-correspondence infinity-category.

## Consequence for arithmetic cohomology

At determinant-orientation level, the power correspondences now form the strict semigroup
\[
 [f_m]\circ[f_n]=[f_{mn}]
\]
with no residual sign character.  Therefore a failure of
\([\Theta,Q]=0\) in the finite Deninger source complex cannot be blamed on an orientation defect
of the monic power maps.  It must occur in the incidence boundary, Gamma completion, or passage
to the source adjoint.

## References

- Elmanto--Hoyois--Khan--Sosnilo--Yakerson, *Framed transfers and motivic fundamental
  classes*, especially the definition of a tangential framing and composition through the
  cotangent transitivity triangle.
- Dég​lise--Jin--Khan, functoriality of motivic fundamental classes for composable lci
  morphisms.

## Novelty audit

The cotangent transitivity triangle and functoriality of fundamental classes are standard.  The
explicit orientation-preserving reduction `(1)` for the power-map presentations is recorded here
because it is the exact arithmetic-semigroup coherence needed by the Deninger construction.
No novelty beyond that specialized extraction is claimed.
