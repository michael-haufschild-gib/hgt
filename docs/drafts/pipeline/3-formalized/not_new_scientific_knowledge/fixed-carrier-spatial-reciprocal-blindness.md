# Fixed-carrier spatial change is reciprocal-spectrally invisible

- **ID:** `fixed-carrier-spatial-reciprocal-blindness`
- **Stage:** 3-formalized
- **Type:** exact connection no-go / positive representation boundary
- **Scientific status:** `[PAPER-PROVED] [REDISCOVERED] [BRIDGE]`
- **Parents:** `../1-in-progress/source-generated-ternary-reciprocity-law.md`,
  `../1-in-progress/purity-boundary-theory-of-everything.md`

## Exact theorem

Let

\[
D\in M_{m,n}(\mathbb C),\qquad
A\in M_m(\mathbb C),\qquad
B\in M_n(\mathbb C)
\]

with

\[
A^\dagger=-A,\qquad B^\dagger=-B.
\]

Define a two-sided spatial variation of the rectangular transfer by

\[
E=AD+DB.
\tag{1}
\]

For the reciprocal squares

\[
Q=D^\dagger D,\qquad G=DD^\dagger,
\]

their first algebraic variations are

\[
\delta Q=E^\dagger D+D^\dagger E,\qquad
\delta G=ED^\dagger+DE^\dagger.
\]

Then

\[
\boxed{\delta Q=QB-BQ}
\tag{2}
\]

and

\[
\boxed{\delta G=AG-GA.}
\tag{3}
\]

Consequently every cyclic power reporter is blind to the spatial variation:

\[
\operatorname{tr}(Q^kB-BQ^k)=0,\qquad
\operatorname{tr}(AG^k-G^kA)=0
\tag{4}
\]

for every \(k\in\mathbb N\).

In complex dimension one, every real rate \(r\) defines

\[
\delta_r(z)=irz
\]

on the scalar ternary product

\[
[x,y,z]=x\overline y z.
\]

The maps \(\delta_r\) are pairwise distinct ternary derivations, while

\[
\overline{\delta_r(z)}z+\overline z\,\delta_r(z)=0.
\tag{5}
\]

Thus reciprocal positive observation cannot reconstruct even a one-dimensional phase connection.

## Paper proof

Taking the conjugate transpose of `(1)` and using skew-adjointness gives

\[
E^\dagger
=D^\dagger A^\dagger+B^\dagger D^\dagger
=-D^\dagger A-BD^\dagger.
\]

Hence

\[
\begin{aligned}
E^\dagger D+D^\dagger E
&=(-D^\dagger A-BD^\dagger)D+D^\dagger(AD+DB)\\
&=-D^\dagger AD-BD^\dagger D+D^\dagger AD+D^\dagger DB\\
&=QB-BQ,
\end{aligned}
\]

proving `(2)`.  Similarly,

\[
\begin{aligned}
ED^\dagger+DE^\dagger
&=(AD+DB)D^\dagger+D(-D^\dagger A-BD^\dagger)\\
&=ADD^\dagger+DBD^\dagger-DD^\dagger A-DBD^\dagger\\
&=AG-GA,
\end{aligned}
\]

proving `(3)`.

Cyclicity of finite matrix trace gives

\[
\operatorname{tr}(Q^kB)=\operatorname{tr}(BQ^k),
\qquad
\operatorname{tr}(AG^k)=\operatorname{tr}(G^kA),
\]

which proves `(4)`.

For `(5)`,

\[
\begin{aligned}
\delta_r(x\overline y z)
&=irx\overline y z,\\
\delta_r(x)\overline y z
+x\overline{\delta_r(y)}z
+x\overline y\delta_r(z)
&=(ir-ir+ir)x\overline y z
=irx\overline y z.
\end{aligned}
\]

Thus \(\delta_r\) is a ternary derivation.  Evaluation at \(1\) distinguishes the rates, while

\[
\overline{irz}z+\overline z(irz)
=-ir\overline z z+ir\overline z z
=0.
\]

Every dependency is closed.

## Exact isometric Gram-variation sequence

There is a sharper full-record statement at an isometric carrier. Assume
\[
D^\dagger D=I_n
\]
and define
\[
\mathcal G_D(E)=E^\dagger D+D^\dagger E.
\tag{6}
\]
Then
\[
\boxed{
\ker\mathcal G_D
=
\{AD:A^\dagger=-A\}.
}
\tag{7}
\]
Moreover \(\mathcal G_D\) is surjective onto the Hermitian matrices:
\[
\boxed{
H^\dagger=H
\quad\Longrightarrow\quad
\mathcal G_D\!\left(\tfrac12DH\right)=H.
}
\tag{8}
\]

The easy inclusion in `(7)` is `(2)` with \(B=0\) and \(D^\dagger D=I\). For the converse,
suppose \(\mathcal G_D(E)=0\), put \(K=D^\dagger E\), and define
\[
A
=ED^\dagger-DE^\dagger-DKD^\dagger.
\tag{9}
\]
The kernel equation gives
\[
K^\dagger=E^\dagger D=-D^\dagger E=-K.
\]
Taking adjoints in `(9)` therefore gives \(A^\dagger=-A\). Finally,
\[
\begin{aligned}
AD
&=E-D(E^\dagger D)-DK\\
&=E+DK-DK\\
&=E.
\end{aligned}
\]
This proves `(7)`. Equation `(8)` follows directly from \(D^\dagger D=I\) and
\(H^\dagger=H\).

Thus the infinitesimal sequence
\[
\mathfrak u(m)
\xrightarrow{\ A\mapsto AD\ }
M_{m,n}(\mathbb C)
\xrightarrow{\ E\mapsto E^\dagger D+D^\dagger E\ }
H_n(\mathbb C)
\longrightarrow0
\tag{10}
\]
is exact at the rectangular variation space and surjective at the Hermitian record. This is the
standard tangent/normal sequence for a complex Stiefel frame, written in event-Gram language. For
a \(3\times2\) carrier it supplies the exact local quotient from twelve real amplitude directions
to four real Hermitian record directions.

Equation `(10)` still does not unify forces. The corpus's
`ColorEventLocalResponseIndependence.lean` proves that Hermitian and skew-Hermitian local responses
remain independently prescribable at the same isometric carrier. Any coupling must therefore
come from source-selected succession, not this pointwise quotient.

## Quadratic survivor: invisible transverse change creates a positive record

The exact sequence has a stronger positive survivor which is more relevant than the linear
tangent/normal slogan.  For an arbitrary variation \(E\), put
\[
K=D^\dagger E,\qquad
H=\frac{K+K^\dagger}{2},\qquad
S=\frac{K-K^\dagger}{2},\qquad
N=E-DK.
\tag{11}
\]
Then
\[
H^\dagger=H,\qquad S^\dagger=-S,\qquad D^\dagger N=0,
\]
and
\[
\boxed{\qquad E=DH+DS+N.\qquad}
\tag{12}
\]
This decomposition is unique.  Indeed, multiplying a proposed decomposition by \(D^\dagger\)
recovers \(H+S\); Hermitian/skew-Hermitian splitting then recovers \(H\) and \(S\), after which
\(N\) is the remainder.

Most importantly, a transverse variation \(N\) is absent at first order but returns with a forced
positive sign at second order.  For every \(t\in\mathbb C\),
\[
\boxed{
D^\dagger N=0
\quad\Longrightarrow\quad
(D+tN)^\dagger(D+tN)
=I_n+|t|^2N^\dagger N.
}
\tag{13}
\]
The proof is direct expansion.  Both cross terms vanish because \(D^\dagger N=0\) and
\(N^\dagger D=(D^\dagger N)^\dagger=0\); the surviving new term is a positive square.

The real dimensions of the three spaces in `(12)` are
\[
\dim H_n(\mathbb C)=n^2,\qquad
\dim\mathfrak u(n)=n^2,\qquad
\dim\{N:D^\dagger N=0\}=2n(m-n).
\tag{14}
\]
Thus the primitive \(3\times2\) event has an exact
\[
12=4_{\rm Hermitian}+4_{\rm skew}+4_{\rm transverse}
\tag{15}
\]
split.  Equal size alone occurs whenever \(2m=3n\); the \(3\times2\) case is the primitive one,
and it is uniquely the primitive case whose Hermitian record is \(H_2(\mathbb C)\), where the
determinant is the Lorentz quadratic form.

There is a further exact specialization.  If \(D\in M_{3,2}(\mathbb C)\) is isometric, then
\(\ker D^\dagger\) is one complex dimensional.  Hence every transverse \(N\) has rank at most one,
so \(N^\dagger N\) is a positive rank-at-most-one \(2\times2\) Hermitian matrix.  Under the
corpus's Pauli-coordinate identification this is a closed-future null vector.  Conversely, every
positive rank-one \(2\times2\) Hermitian matrix has such a transverse square root after choosing a
unit vector in \(\ker D^\dagger\).  Quotienting that choice by its \(U(1)\) phase gives exactly the
future null cone:
\[
\{N:D^\dagger N=0\}/U(1)
\ \simeq\
\{Q\in H_2(\mathbb C)_+:\det Q=0\}.
\tag{16}
\]
Positive sums of these extreme rays fill the complete future cone.

Equations `(13)`--`(16)` are still standard Gram/purification geometry, not a physical
actualization theorem.  Uhlmann amplitudes already represent positive operators by nonunique
square roots and carry a connection on that ambiguity
([Dittmann--Uhlmann](https://arxiv.org/abs/quant-ph/9806028);
[Åberg--Kult--Sjöqvist--Oi](https://arxiv.org/abs/quant-ph/0608185)).
Candidate-new content can only be a source-derived statement that the transverse class is
operationally removed from coherent continuation, that its square is physically created as causal
succession, and that composition of these eventwise square-root torsors yields the observed forces
and gravity.

## External parent and hostile verdict

Pluta--Russo prove that every derivation on a TRO is spatial.  Equations `(2)`--`(4)` are the
finite-matrix coefficient-algebra shadow of that standard operator-algebra mechanism.  Unitary
orbit geometry and gauge theory already interpret inner commutators as vertical change, while
Gauss--Codazzi--Ricci and brane constructions already split tangential, normal, gauge, and
gravitational data.

Verdict: `REDISCOVERED / BRIDGE`.

This is not new physics and does not identify a normal defect with gravity.

Primary boundaries:

- R. Pluta and B. Russo, *Derivations on ternary rings of operators*,
  <https://arxiv.org/abs/1712.03436>.
- K. Akama and T. Hattori, *Brane-induced gravity in higher codimension*,
  <https://arxiv.org/abs/1309.3090>, for the occupied tangent/normal,
  normal-connection/gauge, and induced-gravity representation boundary.

## Strongest positive survivor

The theorem kills the proposal that time or gravity can be reconstructed from the cyclic
reciprocal spectra of an endomorphism derivation of one fixed ternary carrier:

```text
fixed-carrier ternary derivative
  -> spatial left/right action
  -> coefficient commutators
  -> reciprocal spectral blindness.
```

This is not a proof that every spatial variation is physically gauge.  Eigenvectors, matrix
elements relative to a source frame, or interference with a reference carrier can detect changes
that cyclic spectra forget; even the scalar phase in `(5)` is detectable relative to another
phase.  Calling the spatial directions gauge therefore requires an independent operational
quotient declaring them source-invisible.

After such a quotient is defined, a candidate source-normal object is the class

\[
\mathcal N_{\rm src}(D)
=
\bigl[\nabla_{\rm src}D\bigr]\!
\mod
\{AD+DB:A^\dagger=-A,\ B^\dagger=-B\}.
\tag{17}
\]

This **source-normal defect** is the obstruction to horizontalizing change inside the present
reciprocal law.  The exact representation lesson is conditional and narrower:

> fixed-carrier spatial change cannot create reciprocal-spectral novelty; if the physical source
> quotients precisely those spatial directions as gauge, surviving novelty lies in the
> source-normal class.

The corpus's exceptional pure-spinor results independently select a colour-preserving normal
four-carrier.  Connecting `(11)` canonically to that exceptional normal channel is an open theorem,
not part of this card.

The stronger physical target is therefore not merely a normal quotient.  It must construct the
source-relative comparison that decides which spatial changes are gauge, which are observable
orientations, and how information absent from each isolated positive square survives between
successive carriers.

## Lean target

Create
`GaloisForLFunctions.HTGeometry.FixedCarrierSpatialReciprocalBlindness` proving:

1. the matrix identities `(2)` and `(3)`;
2. cyclic trace blindness `(4)` for every power;
3. scalar phase ternary Leibniz identity;
4. scalar reciprocal-square blindness;
5. injectivity of the real phase-rate family;
6. isometric Gram-kernel exactness `(7)` with the explicit skew generator `(9)`; and
7. Hermitian-record surjectivity `(8)`;
8. the canonical three-way decomposition `(11)`--`(12)`; and
9. the positive quadratic return law `(13)`;
10. exact identification of the first Gram reporter with twice the Hermitian face; and
11. injectivity of the combined Hermitian/skew/transverse report.

## Gates

- [x] exact statement frozen
- [x] paper proof dependency-closed
- [x] hostile status `REDISCOVERED / BRIDGE`
- [x] strongest positive representation survivor recorded
- [x] exact Lean formalization
- [x] axiom audit; only `propext`, `Classical.choice`, and `Quot.sound`
- [x] targeted final build:
  `lake build GaloisForLFunctions.HTGeometry.FixedCarrierSpatialReciprocalBlindness`
- [x] repository formal lint clean

## Lean certificate

- **Module:** `GaloisForLFunctions.HTGeometry.FixedCarrierSpatialReciprocalBlindness`
- **Direct check:** `lake env lean
  GaloisForLFunctions/HTGeometry/FixedCarrierSpatialReciprocalBlindness.lean`
- **Target build:** passed, `3013/3013`
- **Formal scope:** identities `(2)`--`(5)`, isometric Gram-kernel exactness and Hermitian
  surjectivity, three-way decomposition, positive quadratic return law, exact Hermitian content
  of the first Gram reporter, and injectivity of the combined three-face report
- **Excluded:** all physical identifications and the source-positive causal Hessian conjecture
