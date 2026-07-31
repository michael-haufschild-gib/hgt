# Suzuki marked-secant midpoint Lorentz completion

- **ID:** `suzuki-marked-secant-midpoint-lorentz-completion`
- **Stage:** 2 — fully proved on paper
- **Type:** exact source obstruction + sharp positive survivor
- **Status:** `[PROVED HERE] [UNCONDITIONAL] [SOURCE-PURE ALGEBRA]`
- **Parents:**
  `../../1-in-progress/suzuki-rooted-midpoint-compound-gram.md`,
  `suzuki-global-local-compound-bezoutian-weld.md`
- **Lean target:**
  `formal/GaloisForLFunctions/RHTower/SuzukiMarkedSecantMidpointLorentzCompletion.lean`

## 1. Problem fixed by theorem

Canonical full-jump carrier is compound pair

\[
N=QT-SP,\qquad D=PT,
\]

where `(Q,P)` is local marked Volterra secant pair and `(S,T)` is global completed-Xi pair.  The
remaining RH-bearing problem is positive prime--Gamma Gram factorization of its Hermitian
Bezoutian.  Existing representation did not identify inertia of marked local tensor or amount and
location of source completion needed before a Gram factorization is possible.

## 2. Midpoint/halfgap coordinates

Let `R` be a commutative ring and put

\[
\alpha=m-d,\qquad \beta=m+d,\qquad p=\alpha\beta=m^2-d^2.
\]

For marked local coordinates set

\[
B_0=X+c,\quad U=B_0-mx,\quad V=Y-my,
\quad F=B_0y-xY=Uy-xV.
\]

Recall

\[
Q_{\alpha,\beta}=B_0Y-(\alpha+\beta)xY+\alpha\beta xy,
\qquad
P_{\alpha,\beta}=(Y-\beta y)(Y-\alpha y).
\]

## 3. Theorem A: exact Lorentz--Pluecker decomposition

For arbitrary commutative-ring data,

\[
\boxed{Q_{m-d,m+d}=UV-d^2xy+mF},                     \tag{1}
\]

\[
\boxed{P_{m-d,m+d}=V^2-d^2y^2}.                      \tag{2}
\]

Equivalently, define symmetric and alternating bilinear forms

\[
\begin{aligned}
\mathcal S_{m,d}((r,s),(R,S))
  &=rR-m(rS+sR)+(m^2-d^2)sS,\\
\mathcal A_m((r,s),(R,S))
  &=m(rS-sR).
\end{aligned}
\]

Then

\[
Q_{m-d,m+d}=\mathcal S_{m,d}((B_0,x),(Y,y))
             +\mathcal A_m((B_0,x),(Y,y)),             \tag{3}
\]

and

\[
\mathcal S_{m,d}((r,s),(r,s))=(r-ms)^2-d^2s^2.        \tag{4}
\]

### Proof `[PROVED HERE]`

Use `alpha+beta=2m` and `alpha*beta=m^2-d^2`.  Expanding right side of `(1)` gives

\[
(B_0-mx)(Y-my)-d^2xy+m(B_0y-xY)
=B_0Y-2mxY+(m^2-d^2)xy=Q.
\]

Equation `(2)` is difference of squares.  Expanding `(3)` cancels `-mB_0y` from symmetric part
against `+mB_0y` from alternating part and doubles `-mxY`.  Setting two arguments equal kills
alternating form and completes square, proving `(4)`.  No division is used. \(\square\)

## 4. Theorem B: sharp unique diagonal completion

For real `m,d,kappa`, following are equivalent:

\[
\forall r,s\in\mathbb R,\quad
r^2-2mrs+(m^2-d^2)s^2+\kappa s^2\ge0,                \tag{5}
\]

\[
\kappa\ge d^2.                                       \tag{6}
\]

Indeed exact identity is

\[
r^2-2mrs+(m^2-d^2)s^2+\kappa s^2
=(r-ms)^2+(\kappa-d^2)s^2.                           \tag{7}
\]

At unique minimal rate `kappa=d^2`, completed form is rank-one square `(r-ms)^2`.  If `d!=0`,
uncompleted form has exactly one positive and one negative direction: values at `(1,0)` and
`(m,1)` are `1` and `-d^2` respectively.  Since leading principal coefficient is positive, its
two-dimensional inertia is `(1,1)`.

### Proof `[PROVED HERE]`

Identity `(7)` is expansion.  If `(6)` holds, both terms on right are nonnegative.  Conversely,
apply `(5)` at `(r,s)=(m,1)` to get `kappa-d^2>=0`.  Minimality and inertia witnesses follow
immediately. \(\square\)

This is sharper than generic Schur-complement statement: source owes exactly square of shift
halfgap.  Existing local coefficient `p=alpha*beta=m^2-d^2` plus minimal completion `d^2` becomes
`m^2`, exactly coefficient required for perfect joint square.

## 5. Theorem C: compound numerator splits into three forced channels

For arbitrary global pair `(S,T)`, exact full-jump compound numerator satisfies

\[
\boxed{
N=V(UT-SV)+d^2y(Sy-xT)+mFT.}                         \tag{8}
\]

Its denominator is

\[
D=(V^2-d^2y^2)T.                                     \tag{9}
\]

### Proof `[PROVED HERE]`

Insert `(1)--(2)` into `N=QT-SP`:

\[
\begin{aligned}
N&=(UV-d^2xy+mF)T-S(V^2-d^2y^2)\\
 &=V(UT-SV)+d^2y(Sy-xT)+mFT.
\end{aligned}
\]

Equation `(9)` is immediate. \(\square\)

Thus open Gram is not amorphous.  It has exactly:

1. midpoint projective determinant `V(UT-SV)`;
2. halfgap-squared rooted debt channel `d^2 y(Sy-xT)`;
3. centered Pluecker flux `mFT`.

## 6. Theorem D: midpoint gauge becomes shear and flux is invariant

Under local affine gauge

\[
(x,X)\mapsto(x+\delta y,X+\delta Y),
\]

midpoint variables transform by

\[
(x,U)\mapsto(x+\delta y,U+\delta V),\qquad F\mapsto F. \tag{10}
\]

Consequently Lorentz term in `(1)` changes by

\[
\delta(V^2-d^2y^2)=\delta P,
\]

recovering marked-tensor gauge covariance term-by-term.  This identifies affine gauge as null-cone
shear; it is not hidden in quotient algebra.

### Proof `[PROVED HERE]`

Substitute gauged variables into definitions of `U` and `F`; cross terms in `F` cancel.  Expanding
gauged Lorentz term yields old term plus `delta P` using `(2)`. \(\square\)

## 7. Dyadic Suzuki specialization

For `alpha=-2L`, `beta=-L`,

\[
m=-\frac{3L}{2},\qquad d=\frac L2,qquad
p=2L^2.
\]

Therefore

\[
Q=\left(B_0+\frac{3L}{2}x\right)
  \left(Y+\frac{3L}{2}y\right)
  -\frac{L^2}{4}xy
  -\frac{3L}{2}(B_0y-xY),                             \tag{11}
\]

and sharp missing rooted diagonal coefficient is

\[
d^2=\frac{L^2}{4}.                                   \tag{12}
\]

After payment, total rooted coefficient is

\[
p+d^2=\frac{9L^2}{4}=m^2.                            \tag{13}
\]

This separates pre-existing `2L^2` rooted mass from genuinely missing `L^2/4` completion.  Any
candidate source identity paying only a linear shift cost or an unspecified negative projector
is in wrong coordinates.

## 8. Balanced-boundary obstruction and positive survivor

Corpus proves orthogonal, affine, every positive jet, growing jet, and cofinal two-boundary
von-Mangoldt--Gamma Grams are exactly zero on canonical packet `(+1/2,-1/2)`.  Marked secant does
not vanish there as a representation: rank-one specialization recovers arbitrary affine
intercept `L/D`.

Therefore no producer that factors only through balanced two-boundary Gram and sends zero source
to zero can generate full marked compound carrier.  This is an exact obstruction, not lack of
estimate.

Strongest positive survivor is forced architecture:

> Retain one raw rooted Gamma--Bianchi coordinate before boundary compression.  It must pay exact
> halfgap debt `d^2`.  Combine it with common-prime Julia coordinate through already forced mixed
> cross term.  Only after symmetric block reaches perfect square may boundary balancing occur.

## 9. Corrected RH frontier

### `SUZUKI-ROOTED-MIDPOINT-COMPOUND-GRAM` `[CONJECTURE]`

Specialize `(8)` to actual Volterra phase observations and `(S,T)=(XiC',z^2XiC)`.  Prove from
prime--Gamma source and pointed Ward identity that signed global Xi term supplies exactly `d^2`
times raw rooted Bianchi Gram, plus positive archimedean remainder.  Local marked term supplies
Julia block, forced mixed block with coefficient `-m`, and rooted coefficient
`alpha*beta=m^2-d^2`.  Combined symmetric block is perfect joint square

\[
\operatorname{Gram}(J-mB),                            \tag{14}
\]

with Pluecker phase carried by independently fixed Xi-real quarter-turn.  This factors canonical
compound Bezoutian and existing formal connector proves RH.

Falsifier is one atom coefficient not equal to `d^2`, one wrong forced mixed term, or one negative
finite principal minor after exact Gamma remainder is retained.  No Herglotz/RH premise or fitted
feature is allowed.

## 10. Novelty and external audit

The square completion and two-dimensional inertia are classical linear algebra.  Generalized
Nevanlinna theory studies kernels with one negative square; for example de Snoo--Winkler--Wojtylak,
https://arxiv.org/abs/1011.2081.  Those are parent theories, not novelty claims.

Suzuki's source criterion and 2026 self-adjoint construction are
https://arxiv.org/abs/2206.03682 and https://arxiv.org/abs/2606.09096.  They do not state marked
midpoint pair `(1)--(2)`, compound three-channel identity `(8)`, or sharp rooted debt `(12)`.
Corpus-wide exact searches found none.  Source-specific synthesis and sharpened RH conjecture are
`[CANDIDATE NOVELTY; EXTERNAL PRIORITY UNVERIFIED]`.

## 11. Dependency audit

- Theorems A--D: polynomial identities or square positivity; dependency-closed.
- Balanced-boundary obstruction: uses existing exact zero-Gram and marked rank-one intercept
  theorem; dependency-closed.
- Equation `(14)`: conjecture.  No RH result claimed.

## 12. Formal status

All dependency-closed statements in Theorems A--D, dyadic sharp completion, compound split,
two-resolvent midpoint forcing, physical Neumann-debt identity, and marked-Xi compound connectors
are formalized in `SuzukiMarkedSecantMidpointLorentzCompletion.lean`.  Direct Lean and final SOTA
build pass; foundation audit contains only standard `propext`, `Classical.choice`, and `Quot.sound`.
Open source conjecture `(14)` is deliberately not encoded as an axiom or theorem.
