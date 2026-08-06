# One-sided framed mate-curvature transgression

- **Stage:** 3-formalized

- **ID:** `deninger-one-sided-framed-mate-curvature-transgression`
- **Route:** L / Deninger source
- **Stage:** 2, fully proved on paper
- **Status:** unconditional source construction; RH not proved
- **Inputs:** `deninger-ramified-top-conormal-ambidexterity`,
  `deninger-power-map-orientation-coherence`,
  `deninger-gamma-tensor-square-mate-identification`

## 1. Frontier addressed

The updated Hellinger--Hodge--Green descent paper proves that horizontal
displacement in the joint-depth source is an endpoint character.  Its
ordinary incidence matrices are diagonally similar for every displacement,
so all scalar loop holonomies, determinants, characteristic polynomials, and
cyclic trace moments are horizontally blind.  It identifies the missing
source object as a parameter-dependent nonflat curvature transgression before
reflection-diagonal sewing.

The Deninger source has an extra structure unavailable to the scalar
joint-depth carrier: the framed power correspondence has two distinct
cotangent terms.  The conormal term is transported by the affine
top-conormal law, while the differential term is its target.  A half-density
mate gain can therefore act on only one term.  This one-sided action does not
commute with affine top-conormal transport and creates a genuine rank-two
composition curvature.

## 2. Affine top-conormal representation

Let `R` be a commutative ring.  For a positive power degree `n`, put

\[
 A_n=
 \begin{pmatrix}
 n&n-1\\
 0&1
 \end{pmatrix}.
 \tag{1}
\]

The first coordinate is the conormal line, the second is the differential
line, and the upper-right entry is the coherent top-conormal displacement.
Direct multiplication gives

\[
 A_mA_n=
 \begin{pmatrix}
 mn&m(n-1)+(m-1)\\
 0&1
 \end{pmatrix}
 =A_{mn}.
 \tag{2}
\]

Thus the unique nonraw monomial sector `r_n=n-1` is itself flat.  More
precisely, it is the affine coboundary `r_n=n\cdot1-1`.  This explains why
the top-conormal correction by itself cannot be the nonflat horizontal class
requested by the updated descent theorem.

## 3. One-sided character twist and exact curvature

Let `chi : N_{>0} -> R` be a multiplicative character.  Place it on the
conormal term only:

\[
 D_\chi(n)=
 \begin{pmatrix}\chi(n)&0\\0&1\end{pmatrix},
 \qquad
 T_\chi(n)=D_\chi(n)A_n
 =\begin{pmatrix}
   \chi(n)n&\chi(n)(n-1)\\
   0&1
  \end{pmatrix}.
 \tag{3}
\]

Define its composition curvature by

\[
 F_\chi(m,n)=T_\chi(m)T_\chi(n)-T_\chi(mn).
 \tag{4}
\]

### Theorem 3.1 (one-sided framed curvature)

For every positive `m,n`,

\[
 \boxed{
 F_\chi(m,n)=
 \begin{pmatrix}
  0&\chi(m)(m-1)(1-\chi(n))\\
  0&0
 \end{pmatrix}.}
 \tag{5}
\]

In particular, after removing the canonical nonzero left source factor
`chi(m)(m-1)`, the reduced curvature is

\[
                    f_\chi(n)=1-\chi(n).
 \tag{6}
\]

#### Proof

The diagonal entry of `T_chi(m)T_chi(n)` is
`chi(m)chi(n)mn=chi(mn)mn`, so it cancels the diagonal entry of
`T_chi(mn)`.  The upper-right difference is

\[
\begin{aligned}
 &\chi(m)m\,\chi(n)(n-1)+\chi(m)(m-1)
      -\chi(mn)(mn-1)\\
 &=\chi(m)\bigl(m\chi(n)(n-1)+(m-1)-\chi(n)(mn-1)\bigr)\\
 &=\chi(m)(m-1)(1-\chi(n)).
\end{aligned}
\]

All other entries vanish.  This is `(5)`.

### Theorem 3.2 (nonabelian Bianchi identity)

For arbitrary matrices `T(n)` and
`F(m,n)=T(m)T(n)-T(mn)`, associativity gives

\[
 F(\ell,m)T(n)+F(\ell m,n)
 =T(\ell)F(m,n)+F(\ell,mn).
 \tag{7}
\]

Hence `(5)` is a coherent two-curvature, not an isolated failure of one
composition square.

#### Proof

Both sides expand to

\[
             T(\ell)T(m)T(n)-T(\ell mn).
\]

## 4. Deninger half-density specialization

For `n>0` and `s in C`, define the positive mate-gain character

\[
 \chi_s(n)
  =\lVert n^{1/2-s}\rVert^{-2}
  =\exp\!\bigl((2\operatorname{Re}s-1)\log n\bigr).
 \tag{8}
\]

The logarithm law proves

\[
                  \chi_s(mn)=\chi_s(m)\chi_s(n).
 \tag{9}
\]

Its dual is `chi_s^vee(n)=chi_s(n)^(-1)`.  The difference between the two
reduced one-sided curvatures is

\[
\begin{aligned}
 f_{\chi_s^\vee}(n)-f_{\chi_s}(n)
  &=(1-\chi_s(n)^{-1})-(1-\chi_s(n))\\
  &=\chi_s(n)-\chi_s(n)^{-1}\\
  &=\lVert n^{1/2-s}\rVert^{-2}
       -\lVert n^{1/2-s}\rVert^2\\
  &=K_n(s).
\end{aligned}
\tag{10}
\]

Thus Deninger tensor-square source-inverse/analytic-dagger mate curvature is
not merely a scalar detector: it is exactly the polarization difference of
two nonflat rank-two framed composition curvatures.

For `m,n>=2`, every factor outside `1-chi_s(n)` in `(5)` is nonzero, and

\[
 F_{\chi_s}(m,n)=0
 \quad\Longleftrightarrow\quad
 \chi_s(n)=1
 \quad\Longleftrightarrow\quad
 \operatorname{Re}s=\frac12.
 \tag{11}
\]

This is an exact nonflat horizontal curvature class with critical-line
radical.  Unlike the joint-depth scalar edge character, it cannot be removed
by diagonal similarity: its obstruction is failure of multiplicativity of
the one-sided rank-two transport itself.

## 5. Actual Gamma boundary comparison

The existing ordered `(2,3)` comparison has forced composite carrier degree
`6` and proves

\[
 b_\Gamma(q)=c_{23}K_6(\rho_q),\qquad c_{23}>0.
 \tag{12}
\]

Combining `(10)` and `(12)` gives the source-level factorization

\[
 \boxed{
 b_\Gamma(q)=c_{23}
   \bigl(f_{\chi_{\rho_q}^{\vee}}(6)
         -f_{\chi_{\rho_q}}(6)\bigr).}
 \tag{13}
\]

Therefore actual Gamma/co-Poisson boundary coefficient is a positive
calibration of the polarization difference of two explicit framed
two-curvatures.  This supplies the parameter-dependent nonflat curvature
object missing from the scalar joint-depth descent and identifies its actual
Gamma realization without using `K_6=0`, a Xi-zero-location premise, or RH.

## 6. Hostile novelty and anti-theatre audit

### Classical background, not claimed new

- monic hypersurface cotangent complex and derivative of `x^n-y`;
- affine-matrix identity `(2)`;
- curvature-as-failure-of-multiplicativity and Bianchi identity `(7)`;
- multiplicativity of `exp(alpha log n)`;
- scalar formula `K_n=chi_n-chi_n^{-1}`.

The conormal/differential presentation is standard; see the Stacks Project,
Tag `06BB`, for conormal and differential exact sequences.  Frobenius
semigroup geometry is also established background in the arithmetic-site and
Deninger programs.

### Candidate-new synthesis

No matching construction was found in the project corpus or targeted
literature search.  Candidate-new content is the simultaneous package:

1. identify the coherent top-conormal shift with the flat affine
   representation `(1)`;
2. act by the Deninger mate gain on exactly one framed cotangent term;
3. compute its nonflat two-curvature `(5)` and full Bianchi law `(7)`;
4. identify source/dual reduced-curvature polarization exactly with
   `K_n(s)` in `(10)`;
5. identify actual ordered Gamma boundary with that polarization at the
   forced degree `6` in `(13)`.

This moves the updated paper's frontier from "construct a nonflat horizontal
curvature" to a strictly narrower analytic problem.

### What remains open

This theorem does **not** annihilate the curvature and does **not** prove RH.
It constructs the reporter whose vanishing is equivalent to the critical
line.  The exact remaining hard core is:

`[FRAMED_MATE_CURVATURE_SINGULAR_STOKES_ANNIHILATION]`

> Extend the rank-two curvature `(5)` coefficient-faithfully to the completed
> Xi Green incidence/common-test carrier before reflection-diagonal sewing.
> Construct a source-canonical singular Cartier residue/Stokes functional and
> prove, from an arithmetic boundary law independent of Xi zero locations,
> that it annihilates the source/dual polarization `(10)` while remaining
> conservative on completed Green provenance.

Using the already-known Gamma identification to assume the polarization
vanishes would be circular.  A mere Bianchi identity is also insufficient:
`(7)` holds for every `s`, including off line.

## 7. Formalization target

Lean formalization must prove unconditionally:

- affine top-conormal matrices compose;
- exact one-sided curvature formula `(5)`;
- Bianchi identity `(7)`;
- mate-gain formula and multiplicativity `(8)`--`(9)`;
- reduced source/dual curvature difference equals `K_n(s)`;
- nonflatness criterion `(11)`;
- actual Gamma specialization `(13)`.


- 2026-08-06 — Formalization re-verified on this toolchain: the named Lean module exists, is wired into `GaloisForLFunctions.RHTower`, builds, uses no `native_decide`, and every audited declaration depends only on `propext, Classical.choice, Quot.sound`.  Every gate this card states is closed; what the card lists as still open is its declared successor core, not this theorem.  Card moves to `3-formalized`.
