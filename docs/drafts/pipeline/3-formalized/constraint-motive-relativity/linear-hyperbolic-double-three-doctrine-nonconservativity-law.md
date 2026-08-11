# Linear hyperbolic double: three-doctrine nonconservativity law

- **ID:** `cmr-linear-hyperbolic-three-doctrine-nonconservativity`
- **Stage:** 3-formalized
- **Type:** THEOREM (paper) / FALSIFIER OF A UNIVERSAL FIELD CARRIER
- **Status:** `[PAPER-PROVED] [DEPENDENCY-CLOSED] [WHOLE-FIELD PIVOT]`
  `[MASS] [RECURRENCE] [HYPERTRANSCENDENCE] [NOT RH]`
  `[LEAN-FORMALIZED UNCONDITIONALLY]`
- **Formalized companion:**
  `linear-hyperbolic-double-three-doctrine-nonconservativity-law-formalized.md`.
- **Parent field:**
  `../../1-in-progress/constraint-motive-relativity/polarized-constraint-duality-geometry.md`.
- **Corpus parent:**
  `../../3-formalized/mass-shifted-hankel-flat-quadrature-extension-class.md`.
- **Statement:** The unmarked linear hyperbolic double `K direct-sum K^*` is not jointly
  conservative for affine moment extension, integral recurrence, and differential
  hypertranscendence: each doctrine has exact pairs with the same bare double and different native
  constitutive data.

## 1. Scope

For a finite-dimensional vector space `K` over `k`, write

\[
 \mathbb H(K)=K\oplus K^*,
 \qquad
 h((x,\alpha),(y,\beta))=\alpha(y)+\beta(x).
\tag{NC.1}
\]

Relative-law observer descent and cotangent geometry naturally produce this split hyperbolic
object. The question is whether its unmarked isomorphism class can be the common carrier for all
proof routes.

The answer is no even before topology or infinite dimension enters.

## 2. The theorem

### Theorem 2.1 — three-doctrine nonconservativity

There are exact pairs of objects in each of the following doctrines:

1. singular positive Hankel faces with affine successor moments;
2. two-frequency recurrence systems with integral relation lattices;
3. differential field extensions with relative differential cotangents;

such that the associated bare linear kernel `K`, and hence `H(K)`, is isomorphic within each pair,
while the native constitutive datum is different. Consequently:

> No invariant that factors only through the unmarked isomorphism class of `H(K)` can be jointly
> conservative for the affine-extension, integral-recurrence, and differential-HT doctrines.

More explicitly, the information lost in the three pairs is respectively:

\[
 \text{affine normal orientation},\qquad
 \text{integral relation rank/torus closure},\qquad
 \text{relative differential transcendence rank}.
\tag{NC.2}
\]

## 3. Affine moment-extension countermodel

Let a real moment functional be specified through degree two by

\[
 s_0=1,\qquad s_1=10,\qquad s_2=100.
\tag{NC.3}
\]

Its size-two Hankel matrix is

\[
 H=\begin{pmatrix}1&10\\10&100\end{pmatrix}
 =\begin{pmatrix}1\\10\end{pmatrix}
  \begin{pmatrix}1&10\end{pmatrix}\succeq0.
\tag{NC.4}
\]

It has rank one and null line

\[
 K=\mathbb R(-10,1).
\tag{NC.5}
\]

The monic null polynomial is `p(X)=X-10`. The first unseen shifted-square remainder is

\[
 R(s_3)=L\bigl(Xp(X)^2\bigr)
 =s_3-20s_2+100s_1=s_3-1000.
\tag{NC.6}
\]

Choose two affine successors

\[
 s_3^+=1004,
 \qquad
 s_3^-=984.
\tag{NC.7}
\]

Then

\[
 R(s_3^+)=4,
 \qquad
 R(s_3^-)=-16.
\tag{NC.8}
\]

Both successors have the identical current positive Hankel face, identical determinant,
discriminant, null line, null polynomial, quadrature node, and bare hyperbolic double `H(K)`.
They have opposite outgoing affine orientation. The forgetful map retaining only the current face,
`K`, or `H(K)` identifies the two successors, whereas the affine remainder `R` separates them.

This is the `n=1` instance of the corpus theorem that changing only `s_(2n+1)` leaves the entire
current Hankel face fixed and translates the monic remainder arbitrarily.

## 4. Integral recurrence countermodel

For `alpha>0`, consider the real detuning map

\[
 d_\alpha:\mathbb R^2\longrightarrow\mathbb R,
 \qquad d_\alpha(x,y)=x+\alpha y.
\tag{NC.9}
\]

For every `alpha`, its real kernel is one-dimensional:

\[
 K_\alpha=\mathbb R(-\alpha,1).
\tag{NC.10}
\]

Hence

\[
 \mathbb H(K_2)\cong\mathbb H(K_{\sqrt2})\cong\mathbb H(\mathbb R).
\tag{NC.11}
\]

The recurrence doctrine retains the integral relation lattice

\[
 \Lambda_\alpha=\ker(d_\alpha|\mathbb Z^2).
\tag{NC.12}
\]

Directly,

\[
 \Lambda_2=\mathbb Z(-2,1),
 \qquad
 \Lambda_{\sqrt2}=0,
\tag{NC.13}
\]

because `m+sqrt(2)n=0` with integers `m,n` forces `m=n=0`.

Equivalently, the phase orbit

\[
 t\longmapsto(e^{it},e^{i\alpha t})\in\mathbb T^2
\tag{NC.14}
\]

is periodic for `alpha=2` and dense in `T^2` for `alpha=sqrt(2)` by Kronecker's theorem. Thus the
same bare real hyperbolic double supports different exact periodicity, relation-lattice rank, and
observer orbit closure.

The lost datum is not another real covector. It is the integral relation lattice and its
annihilator phase hull `widehat(Z^2/Lambda_alpha)`.

## 5. Differential-HT countermodel

Let `(k,delta)` be a differential field of characteristic zero. For `r>=0`, let

\[
 E_r=k\langle y_1,\ldots,y_r\rangle
\tag{NC.15}
\]

be the differential rational-function field in `r` differential indeterminates over `k`. The
structure map

\[
 i_r:k\hookrightarrow E_r
\tag{NC.16}
\]

is injective for every `r`, so its ordinary killed-law kernel is

\[
 K_r=\ker i_r=0,
 \qquad \mathbb H(K_r)=0.
\tag{NC.17}
\]

Nevertheless,

\[
 \operatorname{dtrdeg}_kE_r=r.
\tag{NC.18}
\]

Indeed, the differential monomials generated by the `y_j` have no nonzero differential-polynomial
relation by construction, and they generate `E_r` differentially. The ordinary Kähler module
`Omega^1_(E_r/k)` has `E_r`-basis

\[
 \{d(\delta^ny_j):1\leq j\leq r,\ n\geq0\}.
\tag{NC.19}
\]

With `delta_Omega(da)=d(delta a)`, these form `r` free prolongation towers generated by
`dy_1,...,dy_r`.

Thus `E_r` and `E_s` with `r!=s` have the same zero bare hyperbolic kernel double but different
relative differential dimension. They cannot be isomorphic over `k` as differential field
extensions because differential transcendence degree is invariant.

This proves that relative differential transcendence rank cannot be recovered from the ordinary
killed-law kernel or its bare hyperbolic double. A genuine relative differential
cotangent/prolongation object does recover it.

## 6. Proof of Theorem 2.1

Sections 3--5 construct the three required pairs.

- `(NC.5)--(NC.8)` keep `K` and `H(K)` fixed while changing the affine remainder.
- `(NC.10)--(NC.14)` keep the real isomorphism class of `K` and `H(K)` fixed while changing the
  integral relation lattice and torus closure.
- `(NC.17)--(NC.19)` keep `K=0` and `H(K)=0` fixed while changing differential rank.

If an invariant factors through the unmarked isomorphism class of `H(K)`, it takes the same value
on each pair. The corresponding native constitutive data differ, so the invariant is not jointly
conservative. This proves the theorem.

## 7. Positive survivor: minimum data excluded from the bare double

The theorem does not say unification is impossible. It classifies the minimum additional native
data forced by these three doctrines:

1. **Mass/affine chart:** retain the torsor of successor moments and its source-selected affine
   normal coordinate, not only the current-face kernel.
2. **Recurrence chart:** retain the integer relation lattice `Lambda` and annihilator phase hull
   `widehat(Z^d/Lambda)`, not only the real detuning kernel.
3. **HT chart:** retain the relative differential cotangent/prolongation object and its Kolchin
   growth, not only the kernel of the underlying map.

These additions need not lie in one category. A system of typed dualities and correspondences is
one proposed common carrier. The theorem neither constructs this carrier nor proves its
uniqueness.

## 8. Corpus consequences

1. A theorem about killed classes and failed linear observer descent can be exact and still cover
   only the linear/stable chart.
2. Same singular positive face does not determine Mass outgoing sign. The missing datum is affine,
   not another positive norm on the face.
3. Same real spectral dimension does not determine recurrence. Integral relation rank is invariant
   under integral changes of coordinates, but is not determined by the unmarked real-kernel
   isomorphism class.
4. Zero ordinary kernel does not imply differential algebraicity or finite HT complexity.
5. Calling all three phenomena `curvature of K direct-sum K^*` loses precisely the data the routes
   require and is therefore theatre.

## 9. Falsifiable predictions

1. Any proposed universal route invariant depending only on rank, signature, or determinant of a
   bare linear anomaly space has countermodels of the three forms above.
2. A jointly conservative Mass-to-recurrence comparison must transport or reconstruct the affine
   normal and integral winding/history data. A nonconservative comparison may explicitly forget
   either; matching vector dimensions alone proves nothing.
3. A jointly conservative recurrence-to-HT comparison must reconstruct both lattice/character
   growth and differential prolongation rank. Dense or periodic local phase orbit alone cannot
   determine HT.
4. Any universal field needs doctrine labels or equivalent reconstructible structure. Erasing
   them before comparison destroys joint conservativity.

## 10. No-go closure

- **Exact killing theorem/mechanism:** the forgetful map to `H(K)` identifies pairs with different
  affine, integral, and differential invariants.
- **Strongest positive survivor:** affine orientation, integral relation/phase-hull data, and
  differential prolongation are three kinds of information that no invariant factoring only
  through unmarked `H(K)` can recover.
- **New insight:** a single unmarked linear hyperbolic double cannot be the jointly conservative
  carrier; richer fixed ambient structures remain possible.
- **Status:** Theorem 2.1 dependency-closed and unconditionally formalized in Lean 4 (see the
  formalized companion); polydual-carrier interpretation conjectural.

## Log

- 2026-08-09 — exact Mass `4/-16`, rational/irrational recurrence, and arbitrary differential-rank
  countermodels proved.
- 2026-08-09 — universal cotangent carrier retired; polydual positive survivor recorded.
- 2026-08-11 — unconditionally formalized in Lean 4 and promoted to `3-formalized`.
