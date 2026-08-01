# Deninger power-map orientation coherence

- **ID:** `deninger-power-map-orientation-coherence`
- **Stage:** 3-formalized
- **Type:** SOURCE CONSTRUCTION LEMMA
- **Parent:** `deninger-mw-gamma-brst-complex`
- **Lean modules:**
  `GaloisForLFunctions.RHTower.DeningerArithmeticPowerOrientation` (the matrices and the
  elementary reduction `(1)`),
  `GaloisForLFunctions.RHTower.DeningerPowerOrientationComposition` (the `SL₂` factorization,
  determinant invariance, and the composite differential `(2)`)

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

## Formalized statement

`GaloisForLFunctions/RHTower/DeningerArithmeticPowerOrientation.lean`:

- `deningerPowerIteratedCotangentMatrix a b = !![a, 0; -1, b]` : the cotangent matrix of the
  iterated presentation;
- `deningerPowerOrientationLeft`, `deningerPowerOrientationRight` : the row and column changes
  `L(a)`, `R(b)`, with `det_deningerPowerOrientationLeft`, `det_deningerPowerOrientationRight`
  proving both lie in `SL₂`;
- `deningerPowerIteratedCotangentMatrix_reduction` : `L(a) A(a,b) R(b) = diag(1, ab)`, which is
  `(1)`.

`GaloisForLFunctions/RHTower/DeningerPowerOrientationComposition.lean`:

- `deningerPowerElemUpper`, `deningerPowerSwap`, `deningerPowerReflect` : the card's `E(a)`, `S`,
  `D`, with their determinants `1`, `-1`, `-1`;
- `deningerPowerOrientationLeft_factor` : `L(a) = D S E(a)`, and
  `deningerPowerOrientationRight_eq` : `R(b) = F(b)` — the card's explicit factorization, in which
  the two sign changes cancel;
- `det_deningerPowerIteratedCotangentMatrix`, `det_deningerPowerSplitCotangentMatrix`,
  `det_deningerPowerIteratedCotangent_reduction` : both matrices have determinant `ab`, so the
  reduction preserves the determinant orientation;
- `deningerPowerPoly k y = X^k - C y` and `deningerPowerPoly_derivative` :
  `d/dx (x^k - y) = k x^(k-1)`, so `a` and `b` are genuinely the differentials of the two monic
  presentations rather than abstract ring elements;
- `deningerPowerComposite_derivative` : for `m, n ≥ 1`,
  `(n x^(n-1)) (m (x^n)^(m-1)) = mn x^(mn-1)`, which is `(2)`.  The exponent bookkeeping
  `(n-1) + n(m-1) = mn-1` is done on `ℕ` after writing `m = M+1`, `n = N+1`, so the truncated
  subtraction is exact;
- `deningerPowerPoly_derivative_composite` : the same statement written directly in terms of the
  presentations — the inner differential at `x` times the outer differential at `x^n` is the
  differential of `x^(mn) - z`;
- `deningerPowerIteratedCotangent_composite` : `(1)` and `(2)` combined —
  `L A R = !![1, 0; 0, d/dx(x^(mn) - z)]`.  This is the determinant-level composition law
  `[f_m] ∘ [f_n] = [f_{mn}]` with no residual unit or sign.

All statements are unconditional over an arbitrary commutative ring, with `m, n ≥ 1` the only
hypotheses.

### Verification

- Direct commands: `lake env lean` on both modules — pass with no errors and no warnings.
- Cached module build: `lake build GaloisForLFunctions.RHTower.DeningerPowerOrientationComposition`
  completes (`✔ [1473/1473]`).
- Scratch `#print axioms`: `deningerPowerComposite_derivative` uses only `propext`; the remaining
  headline theorems use `propext`, `Classical.choice`, `Quot.sound` and nothing else.
- Imported by the `GaloisForLFunctions.RHTower` umbrella.

## Gates

- [x] 0 → 1 in-progress: orientation coherence isolated
- [x] 1 → 2 fully-proven: `(1)` and `(2)` proved
- [x] 2 → 3 formalized: `(1)`, the `SL₂` factorization, determinant invariance, and `(2)`
- [ ] 3 → 4 publication-ready: the higher coherence noted below is a separate construction, not
      part of this statement

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

## Log

- 2026-08-01 — Formalized the composition law.  The pre-existing module already carried the
  matrices and the reduction `(1)`, but not the card's `SL₂` factorization `L(a) = D S E(a)`, not
  the determinant invariance, and not `(2)`.  Added `DeningerPowerOrientationComposition`, which
  supplies all three and ties `a`, `b` to `Polynomial.derivative` of the actual monic
  presentations, ending in `deningerPowerIteratedCotangent_composite`:
  `L A R = diag(1, d/dx(x^(mn) - z))`.  Card moved to `3-formalized`.  The tangential-framing
  higher homotopies remain an explicit non-claim of the card, not an open gate of it.
