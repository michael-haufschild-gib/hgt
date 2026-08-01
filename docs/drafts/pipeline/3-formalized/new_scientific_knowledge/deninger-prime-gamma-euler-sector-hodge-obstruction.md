# Prime--Gamma Euler-sector Hodge obstruction

- **ID:** deninger-prime-gamma-euler-sector-hodge-obstruction
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Source:** `docs/Deninger program.md`, Sections 6--8
- **Statement:** Absolute-convergence prime--Gamma Cauchy sectors support source Poincare
  duality, but canonical complex conjugation does not identify a lower atom with the same Weil
  test in the upper sector; hence this core alone cannot supply Deninger's diagonal Hodge metric.

## Goal

Locate exactly where source-defined prime--Gamma packet cohomology stops.  This prevents the
source cup pairing from being renamed a positive Hodge form and fixes the next construction:
analytic continuation or additional arithmetic geometry must supply the Hodge comparison.

## Gates

- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [x] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [x] 2 → 3  formalized: Lean theorem
  `deningerPrimeGammaLowerCauchyTest_ne_conjugateUpperAtom`, direct Lean check and axiom audit
- [ ] 3 → 4  publication-ready: standalone paper

## Setup

Write
\[
  s(z)=\frac12+iz .
\]
The source packet construction uses
\[
  L=\{z\in\mathbb C:1<\Re s(z)\}
\]
and
\[
  U=\{w\in\mathbb C:
      1<\Re(\tfrac12+i\overline w)\}.
\]
For \(z=x+iy\),
\[
  \Re s(z)=\frac12-y.
\]
For \(w=u+iv\),
\[
  \Re(\tfrac12+i\overline w)=\frac12+v.
\]
Consequently
\[
  z\in L\Longrightarrow \Im z<-\frac12,\qquad
  w\in U\Longrightarrow \Im w>\frac12.                 \tag{1}
\]

The lower Cauchy atom with coefficient \(c\) is
\[
  F_{z,c}(a)=\frac{c}{a-z}.                             \tag{2}
\]
For an upper atom \((w,d)\), the construction first forms the linear sharp test
\[
  S_{w,d}(a)=\frac{d}{a-\overline w}
\]
and then applies the Weil involution
\[
  G^\#(a)=\overline{G(\overline a)}.
\]
Thus its actual upper test is
\[
  G_{w,d}(a)=\frac{\overline d}{a-w}.                   \tag{3}
\]

## Theorem `[PROVED HERE]`

1. The sectors \(L\) and \(U\) are disjoint.
2. Complex conjugation gives a bijection
   \[
     \kappa:L\longrightarrow U,\qquad z\longmapsto\overline z.
   \]
3. On a lower atom, conjugating both parameter and coefficient gives
   \[
     G_{\overline z,\overline c}(a)
       =\frac{c}{a-\overline z},                        \tag{4}
   \]
   not \(F_{z,c}(a)\).
4. If \(c\ne0\), the two rational test functions in `(2)` and `(4)` are distinct.

### Proof

Assertion 1 follows immediately from `(1)`.  Conjugation negates imaginary part, so `(1)` also
proves assertion 2.  Formula `(3)` gives assertion 3.

For assertion 4, `(1)` implies \(z\ne\overline z\).  Evaluate at \(a=z\), using the totalized
field inverse convention:
\[
  F_{z,c}(z)=c\,(z-z)^{-1}=0,
\]
whereas
\[
  G_{\overline z,\overline c}(z)
    =c\,(z-\overline z)^{-1}\ne0
\]
because \(c\ne0\) and \(z-\overline z\ne0\).  Hence the functions differ. \(\square\)

## No-go closure

- **Exact killing theorem/mechanism:** strict absolute Euler convergence forces the lower and
  upper Cauchy parameters into disjoint half-planes.  Canonical conjugation changes the pole from
  \(z\) to \(\overline z\), so it cannot turn the bilinear source cup pairing into a diagonal
  Hermitian norm on the same packet vector.
- **Strongest positive survivor:** the already constructed radical quotients and their
  nondegenerate alternating cup form remain a genuine source-defined algebraic
  \(H^1_-\oplus H^1_+\) with Poincare duality.  Only the Hodge identification is absent.
- **New insight:** Deninger's missing positive metric is not an algebraic quotient operation on
  the absolute-convergence packet core.  It requires either a source-controlled continuation
  across the critical strip or a new arithmetic geometric object carrying a flow-natural Hodge
  star before comparison with the Xi divisor.
- **Status:** paper proof dependency-closed; Lean batch verified in
  `DeningerPrimeGammaEulerSectorObstruction.lean` — the module compiles and builds, and every
  declaration audits to `propext, Classical.choice, Quot.sound`.

## Log

- 2026-07-26 — `[PROVED HERE]`; direct Deninger scope, no Xi-zero enumeration or RH premise.

## Lean status

### All four assertions landed

`formal/GaloisForLFunctions/RHTower/DeningerPrimeGammaEulerSectorObstruction.lean`.  Axiom audit:
`propext, Classical.choice, Quot.sound`.

- `deningerPrimeGammaLowerPoint_im_lt`, `deningerPrimeGammaUpperPoint_im_gt` — **`(1)`**: strict
  absolute-Euler convergence puts the lower parameters below `-1/2` and the upper ones above
  `1/2` in imaginary height.
- `deningerPrimeGammaLower_coe_ne_upper_coe` — **assertion 1**: the two sectors are disjoint.
- `deningerPrimeGammaPointConjEquiv` (companion module) with
  `deningerPrimeGammaLower_ne_conj` — **assertion 2**: conjugation is the bijection `L → U`, and
  no lower parameter is fixed by it.
- `deningerPrimeGammaLowerCauchyTest_single`, `deningerPrimeGammaUpperCauchyTest_single`,
  `deningerPrimeGammaUpperCauchyTest_conjugateAtom` — **`(2)`–`(4)`, assertion 3**: the upper test
  of an atom is the Weil involution of its sharp test, so conjugating parameter and coefficient of
  a lower atom moves the Cauchy pole from `z` to `conj z`.
- `deningerPrimeGammaLowerCauchyTest_ne_conjugateUpperAtom` — **assertion 4**, the no-go: for a
  nonzero coefficient the two rational tests differ, evaluated at `a = z` where one side is zero by
  the totalized inverse convention and the other is not.

### Remaining

Nothing.  The card's "new insight" — that the missing positive metric needs analytic continuation
or new arithmetic geometry — is a statement about future construction, not a theorem of this card.
