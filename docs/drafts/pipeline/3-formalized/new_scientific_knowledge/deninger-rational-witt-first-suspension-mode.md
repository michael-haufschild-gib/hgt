# Rational-Witt first suspension-mode transgression

- **ID:** `deninger-rational-witt-first-suspension-mode`
- **Stage:** 3-formalized
- **Type:** POSITIVE SURVIVOR THEOREM
- **Label:** `DAC_RATIONAL_WITT_FIRST_SUSPENSION_MODE`
- **Parents:** `deninger-rational-witt-finite-transverse-visibility`,
  `deninger-rational-witt-packet-restriction-double-obstruction`
- **Scientific status:** `[NEW ARITHMETIC CONJUNCTION; HILBERT-TENSOR PARENT STANDARD]`

## Variance correction

The finite rational-Witt evaluation theorem produces functions on the profinite quotient packet
\[
 B_p=
 \operatorname{Aut}(\overline{\mathbb F}_p^\times)/
 \overline{\langle\operatorname{Frob}_p\rangle}.
 \tag{1}
\]
This is not yet the positive transverse middle sector.  The literal arithmetic prime fibre already
constructed in Route L is the mapping torus
\[
 X_p\simeq B_p\times S_p,\qquad
 S_p=\mathbb R/\log p\,\mathbb Z.                                \tag{2}
\]
Horizontal functions on \(B_p\) are precisely the sector which the Arakelov residue complex must
remove.  Sending those same functions directly to the middle Green target confuses degree-two
residue data with degree-one Cauchy data.

## Canonical suspension lift

Let
\[
 e_{p,1}(t)=\exp\!\left({2\pi i t\over\log p}\right)              \tag{3}
\]
be the first normalized Fourier character of \(S_p\).  With normalized Haar measures define
\[
 \Sigma_{p,1}:L^2(B_p,\mathbb C)\longrightarrow
 L^2(B_p\times S_p,\mathbb C),\qquad
 (\Sigma_{p,1}f)(b,t)=f(b)e_{p,1}(t).                            \tag{4}
\]

`[PROVED HERE] [DAC_RATIONAL_WITT_FIRST_SUSPENSION_MODE]`

The map `(4)` is a complex-linear isometry.  Its image lies in the first circle-oscillatory
sector, is orthogonal to every circle-horizontal function, and the Tate-normalized transverse
generator
\[
 \widehat A_p=(\log p)|D_{S_p}|
 \tag{5}
\]
acts on it with the prime-independent eigenvalue \(2\pi\).  Consequently the unsmoothed local
Green energy is
\[
 G_{p,0}(\Sigma_{p,1}f,\Sigma_{p,1}f)
 =2\pi\|f\|_2^2,                                                 \tag{6}
\]
strictly positive for \(f\ne0\).

### Proof

Normalized Haar measure on \(S_p\) gives \(\|e_{p,1}\|_2=1\) and
\(\int_{S_p}e_{p,1}=0\).  Fubini therefore gives
\[
 \|\Sigma_{p,1}f\|_2^2
 =\int_{B_p}|f(b)|^2\,db\int_{S_p}|e_{p,1}(t)|^2\,dt
 =\|f\|_2^2,
\]
and the same separated-product calculation gives orthogonality to the zero circle mode.
The ordinary circle frequency is \(2\pi/\log p\); multiplication by \(\log p\) in `(5)` gives
\(2\pi\), proving `(6)`.

## Rational-Witt admission

For every finite Frobenius stage \(s\), every
\[
 F:B_{p,s}\to\mathbb C                                         \tag{7}
\]
has an arithmetic-Frobenius-fixed witness
\[
 w\in
 \mathbb C[\mu_{n_s}]
 \hookrightarrow
 \mathbb C[\overline{\mathbb F}_p^\times]
 \cong
 \mathbb C\otimes W_{\rm rat}(\overline{\mathbb F}_p)
 \tag{8}
\]
whose packet evaluation is the pullback of \(F\).  Applying `(4)` gives the literal prime-fibre
mode
\[
 (b,t)\longmapsto F(r_{p,s}(b))e_{p,1}(t).                       \tag{9}
\]
If \(F\ne0\), surjectivity of \(r_{p,s}\) and isometry of `(4)` make `(9)` nonzero with positive
energy `(6)`.  Thus every finite rational-Witt packet function enters the correct local
circle-oscillatory Cauchy sector, rather than being mislabelled as a horizontal middle vector.

## Exact scope

The theorem repairs local variance and supplies a canonical source-native transgression.  It does
not solve the global Bessel obstruction: a raw global Teichmüller coordinate still produces
unit-norm first modes at cofinitely many primes.  The relevant coefficient must decide which
finite-support/rapid/graph combinations of `(9)` form its global degree-one domain.

The next hard theorem is therefore no longer “find a nonzero packet mode.”  It is:

`[CONJECTURE] [DAC_SUSPENSION_MODE_GRAPH_DOMAIN_DESCENT]`

Prove that the derived relevant coefficient's degree-one Cauchy restriction factors locally
through `(4)`, contains every finite rational-Witt stage `(9)`, and globally lands in the
Tate-graph restricted sum with kernel exactly the closed middle boundaries.

## Theatre audit

- `(4)` uses the literal mapping-torus circle and its first character; no divisor label or
  arbitrary damping is introduced.
- Isometry prevents a hidden local collapse.
- The theorem explicitly leaves the global cofinite norm-floor obstruction open.
- A horizontal Wrat function is not itself declared middle cohomology.  The suspension character
  supplies the missing transverse variance.

## Novelty audit

Separated-product \(L^2\) isometry and Fourier orthogonality are standard.  Corpus and primary
searches found no use of the canonical first Deninger suspension character to transgress the full
finite rational-Witt packet algebra into a prime-independent Tate-energy sector.  Claimed new
content is this arithmetic identification and variance repair.

## Gates

- [x] exact paper theorem and proof
- [x] unconditional Lean formalization
- [x] link every finite rational-Witt witness to the first suspension mode
- [ ] source graph-domain descent
- [ ] global Bessel and boundary-kernel theorem

## Lean certificate

`formal/GaloisForLFunctions/RHTower/DeningerRationalWittFirstSuspensionMode.lean`, imported by
`GaloisForLFunctions.RHTower`, formalizes:

- `deningerPrimeSuspensionFirstMode`, `norm_deningerPrimeSuspensionFirstMode`, and
  `deningerPrimeSuspensionFirstMode_injective`: the isometric lift `(4)`;
- `inner_deningerPrimeSuspensionFirstMode_horizontal`: exact orthogonality to the zero circle mode;
- `deningerPrimeSuspensionFirstModeGreenEnergy_eq` and `_pos`: `(6)` and strict positivity;
- `deningerPrimeComplexifiedRationalWitt_exists_nonzero_firstSuspensionMode`: every nonzero finite
  packet function has an arithmetic-Frobenius-fixed Wrat witness, a nonzero first suspension mode,
  and positive Tate energy.

Direct `lake env lean`, targeted module build, and scratch `#print axioms` pass.  The declarations
use only `propext`, `Classical.choice`, and `Quot.sound`.

## References

- Christopher Deninger, *Dynamical systems for arithmetic schemes*,
  https://arxiv.org/abs/1807.06400.
- `DeningerPrimeFibreComparison.lean`
- `DeningerRationalWittFiniteEvaluationBridge.lean`
- `L2SeparatedProductDensity.lean`
- `DeningerTateGraphGreenPrimeSector.lean`

## Log

- 2026-08-01 — corrected finite Wrat modes from horizontal residue variance to first
  mapping-torus suspension variance and isolated the remaining global graph-domain theorem.
