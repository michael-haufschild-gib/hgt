# Gravitational horizon-edge relative law and charge pairing

- **ID:** `gravitational-horizon-edge-relative-law-and-charge-pairing`
- **Stage:** 1 — in progress
- **Type:** EXTERNAL PHYSICS INSTANTIATION / CONSTRAINT-RELATIVITY CHART
- **Status:** `[EXACT FIRST-VARIATION CHART ABOUT MATCHED CORNER] [EXTERNAL GRAVITY INPUT]`
  `[ANTI-DIAGONAL CHARGE DERIVATIVE PROVED HERE] [BRIDGE] [NOT WORMHOLE]`
  `[ARITHMETIC TRANSFER OPEN] [NO LEAN WRITTEN]`
- **External source:** V. Chandrasekaran and E. E. Flanagan,
  *Subregion algebras in classical and quantum gravity*, arXiv:2601.07915.
- **Paper anchor:**
  `../../2-fully-proven/constraint-relativity/banach-two-boundary-observer-radical-and-horizon-layer-duality.md`.
- **Statement:** At a continuous matched-embedding background, source paper's split-horizon
  extended phase space contains a relative translation coordinate. Its two-sided charge detects an
  anti-diagonal variation only when functional `(GHR.8)` is nonzero. On stationary data, displayed
  cross term and this first variation vanish at quoted perturbative order. This supplies a
  source-specific gravity chart for relative-law/observer pairing; it does not establish a
  split/dressing-independent gravitational invariant, arithmetic class, two-boundary wormhole
  interior, or wormhole length.

## 1. Exact external input

Chandrasekaran--Flanagan split a null horizon across a thin Cauchy region and introduce independent
translation edge modes `Upsilon_0^+` and `Upsilon_0^-`. Their corner symplectic form contains

\[
 \Omega_{\mathrm{cross}}
 =\frac1{8\pi}\int_{S_0}
 \delta\Upsilon_0^+\wedge\delta\Upsilon_0^-
 \mathcal L_\ell(\boldsymbol\mu\Theta).
 \tag{GHR.1}
\]

Their integrable half-sided null-translation charge is

\[
 \mathscr P_\alpha
 =-\frac1{8\pi}\int_{S_0^+}\alpha e^{\Gamma_0^+}
 \left[
 \mathcal L_\ell\boldsymbol\mu
 -(\Upsilon_0^+-\Upsilon_0^-)
 \mathcal L_\ell(\boldsymbol\mu\Theta)
 \right].
 \tag{GHR.2}
\]

These formulas are quoted inputs from equations `intro-corner-symplectic` and
`intro-A-P-def`/`nulltranslationgenerator` of source paper. They are derived to first order about
continuous matched embedding background

\[
 \Upsilon_0^+=\Upsilon_0^-,\qquad \Gamma_0^+=\Gamma_0^-,
 \tag{GHR.2a}
\]

with independent variations; terms quadratic in `Upsilon_0^+-Upsilon_0^-` are dropped. Source
paper also gives equivalent constrained expression

\[
 \mathscr P_\alpha
 =-\frac1{8\pi}\int_{S_0^-}
 \alpha e^{\Gamma_0^+}\mathcal L_\ell\boldsymbol\mu.
 \tag{GHR.2b}
\]

Paper also constructs crossed-product horizon-cut algebras and, after perturbative quantization,
Type `II_infinity` factors with half-sided translation dynamics. This card does not reprove those
gravity statements.

## 2. Relative tangent at a split corner

At fixed background, let

\[
 E_+=C^\infty(S_0),\qquad E_-=C^\infty(S_0),\qquad E=E_+\oplus E_-.
 \tag{GHR.3}
\]

Choose `Z_2`-symmetric tangent retraction and define relative coordinate explicit in source formula
for chosen split/dressing

\[
 A(u_+,u_-)=\frac{u_++u_-}{2},
 \qquad
 R(u_+,u_-)=u_+-u_-.
 \tag{GHR.4}
\]

Then

\[
 \ker A=\{(h,-h):h\in C^\infty(S_0)\},
 \qquad R(h,-h)=2h.
 \tag{GHR.5}
\]

Map `A` is chosen Constraint-Relativity chart, not construction claimed by source paper; relative
difference `R` is explicit in source formula for chosen split/dressing. In this chart diagonal coarse observation erases an anti-diagonal
relative tangent. This is elementary linear algebra, independent of gravity. Formula `(GHR.2)`
supplies nontrivial gravitational content: source paper's integrable two-sided charge is observer
of relative coordinate.

## 3. Exact anti-diagonal charge derivative

Put

\[
 F=\mathcal L_\ell\boldsymbol\mu=\boldsymbol\mu\Theta,
 \qquad
 W=\mathcal L_\ell(\boldsymbol\mu\Theta)=\mathcal L_\ell F.
 \tag{GHR.6a}
\]

At background satisfying `(GHR.2a)`, hold `alpha` and `Gamma_0^+` fixed and vary edge modes/cuts by

\[
 \delta_h\Upsilon_0^+=h,
 \qquad
 \delta_h\Upsilon_0^-=-h.
 \tag{GHR.6}
\]

Then

\[
 \boxed{
 d\mathscr P_\alpha(\delta_h)
 =\frac1{8\pi}\int_{S_0^+}
 \alpha e^{\Gamma_0^+}hW.}
 \tag{GHR.7}
\]

### Proof

Under `(GHR.6)`, `delta_h(Upsilon_0^+-Upsilon_0^-)=2h`. Moving future cut also gives
`delta_h(F|_(S_0^+))=hW`. Hence variation of bracket in `(GHR.2)` is

\[
 hW-2hW=-hW.
\]

Multiplying by overall `-1/(8 pi)` proves `(GHR.7)`. Equivalently, `(GHR.2b)` and
`delta_h S_0^-=-h` give same result. `[PROVED HERE FROM EXTERNAL FIRST-VARIATION FORMULA]`

Consequently the charge detects the anti-diagonal relative tangent precisely when the linear
functional

\[
 h\longmapsto\int_{S_0^+}\alpha e^{\Gamma_0^+}hW
 \tag{GHR.8}
\]

is nonzero. If `alpha` may range over all smooth test functions, every anti-diagonal `h` for which
`hW` is not identically zero is detected by some `alpha`.

## 4. Stationary boundary and exact no-go

If

\[
 \mathcal L_\ell(\boldsymbol\mu\Theta)=0
 \tag{GHR.9}
\]

on the cut, then displayed complementary-translation cross term `(GHR.1)` and anti-diagonal first
variation `(GHR.7)` vanish. In particular, source paper's stationary special case
`Theta=0=L_ell Theta` implies `(GHR.9)`. Other terms in full corner symplectic form need not vanish. Therefore this
perturbative charge channel does **not** universally detect relative displacement.

Strongest positive survivor:

> Null derivative `W=L_ell(boldsymbol mu Theta)` of expansion density is constitutive coefficient
> for this specific cross-corner channel, soldering relative edge displacement to a canonical
> two-sided observer.

The relative direction exists even when coefficient vanishes; physical observability is a separate
constitutive condition. Within this split/dressing chart, this is a structural gravity analogue of
arithmetic source-class/observer separation, not an invariant identification and not evidence that
coefficients are same object.

## 5. Constraint-Relativity interpretation

The chart has four different organs:

| Organ | Horizon realization |
|---|---|
| source split | complementary null regions around `S_0` |
| relative tangent law | anti-diagonal edge displacement `(h,-h)` |
| observer cotangent | charge differential `d P_alpha` |
| constitutive soldering | density `L_ell(boldsymbol mu Theta)` |

This chart explains why diagonal coarse observation loses relative law: relative coordinate is
killed by chosen averaging map, while integrability formula depends on both edge modes. Source
paper supplies no autonomous one-corner representation preserving all declared physical data. A
source-relative law can be geometrically real without being visible to a particular physical
state; visibility depends on constitutive background.

The exact lesson for RH is structural only. Route R similarly has a retained arithmetic relative
class and a physical observer whose coefficient can vanish or survive. What remains missing is a
source-derived arithmetic constitutive law selecting simultaneous nonerasure/axis avoidance. The
horizon formula does not provide that law.

## 6. Time geometry

The horizon-cut family carries half-sided modular/translation dynamics. Its natural group is affine:
boosts dilate translations. This is hyperbolic phase-scale geometry, not compact recurrence phase.
Quantum recurrence and Brown--Susskind-type interior growth therefore cannot be imported merely by
renaming modular time.

### Bold transfer question

Does a source possess two time sectors,

\[
 \text{elliptic recurrence phase}\quad\text{and}\quad
 \text{hyperbolic relative-cut scale},
 \tag{GHR.10}
\]

whose noncommuting joint transport creates observer curvature? A valid theory must construct both
actions and their comparison from same source. An analytic continuation between them, or an
analogy between prime phases and modular boosts, is not enough.

### Prediction

If such a joint action exists, a one-parameter clock should miss mixed two-curvature, whereas a
two-control experiment varying recurrence phase and cut scale should detect it. The invariant must
survive changes of edge frame and must reduce to `(GHR.7)` on gravitational horizon chart.

## 7. Wormhole boundary

Nothing above constructs:

1. two asymptotic boundaries;
2. an Einstein--Rosen bridge;
3. state-independent black-hole interior;
4. wormhole length or its Brown--Susskind growth law;
5. map from prime/arithmetic source to horizon edge algebra.

A finite thermofield standard-form model already reproduces two faces, a relative line, modular
phase, and bilocal observer without gravity; see paper anchor. Therefore these incidence features
cannot diagnose wormhole geometry. Genuine wormhole claim requires an additional gravitational
constraint, semiclassical reconstruction map, and quantitative length observable.

## 8. Falsifiers and next gates

1. **Physics falsifier:** construct autonomous one-corner algebraic representation of quoted charge
   without complementary cut, dressing, or constraint data while preserving integrability and
   constraints.
2. **Field falsifier:** construct a strictly one-face continuous observer that detects
   anti-diagonal kernel, contradicting exact locality no-go.
3. **Arithmetic falsifier:** show Route-R retained class admits source-natural absolute descent;
   relative-observer organ would then be unnecessary there.
4. **Transfer gate:** construct source-functorial map from arithmetic relative chart into a horizon
   or two-boundary gravitational chart, preserving pairings and time transport.
5. **Wormhole gate:** identify actual two-boundary algebra, relative edge variable, canonical
   observer, and geometric length; prove one nontrivial equality among them.
6. **Gravity-invariance gate:** prove relative pairing survives changes of horizon splitting,
   dressing/trivialization, and allowed Wald--Zoupas symplectic-potential choices after full gauge
   reduction. Failure makes it chart-dependent bookkeeping rather than gravitational invariant.

Until gates 4--6 close, label is `HORIZON BRIDGE`, not `WORMHOLE GEOMETRY`.

## Lean notes

- No Lean code was written or built.
- Sections 2--3 reduce to linear-map kernels and differentiation of an externally supplied
  functional. If later formalized, likely use finite-dimensional test-function truncations first.
- External general-relativity construction is not a current Lean target.
