# Kummer-ray smooth suspension resolution

- **ID:** `deninger-kummer-ray-smooth-suspension-resolution`
- **Stage:** 2-fully-proven
- **Type:** SOURCE NUCLEAR-SUSPENSION THEOREM
- **Labels:** `DAC_KUMMER_RAY_SMOOTH_SUSPENSION`,
  `DAC_KUMMER_RAY_AUGMENTATION_RESOLUTION`
- **Parent:** `deninger-poisson-hodge-polarization`
- **Statement:** smooth suspension converts every positive-rational
  Kummer orbit into an ordinary radial copy with strongly continuous
  flow; canonical nuclear augmentation has a strict two-term
  resolution whose quotient is exactly one scalar radial sector.

## 1. Orbitwise radialization

Let
\[
 V=
 (\overline{\mathbb Q}^{\times}/\mu_\infty)
 \otimes_{\mathbb Z}\mathbb Q
\]
and let \(f_a\in H_{\mathrm{Kum}}\) be the logarithmic Kummer vector.
For \(a\ne0\), put
\[
 r(a)=\|f_a\|>0.
\]
Positive rational powers satisfy
\[
 r(qa)=q\,r(a).                                                 \tag{1}
\]
Let
\[
 \mathbb P_+(V)
 =
 (V\setminus\{0\})/\mathbb Q_{>0}.
\]
On \((V\setminus\{0\})\times\mathbb R_{>0}\), use Deninger's deck
relation
\[
 (a,u)\sim(qa,u/q).                                             \tag{2}
\]

`[PROVED HERE] [DAC_KUMMER_RAY_SMOOTH_SUSPENSION]`

The map
\[
 [(a,u)]
 \longmapsto
 \left([a],x=u\,r(a)\right)                                    \tag{3}
\]
is a bijection
\[
 \left((V\setminus\{0\})\times\mathbb R_{>0}\right)/
 \mathbb Q_{>0}
 \cong
 \mathbb P_+(V)\times\mathbb R_{>0}.                            \tag{4}
\]
Under `(4)`, Deninger's flow is
\[
 \phi^t([a],x)=([a],e^tx).                                     \tag{5}
\]

### Proof

Equation `(1)` makes \(x\) invariant under `(2)`:
\[
 (u/q)r(qa)=ur(a).
\]
Thus `(3)` is well defined.  If two pairs have the same ray and
same \(x\), write \(b=qa\).  Equality of \(ur(a)\) and \(vr(b)\)
gives \(v=u/q\), so they are equivalent.  Surjectivity follows by
choosing any representative of a ray and taking \(u=x/r(a)\).
Formula `(5)` is immediate.

## 2. Nuclear smooth sections

Let \(H_-\) be Meyer's all-weight radial Schwartz space.  Define the
locally convex direct sum
\[
 \mathscr S_{\mathrm{ray}}
 =
 \bigoplus_{[a]\in\mathbb P_+(V)} H_- .                         \tag{6}
\]
Elements have finite ray support and a nuclear radial component.
The flow acts componentwise by Meyer's dilation.

Because each element has finite ray support and dilation is strongly
continuous on \(H_-\), `(5)` defines a strongly continuous
representation on `(6)`.  This is the smooth/nuclear survivor of
`DAC_BARE_KUMMER_MODE_ELL2_FLOW_NO_GO`: the suspension-height
variable is retained before completion.

Galois maps permute the ray index.  Positive-rational power maps act
trivially on the ray after deck descent and act through radial
dilation before descent.  Hence the construction is
Galois-, power-, and flow-natural.

## 3. Canonical unit augmentation

Define
\[
 \varepsilon_{\mathrm{ray}}:
 \mathscr S_{\mathrm{ray}}\longrightarrow H_-,
 \qquad
 (h_{[a]})\longmapsto\sum_{[a]}h_{[a]}.                        \tag{7}
\]
The sum is finite.

`[PROVED HERE] [DAC_KUMMER_RAY_AUGMENTATION_RESOLUTION]`

The sequence
\[
 0\longrightarrow
 K_{\mathrm{ray}}
 \longrightarrow
 \mathscr S_{\mathrm{ray}}
 \xrightarrow{\varepsilon_{\mathrm{ray}}}
 H_-
 \longrightarrow0,
 \qquad
 K_{\mathrm{ray}}=\ker\varepsilon_{\mathrm{ray}},              \tag{8}
\]
is strict exact in complete locally convex spaces after taking the
standard completed locally convex direct sum.  It is equivariant for
flow and Galois action.

Equivalently, the two-term complex
\[
 K_{\mathrm{ray}}
 \xrightarrow{\mathrm{incl}}
 \mathscr S_{\mathrm{ray}}                                     \tag{9}
\]
has only degree-zero cohomology, canonically \(H_-\).

### Proof

Continuity of `(7)` is the universal property of the locally convex
direct sum.  It is surjective: for any chosen ray \(r_0\), placing
\(h\) in the \(r_0\)-summand gives a continuous linear section.
Existence of a continuous section proves openness and strictness;
the quotient and its identification with \(H_-\) are independent of
the chosen section.  Equivariance follows because Galois maps only
permute a finite support and dilation commutes with finite summation.
The cohomology statement is exactly strict exactness of `(8)`.

The same construction with \(H_\cap\) in degree zero commutes with
Meyer's operator:
\[
 \varepsilon_{\mathrm{ray}}\!
 \left((Zh_{[a]})_{[a]}\right)
 =
 Z\!\left(\sum_{[a]}h_{[a]}\right).                            \tag{10}
\]
Thus the augmentation resolution can be attached before the
Poisson differential and produces one, not ray-many, copies of the
Poisson complex.

## 4. Exact Green frontier

The local Green energies from
`DAC_KUMMER_PHASE_POISSON_GREEN_BOUNDARY` define positive diagonal
forms before augmentation.  They do not descend by the naive Hilbert
quotient: `DAC_UNWEIGHTED_KUMMER_RAY_HILBERT_AUGMENTATION_NO_GO`
proves that the induced quotient seminorm would be zero.

The remaining theorem is therefore not cohomological ray collapse;
`(8)`--`(10)` already close that.  It is the construction of a
closed positive source Green form \(E_{\mathrm{tot}}\) on the nuclear
resolution `(9)` for which
\[
 \overline{K_{\mathrm{ray}}+\operatorname{im}d}^{\,E_{\mathrm{tot}}}
 \quad\text{is closed and has a faithful harmonic complement}. \tag{11}
\]
That harmonic complement must map flow-equivariantly and
cup-isometrically to \(M_\zeta\).  Exact cochains need not be null
vectors of the chain energy; Hodge theory removes them by orthogonal
projection.  Cross-ray terms or a source transverse current are
load-bearing in `(11)`.

## Hostile audit

- No Hilbert norm is placed on the infinite ray sum before
  augmentation.
- Strict exactness uses a section only to prove topology; no chosen
  ray enters the canonical quotient map or final cohomology.
- Strong continuity comes from radial smooth suspension, not the
  discontinuous bare permutation representation.
- Green closed-range, harmonic-complement, and faithfulness theorems
  are explicitly left open.
- No zeta zero, RH premise, CCM object, or numerical computation
  occurs.

## References

- Christopher Deninger, *Dynamical systems for arithmetic schemes*,
  suspension construction in §12:
  https://arxiv.org/abs/1807.06400.
- Frederic Paugam, *Spectral symmetries of zeta functions*, smooth
  suspension functor: https://arxiv.org/abs/0803.0199.
- `DAC_DENINGER_HILBERT_KUMMER_RADIAL_SUSPENSION`.

## Log

- 2026-07-27 — Identified the Kummer-mode suspension orbitwise with
  projective rays times the Hilbert--Kummer radius, proved strong
  continuity, and constructed the strict canonical augmentation
  resolution to one scalar radial Poisson sector.
