# Logarithmic-differential defect lattice of an exponential tuple

- **ID:** schanuel-logarithmic-differential-defect-lattice
- **Stage:** 3-formalized
- **Type:** THEOREM (paper)
- **Source:** failed Ax-compatible deformation conjecture; Ax/Kirby exponential differential equation
- **Statement:** Every finite `Q`-linearly independent complex exponential tuple has a canonically injective integral defect lattice in the Kahler differentials of its value field.

## Goal

Identify exactly what survives when the numerical exponential graph is passed to the function field
of its algebraic locus.  The exponential differential equation does not survive, but its failure is
not arbitrary: the defects of independent exponent directions remain integrally independent.  This
isolates a coefficient-field jump, from `Z`-independence to independence over the value field, as
the missing step in differential attacks on Schanuel.

## Gates

- [x] 0 -> 1  in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [x] 1 -> 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [x] 2 -> 3  formalized: unconditional Lean proof, wired into project umbrellas
- [ ] 3 -> 4  publication-ready: external novelty audit and comparison with exponential derivations pending

## Statement

Let `x_1,...,x_n` be `Q`-linearly independent complex numbers, put `y_i = exp(x_i)`, and set

\[
  K=\overline{\mathbb Q}(x_1,\ldots,x_n,y_1,\ldots,y_n)\subset\mathbb C.
\]

In `Omega = Omega_{K/Qbar}`, define

\[
  \epsilon_i=d\log y_i-dx_i=\frac{dy_i}{y_i}-dx_i.
\]

Then the homomorphism

\[
  \epsilon:\mathbb Z^n\longrightarrow\Omega,
  \qquad m\longmapsto\sum_i m_i\epsilon_i
\]

is injective.

## Proof

Assume `epsilon(m)=0`.  Put

\[
  s=\sum_i m_i x_i\in K,
  \qquad w=\prod_i y_i^{m_i}=\exp(s)\in K^\times.
\]

Then `ds = dw/w` in `Omega`.

We first prove a stronger field-theoretic lemma.  Let `C -> L` be any characteristic-zero field
extension, let `w != 0`, and suppose `dw = w ds` in `Omega[L/C]`.  Then both `s` and `w` are
algebraic over `C`.

Assume instead that `s` is transcendental.  Extend `{s}` to a transcendence basis `B` of `L/C`,
put `F=C(B)`, and prescribe the coordinate derivation `partial` on `F` by `partial(s)=1` and
`partial(b)=0` for `b != s`.  Since `L/F` is algebraic and characteristic is zero, `partial`
extends to `L`.  Evaluating `dw=w ds` gives `partial(w)=w`.

Let `p in F[X]` be the monic minimal polynomial of `w`, of degree `n>0`, and differentiate
`p(w)=0`.  If `partial_coeff(p)` denotes coefficientwise differentiation, then

\[
  q=\partial_{\mathrm{coeff}}(p)+Xp'
\]

also vanishes at `w`.  Its leading coefficient is `n`, so `q-np` has degree below `n`; minimality
forces `q=np`.  The constant coefficient `a_0` is nonzero because `w != 0`, and comparison of
constant coefficients gives `partial(a_0)=n a_0`.  No nonzero rational function in `C(B)` can be
an eigenvector of the free-coordinate derivation with nonzero constant eigenvalue: writing it as a
reduced quotient of polynomials in the coordinate `s`, comparison of `s`-degrees after
differentiation gives a strict degree drop.  Contradiction.  Hence `s` is algebraic over `C`.
Then `ds=0`, so `dw=0`, and the kernel theorem for the universal derivation makes `w` algebraic
over `C` as well.

Returning to the tuple, rational linear independence gives `s != 0` whenever `m != 0`.
Hermite--Lindemann then makes `exp(s)=w` transcendental over `Q`, contradicting `w in Qbar`.
Therefore `m=0`, proving injectivity. **[PROVED HERE]**

## Consequences

1. For `n=2` and `trdeg_Q K=1`, `Omega` is one-dimensional over `K` but contains two
   `Q`-linearly independent defect forms. Their quotient is a canonical defect slope. The later
   theorem `schanuel-defects-algebraic-coefficient-independent.md` strengthens this to
   `rho notin Qbar`.
2. The theorem cannot imply Schanuel by dimension counting: `Q`-linear independence inside a
   `K`-vector space gives no lower bound on `dim_K Omega`.
3. Algebraic-coefficient independence is now proved. Upgrading it further to `K`-linear
   independence would imply Schanuel immediately, since `dim_K Omega = trdeg_Q K`. On the slice
   where all `y_i` are algebraic, this last upgrade is exactly algebraic independence of logarithms
   of algebraic numbers.

## Failed conjecture and no-go closure

- **Failed conjecture:** a numerical counterexample's Zariski locus admits a nonconstant arc through
  the point satisfying `dy_i/y_i=dx_i`, so Ax--Schanuel applies.
- **Exact killing mechanism:** a numerical algebraic relation supplies no invariant tangent
  direction.  On any algebraic function field, `ds=dw/w` forces both `s` and `w` constant by the
  pole-order mismatch above.  Thus a nonconstant algebraic Ax-compatible lift is impossible already
  in one exponential direction.
- **Strongest positive survivor:** the defect map is injective over `Z`.
- **New insight:** every differential route reaches the same typed wall: available arithmetic gives
  constant-coefficient independence, while transcendence degree requires value-field-coefficient
  independence.
- **Status:** **[LEAN-PROVED]**.  Formal declarations:
  `ne_self_of_isAlgebraic_freeCoordinateDerivation`,
  `isAlgebraic_left_of_kaehlerD_eq_smul`,
  `algebraic_of_kaehlerD_eq_smul`, `schanuelDefect_integer_relation`, and
  `schanuelDefect_integer_relation_in_intermediateField`.  Kernel audit uses only `propext`,
  `Classical.choice`, and `Quot.sound`; no project axiom, `sorry`, `admit`, `opaque`, or `unsafe`.

## Literature audit

- Ax proves the differential Schanuel inequality when the exponential differential equation is
  present.
- Kirby's exponential-derivation and exponential-algebraic-closure frameworks study that equation
  and its induced pregeometry.
- Targeted searches found no source stating the injective numerical defect-lattice formulation
  above.  External novelty remains **unconfirmed**; no priority claim is made.

## Log

- 2026-08-14 -- Ax-compatible lift conjecture killed; injective defect lattice extracted and proved.
- 2026-08-14 -- Replaced divisor argument by a stronger free-coordinate/minimal-polynomial proof;
  formalized ambient and intermediate-field versions in Lean 4 and wired both umbrellas.
