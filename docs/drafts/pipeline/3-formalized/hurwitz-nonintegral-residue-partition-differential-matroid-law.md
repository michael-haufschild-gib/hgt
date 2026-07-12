# Hurwitz nonintegral residue partition differential-matroid law

- **ID:** `hurwitz-nonintegral-residue-partition-differential-matroid-law`
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Scientific status:** `[PROVED IN LEAN] [NOVELTY AUDIT PASSED] [NEW SCIENTIFIC KNOWLEDGE]`

## Main law

Let `s : I → ℂ` be any finite family of nonintegral exponents.  Then

\[
  \bigl(a\mapsto\widetilde\zeta(s_i,a)\bigr)_{i\in I}
  \text{ is differentially algebraically independent over }\mathbb C(a)
  \quad\Longleftrightarrow\quad
  i\longmapsto e^{-2\pi i s_i}\text{ is injective}.
\]

Since equality of the monodromy values is equivalent to `s_i-s_j∈ℤ`, the differential matroid is
exactly the partition matroid induced by the value map to `ℂ/ℤ`.

The intrinsic formal theorem is `continued_hurwitz_intrinsic_residue_differentialMatroid_law` in
`formal/GaloisForLFunctions/Hurwitz/IntegerTranslationDifferentialMatroid.lean`.

On `Re(s_i)>1`, `hurwitz_intrinsic_residue_differentialMatroid_law` proves the identical
classification for the ordinary convergent Hurwitz series.  The closed theorem
`hurwitz_threeHalves_fourThirds_differentialIndependent` gives an assumption-free classical
instance at exponents `3/2` and `4/3`.

The encoded class-and-offset form
`continued_hurwitz_integerTranslation_differentialMatroid_law_of_integerResidueSeparated` is an
immediate structured version for arbitrary finite selections from named residue classes.

## Stronger independence surface

The classification rests on the following formalized chain.

1. `additiveGrid_zero_of_robust_increment_span`: a degree-`D` polynomial vanishing on an affine
   sum of orbit columns is zero whenever deletion of any `D` columns leaves the consecutive
   increments spanning the value space.
2. `hurwitz_survivingIncrement_span_eq_top`: for the joint `N`-jet Hurwitz rectangle,
   `N+D+1` independently looped branch points satisfy that robust spanning condition when the
   monodromy values are pairwise distinct and nontrivial.
3. `continued_joint_hurwitz_ladder_independence_of_integerResidueSeparated`: every finite
   analytically continued Hurwitz ladder is algebraically independent under exactly the
   nonintegral, pairwise-incongruent exponent condition.
4. `continued_joint_hzeta_hypertranscendental_in_shift_of_integerResidueSeparated`: the same
   condition gives joint independence of all finite derivative rectangles.
5. `continued_joint_hzeta_upperEnd_differentialIndependent_finite_of_integerResidueSeparated`:
   the result holds in the concrete upper-end meromorphic differential field over `ℂ(a)`.

## Proof mechanism

A single common multiplicative orbit can retain higher monomial resonances.  The continued Hurwitz
family supplies arbitrarily many independently looped branch points.  For a relation of degree
`D`, a consecutive translation difference lowers total degree and consumes one branch column.
Induction therefore tolerates deletion of `D` columns.  Among the remaining columns, ordinary
Vandermonde separation of the distinct monodromy values isolates each exponent label, and any
`N+1` distinct branch points span its `N`-jet block.  The surviving increments span the complete
joint value space, forcing translation invariance in every direction and hence constancy; grid
vanishing then forces zero.

The converse is exact: two exponents in the same integer-translation class are connected by the
continued derivative ladder, producing differential dependence.

## Carrier boundary

The law is proved both for the Taylor-regularized analytic continuation `continuedHzeta` at every
nonintegral complex exponent and, by formal equality on `Re(s)>1`, for the ordinary convergent
Hurwitz series.  The nonintegral condition excludes the exceptional integer class, where
Bernoulli-polynomial and pole phenomena form a separate positive classification problem.

## Verification

- Exact module builds pass for the ladder, hypertranscendence, upper-end, and matroid modules.
- `scripts/formal_tools.py lint` passes.
- The axiom audit reports only `propext`, `Classical.choice`, and `Quot.sound`.
- There are no `sorry`, `admit`, project `axiom`, `opaque`, or `unsafe` declarations in the proof
  chain.

## RH interface

`formal/GaloisForLFunctions/RHTower/XiZeroHurwitzDifferentialIndependence.lean` now consumes the
intrinsic law.  The existing theorem `xi_divisor_support_re_mem_open_unit` automatically discharges
both arithmetic conditions: every Xi zero is nonintegral, and two distinct open-critical-strip
points cannot differ by an integer.  Consequently
`xi_zero_hurwitz_differentialIndependent` proves unconditionally that every finite injective family
of actual Xi-divisor support values indexes a jointly differentially independent continued-Hurwitz
family over `ℂ(a)`.

This is a direct Xi-divisor-to-Hurwitz-rigidity bridge, but not a zero-location theorem.  It turns a
finite set of distinct zeros into a family with no algebraic differential relation; it does not
deduce the critical-line condition.  `RHTower/HurwitzShiftedBridge.lean` still varies the spectral
variable with the shift fixed, so its frequency-independence hypotheses are orthogonal and are not
discharged by this law.  The remaining positive RH construction problem is a typed mechanism that
turns scalar zero-location data into a functional relation in the Hurwitz shift variable.  If such
a relation uses pairwise incongruent nonintegral exponents, the present theorem forces it to be
trivial; thus any successful nontrivial encoding must expose an integer-resonant collision or add
structure outside this differential-polynomial carrier.

## Literature audit

The nearest established results occupy different variables or exceptional strata.

1. Amou--Katsurada, *Differential transcendence of a class of generalized Dirichlet series*,
   Illinois J. Math. 45 (2001), 939--948, DOI
   [10.1215/ijm/1258138161](https://doi.org/10.1215/ijm/1258138161), differentiates the formal
   Dirichlet series with respect to the spectral variable `s`, with the Hurwitz parameter fixed.
   It does not classify differential relations in the shift variable `a`, joint families of
   complex exponents, or the exact `ℂ/ℤ` dependence locus.
2. Lagarias--Li, *The Lerch zeta function III. Polylogarithms and special values*,
   [arXiv:1506.06161](https://arxiv.org/abs/1506.06161), computes multivariable continuation and
   monodromy and obtains finite-order ODEs on positive-integer specializations.  It supplies the
   closest monodromy parent but no algebraic-differential independence theorem for arbitrary
   nonintegral Hurwitz exponents.
3. Espinosa--Moll, *A generalized polygamma function*,
   [arXiv:math/0305079](https://arxiv.org/abs/math/0305079), constructs and studies complex-order
   polygamma functions through Hurwitz zeta.  It does not determine their joint differential
   algebra or a residue-class matroid.
4. Bouillot, *The algebra of Hurwitz multizeta functions*, C. R. Math. 352 (2014), 865--869,
   DOI [10.1016/j.crma.2014.09.006](https://doi.org/10.1016/j.crma.2014.09.006), describes a
   polynomial algebra for positive-integer Hurwitz multi-indices.  This is algebraic rather than
   differential and lies in the integer class excluded by the present theorem, where the derivative
   ladder itself creates dependence.
5. Laurinčikas--Matsumoto, *The joint universality and the functional independence for Lerch
   zeta-functions*, Nagoya Math. J. 157 (2000), 211--227, DOI
   [10.1017/S002776300000725X](https://doi.org/10.1017/S002776300000725X), varies the spectral
   variable with the Lerch parameters fixed.  Its universality hypotheses and conclusion do not
   imply the shift-variable classification here.

Exact-phrase and theorem-surface searches found no prior theorem asserting either direction of the
present equivalence, no prior complete differential-matroid classification for complex-order
Hurwitz functions, and no prior robust additive-grid saturation theorem in the form used here.

## Novelty and significance verdict

The main law is not a repackaging of individual hypertranscendence.  It identifies every finite
dependent set, proves both sufficiency and necessity, extends through analytic continuation, and
has a direct unconditional Xi-divisor application.  The proof introduces a degree-sensitive robust
translation-saturation principle that is reusable beyond Hurwitz functions.

- **Novelty:** 93/100.
- **Structural significance in special-function differential algebra:** 90/100.
- **Direct present RH leverage:** 55/100; the zero-indexed rigidity theorem is unconditional, while
  zero location remains a separate value-coupling problem.
- **Publication verdict:** one-main-law paper justified.  The additive-grid theorem is the proof
  engine and the Xi-zero theorem is a corollary, not competing headline results.
