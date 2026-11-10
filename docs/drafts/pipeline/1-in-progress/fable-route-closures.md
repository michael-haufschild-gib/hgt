# Closure tasks in the consolidated review

- **ID:** fable-route-closures
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Source:** `docs/reports/review-1011/fable.md`, §12.3.
- **Goal:** Resolve all ten tasks in the explicitly named §12.3 with unconditional Lean proofs. §12.1 instead lists nine unfinished assemblies; the positivity ceiling belongs to both.

## Obligations

| Item | Required scope | Status |
|---|---|---|
| Calibrations of B13, Landing, DH | Exact scope of the three model theorems and joint rigidity | Euler-product Landing countermodel and Hamburger coefficient rigidity already formalized |
| Arithmetic constituents | Wiener obstruction and the remaining bounded class | Bounded case `0 ≤ x < 1/2` remains open |
| First rung by sizes | Exact barrier and positive boundary theorem | Existing barrier; no new producer established |
| Section rings of the square | Tower product formula and planar ideal equality | Planar equality already formalized; tower scope unresolved |
| Covers and averaged families | Fixed-part and character-index laws, with rightmost-zero exception | Exact scope unresolved |
| S3 transfer | Exact implication and status of the transfer itself | Source proves transfer ⇒ (`Θ < 1` ⇒ RH); transfer remains unproved |
| Window and theta stages | Verification law and obstruction to unconditional induction | Exact scope unresolved |
| Scheduled sums and source completions | Exact criteria for all named routes | No advancing-history estimate established |
| Positivity census | Decide 70% at every bandwidth | 70% excluded at `4/3`; all-bandwidth question open |
| Short mean values as detectors | Relocation invariance and positive density/census scope | Fixed mean spectra invariant; growing test lengths not covered by the located theorem |

## Existing scope statements

- `ArithmeticPositiveDuality/AnApproachingIntegerNormEulerProduct.lean`,
  `exists_integer_norm_euler_product_not_landingLaw`: natural norms and coefficients,
  linear counting, continuation across the critical line, and failure of Landing.
- `HTGeometry/HamburgerFunctionalEquation.lean`,
  `coeff_eq_of_completed_functional_equation`: absolute Dirichlet convergence,
  the two completed boundary identities and strip decay force constant coefficients.
  The decay and polar-part conditions belong to its scope; the functional equation alone
  is not its full hypothesis.
- `AbsoluteGeometryOfSpecZ/BezoutIsAnEqualityOnThePlanarSquare.lean`,
  `planarValues_eq_prod`: values of sections vanishing on finitely many graphs equal
  the product of their contact ideals.
- `ArithmeticPositiveDuality/FiniteZeroRelocationPreservesTheMeanSpectrum.lean`,
  `relocatedZeta_meanSquare`, `relocatedZeta_fourierMean_log`,
  `relocatedZeta_fourierMean_off_spectrum`: finite rational relocation preserves the
  Carlson square mean and every fixed Fourier mean in `1/2 < σ < 1`.

## Positivity question

**Proved:** positivity alone does not certify 70% at bandwidth `4/3`.
A periodic sinc majorant plus a Fejér kernel produces one hundred nonnegative
spike coefficients, the first exceeding `61/200`. Triangular smoothing preserves
pair-density positivity and exact sub-threshold data. The weighted integral exceeds
`7/45`, hence the Frobenius value exceeds `13/10`.

Complete paper proof and Lean result:
[positivity-seventy-percent-four-thirds](../3-formalized/positivity-seventy-percent-four-thirds.md).
Both modules pass direct Lean checking and are wired into their umbrella.

The all-bandwidth obstruction remains open. A single counterexample at `4/3`
does not settle it; any fixed integrable perturbation of the constant form factor
has Frobenius value tending to one as bandwidth tends to infinity.

A stronger candidate is a positive off-diagonal pair measure with an atom of
mass greater than `3/10` at zero and the prescribed sub-threshold Fourier data.
The identity `frobenius(F,λ)=1+∫sinc²(πλx) dp(x)` would then exclude 70% at
every bandwidth. Positivity of its dual form factor is an additional obligation;
positive quadrature alone does not discharge it. To stay in the continuous,
integrable-perturbation class of the finite-spike theorem, the atom would also
need regularization preserving the exact sub-threshold data. No such measure
or regularization is proved here.

## Completion gates

Exact statements, paper proofs, direct `lake --old env lean` checks,
umbrella imports, and positive survivors for every retired route.
No numerical optimization or assumed analytic inputs.
