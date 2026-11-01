# Three orthogonal RH approaches: source and obstruction audit

- **ID:** ARGON-3
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Source:** `docs/reports/review-3110/argon.md`, §§2.2–2.4.
- **Goal:** Find and formalize substantive unconditional consequences of the three proposed approaches; prove precise obstructions where mechanisms fail. A missing proof does not establish impossibility of a paradigm.

## A. Gauss–Mayer and loop-Eisenstein scattering

`TheLoopEisensteinReflectionCarriesTheHodgeDefect.lean` defines `reflectionPoles` as denominator zeros, not analytic poles. Its RH equivalence is proved. Numerator noncancellation and the bridge to the Mayer operator require separate verification.

`SelbergScatteringNativeResidual.lean` already proves that every actual Xi scattering energy has strictly positive optimal residual in the original modular self-adjoint domain, including critical zeros. Reusing self-adjoint spectral exclusion would therefore reject the desired zeros too. This existing obstruction is not a new result.

**Open target:** Identify a source-specific resonance exclusion mechanism surviving this domain obstruction.

## B. Böttcher and arithmetic period rigidity

`AlgebraicVerticalFirstJets.lean` detects all polynomial partial derivatives only at algebraic torus points with algebraic coefficients. Applying it at a zeta zero requires an independently proved arithmetic realization. The proposed nonlinear equation and realization have not been specified.

**Open target:** Construct an exact arithmetic realization or prove an obstruction for a precise proposed class. Audit existing Böttcher monodromy and hypertranscendence results before formulating that class.

## C. Two-place Krein reciprocity

`TheGluingFormulaAtEveryPlace.lean` gives the full index identity. Its state is defined on rational affine transformations: the successor term uses the p-adic norm, but `ratCorr` remains a global, archimedean-continuous dilation correlation. Compact Fourier support of local indicators does not establish compact support or even p-adic continuity of this correlation.

**Conjecture to audit:** A nonconstant archimedean-continuous rational dilation correlation cannot extend continuously to the p-adic slope group. If proved, determine the exact surviving two-place domain and source information needed there.

## Gates

- [x] Scope: three approaches, confirmed by user.
- [ ] Dependency-closed paper proofs of new results.
- [ ] Lean formalization, direct file checks, transitive axiom audits, umbrella imports.
- [ ] Positive survivor audited before any route retirement.
