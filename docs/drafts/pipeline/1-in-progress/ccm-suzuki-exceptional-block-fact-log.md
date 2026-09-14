# CCM/Suzuki exceptional-block fact log

Scope: Codex `/root` research only. Facts and no-gos; no chronology or status diary.

## Facts

- For every positive aperture, real-parameter movable Suzuki raw deficiencies have dense complex
  linear span in Suzuki energy space
  (`suzukiTaRawDeficiencySpan_closure_eq_top`).
- Literal CCM two-pole constraint is exactly orthogonality to deficiencies at parameters
  `-1/2` and `1/2` (`isPolarConstrained_suzukiTaToFormCLM_iff`).
- Orthogonally pole-corrected movable Suzuki CCM responses remain total in constrained CCM form
  sector (`suzukiTaPolarOrthogonalMovableCCMResponseSpan_closure_eq_top`).
- Restricted-Weil form has finite-dimensional reducing exceptional block, coercive exterior,
  and exactly zero mixed form (`CCMRestrictedWeilReducingBlockCertificate`).
- Projected actual movable Suzuki responses span constrained-visible exceptional range densely;
  finite dimensionality upgrades closure to exact algebraic span
  (`suzukiTaMovableReducingExceptionalSpan_eq_top`).
- A finite linearly independent subset of projected actual movable responses spans constrained-visible
  exceptional range (`exists_finite_suzukiTaMovableReducingExceptional_basis`).
- RH is equivalent to nonnegativity of restricted-Weil quadratic on constrained-visible finite
  exceptional range at every positive aperture
  (`riemannHypothesis_iff_movableReducingExceptional_nonnegative`).
- Restricted-Weil ground energy is antitone and continuous in aperture, and is strictly positive at
  sufficiently small aperture (`ccmRestrictedWeilGroundEnergy_antitone`,
  `continuous_ccmRestrictedWeilGroundEnergy`, `exists_suzukiSmallAperture_ccmGroundEnergy_pos`).
- If RH fails, first zero of unrestricted ground energy is attained by a nonzero completion-boundary
  vector not represented by any strict smooth interior source
  (`riemannHypothesis_or_ccmFirstContactBoundaryRoughness`).
- Projected raw movable Suzuki responses span every full reducing exceptional block exactly, with a
  finite linearly independent subfamily
  (`suzukiTaMovableFullReducingExceptionalSpan_eq_top`,
  `exists_finite_suzukiTaMovableFullReducingExceptional_basis`).
- At any nonnegative aperture, every zero-energy vector lies entirely in every reducing exceptional
  block (`mem_reducingExceptional_of_nonnegative_of_null`).
- Hence RH failure has an exact finite actual movable-source first-contact realization despite its
  exclusion from smooth interior core
  (`riemannHypothesis_or_firstContactFiniteMovableExceptionalCoordinates`).

## No-gos

- Per-height scalar Suzuki/Schur contraction does not control cross-height terms, so it cannot prove
  quadratic nonnegativity on finite linear combinations of movable sources.
- Totality transfers coverage, not metric contraction; density alone cannot prove restricted-Weil
  positivity.
- Ordinary Hilbert Gram positivity of linearly independent source vectors is irrelevant to remaining
  sign problem: restricted-Weil quadratic is induced by `I - K`, not ambient inner product.
- Generic finite-negative-index reduction localizes all possible negativity but does not determine
  arithmetic sign of exceptional Hermitian matrix.
- Smooth-core aperture perturbation cannot exclude first contact: under RH failure, Lean forces the
  first null state to live outside every strict smooth interior source representation.

## Current exact frontier

- For each positive aperture, determine sign of restricted-Weil Hermitian matrix on one finite basis
  of projected actual movable Suzuki responses. Any successful argument must use arithmetic
  prime--polar cancellation or a structure forcing spectrum of constrained-visible compression below
  `1`; abstract Hilbert-space Gram positivity cannot supply it.
- At hypothetical first contact, identify arithmetic orientation of finite movable-source null
  relation without replacing spectral projection by regionwise absolute-value bounds. Current finite
  basis parameters and coefficients are existential; coefficient-faithful boundary transport is the
  missing source-side law.
