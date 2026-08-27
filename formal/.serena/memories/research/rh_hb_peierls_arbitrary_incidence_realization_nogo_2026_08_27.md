# HB Peierls arbitrary-incidence realization no-go (2026-08-27)

Formal module: `formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMSecondHarmonicPeierlsArbitraryIncidenceRealizationNoGo.lean`.

Constructed fixed two-dimensional complex carrier `ℂ×ℂ`, coordinate bilinear
pairing, componentwise symmetric quadratic residual (with cyclic cubic tensor),
and target-scaled standard symplectic propagator. Fixed branches `(2,0)` and
`(0,1)` have quadratic residuals forming a unit symplectic cell.

For every `T:ℂ`, Peierls pairing is skew, polarized incidence is exactly `T`,
and phase-normalized cubic cut is exactly `2T`.

Instantiating `T` with each BM source-scaled boundary concomitant satisfies the
conditional HB incidence premise copywise and manufactures the complete BM wall
receiver with retarded maps `Delta_T` and advanced maps zero. Thus symmetry,
cyclicity, skewness, and abstract incidence are producer-nonselective.

Positive survivor: one fixed propagator realizes all BM Xi copies iff the complete
BM boundary-concomitant target is constant across the Xi divisor. Remaining HB
gate is literal divisor-independent/global Einstein–Teukolsky source semantics.

Verification: direct Lean, targeted build, axiom audit passed.
Axioms only `propext`, `Classical.choice`, `Quot.sound`.

Card: `docs/drafts/pipeline/3-formalized/hb-peierls-arbitrary-incidence-realization-no-go.md`.