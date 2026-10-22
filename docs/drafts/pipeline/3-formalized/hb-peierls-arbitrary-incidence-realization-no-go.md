# HB Peierls arbitrary-incidence realization no-go

- **ID:** HB-PAIR
- **Stage:** 3-formalized
- **Type:** PRODUCER NO-GO WITH MINIMAL POSITIVE REALIZATION
- **Parent:** HB-PRO / HB-PEIERLS-LANDING
- **Frontier-map policy:** read only

## Frozen conjecture

Construct one explicit two-dimensional complex Peierls model with:

- field and residual spaces `X=Y=ℂ×ℂ`;
- complex-bilinear dot pairing;
- componentwise symmetric quadratic residual `B` whose induced cubic tensor is
  cyclic;
- scaled standard symplectic propagator `Delta_T` for arbitrary `T:ℂ`;
- fixed branches `p=(2,0)` and `m=(0,1)`.

Prove unconditionally for every target `T`:

1. `B` is symmetric;
2. the pairing/B cubic tensor is cyclic;
3. the induced Peierls source pairing is skew;
4. the `++` residual pairing is exactly `T`;
5. the phase-normalized cubic Peierls cut is exactly `2T`.

Then instantiate `T` by the BM source-scaled boundary concomitant for every Xi
copy and show the incidence premise of the conditional HB landing is always
abstractly realizable, on and off the critical wall.

## Corpus basis

- `d4GaugeFixedTeukolskyPhaseNormalizedPeierlsCubicCut_eq_polarized`.
- `d4BMXiSecondHarmonicCokernelCausalCut_eq_PeierlsPolarizedCandidate`.
- Existing HB source-orientation modules show copywise fitted corrections can
  cancel unconditionally but do not classify abstract Peierls realizability.
- Mandatory corpus search found no arbitrary-target Peierls incidence model.

## Expected consequence

Proves symmetry, cyclicity, Peierls skewness, and abstract source incidence are
collectively nonselective: they realize every complex target in fixed dimension
two.  HB can survive only if literal global Einstein--Teukolsky source semantics
restrict the model beyond these algebraic axioms.

Positive survivor: a dimension-two universal realization theorem, including an
exact formula for every polarized incidence and cubic cut.

## Provisional literature audit

- arXiv:1402.1282 reviews precise hypotheses connecting covariant phase space
  and the Peierls formula.
- arXiv:math-ph/0408008 derives Peierls--DeWitt brackets from covariant
  symplectic geometry.
- arXiv:1906.08616 treats covariant phase space and boundaries.

No audited source states this universal two-dimensional cubic-incidence
realization or its HB no-go. Priority remains provisional.

## Status

- Mandatory corpus search complete.
- Conjecture frozen.
- Paper proof dependency-closed.
- Formalized in
  `GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMSecondHarmonicPeierlsArbitraryIncidenceRealizationNoGo`.
- Direct `lake env lean` check passed.
- Targeted module build passed.
- Axiom audit passed: only `propext`, `Classical.choice`, and `Quot.sound`.

## Formal theorem package

- `hbUniversalPeierlsQuadraticResidual_symmetric`
- `hbUniversalPeierlsPairing_quadraticResidual_cyclic`
- `hbUniversalPeierlsSourcePairing_skew`
- `hbUniversalPeierls_incidence_eq`
- `hbUniversalPeierls_cubicCut_eq`
- `hbUniversalPeierls_BM_incidence_eq`
- `hbUniversalPeierls_fixedPropagator_BM_incidence_iff`
- `hbUniversalPeierlsBMTarget_eq_zero_iff`
- `hbUniversalPeierls_BM_cokernelCausalCut_eq_candidate`
- `hbUniversalPeierls_BM_retardedSection_eq_advancedSection_iff_criticalLine`

## New exact insight

Dimension two already realizes every complex polarized Peierls incidence while
satisfying all abstract symmetry, cyclicity, and skewness laws.  The fixed
branches have quadratic residuals forming a unit symplectic cell, and scaling
the standard symplectic propagator by `T` makes incidence exactly `T` and cubic
cut exactly `2T`.

Choosing `T` to be the BM boundary concomitant makes every premise of the
conditional Peierls landing true copywise, for every Xi divisor, and produces
the wall receiver with no new source theorem.  This is a formal producer no-go:
abstract Peierls structure cannot distinguish literal incidence from target
fitting.

The strongest positive survivor is the global compatibility law: one fixed
propagator realizes all BM copies iff the complete BM boundary-concomitant target
is constant across the Xi divisor.

## Remaining HB boundary

- Derive one divisor-independent/global Peierls propagator from the literal
  Einstein--Teukolsky action and boundary conditions.
- Prove its induced BM target satisfies the required global compatibility,
  without copywise scalar fitting.
- Preserve biorientation and left-QNM normalization through that construction.
