# Shared-clock rank-one observation rigidity

- **ID:** `shared-clock-rank-one-observation-rigidity`
- **Stage:** 3-formalized
- **Type:** `[BRIDGE] [CORPUS-USEFUL] [NOT A NOVELTY CLAIM]`
- **Lean source:**
  `formal/GaloisForLFunctions/HTGeometry/SharedClockRankOneRigidity.lean`
- **Statement:** A nonzero separable observation matrix determines its shared clock coordinate and
  channel-response factors uniquely up to one global nonzero calibration.  Applied to the existing
  Gamma translation curvature, the highest-jet source functional and factorial-tail observation
  vector are therefore projectively identifiable from the curvature itself.

## Exact value relation

For functions `t : I -> K` and `beta : J -> K`, define the static observation matrix

```text
T(i,j) = t(i) * beta(j).                                  (1)
```

Suppose the same matrix has another factorization

```text
T(i,j) = t'(i) * beta'(j),                                (2)
```

and one marked value of `t` and one marked value of `beta` are nonzero.  Then there is a unique
`c != 0` such that

```text
t'(i)    = c * t(i),
beta'(j) = c^(-1) * beta(j).                              (3)
```

Thus the observation matrix identifies one projective clock, not an absolute time scale.  A
normalization selects a representative but adds no dynamical evolution.

## Genomics, genetics, ML, and AI source

Li--Wang--Yang--Zhou, *On the Mathematics of RNA Velocity II: Algorithmic Aspects*,
arXiv:2306.05707, infer a global gene-shared latent time from a cell-by-gene time matrix.  Their
noiseless model has the rank-one form `(1)`, while their normalization fixes the otherwise
undetermined global scale.  The paper's optimization and Perron--Frobenius machinery address noisy
positive data; theorem `(3)` is the exact algebraic identifiability core relevant to this corpus.

This also gives a clean AI/latent-model audit.  A learned separable clock representation can change
its internal time and response coordinates without changing any output, but only through the
single scale gauge in `(3)` once the observation is genuinely rank one and nonzero.  More general
neural-ODE diffeomorphism gauges are not collapsed to this theorem.

## Direct application to the existing Lean corpus

The corpus already proves

```text
gammaClockCurvature(n)(a)(i)
  = a(last n) * gammaClockBoundaryVector(n)(i).            (4)
```

For every positive resolution, the new theorem proves that any alternative separation

```text
gammaClockCurvature(n)(a)(i) = source(a) * boundary(i)     (5)
```

must have the unique form

```text
source(a)   = c * a(last n),
boundary(i) = c^(-1) * gammaClockBoundaryVector(n)(i).     (6)
```

This strengthens the earlier rank-one statement.  Rank alone says that the curvature image is one
dimensional; `(6)` says the two observable factors are reconstructible projectively.  The Gamma
clock's source/boundary split is therefore not an arbitrary presentation.

## No-go and significant positive statement

**No-go.**  A rank-one shared observation cannot identify an absolute clock scale.  Genomic latent
time, an ML latent clock, or the Gamma clock curvature retains the calibration symmetry
`(t,beta) -> (c*t,c^(-1)*beta)`.

**Positive theorem.**  This scale is the complete ambiguity.  There is no additional hidden
factorization freedom once one clock and one response reading are nonzero.  Consequently the
projective clock coordinate and the reciprocal response coordinate are exactly observable from
the static constraint.

## RH impact

The theorem does not orient an off-line zero and does not discharge the open theta susceptibility
or Gibbs-moment inequalities.  Its proof-search value is architectural and exact: any rank-one
clock factorization proposed for the prime--Gamma source can now be audited modulo one scalar,
rather than treated as a freely chosen source/boundary split.  To advance RH, a future application
must still supply a source-specific sign, value, or incidence after this calibration gauge is
removed.

## Formal theorem surface

- `sharedClockObservation`
- `sharedClockObservation_factorization_unique_up_to_scale`
- `gammaClockCurvature_factorization_unique_up_to_scale`

## Verification

- the exact new module target was built because its artifact was absent; all dependencies were
  reused from cache;
- the touched source passed a direct `lake env lean` check;
- both theorem declarations depend only on `propext`, `Classical.choice`, and `Quot.sound`;
- no numerical computation, full build, or self-concurrent Lean build was run.

## Gates

- [x] existing general rank-one, clock-calibration, Gamma-curvature, genomics, and ML interfaces
  checked before formalization
- [x] exact positive algebraic relation isolated from the noisy inference architecture
- [x] general HTGeometry theorem formalized
- [x] direct existing Gamma-clock consumer formalized
- [ ] no source-specific RH orientation or theta-cusp scalar hypothesis discharged
