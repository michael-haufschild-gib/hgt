# Divisor-metric classification and dense-radical no-go for the Hedenmalm theta pair

- **ID:** `hedenmalm-divisor-metric-dense-radical-no-go`
- **Stage:** 3-formalized
- **Type:** THEOREM PACKAGE / HILBERT--PÓLYA METRIC CLASSIFICATION AND TOPOLOGY NO-GO
- **Scientific status:** `[PROVED] [FORMALIZED] [CURRENT-LITERATURE AUDITED 2026-07-27]`
- **Direct parent:** H. Hedenmalm, *Spectral interpretation of Riemann zeta zeros*,
  arXiv:2606.17494 (2026)

## Closed question

Which positive source-core metrics can symmetrize Hedenmalm's theta differential pair, and can
any nonzero such metric belong to the ordinary `L²(R)` form topology?

## Answer

Normalize Hedenmalm's logarithmic theta source `k` so that its Fourier transform is the centered
completed zeta function `Xi`. Let `Q` be a jointly continuous nonnegative sesquilinear form on
complex Schwartz space. Assume

```text
Q(Du,v)=Q(u,Dv),                 D=-i d/dx,
Q(k,k)=0.
```

Then:

1. there is a unique positive measure `mu` of temperate growth such that

   ```text
   Q(u,v)=integral hat(u)(t) conjugate(hat(v)(t)) dmu(t);
   ```

2. `mu` is supported on the real zero set of `Xi`, hence

   ```text
   mu=sum_(Xi(gamma)=0, gamma real) c_gamma delta_gamma,
   c_gamma>=0;
   ```

3. conversely every such temperate atomic measure defines an admissible form;
4. if `Q` is nonzero, the ordinary-`L²` image of its left radical is dense, proper, and nonclosed;
5. every nonzero such `Q` fails sequential closability through ordinary `L²`;
6. for every Schwartz vector `u`, there is a sequence `z_n` with

   ```text
   ||z_n||_2 -> 0,
   Q(z_m-z_n,z_m-z_n)=0,
   Q(z_n,z_n)=Q(u,u).
   ```

7. the radical of a nonzero `Q` strictly contains the source-kernel line `Ck`.

Thus no nonzero admissible source-core metric has an ordinary-`L²`-closed radical or is the
restriction of a closed nonnegative quadratic form on ordinary `L²`. Every surviving metric is a
singular Fourier-sampling rigging carried by the real `Xi` divisor.

## Hedenmalm consequence

For Hedenmalm's pair

```text
L=k D k^(-1),       q_1(u,v)=q_2(Lu,Lv),
```

pair self-adjointness is precisely momentum symmetry of `q_1`, and `Lk=0` gives theta nullity.
If `q_2` were positive definite on the full algebraic range `L S(R)`, the pullback radical would
be exactly `ker L=Ck`. The dense-radical law makes that impossible. Therefore no
positive-definite metric exists on the full algebraic range when its pullback is jointly
Schwartz-continuous and pair-symmetric. Every nonzero semidefinite extension has the singular
divisor-supported form above and is nonclosable in ordinary `L²`. This does not exclude a
target-domain form defined only on the finite zero-eigenfunction span. It completely excludes the
positive-definite source-core metric, the ordinary translation-stable `L²` completion, and
classifies the surviving semidefinite alternative.

## Exact eigenfunction sampling

For a zero `alpha` of `Xi`, the Fourier transform of Hedenmalm's eigenfunction is

```text
hat(u_alpha)(t)=-i Xi(t)/(alpha-t).
```

Every classified metric kills a nonreal-zero eigenfunction. At a real zero,

```text
Q(u_alpha,u_alpha)=c_alpha |Xi'(alpha)|^2.
```

Consequently strict positivity on every theta eigenfunction implies RH and simplicity, and in the
atomic class conservativity is exactly positive mass on every zero fiber plus simplicity.

## Proof architecture

1. Momentum symmetry differentiates the simultaneous translation orbit and forces exact
   translation invariance.
2. The Bochner--Schwartz theorem gives the unique positive temperate Fourier measure.
3. `Q(k,k)=0` and `hat(k)=Xi` give `integral |Xi|² dmu=0`; positivity forces divisor support.
4. The real zero set is discrete, so the measure is atomic.
5. The theta source is cyclic under ordinary `L²` translations because `Xi` is nonzero almost
   everywhere. Its whole translation orbit lies in the radical.
6. Cyclicity makes the radical image dense. Nonzero `Q` makes it proper, hence nonclosed.
7. Approximation of any source vector by radical vectors produces the fixed-energy `L²`-null
   sequence and proves nonclosability.

## Primary-literature audit

Searches through 2026-07-27 covered the complete June 2026 Hedenmalm preprint, its exact title and
keyword combinations with `metric`, `inner product`, `Bochner--Schwartz`, `divisor-supported`,
`cyclic`, `radical`, `closability`, and `L²`, plus current Hilbert--Pólya surveys and arXiv
follow-ups. No source containing this classification or topology no-go was found. Hedenmalm asks
for an appropriate Hilbert form on the finite eigenfunction span; he does not study continuous
Schwartz-source extensions, classify their measures, or prove the dense-radical/nonclosability
law. The harmonic-analysis ingredients are classical; novelty attaches only to their exact
assembly for this theta pair.

## Formal theorem surface

```text
formal/GaloisForLFunctions/HTGeometry/SchwartzPositiveMeasureRepresentation.lean
formal/GaloisForLFunctions/RHTower/ThetaCuspSchwartzFourierXi.lean
formal/GaloisForLFunctions/RHTower/XiThetaL2MetricSingularity.lean
formal/GaloisForLFunctions/RHTower/XiThetaSchwartzL2Nonclosability.lean
formal/GaloisForLFunctions/RHTower/XiThetaSpectralOrientationClassification.lean
formal/GaloisForLFunctions/RHTower/HedenmalmUniversalPositiveFormClassification.lean
formal/GaloisForLFunctions/RHTower/HedenmalmThetaNullTemperedDenseRadicalUniversalityLaw.lean
formal/GaloisForLFunctions/RHTower/XiDivisorSupportedMetric.lean
```

Headline declarations:

```text
existsUnique_temperateSpectralRepresentation_supported_realDivisor_of_thetaNull
universalPositiveForm_canonicalMeasure_atomic_of_thetaNull
universalPositiveForm_thetaNull_sequentiallyL2Closable_iff_zero
universalPositiveForm_nonzero_thetaNull_temperedDenseRadicalLaw
not_exists_nonzero_universalPositiveForm_thetaNull_l2ClosedRadical
not_exists_nonzero_universalPositiveForm_thetaNull_exactSourceLineRadical
exists_xiThetaL2Null_constantEnergy_sequence
xiDivisorSupportedPolarization_thetaEigen_diagonal
xiThetaMetricConservative_implies_rh_and_simple
xiThetaMetricConservative_iff_mass_pos_and_simple
```

## Gates

- [x] complete paper proof
- [x] exact theta normalization and Fourier identity
- [x] positive-form representation and uniqueness
- [x] real-divisor support and atomic decomposition
- [x] converse classification
- [x] dense proper nonclosed radical
- [x] fixed-energy null sequence
- [x] exact ordinary-`L²` nonclosability classification
- [x] exact eigenfunction sampling and conservativity boundary
- [x] current primary-literature search
- [x] named closed-radical no-go theorem
- [x] named positive-definite source-core no-go theorem
- [x] standalone publication manuscript and hostile referee audit
