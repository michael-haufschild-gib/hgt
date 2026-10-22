# Xi transverse spectral universality law

- **ID:** xi-transverse-spectral-universality-law
- **Stage:** 1-in-progress
- **Type:** THEOREM (paper proved, hostile-audited, Lean-direct-checked; no priority claim)
- **Source:** Bottom-up join of terminal `XiZeroHalfPlaneBound alpha` classifiers found in the
  post-Law-17 equality-endpoint scan
- **Statement:** At every positive transverse scale, one complete Hedenmalm Gaussian Hankel tail
  cone is equivalent to simultaneous validity of all 18 exact classifiers found in the closure:
  analytic continuation, power envelope, exact and covering negative-channel energy, actual,
  prime--Gamma, and prime--polar energy/abscissa/summatory growth, projective radius, faithful
  thermal moments, and cold-partition free energy.

## Gates

- [x] 0 → 1 in-progress: theorem-first closure and exact hypotheses
- [x] Complete paper proof with no open dependency
- [x] Lean source passes `lake env lean <file>`
- [x] Direct tree-file Lean check
- [x] Hostile literature noncollision audit
- [ ] Final module build, lint, and axiom audit

## Lean inputs

1. `hedenmalmGaussianHankelTailCone_iff_xiZeroHalfPlaneBound` identifies complete Gaussian
   Hedenmalm tail positivity with the common half-plane predicate.
2. `xiZeroHalfPlaneBound_iff_inverseTiltedDyadicSourceAnalyticAbove` and
   `xiZeroHalfPlaneBound_iff_criticalMellinDefectAnalyticAbove` give two analytic charts.
3. `xiRectangularWeilTailPowerLower_iff_all_xiZeros_re_le` supplies the one-sided power chart.
4. `all_xiZeros_re_le_iff_negativeChannelSpectrum`,
   `xiZeroHalfPlaneBound_iff_rectangularNegativeEnergyAbove`, and
   `xiZeroHalfPlaneBound_iff_primeGammaTailNegativeEnergyAbove` supply exact split, intrinsic,
   and explicit prime--Gamma energy charts.
5. `all_xiZeros_re_le_iff_rectangularPrimePolarSource_negativeEnergyAbove`,
   `all_xiZeros_re_le_iff_rectangularPrimePolarSource_negativeAbscissa_le`, and
   `primeGamma_abscissa_le_iff_forall_thermalProjectiveMoment_le` supply finite-source and
   abscissa charts.
6. `xiRightTransverseSup_le_iff_exists_negativeEnergyMajorantAbove` and
   `xiRightTransverseSup_le_iff_exists_twoChannelEnergyCoverAbove` add order-ideal and positive
   covering certificates without exact source identification.
7. `xiZeroHalfPlaneBound_iff_primeGammaCumulativeNegativeMassGrowth` and
   `all_xiZeros_re_le_iff_rectangularPrimePolarSource_cumulativeNegativeMassGrowth` give the
   explicit prime--Gamma and Gamma-free summatory charts.
8. `xiZeroHalfPlaneBound_iff_projectiveReflectionRadius_le` gives the projective chart.
9. `xiZeroHalfPlaneBound_iff_forall_thermalProjectiveMoment_le`,
   `xiZeroHalfPlaneBound_iff_exists_eventually_thermalProjectiveMoment_le`, and
   `xiZeroHalfPlaneBound_iff_exists_eventually_thermalProjectiveColdPartition_le` give exact
   moments, cofinal moments, and cold free energy.

## Paper proof

Assume the Hedenmalm tail cone. Input 1 gives `XiZeroHalfPlaneBound alpha`. The power-envelope
equivalences also identify this predicate with `xiRightTransverseSup ≤ alpha`. Apply the forward
direction of Inputs 2--9 to obtain every component of the universal certificate. Conversely,
the certificate contains the inverse-tilted analytic chart; the reverse direction of Input 2
recovers `XiZeroHalfPlaneBound alpha`, and the reverse direction of Input 1 recovers the
Hedenmalm tail cone. All hypotheses match at the same `alpha`; positivity of `alpha` is used only
by the cofinal geometric moment chart, while the other inputs need nonnegativity. `[PROVED HERE]`

## Formalization target

- Module: `formal/GaloisForLFunctions/RHTower/XiTransverseSpectralUniversalityLaw.lean`
- Certificate: `XiTransverseUniversalCertificate`
- Capstone: `hedenmalmGaussianHankelTailCone_iff_transverseUniversalCertificate`

## Internal noncollision audit

`scripts/formal_tools.py research "Hedenmalm Gaussian Hankel tail cone negative channel cumulative
mass thermal projective moments"` found the individual endpoints but no common certificate or
theorem. Direct text search found no module containing both `HedenmalmGaussianHankelTailCone` and
the cumulative negative-mass or arbitrary negative-channel-split criteria.

## Hostile literature audit

Exact searches included `"Hedenmalm Gaussian Hankel" "thermal" Riemann`, `"Xi transverse"
"cumulative negative"`, `"projective reflection radius" "Riemann"`, `"negative-channel"
"Riemann xi" Hankel`, `"Hedenmalm Gaussian" "negative energy majorant"`, `"Hedenmalm"
"prime-Gamma" abscissa thermal moment`, and `"Riemann xi" "two-channel" Dirichlet energy`, plus
arXiv searches joining Hedenmalm, zero-free half-planes, negative Dirichlet mass, thermal moments,
and projective radius. No exact collision was found. Closest
primary sources were Hedenmalm's
[Spectral interpretation of Riemann zeta zeros](https://arxiv.org/abs/2606.17494), which develops
a theta-based differential-operator eigenproblem and conditional self-adjointness route;
Gallardo-Gutiérrez--Seco's
[Zero-free regions and weighted Dirichlet spaces](https://arxiv.org/abs/2206.02654), which gives
approximation criteria for zeta zero-free regions; and Connes--Consani's
[The Scaling Hamiltonian](https://arxiv.org/abs/1910.14368), which studies semi-local spectral
realization and Weil positivity. None contains the 18-chart equivalence, its explicit negative
mass sequences, positive covers, or thermal/projective synchronization. Evidence supports
noncollision only;
no priority claim is made.

## Log

- 2026-07-22 — Found by enumerating terminal equality classifiers with same-object declarations
  in other modules. Exact hypotheses reconciled across all ten charts; paper proof closed.
- 2026-07-22 — Exact direct check
  `lake env lean GaloisForLFunctions/RHTower/XiTransverseSpectralUniversalityLaw.lean` passed.
- 2026-07-22 — Hostile exact and neighboring-concept literature audit passed; nearest primary
  Hedenmalm, weighted-Dirichlet, and semi-local spectral papers are materially different.
- 2026-07-22 — Post-law terminal scan exposed eight omitted exact endpoints: power lower,
  intrinsic and prime--Gamma energy, prime--polar energy/abscissa, positive majorant/two-channel
  covers, and prime--Gamma abscissa. Strengthened certificate from ten to 18 charts; exact direct
  Lean check and expanded hostile search passed.
