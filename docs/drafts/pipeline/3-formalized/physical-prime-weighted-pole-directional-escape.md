# Physical prime weighted-pole directional escape

- **ID:** `physical-prime-weighted-pole-directional-escape`
- **Stage:** 3 — formalized in Lean 4
- **Type:** THEOREM / exact RH criterion (Lean)
- **Source route:** D2 / FCRJ physical corrected-prime contour
- **Statement:** A hypothetical off-line Xi zero forces cofinally many exact natural-aperture
  physical squares times the direct infinite-prime source to have real part below every level in
  every neighborhood. Eventual local lower boundedness of these literal prime integrands is
  equivalent to RH.

## Goal

Close the local joint phase/source burden left by Loops 90--92. Prove an actual weighted-prime
escape law, not merely failure of abstract scalar monotonicity and not a completed-source proxy.

## Gates

- [x] 0 → 1 in-progress: corpus-derived pole-residue and log-mesh attack
- [x] 1 → 2 fully-proven: dependency-closed paper proof and exact route classification
- [x] 2 → 3 formalized: closed Lean theorems, direct check, targeted build, axiom audit
- [ ] 3 → 4 publication-ready: standalone theorem/no-go note

## Exact theorem

For positive physical widths `L,A,c`, real translation `a`, and centered coordinate `z`, define

```text
T_a(z) = xiPhysicalThetaAbelEnergyTwoEdgeTransform(L,A,c,a,z),
P_a(z) = T_a(z)^2 * (-i * infinitePrimeFlux(1/2+i z)).
```

At every centered point `alpha` with `0<Im alpha<1/2`, Lean proves the exact punctured limit

```text
(z-alpha) P_a(z)
  -> ord_alpha(Xi) * T_a(alpha)^2.                         (1)
```

If `XiC(alpha)=0`, `Re alpha>0`, and `L,A,c>0`, Loop 92's natural log-mesh phase argument extends
from rational D2 points to `alpha`: for every `N`, some `n>=N` has

```text
Im T_{log n/2}(alpha) != 0.                               (2)
```

Hence the residue in `(1)` is nonzero. For every `r>0` and `B in R`, the same selected `n`
satisfies

```text
exists z,
  0<Re z, 0<Im z<1/2, XiC(z)!=0, dist(z,alpha)<r,
  Re P_{log n/2}(z) < B.                                  (3)
```

Define eventual local lower boundedness to mean that some `N` makes every `n>=N` and every
centered upper-strip point possess a neighborhood on which `Re P_{log n/2}` has a finite lower
bound. Then

```text
XiPhysicalThetaAbelEnergyPrimeLogMeshEventuallyLocallyBoundedBelow(L,A,c)
  <-> RiemannHypothesis.                                  (4)
```

The unit-window specialization of `(4)` is a closed, premise-free theorem.

## Proof

Put `sigma=1/2+i alpha`. The corpus normalized zeta logarithmic-derivative theorem gives

```text
(s-sigma) * zeta'(s)/zeta(s) -> ord_sigma(xi).
```

Since `infinitePrimeFlux=-zeta'/zeta` and
`(1/2+i z)-sigma=(z-alpha)i`, the contour orientation cancels exactly:

```text
(z-alpha)(-i * infinitePrimeFlux(1/2+i z))
  = ((1/2+i z)-sigma) * zeta'(1/2+i z)/zeta(1/2+i z).
```

Analyticity of `T_a^2` proves `(1)` without an archimedean correction. The physical one-edge
noncensorship theorem and Loop 92's phase-aligned ceiling selector prove `(2)`, so multiplicity
times `T(alpha)^2` is nonzero.

The reusable directional-pole lemma is complex-coordinate invariant. If
`(z-alpha)f(z)->C!=0`, take `epsilon_k=1/(k+1)` and

```text
z_k=alpha-epsilon_k C.
```

Then `epsilon_k f(z_k)->-1`. Its real part therefore lies below `-1/2` eventually, while
`epsilon_k B->0`; positivity of `epsilon_k` yields `Re f(z_k)<B`. The points can be selected in
any prescribed neighborhood. Taking the intersection of a ball with the centered open strip and
using the nonzero normalized product also gives `XiC(z_k)!=0`, proving `(3)`.

Under RH, `XiC` is zero-free in the centered upper half-plane. The zeta denominator and its
derivative are locally analytic, so each fixed `P_{log n/2}` is continuous and locally bounded
below. Conversely, false RH supplies a strict-right upper zero copy; Schwarz reflection gives an
`alpha` satisfying the hypotheses above. Cofinality in `(2)--(3)` contradicts any eventual local
bound, proving `(4)`.

## Strongest positive survivor and route impact

- **Exact killing mechanism:** Any proposed eventually uniform pointwise lower bound for the
  actual physical direct-prime integrand fails locally and without limit loss if RH is false.
- **Strongest positive survivor:** Exact residue identity `(1)`, coordinate-free directional-pole
  escape, cofinal natural-aperture detector `(3)`, and exact prime-only criterion `(4)`.
- **New insight:** Complex physical phase is not only an order-transport obstruction. Coupled to
  the zeta pole, its square selects a nonzero complex residue whose own opposite direction forces
  an actual negative source sample. Gamma completion and contour integration are unnecessary for
  this local detector.
- **Remaining burden:** Prove eventual local lower boundedness in `(4)` from unconditional prime
  arithmetic. This is now an exact pointwise direct-prime endpoint; aperture-phase rescue is
  closed, not open.

## Lean certificate

- Module:
  `formal/GaloisForLFunctions/RHTower/XiPhysicalPrimeApertureThetaAbelEnergyPrimeWeightedPoleEscape.lean`
- Umbrella: `formal/GaloisForLFunctions/RHTower.lean`
- Direct source check: PASS
- Targeted build: PASS (`12921/12921`)
- Axiom audit: `[propext, Classical.choice, Quot.sound]`
- Principal declarations:
  `exists_realPart_lt_near_of_punctured_residue`,
  `tendsto_xiPhysicalThetaAbelEnergyPrimeWeightedSource_normalizedResidue`,
  `xiPhysicalThetaAbelEnergyTwoEdgeTransform_logMesh_cofinally_nonreal_at_centeredUpperStrip`,
  `exists_logMesh_physicalPrimeWeightedSource_cofinally_unboundedBelow_near_of_xiZero`,
  `xiPhysicalThetaAbelEnergyPrimeLogMeshEventuallyLocallyBoundedBelow_iff_riemannHypothesis`,
  `unitPhysicalThetaAbelEnergyPrimeLogMeshEventuallyLocallyBoundedBelow_iff_riemannHypothesis`.
- Formal lint: new wired module clean; repository-wide lint remains blocked only by unrelated
  unwired dirty-tree modules.

## Novelty audit

Targeted corpus searches found normalized Xi/zeta residue laws, completed-source local criteria,
direct-prime contour criteria with explicit archimedean correction, and the preceding physical
phase theorem, but no physical-weighted literal-prime local residue/escape theorem or criterion
`(4)`.

Primary-literature searches through 2026-08-28 found compact-window Weil positivity and decay,
continuous screw/operator formulations, numerical Archimedean spectral laws, and finite-core
Volterra/Weyl reductions. None states `(1)--(4)`, uses the exact natural physical two-edge square
to retain a direct-prime pole, or gives this eventual local lower-bound equivalence. Candidate-new
content is restricted to this exact route-specific formal synthesis.

Primary comparison points:

- M. Chuk, [*Weil positivity in compact windows: certified two-sided bounds and a Landau--Widom
  decay law*](https://arxiv.org/abs/2608.24827).
- M. Suzuki, [*Weil's quadratic form via the screw function*](https://arxiv.org/abs/2606.09096).
- T. Kim et al., [*A Numerical Realization of Suzuki's Weil-Quadratic-Form Operator*](https://arxiv.org/abs/2607.24830).
- M. B. Freedman, [*Finite-core Volterra reductions for a Weyl-positive Riemann phase kernel*](https://arxiv.org/abs/2606.29555).

## Log

- 2026-08-28 — Mandatory corpus search found normalized Xi/zeta residues, completed-source local
  gates, reciprocal-square sector escape, and exact physical log-mesh phase escape, but no
  weighted direct-prime directional-pole theorem.
- 2026-08-28 — Proved generic residue-opposite escape in every neighborhood.
- 2026-08-28 — Proved exact physical direct-prime normalized residue and cofinal natural-aperture
  noncensorship at every centered upper-strip point.
- 2026-08-28 — Proved actual local unboundedness below near every hypothetical off-line zero and
  exact eventual local-boundedness equivalence with RH.
- 2026-08-28 — Direct source check, targeted `12921/12921` build, standard axiom audit, umbrella
  wiring, and local lint audit passed.
