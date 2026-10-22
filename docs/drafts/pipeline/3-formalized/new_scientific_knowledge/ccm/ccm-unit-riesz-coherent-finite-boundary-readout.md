# Finite HG boundary readout of completed unit-Riesz charge

- **ID:** `ccm-unit-riesz-coherent-finite-boundary-readout`
- **Stage:** 3-formalized
- **Type:** FINITE TAIL-MODE ELIMINATION / UNIFORM HG READOUT / SOURCE CHARGE
- **Scientific status:** `[UNCONDITIONALLY PROVED IN LEAN]`
  `[CANDIDATE NEW SCIENTIFIC KNOWLEDGE] [EXTERNAL PRIORITY UNVERIFIED] [NOT AN RH PROOF]`
- **Formal module:**
  `formal/GaloisForLFunctions/RHTower/CCM/CCMUnitRieszCoherentFiniteBoundaryReadout.lean`
- **Parent:** `ccm-unit-riesz-coherent-principal-relative-carrier`

## Result

Let `L=log N`, `r=exp(-L/2)`, and use logarithmic-step codiagonal

```text
D_N(u)=C_N(u+L)-C_N(u).
```

Principal-relative carrier initially reconstructed half resolvent by infinite series
`sum_(j>=0)D_N(jL)`. Exact post-aperture response has only two tail modes, with ratios `r` and
`r^2`. Lean eliminates both modes and proves finite identity

```text
R_1(L)/2
 = D_N(0)
   + ((1-r-r^2)D_N(L)+D_N(2L))/((1-r)^2(1+r)).
```

For every integer `N>=2`, Lean proves `r<=3/4`, hence denominator is uniformly separated from zero.
A coarse explicit aperture-independent estimate is

```text
|R_1(L)/2| <= |D_N(0)| + 48|D_N(L)| + 16|D_N(2L)|.
```

Same inequality is proved for real parts of three samples of single canonical HG-admissible
profile `unitRieszCoherentCompletedShiftCodiagonalProfile N L`.

## Scientific consequence

Infinite-series/summable-dual obstacle identified by relative-carrier theorem is not fundamental.
Literal source tail has finite recurrence rank two. Matching codiagonal step to aperture converts
arithmetic boundary charge into uniformly conditioned three-point observation of admissible bulk.

This changes common CCM open core. No route now needs bound unweighted infinite translation sum.
It suffices to control three graph/HG samples at `0`, `log N`, and `2 log N` by a subpower source
law. This is compatible with Route O near-ground observation, GS finite incidence, HG boundary
density, FU source transport, UR smoothing, and EP finite operator-valued boundary blocks.

## Claim-to-Lean closure

| Claim | Declaration |
|---|---|
| generic two-mode finite readout | `twoModeConstant_eq_threeIncrementReadout` |
| square-mode simplification | `squareMode_threeIncrementReadout_simplify` |
| general uniformly conditioned estimate | `abs_squareMode_threeSampleReadout_le` |
| literal finite charge readout | `unitRieszCoherentCompletedLogCodiagonal_finiteChargeReadout` |
| literal simplified three-sample identity | `unitRieszCoherentCompletedLogCodiagonal_threeSampleReadout` |
| uniform tail ratio | `unitRieszCoherent_logTailRatio_le_three_quarters` |
| literal three-sample inequality | `abs_criticalMellinChebyshevResolventSource_half_le_threeCodiagonalSamples` |
| same inequality in HG profile | `abs_criticalMellinChebyshevResolventSource_half_le_threeHGProfileSamples` |

All eight declarations have `#print axioms` output exactly
`[propext, Classical.choice, Quot.sound]`. Direct module check and exact leaf build pass. Module is
wired into `GaloisForLFunctions.RHTower`; umbrella itself was not built.

## Theatre and novelty audit

Solving a two-mode recurrence is elementary and not claimed as new. Candidate novelty is
source-specific alignment:

```text
CCM aperture L = log N
  = codiagonal step making entire nondecaying arithmetic charge
    a uniformly conditioned three-sample functional of one HG leak profile.
```

Proof explicitly checks conditioning; no hidden `sqrt N` loss survives. Result removes named hard
functional-analytic obstacle but does not bound three samples. External priority remains
unverified.

## New open core

Prove source-specific subpower control of three literal profile samples—or one graph/boundary
energy estimate implying it. Since sample count and coefficients are uniform, no infinite-channel
or tail summability argument is needed. A successful estimate immediately controls aperture
resolvent on integer logarithmic lattice; remaining endpoint work must transfer that lattice bound
to established CCM-FU/UR RH criterion without exponent loss.

## Gates

- [x] infinite relative reconstruction
- [x] finite tail-mode elimination
- [x] aperture-uniform conditioning
- [x] HG-profile formulation
- [x] unconditional Lean proof
- [x] umbrella wiring
- [ ] independent mathematical audit
- [ ] external priority audit
- [ ] three-sample subpower bound
- [ ] integer-log lattice-to-RH endpoint
- [ ] RH

## Log

- 2026-08-16 -- Discovered logarithmic-step tail recurrence rank two.
- 2026-08-16 -- Proved exact three-sample charge formula.
- 2026-08-16 -- Proved uniform `r<=3/4` conditioning and explicit `1,48,16` bound.
- 2026-08-16 -- Recast bound as three samples of one HG-admissible profile.
- 2026-08-16 -- Audited axioms, built leaf, wired umbrella.
