# HB finite-rank global AIME source-response no-go

- **ID:** HB-FR-AIME-2026-08-31
- **Stage:** 3-formalized
- **Type:** THEOREM / route-class no-go
- **Status:** `[PROVED HERE] [LEAN-PROVED] [NOVELTY UNVERIFIED]`

## Result

No finite-algebraic-rank complex-linear global Xi-packet response can cancel the exact cubic AIME
coefficient on every Xi fibre.  Response receives literal AIME source packet, may mix all fibres,
and is subject to no diagonal, locality, finite-band, passivity, Schwarz, boundedness, or spectral
regularity condition.

Phase and perturbative order are exact: source packet and full response are odd under `A ↦ -A`
and homogeneous of degree three under real rescaling.  Thus result reaches source-adapted,
phase-odd cubic threshold class; it is not phase-blind or seed-linear no-go.

## RH proof chain killed

Eliminated chain:

`finite-rank source-adapted cubic response` → `universal radiative ++ extinction` →
`full retarded-minus-advanced causal-cut extinction` → `source-FE physical-clock covariance` →
exact FZZ-P information-force, PW-B recoil, and RBH multiplicity Ward images → common Ward
endpoint → RH.

Surviving HB producer must have infinite algebraic rank before divisor selection.  Finite local
order, finite spectral aperture, and arbitrary finite cross-fibre mixing are all subsumed.

## Paper proof

Let `Delta : (XiZeroCopy →₀ ℂ) →ₗ[ℂ] (XiZeroCopy →₀ ℂ)` have finite-dimensional range.

1. Every finite-dimensional subspace of a `Finsupp` space has common finite coordinate support:
   choose finite module generators and unite their finite supports.
2. `XiZeroCopy` is infinite, so choose `q` outside that common support.
3. `Delta` of every input has zero `q` coordinate.  In particular response to literal packet
   `single q N_A(q)` has zero `q` coordinate.
4. Universal cancellation at `q` would reduce to `N_A(q)=0`.
5. Exact AIME nonvanishing gives `N_A(q)≠0` for every `A≠0` and every Xi copy. Contradiction.

Sharp positive survivor: universal source-adapted cancellation implies
`¬ FiniteDimensional ℂ (LinearMap.range Delta)`.

## Lean artifact

- Module:
  `GaloisForLFunctions.RHTower.ThetaCuspHawkingHBFiniteRankGlobalAIMESourceResponseNoGo`
- New infrastructure:
  `exists_common_finset_support_of_finiteDimensional_finsupp`
- Local no-go:
  `not_d4HBFiniteRankGlobalAIMESourceResponse_universalCancellation`
- Positive survivor:
  `d4HBGlobalAIMESourceResponse_universalCancellation_forces_infiniteRank`
- Closed certificate:
  `d4HBFiniteRankGlobalAIMESourceResponseCancellationRouteKilled`

Module is wired into `GaloisForLFunctions.RHTower`.

## Novelty audit, 2026-08-31

Internal corpus search found finite-local-angular, finite-variation causal-spectrum,
phase-blind-threshold, direct-third-jet, and fixed-propagator no-gos, but no theorem excluding
finite-dimensional range for global response to literal cubic AIME packet.

Primary literature reviewed:

- [Sberna et al., AIME](https://arxiv.org/abs/2112.11168) identifies AIME as third-order mass
  backreaction with cubic excitation amplitude, but has no global finite-rank obstruction.
- [Zhang--Ren, causal Green decomposition](https://arxiv.org/abs/2607.26010) keeps causally distinct
  QNM and tail sectors in full Green response; it does not state this rank theorem.
- [Hui--Kabat--Wong, QNMs, echoes, and causal Green functions](https://arxiv.org/abs/1909.10382)
  derives causal echo/Green expansions, not an Xi-labelled cubic source-response rank law.

Novelty claim is limited to exact HB/AIME route-class application and Lean proof.

## Hostile audit

- No RH, zero simplicity, zero locations, numerical input, or computation is used.
- Cross-fibre mixing is arbitrary; proof uses only finite-dimensional range.
- Input is exact cubic AIME source, so source adaptation and half-turn oddness remain available.
- Theorem does not exclude infinite-rank, nonlinear-in-source, or non-`Finsupp` completed response.
  Infinite algebraic rank is exact positive survivor.

## Verification

- Direct `lake env lean` check: passed.
- Targeted build:
  `lake build GaloisForLFunctions.RHTower.ThetaCuspHawkingHBFiniteRankGlobalAIMESourceResponseNoGo`
  passed `11894/11894`.
- Axiom audit for infrastructure, phase/scale laws, local no-go, infinite-rank survivor, and closed
  certificate reports only `propext`, `Classical.choice`, and `Quot.sound`.
- Formal lint confirms umbrella reachability and reports no defect in this module. Its nonzero exit
  is caused by pre-existing unwired Deninger, Hedenmalm, XiWard, and lower-ramification modules
  outside this card.
