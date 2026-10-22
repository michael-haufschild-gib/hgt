# HB Isolated Unit-Amplitude Nonlinear Covariance

- **ID:** HB-IUANC
- **Stage:** 5-failed
- **Type:** FALSIFIED
- **Statement:** Universal source-FE covariance asserted only on each canonical unit Xi basis packet can independently select the RH wall.

## Exact killing theorem/mechanism

`[LEAN-PROVED]` `d4HBIsolatedUnitAmplitudeNonlinearEvolutionRouteKilled` constructs, for every overtone and every real clock time, a finite-support-preserving coordinatewise degree-three evolution with the centered BM vacuum first variation and exact source-FE covariance on every unit basis packet.

The correction `x_q^2(x_q-1)K_q` is invisible to the vacuum first variation and vanishes at unit input, but at the transported cocycle amplitude it interpolates the full reflected clock defect. Thus the isolated covariance premise holds unconditionally, including tilted Xi fibres.

## Strongest positive survivor

The boundary is exact. `hbXiPeierlsIsolatedUnitClockInterpolant_fullCovariant_iff_rh` proves that at nonzero time, upgrading this same interpolant from unit-basis covariance to full finite-packet covariance is equivalent to RH.

## New insight

Vacuum differentiability of dynamics does not constrain isolated finite-amplitude symmetry values. HB requires covariance itself on an amplitude family accumulating at vacuum/full packet space, or a physical coefficient law that rules out interpolation. Remaining alternatives are vacuum-singular dynamics, changed linearized clock/literal source transport, or independently derived full covariance.

## Status

- Lean module: `formal/GaloisForLFunctions/RHTower/ThetaCusp/ThetaCuspHawkingBMIsolatedUnitAmplitudeCovarianceInterpolationNoGo.lean`
- Targeted build: passed.
- Axiom audit: `propext`, `Classical.choice`, `Quot.sound` only.
- Literature boundary: general Whitney/Borel jet interpolation is established parent theory; current nonlinear Teukolsky/QNM work constructs perturbative sources and quadratic modes but no Birmingham--Mokhtari/Xi finite-amplitude covariance selector was found ([Spiers--Pound--Moxon 2023](https://arxiv.org/abs/2305.19332), [Green et al. 2024](https://arxiv.org/abs/2210.15935), [Bourg et al. 2025](https://arxiv.org/abs/2503.07432), [Slutsky--Sodin--Wennman 2025](https://arxiv.org/abs/2507.12058)).

