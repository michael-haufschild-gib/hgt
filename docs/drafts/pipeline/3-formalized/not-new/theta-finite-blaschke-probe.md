# Finite Blaschke probes for theta-square frequencies

- **ID:** theta-finite-blaschke-probe
- **Stage:** 3-formalized / infrastructure
- **Type:** THEOREM (Lean), `[SEARCH + BRIDGE]`
- **Date:** 2026-07-10
- **Module:** `GaloisForLFunctions.RHTower.ThetaBlaschkeProbe`
- **Retired consumer:** `../../5-failed/theta-blaschke-condition-number.md`
- **Replacement coordinate:** `../new/xi-theta-critical-log-translation-seam.md`

## Formal surface

- `thetaFiniteBlaschkeProbe_self` — normalization at the selected square.
- `thetaFiniteBlaschkeProbe_other` — exact annihilation of every other square through depth `N`.
- `norm_thetaBlaschkeFactor_mul_I` — unit boundary modulus of each half-plane factor.
- `thetaFiniteCondition` — normalization condition number.
- `one_le_norm_thetaBlaschkeNormalize` — every distinct factor costs at least one.
- `thetaLowerBand_card` — the lower half-band contains `floor(n/2)` indices.
- `thetaFiniteCondition_lower` — condition number at least `(5/3)^(floor(n/2))`.
- `norm_thetaFiniteBlaschkeProbe_zero` — exact boundary-height-zero norm.
- `norm_thetaFiniteBlaschkeProbe_zero_lower` — exponential boundary amplification.

## Certificate

- Targeted source check and module build: passed.
- Full/umbrella build: deliberately not run.
- Axiom audit: `[propext, Classical.choice, Quot.sound]` only.
- Active `sorry`, `admit`, `axiom`, `opaque`, `unsafe`: none.
- Generated API refreshed; formal lint passed.

## Novelty status

Finite Blaschke interpolation is parent Hardy-space infrastructure and is not claimed as new
knowledge. Its specialization proves exponential boundary amplification for a Laplace-variable
reader. The proposed completed-Mellin consumer was falsified: the actual critical trace is Fourier
in the logarithmic variable. The finite probe remains correct but is not an RH-facing coordinate.
