# HB BM third-order cokernel necessity

- **ID:** HB-BMTCN
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `rh-current-frontier-map.md` · HB `DYN ORIENT LAND`
- **Statement:** At a critical Xi fibre, exact BM incidence fixes the total non-AIME third-order resonant projection to exactly the negative AIME numerator. For nonzero absorbed seed this projection is nonzero, forcing a nonexact linearized Einstein--Teukolsky cokernel class in the charge-orthogonal stationary cascade, second-harmonic cascade, or direct third variation.

## Goal

Upgrade HC11's scalar statement “same-pole remainder must be nonzero” to a source-faithful exact law and cohomological classification across the complete third-order Einstein `++-` channels.

## Gates

- [x] 0 → 1 in-progress: mandatory corpus search found exact charge split and abstract cancellation cohomology but no BM-incidence bridge
- [x] 1 → 2 fully-proven: dependency-closed paper proof
- [x] 2 → 3 formalized: Lean theorems, targeted build, axiom audit, umbrella wiring
- [ ] 3 → 4 publication-ready: standalone exposition

## Theorem HC12

Let `L` be the linearized Einstein--Teukolsky operator and `ell` a left resonant state annihilating
`range L`. Split the complete `++-` coefficient with mass-charge projector `P` into AIME channel,
charge-orthogonal stationary cascade, second-harmonic cascade, and direct third variation.

If the full projected residue matches the unit BM target at a critical Xi copy, then

`ell(orthogonal stationary + second harmonic + direct third variation) = -AIMENumerator`.

For nonzero absorbed seed the right side is nonzero. If the AIME projection is the source-derived
numerator, at least one of the three non-AIME channels lies outside `range L`.

## Proof

HC11's exact same-pole correction theorem specializes at a critical Xi fibre because the unit BM
target vanishes there. It gives the aggregate non-AIME projection as exactly the negative AIME
numerator. Source-derived AIME nonvanishing makes this aggregate projection nonzero for nonzero
seed.

Adding the AIME channel makes the complete third-order resonant projection zero. The corpus charge
split identifies this sum with the full Einstein `++-` coefficient. If all three non-AIME channels
were in `range L`, the left resonant state would annihilate each, contradicting the exact nonzero
aggregate projection. Therefore the orthogonal stationary cascade, second harmonic, or direct
third variation represents a nonzero cokernel class.

## Novelty audit (2026-08-28)

Corpus search found the third-order Einstein charge split and general resonant-cancellation
cohomology, but no theorem connecting them to exact BM incidence. Literature develops nonlinear
Kerr/Teukolsky perturbation theory through second order, absorption-induced mode excitation, and
second-order quasinormal modes, but the audit found no critical-Xi BM/AIME identity fixing the
aggregate third-order non-AIME projection or its cokernel trichotomy. Primary references:
Spiers--Pound--Moxon, [Second-order Teukolsky formalism in Kerr spacetime](https://arxiv.org/abs/2305.19332);
Green--Hollands--Zimmerman, [Teukolsky formalism for nonlinear Kerr perturbations](https://arxiv.org/abs/1908.09095);
Sberna--Bosch--East--Green--Lehner, [Nonlinear effects in the black hole ringdown: Absorption-induced mode excitation](https://arxiv.org/abs/2112.11168);
Nakano--Ioka, [Second Order Quasi-Normal Mode of the Schwarzschild Black Hole](https://arxiv.org/abs/0708.0450).

## Lean certificate

- Module: `GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMThirdOrderCokernelNecessity`
- Theorems:
  - `d4EinsteinThirdOrder_nonAIMEProjection_eq_neg_AIME_of_unitBMTarget_of_criticalLine`
  - `d4EinsteinThirdOrder_nonAIMEProjection_ne_zero_of_unitBMTarget_of_criticalLine`
  - `d4EinsteinThirdOrder_unitBMTarget_of_criticalLine_forces_nonexact_channel`
- Axioms: only Mathlib foundations `propext`, `Classical.choice`, `Quot.sound`.
- Direct `lake env lean` check and target-specific `lake build` pass; module wired into RHTower umbrella.
- No `sorry`, `admit`, added `axiom`, `opaque`, or `unsafe` declaration. Repository-wide lint reports only unrelated unreachable modules.

## Log

- 2026-08-28 — conjectured from HC11 forced counterterm plus corpus third-order source cohomology.
- 2026-08-28 — strengthened from a channel disjunction to exact aggregate projection and nonvanishing laws.
- 2026-08-28 — paper proof, Lean proof, targeted build, axiom audit, umbrella wiring, and lint-scope audit completed.
