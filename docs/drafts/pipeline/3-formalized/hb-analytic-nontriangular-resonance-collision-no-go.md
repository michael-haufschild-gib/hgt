# HB analytic perturbative QNM-clock route kill

- **ID:** C-HB.1
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:** Arbitrary analytic all-order BM backreaction has a unique continuous pole germ through each Xi QNM; nontrivial perturbative branch collision is impossible.

## Route closure

Chain targeted:
`all-order clock renormalization → nontriangular pole collision → Ward sign → HB extinction → RH`.

All triangular history-local towers absorb the source. Their analytic nontriangular escape is now dead: simple physical BM Jost derivative plus holomorphic IFT gives one analytic pole germ, unique among all continuous root germs. Off-wall FE--Schwarz partner germs remain distinct near zero coupling.

## Proof

For returned relation
`F(ε,ω)=J(ω)+ε K(ω)+ε² H(ε,ω)`, arbitrary `H` analytic at `(0,ω₀)`:

1. `F(0,ω₀)=J(ω₀)=0`.
2. `∂ωF(0,ω₀)=J'(ω₀)≠0` at every Xi descendant.
3. Parametric holomorphic IFT supplies analytic root germ `ω(ε)` and makes it unique against every continuous root germ through `ω₀`.
4. Thus two distinct such germs cannot exist. Combined with all-order triangular nonselection, analytic perturbative QNM-clock selection is exhausted.

Scope: nonanalytic zero-coupling behavior and remote strong-coupling exceptional points survive.

## No-go closure

- **Exact killing theorem:** `d4HBAnalyticPerturbativeQNMClockAndCollisionRouteKilled`.
- **Positive survivor:** exact pole germ exists uniquely and off-wall partner doublet stays resolved.
- **New insight:** exceptional-point escape cannot originate in analytic weak-coupling BM perturbation; remaining producer must be nonanalytic/strong-coupling or the physical source Ward sign.
- **Novelty audit:** Birmingham--Mokhtari computes exact linear QNMs; 2025--26 exceptional-point papers study tuned toy/phenomenological models. No exact all-order BM source/backreaction germ classification found through 2026-08.

## Lean

- Module: `GaloisForLFunctions.RHTower.ThetaCuspHawkingBMAnalyticNontriangularResonanceCollisionNoGo`
- Main intermediate: `exists_unique_d4BMXiGaugeFixedTotalPeriodAllOrderReturnedJostPoleGermMinus`
- Direct `lake env lean`: PASS
- Targeted `lake build`: PASS (`12542` jobs)
- Axioms: `propext`, `Classical.choice`, `Quot.sound`
- Umbrella: wired; full umbrella not built
- Lint: new module reachable; repository lint fails only unrelated pre-existing unwired modules
