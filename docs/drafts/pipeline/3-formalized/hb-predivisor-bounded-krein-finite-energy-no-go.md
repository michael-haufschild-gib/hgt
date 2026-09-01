# HB pre-divisor bounded-Krein finite-energy no-go

- **ID:** HB-KREIN-L1
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `rh-current-frontier-map.md` (read-only) · HB pre-divisor compensation survivor
- **Statement:** No finite-energy Hilbert feature field with any bounded operator metric realizes the exact HB pre-divisor cancellation kernel on `(0,1/2)^2`.

## Goal

Kill HB chain edge `exact compensation kernel → bounded indefinite/Krein source field → finite-energy physical producer`. This removes indefinite signature as a rescue of the positive-Gram hard-edge obstruction; unbounded/rigged, renormalized/distributional, and hard-edge-domain-excluding carriers survive.

## Gates

- [x] 0 → 1  in-progress: exact corpus kernel, named survivor, dependency-closed attack
- [x] 1 → 2  fully-proven: `[PROVED HERE]`; Cauchy--Schwarz plus exact hard-edge divergence
- [x] 2 → 3  formalized: `d4HBPreDivisorFiniteEnergyBoundedKreinRouteKilled`; direct Lean and targeted build pass; axiom audit pass
- [ ] 3 → 4  publication-ready: standalone theorem/proof/certificate

## Approach

Let `S(x)` be exact susceptibility, `K(x,y)` its polarization, `Φ(x)` a Hilbert feature, and `J` any bounded operator with `⟪Φ(x),JΦ(y)⟫=K(x,y)`. Corpus proves `x⁻² ≤ S(x)` and `∫₀^{1/2}S=∞`. On diagonal,

`S(x)=Re⟪Φ(x),JΦ(x)⟫ ≤ |⟪Φ(x),JΦ(x)⟫| ≤ ‖J‖‖Φ(x)‖²`.

Finite `∫‖Φ‖²` would make `S` integrable, contradiction. No self-adjointness, involution, finite index, or dimension premise is used.

## No-go closure

- **Exact killing theorem/mechanism:** bounded metric plus Cauchy--Schwarz transfers finite feature energy to finite kernel-diagonal energy, contradicting inverse-square hard-edge divergence.
- **Strongest positive survivor:** any indefinite realization must use unbounded/rigged metric or infinite hard-edge feature energy, or leave function-valued scalar pairing through renormalization/distributions/domain exclusion.
- **New insight:** indefinite signature cannot cure HB hard-edge energy; only loss of bounded metric or ordinary finite energy can.
- **Status:** internal corpus search found positive-Hilbert finite-energy and abstract split-Krein results, but not their bounded-indefinite combination. General reproducing-kernel Krein linearization is standard (Gheondea, arXiv:1309.2393); exact HB hard-edge exclusion found no literature precedent in targeted search through 2026-08. Lean module `ThetaCuspHawkingPreDivisorFiniteEnergyBoundedKreinNoGo`; axioms only `propext`, `Classical.choice`, `Quot.sound`. Global lint reaches only unrelated pre-existing unwired modules.

## Log

- 2026-09-01 — `[PROVED HERE] [LEAN-PROVED]`; targeted module build passes.
