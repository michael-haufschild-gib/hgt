# Apex independence: nontrivial ladder charges lie outside every torsion reading of prime flux

- **ID:** apex-independence-ladder-vs-prime-flux
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) — `[PROVED HERE]`, axiom-clean
- **Source:** composition of `WeldChargeFaithfulness` (prime-flux torsion collapse) + `WeldChargeConnecting` (realization of every deck charge as a connecting-map value) + `XiDeckCharge` (ξ ladder observable)
- **Statement (delivered):** `[PROVED HERE]`
  - Every `ZMod n`-valued charge on real weld cohomology sends every prime-flux class to `0` (`primeFluxHom_charge_eq_zero`); the charge image of the prime-flux lattice is `{0}`.
  - A nontrivial deck/ladder charge `wCharge n idx ≠ 0` is unequal to every such reading (`nontrivial_wCharge_ne_primeFlux_charge`) and does not lie in that image.
  - Every nontrivial charge is still realized as `chargeConnectingHom T n (obstructionClass ω)` for an explicit integer symplectic weld class, and that value misses every prime-flux torsion reading (`exists_weldClass_realizing_nontrivial_outside_primeFlux`).
  - Capstone `apex_independence`: image zero ∧ miss ∧ realization, for every nontrivial index.
  - ξ instance: if `xiDeckCharge k ρ ≠ 1` (equivalently `2^k ∤ ord_ρ ξ`), the additive ladder charge at `ρ` lies outside every torsion image of prime flux (`xi_nontrivial_ladder_charge_ne_primeFlux_charge`, `xi_apex_independence`). No off-line zero is assumed.

## Goal
Make precise the independence of the two apices already named in `WeldChargeConnecting`: ladder/deck charge versus prime-flux weld class, under every torsion connecting/charge map. Blocks the route "read nontrivial ladder charges off prime-flux classes via a torsion charge."

## What is / is not claimed
- **Is:** value-level independence of nontrivial ladder charges from the torsion image of `primeFluxHom`.
- **Is not:** RH; existence of off-line zeros; identification of a specific `𝓜⁺` class with `ξ`'s ladder; a claim that primes do not determine zeros in the explicit-formula sense (distributional pairings are a different channel).

## Lean
- Module: `formal/GaloisForLFunctions/RHTower/ApexIndependence.lean`
- Umbrella: imported by `formal/GaloisForLFunctions/RHTower.lean`
- Capstones: `apex_independence`, `xi_apex_independence`, `nontrivial_wCharge_ne_primeFlux_charge`, `exists_weldClass_realizing_nontrivial_outside_primeFlux`
- `#print axioms` = `{propext, Classical.choice, Quot.sound}` (standard mathlib only)
- `lake env lean GaloisForLFunctions/RHTower/ApexIndependence.lean` green

## Novelty / significance (register)
- **Formal content:** composition theorem packaging collapse + realization + ξ ladder dictionary. The ingredients were already banked; the contribution is the joint independence statement and the ξ instance.
- **Dual gate:** significant as a method-limitation on torsion readings of prime flux; novelty is packaging/bridge inside this formalization, not a new classical zeta theorem.

## Log
- 2026-07-08 — formalized in `ApexIndependence.lean`; build green; card opened in 3-formalized/new.

## Update: strong (class-level) form (2026-07-08)

Added to the same Lean module:

- `ladderWeldClass idx := weldClassHom (idx : ℝ)` — specific class in real `H²`
- `connectingHom_ladderWeldClass` — connecting value = `idx`
- `ladderWeldClass_notMem_primeFlux_image` — for `idx ≠ 0`, class ∉ `range primeFluxHom` in `H²` (uses `weldClassHom_injective` + `primeLog_indep_mod_one`)
- `strong_apex_independence` — capstone
- `xiLadderWeldClass` / `xi_strong_apex_independence_of_zero` — at any zero of `ξ`, the order class is outside prime flux in `H²`

**Dual-gate note:** stronger than torsion packaging; still a composition of banked `{1}∪{log p}` independence with the weld embedding under a native name. Not a distributional no-go; not a geometric monodromy construction from `ξ` beyond the conversion-constant dictionary.
