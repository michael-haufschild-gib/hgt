# Completed-exponent line-reflection blow-up transport

- **Stage:** 3 — formalized in Lean 4
- **Route:** L — Deninger/Green/Hodge source descent
- **Status:** [LEAN-PROVED] [UNCONDITIONAL] [NOT RH]
- **Date:** 2026-08-11
- **Module:**
  `formal/GaloisForLFunctions/RHTower/Deninger/DeningerExponentLineReflectionBlowupTransport.lean`
- **Paper proof:**
  `../2-fully-proven/new_scientific_knowledge/deninger/deninger-completed-exponent-line-reflection-blowup-transport.md`

## Formal theorem package

Lean constructs the completed exponent source

`EΞ(z,s) = ξ(s) / ξ(zs)`

and its forced open-strip source involution

`(z,s) ↦ (conj ((1-zs)/(1-s)), 1-conj s)`.

The module proves:

1. reflected product coordinate is exactly `1-conj(zs)`;
2. completed exponent activation is conjugated by transport;
3. transport is involutive on full two-variable open-strip source;
4. induced exceptional direction sends zero face to zero face and marked pole `-rho` to
   `-(1-conj rho)`;
5. its anti-linear coefficient is uniquely forced by marked-pole transport;
6. actual Xi multiplicity is preserved;
7. full exceptional profile is conjugated on every regular direction;
8. exceptional direction transport is involutive over line-reflected divisor;
9. exact all-grade Gamma-six tame reader is reflection-odd.

All theorem statements are closed and unconditional. No RH premise, added axiom, target-domain
membership assumption, or numerical computation is used.

## Frontier effect

Local singular reflection transport is no longer open: it exists as an explicit involution of the
source before specialization, not only as a divisor-side pole displacement. This does not prove
global trace-ideal preservation for the complete corrected Möbius tensor remainder and does not
prove fixed-reader cyclicity. Those remain Route L's RH-bearing steps.

## Audit

- [x] `lake env lean GaloisForLFunctions/RHTower/Deninger/DeningerExponentLineReflectionBlowupTransport.lean`
- [x] axiom audit: only `propext`, `Classical.choice`, `Quot.sound`
- [x] `lake build GaloisForLFunctions.RHTower.Deninger.DeningerExponentLineReflectionBlowupTransport`
- [ ] repository lint reachability
