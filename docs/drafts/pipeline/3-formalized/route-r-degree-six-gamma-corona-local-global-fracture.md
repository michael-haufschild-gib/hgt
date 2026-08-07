# Route R degree-six Gamma-corona local/global fracture

- **ID:** `route-r-degree-six-gamma-corona-local-global-fracture`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Paper proof:** `../2-fully-proven/route-r-degree-six-gamma-corona-local-global-fracture.md`
- **Scientific status:** `[LEAN-PROVED] [CORPUS-NEW EXACT BRIDGE] [NOT RH]`

## Formal result

Lean proves unconditionally:

1. the fixed degree-six BV--Green boundary equals centered rate times a strictly positive
   hyperbolic-sinc gauge;
2. an exact division-free value identity carries that boundary to the ordered `(2,3)`
   Gamma/Cartier port;
3. the literal coordinate-local source action lands in the finite arithmetic core and therefore
   vanishes in the algebraic singular corona;
4. fixed physical global action minus local source action is exactly the retained Cartier port on
   the nonzero corona horizon;
5. global/local equality is equivalent to the requested fixed-reader equality
   `R_phys(B_6)=tau_6(B_6)`.

This isolates one remaining RH-strength statement: construct a coefficient-faithful all-prime
globalization law intertwining coordinate-local source action with fixed full-support physical
action.  No critical-line or RH premise is used in this module.

## Lean certificate

- Module: `formal/GaloisForLFunctions/RHTower/RouteRDegreeSixGammaCoronaLocalGlobalFracture.lean`
- Umbrella: `formal/GaloisForLFunctions/RHTower.lean`
- Rebuilt artifact:
  `formal/.lake/build/lib/lean/GaloisForLFunctions/RHTower/RouteRDegreeSixGammaCoronaLocalGlobalFracture.olean`
- Artifact timestamp: 2026-08-07 13:48:53; source timestamp: 2026-08-07 12:51:37
- Forbidden declarations: none

## Principal theorem names

- `routeRDegreeSixBVGreenGammaCartier_divisionFreeComparison`
- `deningerCalderonWittCrossPrimeSingularCoronaClass_localPacketAction`
- `routeRTwoThreeGammaCorona_global_sub_local_eq_port`
- `routeRTwoThreeGammaCorona_global_eq_local_iff_port_eq_zero`
- `routeRTwoThreeGammaCorona_global_eq_local_iff_degreeSixFixedReaderEquality`

## Gates

- [x] dependency-closed paper proof
- [x] unconditional Lean formalization
- [x] umbrella wiring
- [x] rebuilt artifact newer than source
- [ ] independent all-prime local/global intertwining
- [ ] RH

## Log

- 2026-08-07 — exact bridge, local source annihilation, and local/global fracture formalized.
