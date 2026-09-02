# FZZ worldsheet replica genus continuation no-go

- **ID:** FZZ-REPLICA-GENUS-NOGO
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:** Literal integer-genus topology cannot produce the nonzero first worldsheet-replica tangent at physical `k > 3`.

## RH chain killed

`literal n-sheeted FZZ surfaces -> transported genus/divisor/homology-cycle observable -> nonzero two-cycle replica passivity -> critical line -> RH`.

## Source and proof

Mori--Sakai--Shigemori, arXiv:2509.21796v3, gives `s'=1/(k-2)` and formal genus `g(delta)=(1-s')delta` for `n=1-delta`. For `k>3`, `0<1-s'<1`; hence `0<g(delta)<1` when `0<delta<=1`, so no literal genus realizes it. Any continuous map from a real neighborhood to `Nat` is locally constant, so every complex observable factoring through literal genus has derivative zero. The formal genus derivative is `1-s'>0`; the exact FZZ divisor/genus lock makes formal loop/divisor-charge derivative `2(1-s')>0`. Contradiction.

## No-go closure

- **Kill:** no continuous literal-genus observable has a nonzero replica tangent.
- **Positive survivor:** analytic continuation of full amplitudes/moduli not factoring through literal genus; fixed-genus cycle selector remains exact.
- **Open core:** derive source-specific passivity from that analytic continuation or another `j`-weighted coupling.

## Lean certificate

- Module: `GaloisForLFunctions.RHTower.FZZCigarParityWorldsheetReplicaGenusContinuationNoGo`
- Capstone: `RHTower.fzzCigarParity_worldsheetReplicaGenusContinuation_noGo`
- Direct `lake env lean`: PASS
- Targeted build: `9828/9828` PASS
- Axioms: `propext`, `Classical.choice`, `Quot.sound`
- Umbrella: wired into `GaloisForLFunctions.RHTower`
- Lint: new module clean/reachable; global failure only pre-existing unreachable modules.

## Gates

- [x] 0 -> 1 source-pure exact chain
- [x] 1 -> 2 dependency-closed paper proof
- [x] 2 -> 3 Lean proof, targeted build, axioms audit
- [ ] 3 -> 4 publication-ready
