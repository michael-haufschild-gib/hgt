# FZZ same-scale Laurent radial critical-sector no-go

- **ID:** FZZ-JSRN
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:** No fixed same-scale Laurent monomial fusion of the FZZ Fermi radial coordinate and fixed-quintic phase is both unit-sector complete and injective in positive scale.

## RH proof chain closed negatively

Audited chain:

`literal FZZ parity-delay source → same-scale Fermi radial/quintic scalar fusion → dyadic Mellin character of every source mode → critical eigenline incidence → FZZ-P balance → SharedFourRouteWardEndpoint → RH`.

The same-scale scalar Laurent-fusion arrow is impossible. A viable FZZ-P landing must retain the radial coordinate separately or use genuinely non-Laurent dynamics.

## Result

For `beta>0`, write `r(beta)` for the source Fermi radial coordinate and `q(beta)` for the fixed-quintic phase. Existing source theorems give `0<r(beta)<1`, `|q(beta)|=1`, full unit-circle capacity of `q`, and an explicit two-scale collision of `q`.

The new theorem exhausts fixed Laurent sectors:

- positive exponent: `|r^(n+1) q|<1`, so no unit target is admitted;
- negative exponent: `|r^(-(n+1)) q|>1`, so no unit target is admitted;
- zero exponent: every unit target is admitted, but scale injectivity fails by the explicit quintic collision.

Stronger positive classification: an exact match to the dyadic Mellin character forces strict left half-plane, critical line, or strict right half-plane according to positive, zero, or negative radial exponent.

## Lean certificate

- Module: `GaloisForLFunctions.RHTower.FZZCigarParitySameScaleLaurentCriticalNoGo`
- Main theorem: `fzzCigarParitySameScaleLaurentCriticalRouteKilled_all`
- Chamber theorem: `fzzCigarParitySameScaleLaurentEncoding_eq_dyadicMellinCharacter_forces_sector`
- Umbrella: imported by `GaloisForLFunctions.RHTower`
- Direct check: `lake env lean GaloisForLFunctions/RHTower/FZZCigarParitySameScaleLaurentCriticalNoGo.lean` passed.
- Targeted audit: `lake build GaloisForLFunctions.RHTower.FZZCigarParitySameScaleLaurentCriticalNoGo` passed (`9766/9766`).
- Axioms on chamber theorem, three killing branches, and capstone: only `propext`, `Classical.choice`, `Quot.sound`.
- Corpus index: `scripts/formal_tools.py research` returns the new declarations.
- Lint: new module has no forbidden declaration; repository lint stops on unrelated pre-existing umbrella reachability error for `GaloisForLFunctions.HTGeometry.ZeroFreeRadiusSelection`.

## Novelty audit

Internal search found fixed-phase collision, pair-valued joint encoding, and independent-scale chamber trichotomy, but no fixed same-scale Laurent scalar-fusion exhaustion. External searches through 2026-08-31 found no counterpart in FZZ/cigar literature. Closest primary background: [Hikida--Schomerus](https://arxiv.org/abs/0805.3931), [Creutzig--Hikida--Rønne](https://arxiv.org/abs/1012.4731), [Giveon--Itzhaki--Kutasov](https://arxiv.org/abs/1603.05822). Novelty claim is limited to this exact source carrier and Laurent fusion class.

`[PROVED HERE] [LEAN-PROVED] [FZZ-P ROUTE-CLASS KILL]`
