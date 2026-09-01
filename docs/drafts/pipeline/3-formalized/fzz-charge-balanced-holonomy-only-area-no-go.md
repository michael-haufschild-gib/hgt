# FZZ charge-balanced holonomy-only area no-go

- **ID:** FZZ-P-HOL-BAL-NOGO
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `FZZCigarTorusReplicaNeutrality.lean` · `FZZCigarHigherGenusTwistRedshift.lean` · `FZZCigarParityLinearReplicaAreaHolonomySelector.lean`
- **Statement:** Every charge-balanced replica-area completion whose twist dependence consists only of reciprocal multiplicative β/γ characters is twist-independent, even for an infinite neutral screening tower; no scalar predicate of its output can select zero radial twist.

## Goal

Kill exact FZZ-P chain

`canonical Mellin divisor twist → charge-balanced holonomy-only torus area completion → passivity → Im(twist)=0 → Re(ρ)=1/2 → RH`.

This does not kill full FZZ dynamics: a survivor may use twisted determinants, ghosts, prime forms, branch/localization data, or a marked kernel before Jacobian integration.

## Gates

- [x] 0 → 1 in-progress: source-pure statement, exact chain, algebraic attack
- [x] 1 → 2 fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [x] 2 → 3 formalized: Lean theorem, targeted build green, axioms audited
- [ ] 3 → 4 publication-ready

## Corpus derivation

- `higherGenusBetaTwist_mul_gammaTwist`: `β_n(t) γ_n(t)=1`.
- `torusReplicaTangent`: product rule for differentiated positive/negative screening products.
- `torusReplicaTangent_monodromy_invariant_iff_neutral`: nonzero torus sectors must be charge-balanced.
- `neutralScreeningCoefficient_ne_zero`: every neutral depth survives, so proof must cover an infinite tower.
- `fzzLinearReplicaAreaNormalizedResponse_mellinTorusTwist_le_one_iff`: fixed-twist passivity would close critical-line placement.

## Theorem C-HOL

For a sector with screening counts `p±`, reporter counts `r±`, and
`p+ + r+ = p- + r-`, let its twist-dependent tangent be

`c β^r+ γ^r- · T(β^p+, γ^p-, a β^p+, b γ^p-)`,

where `T` is `torusReplicaTangent` and `a,b,c` are twist-independent. Then the term is exactly `c(a+b)`. Consequently any `tsum` of such sectors is twist-independent without a summability premise. For every scalar predicate `P`, it is impossible that

`P(tower(t)) ↔ Im(t)=0`

for all complex twists `t`.

## Paper proof

**[PROVED HERE]** Put `β=β_n(t)` and `γ=γ_n(t)`. The corpus identity gives `βγ=1`. Expanding the replica product rule in one sector gives

`T(β^p+,γ^p-,aβ^p+,bγ^p-)=(a+b)β^p+γ^p-`.

After multiplying by reporter and scalar factors, the sector is

`c(a+b)β^(p+ + r+)γ^(p- + r-)`.

Charge balance makes both exponents the same natural number `N`; hence the character factor is `(βγ)^N=1`. The term is exactly `c(a+b)`, independent of `t`. Termwise equality implies the same closed form for an arbitrary `tsum`, whether or not the series is summable.

If a predicate of the tower output selected `Im(t)=0`, apply it at `t=0` and `t=i`. The tower values agree, while `Im(0)=0` and `Im(i)=1`, contradiction. Taking the predicate to be any fixed norm passivity bound gives the exact FZZ-P route kill.

## Hostile attacks

- External charged insertions do not evade theorem: their β/γ powers are included as `r±` in total balance.
- Infinite screening does not evade theorem: equality is termwise at every depth.
- Twist-dependent determinants or logarithmic derivatives do evade theorem; they are outside holonomy-only class and form positive survivor.
- Full Jacobian integration can also erase a fixed twist; a viable producer needs marked localization before integration. This stronger integration claim is not part of C-HOL.

## Literature boundary

- Halder–Jafferis, arXiv:2402.00932v3, define fractional-winding area insertion and leave torus one-point problem open.
- Hikida–Schomerus, arXiv:0805.3931, include non-character twist dependence through higher-genus path-integral determinants/ghost/prime-form data. C-HOL intentionally excludes this known survivor.
- Search through 2026-08 found no evaluation of the Halder–Jafferis torus area one-point or this charge-balanced holonomy-only classification.

## No-go closure

- **Exact killing mechanism:** total character exponent is balanced, so reciprocal β/γ factors cancel before summing.
- **Strongest positive survivor:** any viable FZZ-P torus-area producer must contain non-character twist dependence and retain/localize the canonical twist before full Jacobian integration.
- **New insight:** bare holonomy response is an exact receiver, but neutral source completion cannot produce its radial orientation from characters alone.
- **Status:** dependency-closed proof and Lean formalization complete in `FZZCigarParityChargeBalancedHolonomyAreaNoGo.lean`.

## Lean certificate

- Sector cancellation: `fzzChargeBalancedHolonomyAreaTerm_eq`.
- Infinite-tower classification: `fzzChargeBalancedHolonomyAreaTower_eq`.
- Universal value-selector no-go: `not_fzzChargeBalancedHolonomyAreaTower_value_selector`.
- Passivity-selector no-go: `not_fzzChargeBalancedHolonomyAreaTower_passivity_selector`.
- Direct `lake env lean`: PASS.
- Targeted `lake build GaloisForLFunctions.RHTower.FZZCigarParityChargeBalancedHolonomyAreaNoGo`: PASS (`9830/9830`).
- Axioms: only `propext`, `Classical.choice`, `Quot.sound`.
- Umbrella wired. Global lint red only on unrelated unreachable modules; new module is reachable and absent from lint errors.

## Log

- 2026-09-01 — C-HOL frozen after corpus and primary-literature audit.
- 2026-09-01 — paper proof, Lean formalization, targeted build, axiom audit, and wiring complete; promoted to 3-formalized.
