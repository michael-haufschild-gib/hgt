# FZZ neutral conjugate-eigenphase collapse

- **ID:** FZZ-P-NCE
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `FZZCigarParityFixedQuinticEigenphaseCompletion.lean`; `FZZCigarParityKreinEigenpairCofinalEscape.lean`; Halder--Jafferis arXiv:2402.00932v3 (3.26), (3.29)--(3.33)
- **Statement:** Every equal-charge monomial of the balanced conjugate FZZ eigenline pair is `1`; coefficient-only neutralization destroys fixed-quintic phase capacity at every screening depth.

## Goal

Kill `neutralized fixed-quintic coefficient phase -> divisor eigenphase landing -> Mellin completeness -> RH`.

## Gates

- [x] 0 → 1  source-pure: HJ vacuum/area expansion has equal total `W⁺`,`W⁻` count; corpus conjugate eigenline is exactly `star y`
- [x] 1 → 2  complete paper proof; no open dependency
- [x] 2 → 3  `fzzCigarParity_neutralConjugateEigenphaseCollapse_noGo`; direct Lean, targeted build, axioms pass; umbrella wired
- [ ] 3 → 4  publication-ready

## Proof `[PROVED HERE]`

For positive scale, corpus gives `|y_beta|=1` and conjugate coordinate `star y_beta`. Thus every neutral depth satisfies

`y_beta^n (star y_beta)^n=(y_beta star y_beta)^n=|y_beta|^(2n)=1`.

So kernel dressing is unchanged, arbitrary postprocessing sees only the kernel, target `-1` is absent, and neutralized fixed quintic is constant `1`.

## No-go closure

- **Exact killing mechanism:** equal-charge conjugate pairing cancels global eigenline phase uniformly in depth and scale.
- **Strongest positive survivor:** any remaining phase lies in a nonconstant position/prime-form kernel or a charge imbalance compensated by external BRST vertices.
- **New insight:** fixed-quintic phase capacity is erased by physical neutralization; FZZ-P must derive kernel phase incidence, not another global source power.
- **Lean:** `GaloisForLFunctions.RHTower.FZZCigarParityNeutralConjugateEigenphaseCollapseNoGo`; targeted build PASS; axioms `[propext, Classical.choice, Quot.sound]`; indexed and umbrella-reachable.

