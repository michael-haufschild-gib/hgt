# CCM infinite-Fock reporter sign no-go

- **ID:** ccm-infinite-fock-reporter-sign-no-go
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:** Every literal prime-power atom has PSD actual-source Fock kernels whose exact projective reporter is positive at outer phase `2π` and negative at outer phase `π`; hence pointwise PSD cannot supply the missing source sign.

## Goal

Kill the chain

`actual-source infinite PSD Fock carrier -> pointwise nonnegative logarithmic reporter -> fixed source Ward/orientation -> shared HB/FZZ-P/PW-B/RBH receiver extinction -> RH`.

The source and reporter are the exact corpus constructions, not an abstract replacement.

## Gates

- [x] 0 → 1 in-progress: exact source-pure statement and route passport
- [x] 1 → 2 fully-proven: dependency-closed proof below, `[PROVED HERE]`
- [x] 2 → 3 formalized: target Lean module and audit
- [ ] 3 → 4 publication-ready

## Theorem and proof `[PROVED HERE]`

Fix a prime-power atom `n = p^(e+1)`. Then `n > 1`, its critical Mellin weight is positive, and `log n > 0`. Put

`ξ+ = 1/log n`, `ξ- = 1/(2 log n)`.

The exact corpus identity is

`Re Z_n(ξ) = cos(2π log(n) ξ) C_n(ξ) + sin(2π log(n) ξ) S_n(ξ)`,

where `C_n(ξ) > 0` whenever the atom weight is positive and `ξ != 0`. At `ξ+`, the outer phase is `2π`, so `Re Z_n(ξ+) = C_n(ξ+) > 0`. At `ξ-`, it is `π`, so `Re Z_n(ξ-) = -C_n(ξ-) < 0`.

The global coherent-Fock kernel is PSD at every frequency. Its exact positive/negative probe ratio satisfies `R_n(ξ) = exp(2 Re Z_n(ξ))`, equivalently `(1/2) log R_n(ξ) = Re Z_n(ξ)`. Therefore `R_n(ξ+) > 1` and `R_n(ξ-) < 1`, despite PSD at both points. A universal implication from pointwise PSD to reporter nonnegativity (or `R >= 1`) is false. ∎

## No-go closure

- **Exact killing mechanism:** literal prime-power phase straddle inside the already-assembled global PSD kernel.
- **Strongest positive survivor:** exact PSD/projective tomography remains valid and retains source phase, but sign extraction must be nonlocal across frequency or use an independent source-specific Ward/phase law.
- **New insight:** infinite-rank nonlinear Fock assembly solves carrier loss but not orientation; positivity survives while its exact logarithmic coordinate changes sign.
- **Novelty audit:** corpus search found the PSD carrier, projective ratio identity, and positive cosine profile separately, but no sign-straddle/no-go theorem. August-2026 Suzuki and Connes–Consani–Moscovici work studies localized Weil positivity and spectral convergence, not this exact matched-source Fock reporter obstruction. Generic coherent-kernel positivity alone is known; the arithmetic sign-straddle and RH-route consequence are new here.

## Lean certificate

- Module: `GaloisForLFunctions.RHTower.CCM.CCMActualHeadMatchedInfiniteFockReporterSignNoGo`
- Positive survivor: `ccmActualHeadMatchedPhaseGlobalProjectiveFockPrimePowerReporterSignStraddle`
- Kills: `ccmActualHeadMatchedPhaseGlobalProjectiveFockPointwiseReporterPositivityRouteKilled`, `ccmActualHeadMatchedPhaseGlobalProjectiveFockPointwiseRatioLowerBoundRouteKilled`
- Audit: direct `lake env lean` PASS; target-only `lake build` PASS; axioms `[propext, Classical.choice, Quot.sound]`; umbrella wired. Global lint has only unrelated concurrently unwired modules.
