# PA — critical Stokes passive deletion is impossible

- **ID:** PA-critical-stokes-passive-deletion-2026-10-17
- **Stage:** 5-failed
- **Type:** FALSIFIED
- **Source:** PA current-frontier selection; local Lean source. Parent investigation: `../1-in-progress/pa-complete-current-source-passivity-2026-10-17.md`.
- **Statement:** No positive deletion/downweighting of the raw critical Stokes carrier reproduces the complete prime–archimedean moment germ, even with arbitrary node-dependent weights and no residual floor.

## Goal

Determine whether the remaining passive-deletion interface can repair the previously disproved raw/supercarrier constructions. The answer is no. PA itself remains live; this retires one completion mechanism, not the complete-current route.

## Gates

- [x] Well-posed source-defined mechanism; no RH or numerical premise.
- [x] `[PROVED HERE]` Dependency-closed paper obstruction and positive survivor; proof below.
- [x] All 25 declarations verified in Lean; all axiom dependencies are `propext`, `Classical.choice`, `Quot.sound`.
- [x] Final direct module recheck passed; global lint failure recorded below without claiming a pass.
- [ ] Publication/novelty audit: not undertaken, as instructed.

## Approach and paper proof

Let `r_p=p^(-1/2)`, `c_p` be the critical Gamma contraction, `g_(p,e)=(e+1)W_p`, and `x_(p,e)=g_(p,e)^(-2)`.

1. The exact identities `r_p^2=1/p` and `c_p^4=(1+r_p)^4/(8(1+r_p^4))` make `r_p,c_p` algebraic. The inverse-tilt formula is `W_p=a_p log p`, with positive algebraic `a_p=(1+r_p^2)/(r_p c_p(1-r_p))`.
2. Equality between gaps from different primes would make their logarithm ratio algebraic. The corpus's unconditional Gelfond–Schneider theorem excludes this. At one prime, positivity of `W_p` separates depths. Thus the squared reciprocal nodes are injective.
3. The source-edge identity gives residue `I_(p,e)=b_(p,e)g_(p,e)=log(p)r_p^(e+1)`. It lies below `log(p)r_p<1`: for `t=log(p)/2`, the exponential quadratic bound gives `exp(t)>=1+t+t^2/2>2t`. Hence each raw singleton has mass `w_(p,e)=2I_(p,e)x_(p,e)<2x_(p,e)`. Off the raw node set its mass is zero. Therefore raw singleton mass is below `2x` for every `x>0`.
4. A Xi zero copy and its distinct functional-equation reflection contribute the same positive thermal node `x`, each with mass `x`. Thus the canonical Xi measure has at least mass `2x` at every thermal node, unconditionally. Raw Stokes singleton mass is strictly smaller at every such node.
5. Existing unrestricted moment-carrier rigidity identifies every complete positive source witness with the canonical Xi measure. It therefore cannot be dominated by the raw Stokes measure. Local compact Markov equality gives the moments of that same measure via the already-proved derivative formula. This refutes both the passive-deletion and purely negative-correction interfaces.
6. Positive summable thermal nodes tend to zero. Their range is infinite: a finite closed range would contain the limit zero, contradicting positivity. Consequently every exact positive witness must increase infinitely many distinct singleton masses. Any repair preserving all but finitely many singleton masses fails.
7. Combining the new non-domination result with the existing positive-supercarrier obstruction proves order incomparability: exact positive completion requires both added and removed mass.

## No-go closure

- **Exact killing theorem:** `RHTower.not_gammaSewnMobiusApertureStokesCriticalPassiveDeletionCompletion`; the equivalent negative-correction interface is also refuted.
- **Strongest positive survivor:** `RHTower.IsPrimeArchMomentWitness.infinite_criticalStokes_atom_deficit`, together with `criticalStokesCarrier_incomparable_of_completedSeamMomentGerm`. These specify the required infinitely many increases and the simultaneous necessity of removal. They do not merely restate the negative conclusion.
- **New insight:** Zeroth/first-moment repair cannot extend by deleting arbitrary raw mass. Every canonical Xi atom exceeds the raw carrier's available mass there. Completion must redistribute mass across infinitely many atoms. This does not rule out non-diagonal spectral transport, arbitrary unbounded reweighting, or a different source construction.
- **Lean module:** `formal/GaloisForLFunctions/RHTower/GammaSewnMobiusApertureStokesCriticalPoleCapacity.lean`.
- **Status:** Paper proof closed; exact survivor and obstruction verified with standard axioms. No extra analytic premise, RH premise, heartbeat increase, or external novelty claim. Final direct check passed; global lint remains blocked by unrelated work as detailed below.
- **Goal credit:** No qualifying RH-route contribution claimed; the complete-current arithmetic sign remains open.

## Verification

The initial direct module check passed. The final source after removing two unused simp arguments was checked in a byte-matching `/tmp` axiom-audit copy: 25 declarations, no warnings/errors, standard axioms only. SHA-256: `87ad1d53741960a2ebdeee44b462a9778f680002c2ade1ae2c0d5b1afb2d0cb3`. Umbrella import added; generated formal indexes refreshed.

`scripts/formal_tools.py lint --check-generated` exited 1: 381 existing large-file warnings, unrelated unwired `RHTower.WeilLineIntegralAnyAbscissa` and `HTGeometry.CayleyDenseResolvent`, and `formal/LEAN_API.md` drift during concurrent edits. Indexes refreshed afterward. No global lint pass or full/umbrella build claimed.

Final direct command from `formal/`: `lake --old env lean GaloisForLFunctions/RHTower/GammaSewnMobiusApertureStokesCriticalPoleCapacity.lean`, exit 0 with no diagnostics. Nine owned scratch files removed; absence verified. No owned process remains.

## Log

- 2026-10-17 — Exact source audit found raw/supercarrier mass obstructions and existing two-jet repair. Gelfond–Schneider pole separation exposed a stronger all-atom obstruction. Dependency-closed paper proof and exact positive survivor formalized; failed mechanism separated from live PA route.
