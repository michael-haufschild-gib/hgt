# Source-isogeny atlas transition (2026-08-04)

## Result
Hostile audit killed `SOURCE-POLARIZED-PARA-S-DESCENT` as an RH route: its periodicity leg is already the unconditional graded-`det₂` anomaly counterboundary, while demanding trivial anomaly is RH-bearing.

For prime `p`, depth `e`, `a_s=2 Re(s)-1`, Route-R anomaly `A_(p,e)`, and Route-L mate gain `delta_p=exp(a_s log p)`,
```
Area_(p,e)=-(1-p^-1)^3 p^-e log p
A_(p,e+1)^p=A_(p,e)
A_(p,e+k)^(p^k)=A_(p,e)
A_(p,e)^(p^(e+3))=delta_p^((p-1)^3)
A_(p,e)=1 iff delta_p=1 iff Re(s)=1/2
```
At `p=2,e=0`, `A_2^8=delta_2`; CCM cofinal readout factors through `(A_2-1)(1+...+A_2^7)` with positive second factor.

With positive `c_(p,e)=(1-p^-1)^3 p^-e log p`, Green fracture `D(s)=2 Re(s)-1`, and nonzero source-pointed Calderón–Witt calibrator `tau_p`,
```
log A_(p,e)=c_(p,e) D(s)
c_(p,e) • (D(s) • tau_p)=(log A_(p,e)) • tau_p
D(s) tau_p=0 iff A_(p,e)=1.
```
R/L/CCM/relation-kernel have obstruction rank one. Vector dimension, Kummer depth, route count do not raise atlas rank. Proved source-vanishing rank remains zero.

## Design verdict
Frankenstein proof must assign distinct roles, not concatenate RH criteria:
- horizontal carrier/detector: existing R/L/CCM/Calderón–Witt organs;
- independent unconditional source-zero producer: missing;
- singular admission/domain, non-erasure, completion: route-specific infrastructure.
Exact open core `SOURCE-ZERO-TO-HORIZONTAL-CARRIER`: construct `z_src=0` from genuine arithmetic boundary/residue/incidence/coherence and a coefficient-faithful singular comparison `Phi(z_src at rho)=D_rho tau_p`, preserving provenance and proving non-erasure before scalar trace.

## Files
- `docs/drafts/pipeline/1-in-progress/rh-current-frontier-map.md`
- `docs/drafts/pipeline/1-in-progress/riemann-source-polarized-two-path-descent.md`
- `docs/drafts/pipeline/3-formalized/source-polarized-holonomy-isogeny-atlas-law.md`
- `formal/GaloisForLFunctions/RHTower/PrimeDepthBVWoldSourceDaggerAtlasTransition.lean`
- `formal/GaloisForLFunctions/RHTower/PrimeDepthBVWoldRelationKernelAtlasTransition.lean`

Both modules direct-compile and targeted-build. Axiom audit reports only `propext`, `Classical.choice`, `Quot.sound`. Global lint reaches both task modules and reports no forbidden declarations in them. Repository-wide lint remained nonzero in concurrent worktree; final audit reported unrelated new umbrella omissions `RHTower.Sieve.CoprimeMaximalWindow` and `HTGeometry.StokesEquivariantGlobalWittLaw`.
