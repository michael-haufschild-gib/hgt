# FZZ pre-correlator support-motion no-go (2026-09-01)

- Primary source: Hikida--Schomerus arXiv:0805.3931 (C.11)--(C.13), (4.18)/(C.18). Moving zeros, Abel--Jacobi twist, and separation Jacobian use μ,z,λ,ϖ,u,y,E,σ,ξ,S,g; radial spin j is absent. j re-enters through Liouville vertex weights in (4.17).
- New class kill: complete pre-correlator support path plus arbitrary prime-form/Jacobian signature, and every postprocessing, are constant along j(P)=-1/2+iP. No predicate selects P=0.
- Positive survivor: append existing source-exact charge-even external-BRST modulus M(P)=-2j(P)/(1-2/k); for k>2, enriched signature is injective in P.
- Killed chain: pre-correlator support motion/Jacobian -> replica-area Ward law -> divisor-mode passivity -> Mellin completeness -> RH.
- Survives: j-weighted modulus/support coupling inside full correlator or higher replica order.
- Lean: `formal/GaloisForLFunctions/RHTower/FZZCigarParitySeparationKinematicSupportRadialBlindnessNoGo.lean`; capstone `fzzTorusSeparationKinematicSupportRadialBlindness_noGo`; umbrella wired.
- Audits: direct Lean PASS; targeted lake build PASS 8841/8841; axioms [propext, Classical.choice, Quot.sound]; no stale Lean. Global lint red only for unrelated pre-existing unreachable modules.
- Cards: `docs/drafts/pipeline/3-formalized/fzz-separation-kinematic-support-radial-blindness.md`; `docs/drafts/pipeline/5-failed/fzz-precorrelator-support-motion-selector.md`.
- Facts status updated: `docs/drafts/pipeline/1-in-progress/rh-four-route-proof-graph-status.md`.