# FZZ separation-kinematic support radial blindness

- **ID:** FZZ-SKRB
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `FZZCigarParityFixedSupportQuillenReplicaNoGo`; `FZZCigarParityExternalBRSTBranchChargeNoGo`; Hikida--Schomerus arXiv:0805.3931, (4.17)--(4.18), (C.11)--(C.18)
- **Statement:** Every observable factoring through the pre-correlator torus separation data (moving zeros, Abel--Jacobi twist, prime-form/Jacobian factors) is constant in physical radial momentum; adjoining the charge-even external-BRST modulus restores injectivity.

## Goal

Kill
`pre-correlator support motion/Jacobian → replica-area Ward law → divisor-mode passivity → Mellin completeness → RH`.
The claim is source-pure: (C.11)--(C.18) contain `μ,z,λ,ϖ,u,y` but no radial spin `j`; `j` first re-enters through Liouville vertex weights in (4.17).

## Gates

- [x] 0 → 1 in-progress: exact factorization class and hostile boundary fixed
- [x] 1 → 2 fully-proven: dependency-closed proof below
- [x] 2 → 3 formalized: `fzzTorusSeparationKinematicSupportRadialBlindness_noGo`; targeted build and standard-axiom audit pass
- [ ] 3 → 4 publication-ready

## Approach

Model a physical separated state as kinematics plus `j(P)=-1/2+iP`. Prove the source projection and every postprocessing of it identify all `P`. Then use the existing exact modulus reconstruction theorem to prove the enriched signature is injective. Hostile boundary: no claim about amplitude-weighted support after the Liouville correlator is inserted.

## Paper proof `[PROVED HERE]`

Let `K` be the complete pre-correlator separation record, including its full support path and Jacobian/prime-form data. Equations (C.11)--(C.12) define `K` using `μ,z,λ,ϖ,u,y,E,σ,ξ,S,g`; (C.13) gives its support velocity; (C.18) gives its Jacobian. None contains radial spin `j`. Hence physical states `(K,P)` and `(K,Q)` have identical kinematic projection for every `P,Q`, as does every postprocessing of that projection. If a predicate selected `P=0`, truth at `P=0` would transfer to `P=1`, forcing `1=0`, contradiction.

For the survivor, set `j(P)=-1/2+iP`. At `k>2`, `q=1-2/k` is nonzero and the source-exact even external-BRST modulus is `M(P)=-2j(P)/q`. Thus `-(q/2)M(P)=j(P)`. Equality `M(P)=M(Q)` implies `j(P)=j(Q)` and comparison of imaginary parts gives `P=Q`. Therefore `(K,M(P))` is injective. Radial selection must enter through interaction/modulus weighting (or higher replica data), not separation kinematics.

## No-go closure

- **Exact killing theorem/mechanism:** complete separation kinematics factor through projection forgetting `P`; arbitrary postprocessing remains blind.
- **Strongest positive survivor:** one source-exact even modulus coordinate makes the enriched signature injective for every physical `k>2`.
- **New insight:** moving support and full separation Jacobian are not radial producers; `j` first re-enters through correlator/modulus weights.
- **Status:** formalized in `FZZCigarParitySeparationKinematicSupportRadialBlindnessNoGo`; direct Lean and targeted build pass; `propext`, `Classical.choice`, `Quot.sound` only; umbrella wired; global lint has unrelated pre-existing unreachable modules, not this module

## Log

- 2026-09-01 — conjecture frozen
- 2026-09-01 — hostile audit passed; paper theorem proved
- 2026-09-01 — formalized and audited
