# Theta-cusp Hawking partner-coherence rigidity endpoint (2026-08-23)

New module:
- `formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingPartnerCoherenceRigidityEndpoint.lean`
- wired into `formal/GaloisForLFunctions/RHTower.lean`.

## Research delta

Primary-literature audit:
- Lin--Chen--Good--Nambu, arXiv:2608.11957 (submitted 2026-08-12): moving-mirror history produces additional two-mode squeezing; approximate thermality can coexist with nontrivial self/mutual correlations; local squeezing preserves partner entanglement spectrum while redistributing laboratory correlations.
- Tomitsuka--Yamaguchi--Hotta, arXiv:1906.05009: partner mode depends strongly on detector design.
- Bianchi--Smerlak, arXiv:1404.0602: flux/entropy relation reduces to zero-energy scattering, but entropy/flux does not determine all-pass phase.
- Fewster--Hollands, math-ph/0412028: QEI gives weighted lower bounds, not raw complex-frequency phase rigidity.

Corpus audit rules out intensity-only phase recovery, generic minimum phase, entropy-only rigidity, and generic phase-defect selection. See `mem:route_r/phase_quadrature_frontier_2026_08_06`, `mem:route_r/physical_quadrature_inheritance_audit_2026_08_06`, and `mem:route_r/phase_defect_character_blindness_no_go_2026_08_05`.

## Exact theorem

For shell pair mode
`f_w(u)=thetaCuspHawkingBornPairKernel(u,w-u)=2 i u(w-u) Xi(w)`,
with coherent amplitude `C(w)=∫f_w=(i/3)w^3 Xi(w)` and intensity
`D(w)=∫|f_w|²=(2/15)w^5 Xi(w)^2`:

- `6 normSq(C(w)) = 5 w D(w)`.
- Gram defect `w D(w)-normSq(C(w))=(1/45)w^6 Xi(w)^2`.
- phase dressing by any total-frequency unit phase leaves defect invariant.
- for arbitrary complex detector weight `h`,
  `C_h(w)=2 i XiC(w) ∫ h(u)u(w-u)du`; if geometric split moment is nonzero, detector dark iff `XiC(w)=0`.
- analytic continuation `G(z)=(1/45)z^6 XiC(z)^2` is entire and
  `G(z)=0 ↔ z=0 ∨ XiC(z)=0`.
- RH iff every analytic shell-coherence degeneracy resonance is real.

Labels: [CANDIDATE NEW SCIENTIFIC KNOWLEDGE] [NOVELTY UNVERIFIED] for exact 5/6 coefficient-faithful Hawking law; [PAPER-PROVED] [LEAN-PROVED] for algebra/formalization; [BRIDGE] [OPEN CORE] for RH endpoint.

## Honest boundary

Real-shell Gram positivity is automatic for every Xi and cannot prove RH. This endpoint removes total-frequency phase gauge and detector-choice ambiguity but remains an observer. Missing producer: independent complex-frequency positivity/backreaction-stability law for this same covariance object; identifying an arbitrary Green orbit or imposing minimum phase would be circular/theatrical.

## Verification

- direct `lake env lean GaloisForLFunctions/RHTower/ThetaCuspHawkingPartnerCoherenceRigidityEndpoint.lean`: pass.
- targeted `lake build GaloisForLFunctions.RHTower.ThetaCuspHawkingPartnerCoherenceRigidityEndpoint`: pass.
- key axiom audit: only `[propext, Classical.choice, Quot.sound]`.
- forbidden declarations in new file: none.
- `scripts/formal_tools.py lint`: new module reachable; global lint fails on unrelated/concurrent unreachable `DeningerDynSysWittCharPoints` and `SoninMellinInversion`.
