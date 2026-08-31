# Shared-Ward channel-resolved Gamma naturality no-go (2026-08-31)

Formalized module:
- formal/GaloisForLFunctions/RHTower/SourceGammaChannelResolvedNaturalityNoGo.lean
- imported by formal/GaloisForLFunctions/RHTower.lean

Main result:
- sharedWardChannelResolvedGammaNaturalityRouteKilled

Mathematics:
- Pair the genuine Calderon--Witt inverse-Gamma reporters with independently fitted archimedean components at primes 2 and 3.
- On the two prime--archimedean Green boundaries, reporter values are exactly
  (0, 2^(-t)-3^(-t)) and (3^(-t)-2^(-t), 0).
- Matching-coordinate/projected naturality holds for every real horizontal grade t, so direct-sum channel separation is unconditional and nonselective.
- Joint full-output naturality holds iff the cross leak vanishes, iff 2^(-t)=3^(-t), iff t=0.
- At t=2 Re(rho)-1 on actual Xi support, universal projected naturality is unconditional; universal joint naturality is equivalent to RH and to the common HB/FZZ-P/PW-B/RBH Ward endpoint.

Route kill:
- Direct-sum/channel-resolved source naturality cannot be the missing shared Ward producer.
- Exact survivor: an irreducible cross-prime source law must annihilate the cross-channel leakage before channel projection or scalarization.

Verification:
- direct lake env lean check passed.
- targeted lake build GaloisForLFunctions.RHTower.SourceGammaChannelResolvedNaturalityNoGo passed (12237 jobs).
- axiom audit on four main theorems: only propext, Classical.choice, Quot.sound.
- formal_tools research indexes the theorem and umbrella.
- global lint failure only on four unrelated pre-existing unreachable modules: SuzukiCheckpointChebyshevMassErrorWeld, CompactFormationFolnerRankEscape, EulerAutonomousPolynomial, RittLogDerivativeEigen.
- temporary files deleted; no own Lean process remains.
- frontier map was read only for this work; its dirty status pre-existed.

Cards:
- docs/drafts/pipeline/3-formalized/shared-ward-channel-resolved-gamma-naturality-no-go.md
- docs/drafts/pipeline/5-failed/shared-ward-channel-resolved-source-naturality.md

Novelty audit:
- internal corpus had scalar shared-ghost rigidity and adjacent cross-prime/operator constructions, but not this projected-vs-joint exact dichotomy.
- bounded external primary-source audit checked Deninger 2018 arithmetic dynamical systems, Deninger 2025 rational Witt vectors, and Connes--Consani 2019 scaling Hamiltonian; no exact collision found.