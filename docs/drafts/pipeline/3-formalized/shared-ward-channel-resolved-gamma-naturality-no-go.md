# Shared-Ward Channel-Resolved Gamma Naturality No-Go

- **ID:** SG-CR
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `SourceGammaNaturalitySharedGhostProducer` plus HB/FZZ-P/PW-B/RBH shared Ward transmutations
- **Statement:** Matching-coordinate naturality of the canonical two-channel inverse-Gamma reporter holds at every horizontal grade, while joint full-output naturality holds exactly at grade zero and globally exactly under RH.

## Goal

Kill channel-resolved direct-sum source/Gamma naturality as the missing producer in

`source/Gamma law -> common Ward charge zero -> HB darkness = FZZ-P equilibrium = PW-B balance = RBH balance -> RH`.

## Result

For grade `t`, pair the two genuine Calderon--Witt prime--archimedean reporters with independently fitted archimedean components `2^(-t)` and `3^(-t)`. On the prime-two and prime-three Green boundaries, the pair reporter reads

`(0, 2^(-t) - 3^(-t))` and `(3^(-t) - 2^(-t), 0)`.

Therefore:

1. projecting each source boundary to its matching prime channel gives exact naturality for every `t`;
2. retaining both coordinates gives joint naturality iff `2^(-t)=3^(-t)`, hence iff `t=0`;
3. after `t=2 Re(rho)-1`, universal projected naturality is unconditional, while universal joint naturality is equivalent to RH;
4. universal joint naturality is equivalent to the conjunction of HB unit source-FE gain, FZZ-P information equilibrium, PW-B partner balance, and RBH multiplicity-leading balance.

Main closed certificate:

`sharedWardChannelResolvedGammaNaturalityRouteKilled`.

## Proof

The two boundary evaluations follow from the exact scalar prime--archimedean defect formula `g_p(t)-c`. Independent choices `c=g_2(t)` and `c=g_3(t)` kill the matching coordinates. If both full pair values vanish, either cross coordinate gives `g_2(t)=g_3(t)`. The existing positive local-ghost Ward laws then construct one shared ghost at primes two and three; two-prime rigidity forces `t=0`. Conversely `t=0` makes both local ghosts one. Specialization to Xi support and the four-route equivalences use already formalized exact receiver theorems.

## No-go closure

- **Exact killing theorem/mechanism:** independently fitted direct-sum channels hide the cross-prime mismatch and are natural on their own projections for every grade.
- **Strongest positive survivor:** cross-channel leakage is exactly the oriented two-prime mismatch. Keeping it makes joint naturality the full shared Ward/RH endpoint.
- **New insight:** source naturality becomes selective only after an irreducible cross-prime comparison. Output dimension or retained labels alone do not help; a viable producer must couple primes before channel projection or scalarization.
- **Status:** paper proof dependency-closed; Lean formalized and umbrella-wired. Frontier map unchanged.

## Novelty audit

Internal corpus searches found scalar shared-ghost rigidity, all-cross-prime incidence, global signed-cancellation no-gos, and PW rescaling-gauge no-gos, but no exact projected-versus-joint two-channel Green-boundary dichotomy.

External primary-source search through 2026-08-31 found adjacent Witt-vector and operator frameworks but no theorem with this exact Calderon--Witt/Gamma channel classification:

- Christopher Deninger, *Dynamical systems for arithmetic schemes*, https://arxiv.org/abs/1807.06400
- Christopher Deninger, *Rational Witt vectors and associated sheaves*, https://arxiv.org/abs/2508.05329
- Alain Connes and Caterina Consani, *The Scaling Hamiltonian*, https://arxiv.org/abs/1910.14368

Novelty claim remains bounded to searched corpus and literature, not absolute priority.

## Verification

- `lake env lean GaloisForLFunctions/RHTower/SourceGammaChannelResolvedNaturalityNoGo.lean` — PASS
- `lake build GaloisForLFunctions.RHTower.SourceGammaChannelResolvedNaturalityNoGo` — PASS (targeted leaf only)
- axiom audit of four main theorems — only `propext`, `Classical.choice`, `Quot.sound`
- umbrella import added; no full umbrella build
- `scripts/formal_tools.py lint` indexes this module through the umbrella; global failure is confined to four unrelated pre-existing unreachable modules (`SuzukiCheckpointChebyshevMassErrorWeld`, `CompactFormationFolnerRankEscape`, `EulerAutonomousPolynomial`, `RittLogDerivativeEigen`)

## Log

- 2026-08-31 — conjecture frozen, hostile proof completed, formalized in Lean.
