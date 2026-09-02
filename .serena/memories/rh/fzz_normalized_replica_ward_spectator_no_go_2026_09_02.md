# FZZ normalized replica-Ward spectator no-go (2026-09-02)

- Killed direct route: normalized Halder–Jafferis replica-area Ward profile → external-leg Gamma momentum-delay saturation → divisor passivity → RH.
- Reason: for A(δ,P)=G(P)C(δ,P), (∂δA)/A=(∂δC)/C, so every δ-independent external factor is invisible.
- Admissible gauge H_c(s)=exp(-c(s-1/2)^3) is entire, nonzero, Schwarz-compatible, reciprocal under s↦1-s, centered at 1, and unit-modulus on Re(s)=1/2. On s=1/2+iP it adds phase cP^3 and delay 3cP².
- For P≠0, choose c=(D(0)-D(P))/(3P²): gauged delay saturates at P while c=0 does not, with identical full normalized replica-Ward profile. Hence no uniform selector from that profile to saturation.
- Positive survivor: mixed ∂P∂δ correlator or source-fixed/asymptotically fixed phase frame.
- Lean: `GaloisForLFunctions/RHTower/FZZCigarParityExternalBRSTNormalizedReplicaWardSpectatorNoGo.lean`; final theorem `fzzHJNormalizedReplicaWardExternalGammaSpectatorRouteKilled`.
- Card: `docs/drafts/pipeline/3-formalized/fzz-normalized-replica-ward-external-gamma-spectator-no-go.md`.
- Facts ledger: `docs/drafts/pipeline/1-in-progress/rh-four-route-proof-graph-status.md`.
- Verification: direct `lake env lean` PASS; targeted `lake build GaloisForLFunctions.RHTower.FZZCigarParityExternalBRSTNormalizedReplicaWardSpectatorNoGo` PASS (13154 jobs); #print axioms only propext, Classical.choice, Quot.sound. Wired into `GaloisForLFunctions/RHTower.lean`.
