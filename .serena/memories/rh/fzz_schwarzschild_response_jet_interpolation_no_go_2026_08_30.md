# FZZ–Schwarzschild response-jet interpolation route kill (2026-08-30)

Formal module: `GaloisForLFunctions.RHTower.ThetaCuspHawkingFZZSchwarzschildResponseJetInterpolationNoGo`.
Card: `docs/drafts/pipeline/3-formalized/fzz-schwarzschild-response-jet-interpolation-no-go.md`.

Exact source classification: with `P(z)=regularizedRiemannZeta(z+2)` and `G(z)=1/Gamma(-z)`, every entire function carrying all factorial-normalized Schwarzschild/FZZ natural-order response samples is uniquely of the form `P + H*G` for an entire `H`. This is theorem `isEntireBlackHoleJetInterpolant_iff_gammaNullDeformation`.

Closed capstone `blackHole_responseJetInterpolation_route_noGo`: for every far-zone scale convention, there is no unique entire interpolation; additionally canonical `P` is not of global minimal exponential type because it has trivial-zeta zeros `-4-2n`. Thus complete perturbative response orders do not select complex-order source data. Surviving route must add off-lattice/nonlocal data or an anisotropic right-half-plane growth law admitting P while excluding all nonzero Gamma-null deformations.

Audits: direct `lake env lean` green; targeted `lake build GaloisForLFunctions.RHTower.ThetaCuspHawkingFZZSchwarzschildResponseJetInterpolationNoGo` green; `#print axioms` only propext/Classical.choice/Quot.sound. Global formal lint sees module via `RHTower.lean` but remains red only because of unrelated pre-existing unreachable modules.