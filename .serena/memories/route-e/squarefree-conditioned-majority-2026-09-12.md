# Route E squarefree conditioned majority (2026-09-12)

Formal module: `formal/GaloisForLFunctions/RHTower/RouteESquarefreeConditionedMajority.lean`.

Key capstones:
- `squarefree_singleton_family_mobius_majority`
- `squarefree_power_bounded_invariant_weight_anchor_majority`
- `squarefree_power_bounded_uniform_conditioned_anchor_majority`

Result: for singleton component histories whose squarefree receivers lie in one interval, have at most four distinct receivers per history, and satisfy width `W < A = ∏ a_i`, inactive factors are pairwise coprime, every history has a repeated receiver, all repeated receivers equal one squarefree `nStar`, every history has at most three exceptions, and
`μ(nStar) * Σ_r μ(n_r) ≥ M - 6`.
Any nonnegative family weight invariant under common slot swaps transports this to a fixed-anchor weighted majority inequality. Existing power assumptions discharge bounded support and `W < A`; the literal squarefree/window-conditioned cell has anchor-swap invariance unconditionally.

Whole-chain implication: bounded receiver diversity is terminal in the wrong direction for Route E. Under multiplicative squarefree rigidity it creates overwhelming same-sign bias, not Möbius cancellation. A surviving construction must allow receiver support to grow with slot count and still prove source-invariant multiplicities plus an unsigned Hall/co-degree, co-moving flux, or equivalent source estimate. Signed column-load control remains circular.

Verification:
- `lake env lean GaloisForLFunctions/RHTower/RouteESquarefreeConditionedMajority.lean` passed.
- `lake build GaloisForLFunctions.RHTower.RouteESquarefreeConditionedMajority` passed.
- Axiom audit of the three capstones reports only `propext`, `Classical.choice`, `Quot.sound`.
- No `sorry`, `admit`, `axiom`, `opaque`, or `unsafe` in the new file.
- Umbrella `GaloisForLFunctions/RHTower.lean` imports the module.
- Repository lint is blocked only by unrelated untracked `GaloisForLFunctions.RHTower.ZetaBinomialHalfKaramataLaw` being unreachable from the umbrella.

Research docs:
- `docs/drafts/pipeline/3-formalized/route-e-squarefree-conditioned-majority.md`
- authoritative frontier and universal-law-field status updated.

Related prior memories: `mem:route-e/co-moving-cube-frontier-2026-08-01`, `mem:route-e/replica-orthogonal-vs-component-shuffle-firewall`.