# FZZ-P diagonal-flow detector horizon (2026-08-28)

Formalized in `formal/GaloisForLFunctions/RHTower/FZZCigarParityDiagonalFlowDetectorHorizon.lean`; imported by `formal/GaloisForLFunctions/RHTower.lean`.

For positive beta, HC5's source-gap stabilized generator
`A_*=[[P,0],[-PQ/R,0]]` has exact flow
`Phi_t(u1,u2)=(exp(Pt)u1,u2-k_beta(t)u1)`,
where `k_beta(t)=(Q/R)(exp(Pt)-1)`.
It is a semigroup and equals `I+((exp(Pt)-1)/P)A_*`.

Pullback of unit second-coordinate energy has HC3 Hermitian coefficients
`(k^2,-k,0,1)`, hence universally separates reciprocal-radius carriers iff
`k^2<=1`. For nonnegative time this is exactly
`t<=T_beta=log(1+R/Q)/P`. Horizon is positive, `k(T_beta)=1`, and boundary
remains separating. Every later time is non-separating. Throughout the closed
window, evolved Mellin readings agree under critical-line reflection iff
`rho.re=1/2`.

Cards:
- `docs/drafts/pipeline/3-formalized/fzz-p-diagonal-flow-detector-horizon.md`
- `docs/drafts/pipeline/5-failed/fzz-p-late-time-diagonal-flow-matching-no-go.md`

Verification: direct `lake env lean`, target-only `lake build`, scoped forbidden-token scan,
`git diff --check`, and axiom audit passed. Axioms only `propext`,
`Classical.choice`, `Quot.sound`. Frontier map untouched.
Novelty status after corpus and literature audit: no exact collision located; not absolute priority claim.