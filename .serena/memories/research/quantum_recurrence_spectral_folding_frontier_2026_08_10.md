# Quantum recurrence frontier — spectral folding/addressability (2026-08-10)

Main paper-proof card: `docs/drafts/pipeline/2-fully-proven/spectral-phase-folding-locality-addressability-law.md`.
Parents: `centralizer-phase-bandwidth-shortcut-extraction-law.md`, `path-local-centralizer-tangent-rigidity-law.md`.

Proved on paper, Lean deferred during corpus refactor:

- Generic path-local centralizer rigidity plus only two rationally independent anchored gaps implies phase-simple exact local-log rigidity.
- Collision-complete sharp dichotomy: any exact local logarithm of (e^{i\phi}e^{-itH}) is physical time plus scalar, or has spectral diameter at least (2\pi). Proof: below (2\pi), a Hermitian logarithm is scalar on every eigenspace of its exponential, hence commutes with (H). Threshold is sharp via (2\pi P).
- Canonical folded log has strict diameter below (2\pi); therefore it is nonlocal already at (|t|W_H\ge2\pi), including collision times.
- Quantitative collision-complete approximate law: if (operatorname{diam}K\le2\pi-\eta), then
  [
  operatorname{dist}_{HS}(K,\operatorname{span}\{I,H\})
  \le (\sigma_H/\gamma_H)((2\pi-\eta)/\sin(\eta/2))\,\varepsilon.
  ]
- Define compact projective affine-alias gap (chi_{H,t,\eta}) over affine logs with diameter at most (2\pi-\eta/2). Under two-gap irrationality and (|t|W_H\ge2\pi), (chi>0). This yields explicit fixed-(H,t) exclusion of every approximate local subwinding logarithm.
- Tangent-only finite holonomy is false: group commutator curvature spans centralizer directions.
- Correct finite-action Lie-word address sets have zero completed-time density below full address dimension, with robust entropy–codimension tube bound. Unbounded action invalidates dimension arguments.
- Composition with formalized Choi plateau: completed-time full-scale circuit hardness coexists with identifiable local parent and nonlocal folded generator.

Honest boundary:
- No arbitrary-circuit lower bound and no Brown ramp.
- Exact remaining theorem: fixed-error nonperturbative circuit-length-to-spectral-address undistortion, uniformly over architectures after one common return excision.
- New pointwise affine-alias positivity is not an ensemble-uniform lower tail.
- Matrix branch-strip uniqueness, divided differences, holonomy, and equidistribution ingredients are standard; novelty is provisional for their local-centralizer/projective-rank/address composition.
- Do not claim in final paper until Lean formalization and axiom audit.
