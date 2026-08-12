# Xi horizontal collision charge endpoint [LEAN-PROVED]

Module `formal/GaloisForLFunctions/RHTower/XiHorizontalCollisionChargeEndpoint.lean`, umbrella-wired.

For strip-window local orders m_rho and horizontal-fibre totals H_rho, define O(T)=sum m_rho(H_rho-m_rho). Exact Lean results:
- ordered distinct-pair normal form;
- O(T)=sum_gamma H_gamma^2-sum_rho m_rho^2;
- O(T) even and monotone;
- exact divisor split and N(T)-O(T)<=N0(T);
- off-line mass<=O(T), off-line mass=2*right-half mass;
- RH iff forall T O(T)<2 iff forall T O(T)=0;
- natural, arbitrary cofinal, and eventual <2 endpoints.

Verification: direct lake env lean pass; exact leaf build pass; axioms only propext/Classical.choice/Quot.sound; no forbidden declarations. Global lint sees module wired and fails only on seven unrelated concurrent unwired modules.

Heavy conjecture audit:
1. O(T)=o(N(T)) does NOT imply RH: persistent reflected pair gives constant charge 2 and density-zero defect.
2. Existing finite prime/Bohr recurrence plus LocallyUniformZeroTransfer applies to depthThreeDirichletFactor, not Xi.
3. Full positive-lower-density zeta self-approximation is Bagchi strong recurrence, equivalent to RH; importing it is circular.
4. Exact producer: literal completed prime-Gamma identity giving O(T)<2 on any cofinal cutoff family, or a charge-specific divisor replication theorem not assuming full zeta self-recurrence.

Card: docs/drafts/pipeline/1-in-progress/xi-horizontal-collision-charge-quantized-endpoint.md. Frontier section appended to rh-current-frontier-map.md.