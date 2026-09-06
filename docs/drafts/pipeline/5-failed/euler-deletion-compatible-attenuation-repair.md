# Compatible attenuation cannot remove the selected curvature

**Stage:** 5-failed. **Scope:** positive contractive completely multiplicative
attenuation with the compatible deletion multiplier `d/b(d)`. **RH implication:**
none. **Novelty:** not certified.

The proposed repair shrinks prime weights and compensates their deletion
multipliers to preserve the one-prime ordinary-admission normalization. It then
recomputes the quadratic factorization curvature using those changed coefficients.

**Exact killing theorem:** for the actual squared mass `b(n)^2*n^(-alpha)`, the
four-channel curvature remains strictly negative for `1<alpha<2`, zero at two,
and strictly positive above two, for all pairwise coprime labels greater than one.
The factor controlling the sign is still `1-r^(2-alpha)` because the reciprocal
normalization cancels the attenuation at the third label. The boundary corresponds
to `Re(s)=1` when `alpha=2*Re(s)`; it is not a critical-line criterion.

**Strongest positive survivor:** the exact factorization determines the full sign
boundary. More strongly, when the first two label weights remain one, curvature
divided by its actual total mass equals the original normalized curvature exactly.
The third label and all other prime weights can vary within the stated class.
The entire family `b(n)=c^(v_5(n))`, `0<c<=1`, therefore preserves the normalized
`2,3,5` curvature after its compatible repair.

**New insight:** enforcing the necessary normalization can undo the intended
effect of smaller inputs. This repair cannot erase or reverse the obstruction;
a source-derived identity or a different observable still needs an independent
proof. No claim is made that every multiplicative weight has the original
ordinary-convergence domain, or that every possible deformation fails.

**Status:** dependency-closed paper proof and Lean proof in
`EulerDeletionCompatibleCurvature`. The fixed attenuation `1/5` gives a closed
theorem with multiplier 25 and strict signs on both sides of two. This completes
the positive survivor of the failed repair, not the main RH objective.
[Paper and literature scope](../2-fully-proven/euler-deletion-compatible-curvature.md),
[formal certificate](../3-formalized/euler-deletion-compatible-curvature.md).
