# HCF: all-time block Jacobi census

Status: formalized and audited. Scope: unconditional full singular-block inertia and all-time determinant census, beyond the existing normal-block kernel classification.

## Corpus frontier

`XiGaussianHeatNormalBlockResolution` gives actual-source nondegeneracy, cofinal regular heads, unique normal blocks, and exact section kernels. `XiGaussianHeatFirstContact` gives a strict preceding head at first contact. Neither identifies how the heat flow unfolds a singular block. Existing Jacobi sign counting still assumes nonzero scalar pivots.

## Conjecture loop

1. Test whether contact is automatically transverse. The derivative chain and the normal-block vanishing rows instead permit higher contact; transversality cannot be inferred from static nullity one. Do not assume it.
2. Candidate: a normal block of length `d` forces the exact first heat jet of every frozen null polynomial `P_n q`; its order is `d - 1 - 2 * natDegree q`, with coefficient determined by the first block coupling and the square of the leading coefficient. This should identify all hidden tangencies without a genericity premise.
3. Stronger target: use these jets to resolve the whole local singular block, including determinant/contact dynamics, rather than stop at a derivative identity.

## Constraints and validation

Use Lean corpus and documented corpus search only; no numerical experiments or web/novelty searches. Actual-source capstone must have no positivity, RH, source-sign or genericity premise. Focused foreground builds only, one at a time; final `lake env lean` audits, standard-axiom audit, umbrella imports, lint, cleanup.

## Progress

Initial deep search completed with full inventory coverage but mostly source-only compiler metadata; applicability must be checked in Lean. A second search targets determinant/Toda mechanisms. No new theorem claimed yet.

The full heat-unfolding conjecture remains unproved; do not replace it by a first-derivative claim. A cross-corpus lead supplies a stronger immediately actionable target: `ABHN.HasseMatrixRanks.matrix_rank_eq_rank_map` transports the exact real nullity profile to the complex inertia used by HCF. Interlacing then determines the complete block inertia from its length and its two nonzero endpoint determinants. Prove an all-time block Jacobi census, eliminating the generic-time and nonzero-intermediate-pivot assumptions from the existing census.

Paper argument: if `d` is block length and `m=floor(d/2)`, both positive and negative indices stay fixed through the first `m` ranks; each grows by `m` from the opposite end. Only an odd block has one remaining sign. Its negative contribution is `q=m+[(-1)^m Δ_n Δ_(n+d)<0]`. At intermediate offset `k`, the positive, negative, null contributions are respectively `k-q`, `k+q-d`, `min(k,d-k)` (natural subtraction). Sum `q` over canonical regular heads to obtain the exact census at every positive heat time.

`XiGaussianHeatBlockInertia.lean` passes its focused `lake --old build +...:olean` without new diagnostics. It proves complexification of nullity, positive-index interlacing, exact block charge, and the full three-index profile. No heartbeat changes or added assumptions.

Completed: `XiGaussianHeatBlockJacobiCensus.lean` proves `hcf_all_time_block_signature` and `hcf_all_time_block_census`. Both modules pass final direct audits. The exploratory heat-unfolding conjecture was not needed for this structural closure.

## Dependency-closed argument

1. Existing actual heat nondegeneracy supplies each finite normal block and its real nullity `min(k,d-k)`. The corpus's field-extension rank theorem, together with rank-nullity, gives exactly the same complex nullity.
2. Positive and negative inertia each increase by either zero or one under a one-coordinate extension. Their sum plus nullity is the dimension. While nullity increases, both signed indices remain fixed; while nullity decreases, both increase by one. At an odd block's midpoint, exactly one signed index increases.
3. At a regular head, the determinant has sign `(-1)^negativeIndex`. This identifies the single unresolved odd-block choice and gives the charge formula above. In particular an even block has no unresolved orientation.
4. Enumerate successive first regular heads. Actual nondegeneracy makes this sequence cofinal. Induction sums the exact block charges to the negative index of every enumerated head. The block profile then determines all three indices at every rank, including singular ranks.
5. Existing actual heat index saturation identifies the supremum of these counts with `xiUpperFrequencies.encard`, in both the finite and infinite cases. The capstone has only a positive heat-time input; no finiteness, positivity, RH, genericity, or nonzero-pivot assumption is exported.

## Exact frontier change and limits

The prior determinant-sign census required every scalar pivot to be nonzero and was available through generic-time selection. This result removes that condition at every positive heat time and gives the missing full inertia inside each singular block. It neither proves complete prime–Gamma source positivity nor selects the no-transition branch. The heat-parameter unfolding conjecture remains unproved and is not part of the claimed result.

## Validation

- Focused `lake --old build +GaloisForLFunctions.RHTower.XiGaussianHeatBlockInertia:olean` and corresponding census target: passed, no new warnings.
- Final `lake env lean GaloisForLFunctions/RHTower/XiGaussianHeatBlockInertia.lean`: passed.
- Final `lake env lean GaloisForLFunctions/RHTower/XiGaussianHeatBlockJacobiCensus.lean`: passed.
- Seven `#print axioms` checks, including both actual-source capstones: only `propext`, `Classical.choice`, `Quot.sound`.
- `scripts/formal_tools.py lint`: passed; both modules wired into `RHTower.lean`. No umbrella build.
- No numerical experiments, added axioms, proof placeholders, or heartbeat changes.

Lean lesson: normalize the entire dependent zero-rank target with `change` before using the empty-head lemma. Simplifying only `heatRegularHead a 0` inside an inertia expression can leave a semireducible dimension inside its hidden `Fintype` instance and produce an identical-looking type mismatch.
