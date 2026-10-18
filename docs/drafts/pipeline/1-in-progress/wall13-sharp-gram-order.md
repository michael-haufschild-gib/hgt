# Wall 13: sharp Gram-determinant detection order

- **ID:** BSU-W13-SHARP-GRAM
- **Stage:** 1-in-progress
- **Type:** CONJECTURE — paper argument awaiting dependency audit and Lean
- **Scope:** BiScaleUncertainty; no RH work.
- **Statement:** for the literal unit-correlation bump and opposite copies at gap T>2, a nonzero amplitude is first distinguished by a Gram determinant of size floor(T)+1.

## Frontier evidence

The [sharp closed-product theorem](../3-formalized/wall13-minimal-cycle-order.md) is now Lean-verified, with all 41 public declarations audited. The completed finite-order obstruction supplies Gram equality from equality of every closed product through the same order. It does not establish a sharp converse for determinants: different cycle terms could cancel.

Corpus search `/tmp/bsu-wall13-gram-threshold-frontier.json` inspected all 20 candidate and 20 source statements. It found related Gram and separated-correlation results, but no applicable exact determinant threshold. Returned ingredient sets do not prove the needed cancellation statement. Search completed without errors; semantic coverage unmeasured, compiler statuses source-only, background refresh incomplete. No exhaustive absence or novelty claim.

Follow-up `/tmp/bsu-wall13-gram-cofactor-search.json` inspected all 20 candidate and 20 source statements. Partial result: semantic retrieval timed out within its budget. Useful installed APIs include `Matrix.det_updateRow_add`, `Matrix.det_updateRow_smul`, `Matrix.det_succ_row_zero` and `Matrix.det_succ_row`; their source signatures were read. `HTGeometry/RowReplacementRecurrence.lean` is a possible reusable parent. These are leads, not verified dependencies of a completed theorem.

## Proposed construction and cancellation proof

Write h for the literal seed correlation, positive exactly on (-1,1). Set q=floor(T)+1 and s=T/q. Since q-1<=T<q and T>2, q>=3, 0<s<1 and 2s>1. Sample at 0,s,...,(q-1)s.

For f_a(u)=b(u)-a b(u-T), every Gram diagonal is R=(1+a^2)h(0). Consecutive entries equal c=(1+a^2)h(s)>0. The endpoint pair has value z=-a h(s). Every other off-diagonal entry vanishes: its distance and distance from T are both at least 2s>1. Thus the nonzero off-diagonal graph is precisely a cycle with one distinguished edge.

Expand the determinant over permutations. Terms using the distinguished edge zero or twice are even in z. A nonzero term using it exactly once contains a permutation cycle joining the path endpoints; after deleting that edge, the unique path forces every vertex into that cycle. Exactly two permutations remain, the two orientations of the full cycle. Each has sign (-1)^(q-1) and product z*c^(q-1). Therefore

    det Gram(f_-a) - det Gram(f_a)
      = 4*(-1)^(q-1)*a*(1+a^2)^(q-1)*h(s)^q,

which is nonzero when a!=0. This argument must be audited for q=3 as well as larger q; q=2 is outside the parameter domain.

An equivalent algebraic proof may be simpler to formalize. Start from the open-chain tridiagonal matrix A with corner entries zero, then add z at both endpoint corners. Multilinearity in the two endpoint rows gives det(A(z))=det(A)+z(B+C)+z^2 D. Symmetry gives B=C. Expanding the first replaced row shows B=(-1)^(q-1) times the determinant of the minor with rows 1,...,q-1 and columns 0,...,q-2. That minor is upper triangular with every diagonal entry c, hence B=(-1)^(q-1)c^(q-1). Subtracting the values at -z and z cancels both the constant and quadratic terms. Installed `Matrix.det_of_upperTriangular` is a candidate for this final minor step; it has not yet been probed in Lean for this construction.

For smaller sizes, every determinant summand is a closed correlation product and the strict packet-charge bound forces equality. For larger sizes, append mutually separated sample points at multiples of 2T+3. Their cross-correlations vanish, leaving a diagonal block with positive diagonal R. The determinant difference is multiplied by a positive power of R.

## Exact target and limits

    exists a real sample configuration of size n with different Gram determinants
      iff a!=0 and T<n.

Instantiate a=exp(-T/2) only after the exact general theorem, obtaining the polar-neutral/positive pair. This would classify the whole Gram detection threshold for this constructed family. It does not prove full-Gram recovery for arbitrary compact sources, stability of recovery, or a transfer between pointwise and Bochner cones. Wall 13 remains open.

## Next checks

1. Reuse the verified concrete seed and sharp closed-product theorem.
2. Audit the cycle-permutation argument or derive the same determinant difference by row multilinearity and a triangular cofactor.
3. Formalize the exact determinant identity, construct the sample configurations, and verify every public declaration.

## Active implementation plan

1. Prove the concrete cycle-matrix determinant difference using two-row multilinearity, symmetric cofactors and the triangular endpoint minor.
2. Realize the cycle matrix as the actual correlation Gram matrix at the first detecting order. Prove every off-cycle entry vanishes and every required factor is nonzero.
3. Extend any detecting configuration by a separated point; prove its determinant gains the common positive mass factor. Combine with the strict closed-product lower bound to classify all orders, including zero amplitude.
4. Instantiate the polar pair, run serial leaf checks, audit every public declaration, wire finished modules, refresh the index and inspect lint.

The preceding goal turn made verified progress. All three parent source hashes still match their checked manifest. The Bézout field README has concurrent additions by another writer; those additions were read, and the file remains read-only for this task. No owned Lean job is carried over. `update_plan` is unavailable; this card persists the plan.
