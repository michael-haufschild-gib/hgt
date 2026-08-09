# Onset–recurrence dimension independence (2026-08-09)

Paper proof: `docs/drafts/pipeline/2-fully-proven/onset-recurrence-dimension-independence-law.md`.
Master: `docs/drafts/pipeline/1-in-progress/static-local-complexity-law.md`.

## Theorem
For every large n and arbitrary large delay L, intersect the capacity-compatible fully coupled diagonal-carrier incubation tube with the conull metric-Diophantine local-chain set. One fixed O(n^3)-preparable cubic-phase seed and a path-local shell set of measure
`A_n(1-96/(kappa^2 D)) L^{-(10n-8)}`, `A_n >= exp(-O(n log n))`, have simultaneously:
- polynomial circuit complexity for all 0<=t<=L;
- every edge interaction Omega(n^-1/2);
- collision <=(2+kappa)/D;
- projective rational rank D-1 and cyclic seed;
- later Omega(D/log M_n) plateau for exp(Omega(D)) time;
- later recurrence and permanent local two-query non-Haar separator;
- exact continuous fidelity first-return exponent
  `lim_(delta->0) log T_fid(delta)/log(1/delta)=(D-2)/2`.

Proof of exponent: local-chain metric extremality gives phase-radius exponent D-2 conull on the shell. For cyclic seed p_j>0, fidelity deficit has positive-definite projective Hessian
`(1/2) sum_jk p_j p_k (phi_j-phi_k)^2`, so radius r corresponds to sqrt(delta).

## Exact insight
Maximal recurrence dimension and current uniform collision, conductance, plateau, and locality thresholds do not upper-bound first complexity onset. This is an independence theorem for the stated invariant class, not a claim against every finer invariant. It strengthens the incubation law and kills recurrence dimension as the missing Brown clock.

## Conjecture loop
1. Exponentially many entanglement cuts -> REDISCOVERED/INSUFFICIENT; gate-normalized additive cut diagnostics have only polynomial range, consistent with Eisert 2021.
2. Additive physical history action -> fails as endpoint lower bound; it is cost of one history.
3. Maximal recurrence dimension forces onset -> FALSIFIED by theorem.
4. Surviving representation: finite-scale subgroup distortion. Intrinsic Hamiltonian time vs ambient local-circuit word/coset distance. Growth=undistortion; fast-forwarding/incubation=distortion; plateau=diameter saturation; recurrence=eventual distortion collapse.

Exact open core: prove quenched finite-scale undistortion at O(n) geometric Brown skeleton times for ordinary path-local shell after explicit weak-cut and named fast-forwardable tubes. This is still not Brown closure.

Hostile boundaries: positive-measure delayed family, not typical growth; recurrence exponent is delta->0 at fixed n,H, not uniform fixed-error large-n; imported Kleinbock-Margulis dependency is not Lean-formalized. Novelty unverified.

No Lean source/process touched during active refactor.