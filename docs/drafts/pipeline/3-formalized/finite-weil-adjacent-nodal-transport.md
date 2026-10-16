# Exact adjacent transport inside every ordered nodal probability fiber

Status: dependency-closed paper proof; formalized in Lean (stage 3, 2026-10-17).
Date: 2026-10-10. Internal verdict: BRIDGE / survives preliminary attack. Local Lean corpus only; no external novelty claim.

Target: for every strictly increasing real node family h : Fin(r+2) -> Real, the positive and negative probability profiles of its normalized nodal-weight vector admit a unique coupling supported on adjacent indices. This coupling is the unique optimal coupling for the cost abs(h_i-h_j). Its edge masses are positive and sum to one. With index cost abs(i-j), its cost is exactly one, at every order and for every node spacing. For any two probability mixtures in the fiber, the optimal index cost is exactly abs(a-b), while their l1 distance is 2*abs(a-b).

Canonical roots must discharge ordering using finiteWeilClusterLogNodes_strictMono. No quadratic-start hypothesis is needed: this is an exact finite-order law for all r,k. For logarithmic-node cost, the endpoint optimum lies between 1/(k+r+3) and 1/(k+2), by the existing logarithmic gap comparison.

Paper proof (n=r+1 >= 1, nodes x_0<...<x_n):
1. Let W_j=product_{l!=j}(x_j-x_l)^(-1), and C_i=sum_{j=0}^i W_j for 0<=i<n. The raw weight has sign sigma_j=(-1)^(n-j), and sum_j W_j=0 by the existing zeroth nodal moment. The central producer is the STRICT prefix-sign law: C_i has sign sigma_i.
2. Prove this by induction on n. At n=1, C_0=(x_0-x_1)^(-1)<0. For n>=2, let L be the raw weights on x_0,...,x_(n-1), extended by L_n=0, and R the weights on x_1,...,x_n, extended by R_0=0. The product formula gives for every j
   W_j=(L_j-R_j)/(x_0-x_n).
   At interior j this follows from L_j=(x_j-x_n)W_j and R_j=(x_j-x_0)W_j; boundary j=0,n follows by the single missing product factor.
3. Therefore C_i=(C_i^L-C_(i-1)^R)/(x_0-x_n). Define C_-1^R=0 and note C_(n-1)^L=0, since the left subfamily has at least two nodes. For interior cuts, induction gives sign(C_i^L)=-sigma_i and sign(C_(i-1)^R)=sigma_i. Their difference has strict sign -sigma_i, and division by the negative endpoint gap gives sigma_i. At i=0 only the first term remains and is nonzero; at i=n-1 only the negative of the second remains and is nonzero. Thus every boundary case is covered without a positivity premise on the prefix sums.
4. Let P,Q be the normalized positive and negative probability profiles, delta_i=P_i-Q_i, and D_i=sum_{j<=i}delta_j. The same prefix-sign law holds because delta is a positive scalar multiple of W. Put m_i=abs(D_i)>0 for 0<=i<n, with m_-1=m_n=0. Successive prefix signs are opposite, hence
   delta_i=sigma_i*(m_(i-1)+m_i).
   Since P,Q have disjoint supports with signs sigma_i, their marginals are exactly supplied by the two adjacent edge masses. Orient edge i toward i+1 when sigma_i=+1 and toward i when sigma_i=-1. This constructs a coupling pi of P to Q. Summing abs(delta_i) gives 2*sum m_i=2, so sum m_i=1. Each cut determines its edge mass, proving uniqueness among adjacent couplings.
5. For node cost, set phi_0=0 and phi_(i+1)-phi_i=-sigma_i*(x_(i+1)-x_i). This potential is 1-Lipschitz on the nodes by telescoping and triangle inequality. Finite summation by parts gives
   sum_i delta_i*phi_i=sum_i D_i*(phi_i-phi_(i+1))=sum_i m_i*(x_(i+1)-x_i).
   Every coupling has cost at least this dual pairing. The constructed adjacent coupling attains equality. For any nonadjacent distinct pair, the alternating slopes and strictly positive gaps make the Lipschitz inequality strict. Marginal disjointness excludes diagonals, so any optimum must be adjacent; the preceding uniqueness applies.
6. For index cost every gap is one, so the optimum is sum m_i=1. For canonical logarithmic nodes every gap is between 1/(k+r+3) and 1/(k+2), using the already-proved scaled log-gap inequality. The optimal cost, a convex combination of these gaps, has the same bounds. These roots hold at every start, independently of the asymptotic binomial approximation.
7. For mixtures nu_a=aP+(1-a)Q and nu_b=bP+(1-b)Q with 0<=a,b<=1, retain their common mass on the diagonal and transport the excess abs(a-b) using pi or its transpose. The cost is abs(a-b) times the endpoint cost. The same potential (or its negative) gives the matching lower bound. Strict dual inequality excludes all nonadjacent movement; one directed orientation of adjacent edges is allowed, forcing the common diagonal masses and the excess edge masses. The optimal mixture coupling is therefore unique as well. At a=b, strictly positive off-diagonal costs force the unique diagonal coupling.

Failure audit: alternating signs and zero total mass alone do not suffice. For u>v>0, the vector (u,-v,v,-u) has both properties but its first two nontrivial prefix sums have the same sign. The nodal-weight producer and its deletion recurrence must be proved, rather than adding prefix positivity as a premise. A midpoint/binomial l1 approximation alone is also too coarse to establish this exact transport law.

Prior-corpus audit so far: `barycentric transport` with per-module cap removed returned fifteen declarations in three modules. All fifteen statements/definitions were inspected: CCM rank-one source-faithful Markov transport and its source-sign/RH equivalences, two prime-jet interpolation reporters, and one quantile-cell quadratic debt inequality. None states adjacent nodal coupling or prefix sign rigidity. `nodal cumulative` returned one two-atom cascade summability theorem, inspected and unrelated. Exhaustive relevant source-text search found the LagrangeRectangleContour partial-fraction identity and rectangle-integral representation; both inspected, and the additional call sites use those same identities. Other matches were adjacent-degree energy/trace coupling and a squared nodal-weight reporter norm, inspected and unrelated. No nodal prefix-sum sign theorem was found in the focused moment/canonical modules. Follow-up `adjacent coupling` returned seven declarations, all inspected: five Sonin adjacent-norm convergence/tomography declarations plus the already-read Jacobi trace and arithmetic Ward identities. None is a probability coupling. `nodal prefix` returned zero hits. These completed results are logged under /tmp/hgt-adjacent-coupling-search.json and /tmp/hgt-nodal-prefix-search.json. Installed Lagrange.lean exposes nodalWeight as a product of inverse gaps at line638 and derivative/interpolation/partial-fraction identities, but the targeted declaration search found no ready-made nodal-weight deletion identity.

Lean strategy: finite raw-weight deletion identity, preferably through available product reindexing or the corpus's moment-annihilator classification; then prefix-sign induction; positive adjacent-flow conservation; explicit coupling and dual potential; canonical index/log-cost roots; full-mixture uniqueness. Verify every new API against the installed toolchain. Do not replace the exact coupling and lower-bound claim with an arbitrary definition named transport cost.

## Lean status (2026-10-17) — every claim formalized, general node families

The earlier `WeilLogShift*` chain covered only the canonical logarithmic nodes.  Two new modules
prove the card for every strictly increasing `h : Fin (r+2) → ℝ` (all `r`, all spacings):

`RHTower/FiniteWeilNodalAdjacentCoupling.lean`
- `finiteWeilNormalizedMomentDual_parity`: every nodal weight carries the sign `(-1)^(r+1-i)`
  (from `finiteWeilNormalizedMomentDual_last_pos` and adjacent alternation);
- `finiteWeilNodalProfiles_spec`: `P`, `Q` disjoint probabilities, `Σ|P-Q| = 2`, equal moments `p ≤ r`;
- `finiteWeilNodalPrefixDifference_pos` (strict prefix-sign law, from the deletion recurrence
  `finiteWeilNodalPrefix_sign`), `finiteWeilNodalEdgeMass_pos`, `finiteWeilNodalEdgeMass_sum` (= 1);
- `finiteWeilNodalCoupling` (explicit adjacent coupling), `finiteWeilNodalTransport_eq_of_banded`
  (unique among couplings supported on adjacent indices);
- `finiteWeilNodalCoupling_index_cost` (= 1), `finiteWeilNodalTransport_index_unique_minimizer`.

`RHTower/FiniteWeilNodalMixtureTransport.lean`
- `finiteWeilNodalTransport_node_unique_minimizer`: unique optimal coupling for `|h_i - h_j|`
  (and `..._ordered_unique_minimizer` for every strictly increasing reembedding);
  `finiteWeilNodalCoupling_ordered_cost` (= `Σ m_i (x_{i+1}-x_i)`), `..._node_cost_bounds`
  (between any gap bounds; with the existing `finiteWeilCanonicalLogTransportCost_bounds` this gives
  `1/(k+r+3) ≤ cost ≤ 1/(k+2)` for logarithmic nodes);
- `finiteWeilNodalMomentFiber_iff` (fiber = segment of mixtures), `finiteWeilNodalMixture_abs_distance`
  (`ℓ¹ = 2|a-b|`), `finiteWeilNodalMixtureTransport_index_unique_minimizer` (cost exactly `|a-b|`),
  `finiteWeilNodalMixtureTransport_ordered_unique_minimizer`, `..._ordered_cost_eq_zero_iff`,
  `finiteWeilNodalMixtureCoupling_self_off_diagonal` (diagonal at `a = b`);
- `finiteWeilCanonical*_eq_nodal`: the canonical chain is the case `h = log nodes`;
- `alternating_zero_sum_prefix_signs_not_forced`: the `(u,-v,v,-u)` failure-audit example.

Audit: both files pass `lake env lean` with no errors or warnings; `#print axioms` on all 19 main
theorems (scratch copy) gives only `propext, Classical.choice, Quot.sound`.  Both modules are appended
to `GaloisForLFunctions/RHTower.lean`; name scan found no collisions.  Card moved to `3-formalized`.
