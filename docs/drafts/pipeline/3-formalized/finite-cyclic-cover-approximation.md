# Finite cyclic approximants of the proper infinite image subgroup

- **ID:** FINITE-CYCLIC-COVER-APPROXIMATION-20261009
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean verified)
- **Parent:** `../1-in-progress/xi-capped-surface-uniformization.md`.
- **Source:** `HTGeometry/InfinitePacketObstruction.lean`.
- **Statement:** The explicit proper, infinite-index, profinitely full stabilizer is the eventual-on-every-finite-word-set limit of stabilizers of transitive actions on one distinguished point plus a growing finite cyclic set. Every fixed finite quotient eventually sees the full group.

## Verdict and significance

**BRIDGE.** This tests the discrete mechanism behind the proposed polynomial approximants Pₙ(z)=(z−1)(1+z/(n+1))ⁿ⁺¹. It supplies an exact finite-sheet approximation law; neither the polynomial realization of these actions nor a global analytic coordinate on the Xi surface follows from it. Derivative identities alone would not discharge those obligations. External novelty is unverified because web/literature search is prohibited by the user.

The existing corpus countermodel already proves that finite images and finite normal packets cannot force subgroup equality. The new claim concerns an explicit growing finite-index family and its simultaneous local convergence, not a reproof of that countermodel.

## Complete paper proof [PROVED HERE]

Let W be the free group on x,y. The checked infinite action is on Ω={*}⊔Z, with x translating Z by one and fixing *, and y swapping * with 0. Its stabilizer H at * is proper, has Ω as coset space, and has full image under every homomorphism to a finite group.

For n≥0 set m=n+1 and Ωₙ={*}⊔(Z/mZ). Define xₙ as translation by one on the cyclic part, fixing *, and yₙ as the swap of * with zero. These permutations define an action of W by freeness. It is transitive: y sends * to zero, and powers of x reach every cyclic point. Thus its point stabilizer Hₙ has coset space Ωₙ and index n+2; y∉Hₙ, so every Hₙ is proper.

Let rₙ:Ω→Ωₙ fix * and reduce integers modulo m. For every fixed nonzero integer j, its reduction is nonzero for all m>|j|. Indeed divisibility m|j would imply m≤|j|. Reduction always commutes with integer translation. It commutes with y at any fixed sheet for all sufficiently large n: * and zero are exact for every n; a fixed nonzero integer is eventually neither endpoint of the finite swap.

Induct on a free-group word. The generator and inverse-generator cases follow from these two observations (y is involutive). For a product gh, intersect the eventual commutation statement for h at the chosen sheet with the one for g at the fixed infinite sheet h·s. This proves, for every word w and fixed sheet s, eventually wₙ·rₙ(s)=rₙ(w·s). No bound uniform over all words is asserted.

At s=*, reduction is * exactly when its argument is *, so eventually w∈Hₙ iff w∈H. Intersect these eventual statements for any finite set of words to obtain simultaneous exact membership on that set.

Finally fix a homomorphism q:W→Q with Q finite. For each element of q(W), the already checked equality q(H)=q(W) supplies one preimage lying in H. There are finitely many chosen preimages; eventually they all lie in Hₙ by the preceding convergence. Thus q(Hₙ) contains q(W), and the reverse inclusion is automatic. Hence q(Hₙ)=q(W) eventually for each fixed q, while every Hₙ remains proper with growing index. The cutoff depends on q; exchanging those quantifiers would be false.

## Next obligations

The exact action, coset classification, local convergence and finite-image conclusion are formalized. Separately audit the actual polynomial family and prove its monodromy identifies with these finite actions; do not infer that identification from matching critical-value counts alone. General finite planar realization and normalized analytic compactness remain unresolved.

## Log

- 2026-10-09 — corpus queries for finite polynomial covering approximation and finite stabilizer approximation returned no hits; inspected the complete existing infinite countermodel. Derived the above dependency-closed paper argument for a finite approximation bridge.

- 2026-10-09 — `HTGeometry/FiniteCyclicCoverApproximation.lean` production leaf build passed. All 17 explicit public declarations have standard-only axiom audits; final actual-source `lake env lean` passed with an empty log. Wired into `HTGeometry.lean`; index refresh passed. Global lint reports seven unrelated unreachable modules and no errors in this work. Audit logs: `/tmp/hgt-finite-cyclic-cover-axioms.log`, `/tmp/hgt-finite-cyclic-cover-final.log`.
