# Finite Weil cost kernel: negative hyperplane and reverse Cauchy–Schwarz

- **ID:** finite-weil-cost-kernel-rigidity
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** local Lean: WeilLogShiftFiniteTailCompensation, WeilLogShiftGramFiberCost, WeilLogShiftGramExactImage.
- **Statement:** On distinct real nodes the signed exponential cost kernel is strictly negative on the kernel of its exponential moment; its positive cone satisfies reverse Cauchy–Schwarz, with equality precisely on a single ray.

## Context and attack

Only local Lean corpus and installed Lean dependencies supply mathematical evidence. No external searches, papers, numerical experiments, or external priority claims. The hgtl7 external-audit phases are superseded by the user's explicit local-only instruction. Verdict: **BRIDGE** from finite max-kernel algebra to the actual native tail cost. No claim that elementary Lorentz algebra is new mathematics.

Exact fixed-node realization is already formalized. Cost-preserving replacement of positive mixtures by one test remains OPEN. Nonconvexity of the raw amplitude cost does not disprove convexity of the cost minimized over every realizing test. This card proves the structural obstruction/survivor without conflating these questions.

Local novelty checks: documented lexical searches for cost/convex realization, exponential distance/Lorentz, and min/kernel/quadratic; exhaustive source-text hits for max/quadratic and exponential/Lorentz. Existing cut-family negative-type identities concern different kernels; no existing receiver identified for this native cost kernel.

## Dependency-closed paper proof [PROVED HERE]

For distinct nodes x_i put K_ij = exp(2|x_j-x_i|), Q(u) = sum_ij u_i u_j K_ij, B(u,v) = sum_ij u_i v_j K_ij and L(u) = sum_i u_i exp(-2x_i).

1. **Strict max-kernel defect.** For a finite family of distinct real p_i and R greater than every p_i, let D_R(f) = R(sum_i f_i)^2 - sum_ij f_i f_j max(p_i,p_j). Then D_R >= 0, and D_R = 0 iff every f_i = 0. Induct by deleting the greatest node a. If m is the remaining coefficient sum, the exact identity is D_R(f) = (R-p_a)(f_a+m)^2 + D_(p_a)(f restricted to remaining nodes). Both terms are nonnegative. Equality forces all remaining coefficients zero by induction and then f_a=0. Empty family is immediate. Distinctness ensures p_a strictly exceeds all remaining nodes.

2. **Exponential transport.** Set p_i=exp(4x_i) and f_i=u_i exp(-2x_i). The p_i are distinct and exp(-2x_i)>0. By splitting x_i<=x_j or the reverse and using exp(a+b)=exp(a)exp(b), u_i u_j K_ij = f_i f_j max(p_i,p_j). Hence L(u)=0 implies Q(u)<=0, with equality iff u=0. Choose any R above the finite p_i; no extra assumption is needed. The empty family also satisfies the statement. A coordinate vector has Q=1 on a nonempty family, so there is a positive direction as well.

3. **Reverse Cauchy–Schwarz and rigidity.** Suppose Q(v)>0. Then L(v) != 0 by step 2. Put z=L(v)u-L(u)v. Its L-moment is zero, so Q(z)<=0. Write A=Q(u), C=Q(v)>0, b=B(u,v), l=L(u), m=L(v)!=0. Expansion gives Q(z)=m^2 A-2mlb+l^2 C. Consequently m^2(AC-b^2)+(lC-mb)^2=C Q(z)<=0, proving AC<=b^2. If equality holds, Q(z)=0 and step 2 forces z=0, hence u=(l/m)v. Conversely proportionality gives equality by bilinearity. This proves an exact classification, not just a sign estimate.

4. **Actual nonnegative cost cone.** For nonnegative u,v, the positive entries of K make Q(u),Q(v),B(u,v) nonnegative and Q(v)>0 unless v=0. Step 3 therefore gives B(u,v)>=sqrt(Q(u)Q(v)). Expanding Q(u+v) and taking square roots gives sqrt(Q(u+v))>=sqrt(Q(u))+sqrt(Q(v)), with equality iff the nonzero vectors are proportional (including zero cases as linear dependence). With positive v the proportionality scalar is nonnegative. Native tail cost at outer scale one and B=1 equals Q(|u|) directly from its definition. Thus the nonnegative amplitude cost obeys the reverse triangle law, with strictness off rays.

5. **Unconditional application.** A finite set of real nodes is distinct by construction, so the above statements have no conjectural hypotheses. Alternatively choose the already-proved distinct fixed nodes that realize every coefficient target: the same negative-hyperplane and rigidity laws hold there without any additional premise. These results do not assert convexity or nonconvexity of optimized single-test realization cost.

## Formalization plan / working log

- [x] Local corpus audit and exact statement.
- [x] Complete paper argument; zero/empty cases included.
- [x] Max-kernel defect leaf.
- [x] Exponential transport and reverse Cauchy–Schwarz rigidity.
- [x] Actual tail-cost receiver and unconditional fixed-node application.
- [x] Native leaf builds, public-declaration axiom audit, umbrella wiring, index, lint run (four unrelated umbrella omissions; no owned diagnostics).
- 2026-10-10: paper proof recorded before code. No source edits to existing mathematical leaves planned.
- 2026-10-10: native builds clean for WeilLogShiftMaxKernelDefect, WeilLogShiftCostKernel, and WeilLogShiftCostReverseCauchy. Signed reverse Cauchy–Schwarz includes exact proportionality; its nonnegative-right specialization actually permits arbitrary signed left amplitudes. Square-root superadditivity and equality classification are compiled. Actual receiver leaf written and building; final audit prepared for all 23 public declarations and 69 local API terms. No heartbeat changes or full builds.
- 2026-10-10: WeilLogShiftGramCostGeometry native build clean. Final `/tmp/hgt-cost-geometry-final-audit.lean` passed: all 23 public declarations depend only on `propext`, `Classical.choice`, `Quot.sound`; all 69 explicit API terms checked. All four leaves wired once in RHTower umbrella. Index refreshed; exact receiver search returns `exists_finiteWeilGram_exact_image_cost_geometry` at line 83. Targeted whitespace checks passed. All owned build/search/audit processes terminal.

## Exact Lean delivery

- `WeilLogShiftMaxKernelDefect.lean`: finite max-kernel positive definite defect.
- `WeilLogShiftCostKernel.lean`: exponential-to-max identity, strict moment defect and exact negative-hyperplane zero classification.
- `WeilLogShiftCostReverseCauchy.lean`: signed reverse Cauchy–Schwarz, proportionality equality, nonnegative square-root superadditivity and rigidity.
- `WeilLogShiftGramCostGeometry.lean`: exact absolute-amplitude native cost identity; actual nonnegative cost law with **NNReal** ray scalar; unconditional finite real node-set receiver; unconditional fixed-node exact-image-and-cost receiver.

Verification logs: `/tmp/hgt-max-kernel-defect-build.log`, `/tmp/hgt-cost-kernel-build.log`, `/tmp/hgt-cost-reverse-cauchy-build.log`, `/tmp/hgt-gram-cost-geometry-build.log`, `/tmp/hgt-cost-geometry-final-audit.log`, `/tmp/hgt-cost-geometry-index.log`, `/tmp/hgt-cost-geometry-lint.log`.

Global lint returned four unrelated missing umbrella imports: `RHTower.JointAncestryExplicitSectorBlindBand`, `RHTower.XiHorizontalSlicePolyaFrequencyDensity`, `HTGeometry.PaperMoebiusPrimeLSeries`, `HTGeometry.QKrawtchoukCompanionTriangular`. These shared-worktree files were not changed.

## Research assessment and next cycle

The corpus gains an exact geometric law for its actual native cost, not merely a two-node counterexample or a renamed quadratic-form sign. No external novelty or priority claim: this is an audited bridge. The hardest outstanding question here remains optimized single-test realization cost; the new law does not settle its convexity. Next: strengthen exact fixed-node realization to a uniform linear cost bound by retaining a bounded local preimage in the existing strict-derivative proof, then applying quadratic scaling. No numerical or external work was used.

Follow-up (2026-10-10): that [uniform linear cost bound](finite-weil-uniform-realization-cost.md)
is now formalized and audited. The next paper-proved step is
[coordinate isolation cost](finite-weil-coordinate-isolation-cost.md), now formalized,
which addresses exponential growth of necessary cost constants.
