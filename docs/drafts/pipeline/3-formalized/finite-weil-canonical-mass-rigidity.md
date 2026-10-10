# Canonical absolute mass: equality rigidity and retained sensitivity scale

Status: formalized; all native builds and public-declaration axiom audits passed.
Date: 2026-10-10.
Research scope: local Lean corpus only. No web, papers, numerics, or external novelty claim.

Let beta be the canonical sup-norm-one log-cluster annihilator, S=sum|beta|, and P,Q its canonical disjoint probability profiles. Existing corpus proves S>=2, P-Q=(2/S)beta, alternating adjacent signs, positive final coefficient, exact probability moment fiber C_a=aP+(1-a)Q, and l1(C_a-C_b)=2|a-b|. Corpus search for finiteWeilAbsMass and exhaustive WeilLogShift source search found the lower bound and normalization identities, but no equality classification or retained-S native-cost root.

Targets:
1. Prove S=2 iff r<=1, hence S>2 iff 2<=r, for every cluster start k.
2. Preserve the exact normalization in the full-fiber sensitivity law: gap(v,z;w)*(k+2)^2*2^r*S <= l1(v-z)*B*cost1(w), with B,L supplied by the existing unconditional canonical-dual receiver.
3. Give an actual Gram test reading every mixture parameter a, and prove every such reader satisfies S*(k+2)^2*2^r <= 2B*cost1(w). This retains the factor S/2 discarded previously.

Paper proof:
- For any zero-sum finite c, the nonnegative summands |c_j|+c_j sum to S. Any two distinct summands therefore total at most S.
- For norm-one c with S=2, choose i with |c_i|=1. If c_i=1, its positive summand already equals two, forcing every other c_j<=0. Apply the same argument to -c when c_i=-1. Thus c_i*c_j<=0 for every j!=i.
- If r>=2, the first four cluster nodes contain an adjacent pair avoiding i: choose nodes 2,3 when i<2, otherwise nodes 0,1. Both coefficients have the opposite weak sign to c_i, so their product is nonnegative; strict alternation says it is negative. Hence S cannot equal two; the known lower bound gives S>2.
- For r=0, signs are negative,positive and the zero sum gives S twice the final coefficient, at most two by unit sup norm. For r=1, signs are positive,negative,positive and the zero sum gives S twice the absolute middle coefficient, also at most two. The existing lower bound forces equality. These are symbolic finite-sum proofs, with no evaluation of logarithms or numerical weights.
- For any coefficient vector y, endpoint gap=(2/S)*sum beta_i*y_i. Multiplying its absolute value by S cancels the normalization exactly. Mixture gap adds factor |a-b|, while l1 distance is 2|a-b|. Therefore absolute gap times S equals l1 distance times the absolute canonical pairing.
- Apply the existing canonical Gram-form sensitivity with fixed B,L and identify its form with the cluster pairing. This discharges every analytic premise and gives the full-fiber inequality.
- The existing actual mixture reader supplies existence. For every reader, take mixtures 1 and 0; expectation gap is one and distance is two, yielding the retained-mass cost inequality.

Formalized leaves: `WeilLogShiftMassRigidity.lean` (two generic mass lemmas), `WeilLogShiftCanonicalMass.lean` (three boundary theorems), and `WeilLogShiftMassWeightedSensitivity.lean` (two exact pairing identities and two unconditional receivers). Exact boundary receiver: `finiteWeilCanonicalCluster_mass_eq_two_iff`, second leaf line102. Final analytic receivers: `exists_finiteWeilGram_mass_weighted_fiber_sensitivity`, third leaf line49, and `exists_finiteWeilGram_mass_weighted_coordinate_cost`, line95.

Verification: all three native leaf compiles passed with empty logs. `/tmp/hgt-mass-final-audit.lean` checked all nine public declarations and twelve imported API terms; only `propext`, `Classical.choice`, and `Quot.sound`. Source/direct-dependency freshness, incoming-import scope, unique umbrella imports, local index refresh, and exact final-receiver lookup passed. All owned jobs terminal. No full build, heartbeat changes, or foreign-file repairs.

Global formal lint exited1 on five unrelated missing umbrella imports: `RHTower.RayPolylogMultiplicity`, `RHTower.RieszFunctionStrictMultiplicity`, `HTGeometry.PaperFiniteObservationLaw`, `HTGeometry.QKrawtchoukCompanionTriangular`, and `HTGeometry.ToeplitzBorderedDeflation`. No errors named these three leaves.

Lean implementation notes: splitting the erased sum before the full sum prevented the intended zero-sum rewrite; an explicit full-sum identity fixed it. Finite-index normalization exposed `1 % (r+2)`; `Nat.mod_eq_of_lt` supplied the needed fact in the common branch scope. No mathematical premise was added.

Interpretation: S is an exact normalization invariant in the measurement cost law. Strict improvement starts at order two. No asymptotic growth rate for S is claimed; that needs further control of the exact weight ratios.

Next frontier: derive symbolic magnitude or growth bounds for S from actual log-node gaps and exact nodal ratios. Alternation alone establishes the equality obstruction above, not any asymptotic growth law.

Successor formalized 2026-10-10: [log-grid mass comparison](finite-weil-log-grid-mass-comparison.md). Logarithmic mass now has a proved two-sided comparison to equally spaced-node mass, with distortion ((k+r+3)/(k+2))^(r+1). Both full-fiber sensitivity and actual-coordinate-reader cost inherit this arithmetic reference. Sixteen declarations passed native compilation and standard-axiom audit. The reference's explicit binomial value remains the next target.
