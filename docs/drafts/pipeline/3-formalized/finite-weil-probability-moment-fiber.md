# Exact canonical probability moment fiber

Status: formalized; native compilation and complete public-declaration axiom audit passed.
Date: 2026-10-10.
Scope: local Lean corpus only; no web, external papers, numerical experiments, or external novelty claim.

Objective: classify every probability profile on the `r+2` logarithmic cluster nodes whose moments through order `r` equal those of the canonical positive profile. Prove exact geometry and a uniform native-cost sensitivity law on that entire fiber, with all analytic constants supplied by the existing corpus.

Corpus audit: lexical `probability moment fiber` found eight declarations about complete Hamburger moment fibers; lexical `moment simplex` found general boundary-simplex and unrelated simplex declarations. `FiniteMomentCubicTangent.lean` treats first-order motions of node positions, not this fixed-node probability fiber. Exhaustive source search of `WeilLogShift*.lean` found no existing classification. Direct producers: `finiteWeilMomentWeights_span`, canonical profile specification and `exists_finiteWeilGram_probability_profile_sensitivity`. No external novelty inference.

Let beta be the canonical cluster dual, S=sum |beta|, P=(|beta|+beta)/S, Q=(|beta|-beta)/S, and C_a=aP+(1-a)Q. Existing corpus proves S>=2, P,Q nonnegative with unit mass, P_i Q_i=0, P_i+Q_i>0, sum|P-Q|=2, and matching moments through r. The raw barycentric weights W span all moment annihilators; beta=W/||W||, with ||W||>0.

Paper proof:
1. Any annihilator c has c=A W by the existing span theorem. Since P-Q=(2/S)/||W|| times W and this scalar is positive, c=t(P-Q) for exactly one scalar t.
2. If v has the stated moments, c=v-Q is an annihilator. Thus v=C_t. Positivity and unit mass of P give a coordinate with P_i>0; disjointness gives Q_i=0, so v_i=tP_i>=0 forces t>=0. Likewise a coordinate with Q_j>0 forces 1-t>=0. Conversely every C_t for 0<=t<=1 is nonnegative, has unit mass, and has the stated moments. The positive P coordinate makes t unique.
3. C_a-C_b=(a-b)(P-Q), so sum|C_a-C_b|=2|a-b| for all real a,b. The fiber is therefore exactly a closed line segment with known metric, not merely a subset with two examples.
4. Against any coefficient vector y, expectation(C_a,y)-expectation(C_b,y)=(a-b)(expectation(P,y)-expectation(Q,y)). Existing unconditional profile sensitivity supplies B>0,L>=1 such that, under cluster width 4L(r+1)<=k+2, the endpoint gap times (k+2)^2*2^r is at most B times actual native Gram cost. Multiplication by |a-b| and the exact distance identity give the same inequality for every two fiber members, with factor sum|v-z|/2. All analytic premises are discharged by the existing root.

Formalized leaves: `WeilLogShiftMomentFiber.lean`, `WeilLogShiftMomentFiberSensitivity.lean`. Public results: unique mixture classification (first leaf, line 102), exact l1 distance (line 136), actual Gram test reading the mixture coordinate for every real parameter (second leaf, line 20), and universal sensitivity over the complete canonical moment fiber (line 32).

Verification: both native leaf compiles passed with empty logs. `/tmp/hgt-moment-fiber-final-audit.lean` checked all 12 authored public declarations and 15 imported API terms; only `propext`, `Classical.choice`, and `Quot.sound`. Source and direct-dependency freshness, exact umbrella import counts, and incoming-import scope passed. Local corpus index refreshed successfully. No full build or heartbeat changes.

Global formal lint exited 1 on nine unrelated missing umbrella imports: `RHTower.JointAncestryTwistedKroneckerDomination`, `RHTower.PaperPrimeFredholmReconstruction`, `RHTower.PaperZetaCyclePhysicalReconstruction`, `RHTower.PaperZetaCycleVaryingPeriods`, `RHTower.RayPolylogMultiplicity`, `RHTower.RieszFunctionStrictMultiplicity`, `RHTower.XiGaussianHeatVerticalVarianceLaw`, `HTGeometry.PaperCirclePhysicalHeight`, `HTGeometry.QKrawtchoukCompanionTriangular`. No errors named these two leaves; unrelated shared-worktree files left untouched.

Interpretation: the canonical finite-moment ambiguity has exactly one parameter, while resolving that parameter with actual Gram tests remains exponentially costly. This separates dimension of the ambiguity from sensitivity of its measurements.

Next candidate, not proved here: retain the exact profile scale `2/S` in the native-cost estimate, giving distance factor `sum|v-z|/S` in place of `sum|v-z|/2`; then seek symbolic bounds on S from the exact nodal ratios. Do not infer magnitude growth from alternating signs alone.

Successor formalized 2026-10-10: [canonical mass rigidity](finite-weil-canonical-mass-rigidity.md). The retained-scale candidate is now proved: sensitivity keeps the exact factor S, and every actual mixture-coordinate reader pays S times the geometric scale. Equality S=2 holds exactly for r<=1; S>2 for r>=2. Symbolic growth of S remains open. Nine public declarations passed native compilation and axiom audit.
