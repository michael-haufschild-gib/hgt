# BAG actual selected-kernel convergence

01ax. Active route: actual cubic transfer; RH remains open. Uniform selected
full-plane weighted energy is in final scratch audit. Next hard obligation:
identify the actual moving-family limit, then prove strong lower-order energy
convergence, physical log-coordinate tails and Mellin line tails.

Conjecture: for every real a,b,tau, the literal selected reciprocal kernel
K_(N^-3/4,1/logN)(a,b,(tau/N)*a*b) tends to the sharp-band zero-curvature
kernel with F_infty(x)=1_(1,2)(x)*smoothAFECutoff(x). All original factors
remain. This is not an assumed stationary-profile substitution.

Paper argument: selected parameters are eventually admissible. The actual
slice has norm at most one: cutoff is in[0,1], Gaussian norm is at most one
on positive inputs, and logarithmic denominator is at least one on[1,2].
Inside(1,2), the exact plateau eventually contains x; outside it the cutoff
is identically zero. Hence F_N(x)->F_infty(x) pointwise, including endpoints.
The full triple integrand is supported on[1,2]^3 and bounded in norm by one,
since R^-2<=1 there and the physical window has range[0,1]. Curvature tends
to zero. Finite-cube dominated convergence, with literal joint measurability,
therefore proves the conjecture. A second compact-frequency dominated
convergence gives local weighted-L2 convergence. Combining this with the
already proved uniform higher weighted energy should give global convergence
at every strictly lower order; that tail argument is still to formalize.

Source: ChiCubicPhysicalAmplitudeBudgets, ChiCubicControlledCutoff,
ChiCubicCoupledKernelDecay; SmoothAFECofactorCellStability proves the actual
Gaussian norm bound. Corpus search98825, retained JSON
/tmp/bag-selected-kernel-convergence-search-01ax.json: partial (filter/judge
malformed JSON), all66735files indexed; index1252818, coverage1252839=current;
semantic coverage unmeasured; background refresh incomplete. All20 candidate
and20 source statements inspected. Useful dominated-convergence APIs verified
from installed Mathlib/MeasureTheory/Integral/DominatedConvergence.lean.
No proof_ideas/ingredient_sets returned. Unrelated hits not treated as evidence.

Scratch /tmp/bag-selected-kernel-limit-01ax.lean starts with actual slice bound
and pointwise limit. No analytic/cancellation premise is added to public results.

Audit checkpoint:42001 failed on concrete norm rewrites, reciprocal-limit
name, denominator coercion, eventual-equality syntax, indicator measurability
and integrable-indicator API. Retry63299 left two coercion/indicator issues.
Retry72761 verifies the complete actual pointwise limit and uniform measurable
kernel bounds; two new helper errors remain (1<=weight needs order reasoning;
0<=s without spacing collides with notation). Fixed both and added complete
strong weighted convergence; current19612. P2 now records the full paper proof.
No production convergence leaf or RH closure yet.

01ax STRONG actual selected-kernel convergence CLOSED:
ChiCubicSelectedKernelConvergence479lines/API5. Literal family -> explicit
sharp-band reciprocal kernel globally in weightedL2, every0<=s<3/2.
Actual slice/cube domination/Fubini/DCT, intermediate-order Fatou admission,
and R^(2s-2t) tails pay full convergence without assumed regularity.
Scratch23076PASS; production6711emptyPASS; five axiomprints93079standard3
(combined next physical scratch has separate errors). Index88424PASS/API5,
umbrellaonce,diffcheckPASS. Lint94988terminal1: UnitClassInverseLBounds
unreachable outside this work,362warnings,no owned finding. P2/P3 and BAG
frontier updated. Finished convergence scratch/templates removed; logs retained.
Next single owned Lean89579: /tmp/bag-normalized-physical-kernel-01ax.lean,
exact normalized physical phase with prefactorN and reciprocal1/R. First
candidate93079 exposed vector-coordinate reduction, a star/conjugation simp
loop, and real-to-complex product coercion. Corrected without resource hacks.
P1 bag-physical-nonstationary-log-tails records all hard next obligations.
Uncompiled template /tmp/bag-physical-tail-budgets-01ax.txt gives the actual
polynomial-window attached derivative-budget candidate. RH remains open.
