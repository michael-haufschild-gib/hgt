# TG-C9.10: complete varying-prime cubic and its exact source relation

- **Stage:** 1-in-progress
- **Type:** CONJECTURE / hardest remaining completion question
- **Parents:** `../../../3-formalized/tg-prime-theta-graph-closure.md`,
  `../../../3-formalized/tg-fourier-jet-theta-cubic-classification.md`

## Hard question

Can the COMPLETE varying-prime modular cubic, with every Gram cross term retained,
define a nontrivial closed source action even though its theta factor cannot?
Factor nonclosability cannot answer this: each individual prime has a positive
parameter at which its complete cubic vanishes on every finite depth packet.

## Corpus basis

`PrimeBurnolFourierJetBalancedCubic` provides actual two-output Gram positivity,
its canonical inverse, source columns and complete constant-prime cancellation.
`PrimeBurnolFourierJetThetaClosure` gives exact finite source fidelity and the
sharp two-prime theta graph closure. The general definition
`cubicProjectionAssociatorAlgebra` is `(R-P)^3-(R-Q)^3-(Q-P)^3`.
`matrixTrace_weighted_cubic_single_inverse` reduces the full density-weighted trace
to one inverse while retaining its second polynomial term. These are source facts,
not a trace-class, domain or arithmetic-budget premise.

Search `Fourier jet mixed prime modular cubic packet refinement` had a complete
inventory but partial reranking and mostly irrelevant hits. A lexical name query
returned no hits despite known source occurrences. Neither establishes absence;
the actual definitions and trace-reduction proof were read directly with rg/sed.

## Next conjecture and proof attack

For each finite injective prime-depth packet F, form Q_F with its actual PRIME-DEPENDENT
sech/tanh blocks, C_F from both actual jet outputs, R_F=C_F^-1 Q_F C_F, and full
A_F=(R_F-P_F)^3-(R_F-Q_F)^3-(Q_F-P_F)^3. Use actual source synthesis E_F.
Let L_a be the linear span of pairs (E_F x,E_F A_F x) over all finite packets and x.

The original conjecture is now proved by C9.10b: for every nonzero a, closure(L_a)=G×G.
The stronger finite refinement theorem rules out a single-valued action before completion.
At a=0 the full cubic is zero, so closure is G×{0}, unlike the theta relation.
Do not silently assume the packetwise cubic is refinement-compatible or that L_a is
single-valued; prove or refute that from the actual matrices first.

The first mathematical attack is an exact refinement identity. Q_F and P_F preserve
the included finite source space. In its output-Gram orthogonal splitting, the larger
Q and P are upper triangular while R=Q's physical adjoint is lower triangular.
Compression of the full cubic therefore retains the off-diagonal terms from BOTH
(R-P)^3 and (R-Q)^3. Derive these terms on the actual Gram inclusion, then determine
whether the literal prime-depth graph-core approximation makes them cancel or
generates a nonzero vertical fibre. A generic matrix identity alone is not closure
progress: the target is its exact arithmetic source consequence.

No numerical experiments, modified theta frame, dropped inverse, output-only topology
substitution, or inference from theta saturation. Gamma–Xi identification, Hardy-index
transfer and the arithmetic sub-unit producer remain open. RH goal stays active.

## C9.10a: actual complete cubic at a balancing parameter

The first concrete attack specializes to the positive balancing parameter of a prime p,
then keeps a distinct prime q. All p-packet complete cubics vanish, so their graph
closures supply G×{0}. The common parameter does not balance q. If the COMPLETE
one-column q-depth cubic is invertible at every sufficiently late depth, its graph plus
G×{0} supplies every vertical q-tail source direction. A q-tail graph-core theorem would
then give G×G for the complete cubic relation. This is a new candidate proof, not yet
certified; it uses complete cubic cancellation and cannot follow from theta saturation.

For a one-column packet, the two-output Gram is [[m,b],[b,m]], with real b and m>|b|.
After division by m, let t=b/m. The actual constant-prime Q has entries u=v² and w=vc.
At t=0 the full cubic is zero; its first variation is a nonzero multiple of the real
skew channel whenever u≠1 and 2u≠1. Thus its determinant should have a nonzero leading
quadratic term in t. Prove this exactly and derive punctured invertibility, without
assuming that a generic Gram coupling has the desired sign or limit.

The arithmetic input is the actual large-depth coupling: write lambda=(n+1)log(q),
f_lambda(x)=|x|exp(-lambda|x|) and retain the literal nonzero Euler amplitude. It cancels
in b/m. The corpus's exact rational Fourier transform suggests
lambda^4 inner(f_lambda,F f_lambda)→4, while
|inner(x²f_lambda,F(x²f_lambda))|≤norm(x²f_lambda)^2=O(lambda^-7).
The diagonal is asymptotic to a positive constant times lambda^-3. Consequently
lambda*b/m tends to a positive constant; b/m is eventually nonzero and tends to zero.
These are qualitative source asymptotics needed for full-cubic invertibility, not
optimization of a numerical estimate. Use dilation/substitution and dominated convergence
with the exact Fourier kernel; no experiment or numerical quadrature.

The depth-tail graph-core theorem now passes its production leaf check. Its proof
uses depth N itself as the nonvanishing base for all subsequent integer Laplace
moments. The original resolvent parametrization then gives density in the actual
multiplication graph, not merely in L2.

The actual two-output normalized coupling now passes its production audit: lambda*t→8,
t→0, and t is eventually nonzero. The square-position output is retained throughout.
Its production leaf is `PrimeBurnolFourierJetCellCoupling`.

The exact cubic factorization A(t)=t L(t) and
L(0)=(2u−1)(1−u)J now pass a production audit. Continuity of the determinant
proves punctured invertibility when w²=u(1−u), u≠1 and 2u≠1. Production leaf:
`PrimeBurnolFourierJetCellCubic`. Actual packet identification and eventual complete
cubic invertibility pass in `PrimeBurnolFourierJetCellInvertibility`.

**C9.10a is solved:** `PrimeBurnolFourierJetCubicClosure` proves closure(L_a)=G×G at
every prime balancing parameter, closure(L_0)=G×{0}, unconditional existence of
positive saturated parameters, and no single-valued closed extension retaining every
packet at balance. Its production check passes. Canonical paper proof and final audit:
`../../../3-formalized/tg-complete-fourier-jet-cubic-saturation.md`. This retires the all-packet
closed-extension candidate at balance; C9.10b now settles the general nonzero-a conjecture above. The positive frequency-scaled skew symbol now passes its production check for
every prime and parameter: lambda*A_singleton→8(2u−1)(1−u)J. The next concrete attack
on general nonzero parameters is recorded in `../../../3-formalized/tg-fourier-jet-two-depth-refinement.md`:
prove invertibility of the ACTUAL two-depth packet action minus its singleton actions.

## C9.10b solved; remaining TG frontier

The exact two-depth refinement defect is eventually invertible at each nonzero
unbalanced prime parameter. Every nonzero parameter has an unbalanced prime.
Consequently the actual finite relation is single-valued iff a=0, and its closure
is G×G iff a≠0 (G×{0} at zero). Canonical paper proof and audit:
`../../../3-formalized/tg-fourier-jet-two-depth-refinement.md`.

The original completion question is closed. This parent now tracks the remaining
source-derived cofinal relative prime–Gamma construction: it must account for the
proved finite refinement anomaly, not assume compatible unchanged packet actions.
The corpus has a unique finite Sonin principal-relative trace splitting, but neither
its cofinal compatibility nor a Gamma–Xi/Hardy identification is supplied by that
finite theorem. Construct the actual joint datum and solve these analytic/arithmetic
problems; do not substitute an abstract closure or sub-unit premise.
