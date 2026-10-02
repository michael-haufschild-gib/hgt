# TG-C9.10a: complete Fourier-jet cubic saturation at balance

- **ID:** TG-C9.10a-20261002-01a0
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Parent:** `../1-in-progress/tg-fourier-jet-mixed-cubic-closure.md`
- **Main leaf:** `PrimeBurnolFourierJetCubicClosure`

## Hard question and exact answer

Single-prime complete cubic cancellation survives unbounded theta factors. Does that
cancellation give a closed action when every literal prime-depth packet is retained?

Let G be the completed even Fourier-jet graph, including both source coordinates and
both physical outputs. For each finite injective prime-depth packet F, retain its
actual two-output Gram C_F, canonical inverse, and prime-dependent theta Q_F. Let
A_F=(C_F⁻¹ Q_F C_F−P_F)³−(C_F⁻¹ Q_F C_F−Q_F)³−(Q_F−P_F)³.
Let L_a be the linear span of all pairs (E_F x,E_F A_F x).

At any prime's balancing parameter, closure(L_a)=G×G. At a=0 it is G×{0}.
Every prime has a positive balancing parameter, so the existence theorem has no
analytic, invertibility, density, or RH premise. A single-valued closed linear
extension agreeing with every finite packet action is impossible at balance.

L_a contains finite sums of packet graphs. The theorem does NOT assert that those
sums equal the graph of one larger packet. It assumes neither packet-refinement
compatibility nor a single-valued finite action. General nonzero-a saturation is now proved in
`tg-fourier-jet-two-depth-refinement.md`. No Gamma–Xi identification, Hardy-index passage, sub-unit action, or RH conclusion.

## Dependency-closed paper proof

1. Every depth tail of one prime is a core for the actual even multiplication graph.
   In the Laplace-moment proof, depth N replaces depth zero as the nonvanishing base.
   The existing resolvent parametrization upgrades this to graph density. Continuous
   assembly gives the same completed two-input/two-output graph G for every tail.
2. For one literal cell, C=m[[1,t],[t,1]], with m>0 and real t. This is an equality
   of the ACTUAL Gram; both Fourier cross terms and the Euler amplitude are retained.
   With λ=(n+1)log p, exact Fourier integration and dominated convergence give λt→8.
   The position-square contribution is controlled by its exact norm and Fourier
   isometry. Thus t→0 and t is eventually nonzero. No numerical experiment.
3. Put Q=[[u,w],[w,1−u]], w²=u(1−u), and C(t)=I+tS. The complete cubic factors as
   A(t)=t L(t), with L continuous at zero and L(0)=(2u−1)(1−u)J,
   J=[[0,1],[−1,0]]. Its determinant at zero is nonzero whenever u≠1 and 2u≠1.
   Hence the complete literal singleton cubic is eventually invertible at every
   nonzero parameter that does not balance that prime.
4. At p's balancing parameter, all p-packet cubics vanish. The p graph core puts
   G×{0} in closure(L_a). Choose q≠p; balance uniqueness makes q unbalanced.
   Invertibility of each sufficiently late q singleton realizes every vector in
   that cell as a cubic output. Subtract the horizontal pair to obtain its entire
   vertical cell. Tail graph density then gives {0}×G.
5. Adding these directions yields G×G. The reverse inclusion follows because all
   finite source and response vectors lie in G. At zero Q_F=P_F, so the complete
   cubic is identically zero and the graph-core theorem gives precisely G×{0}.

## Strongest positive survivor

Every pair of completed source and response vectors is simultaneously approximable
by finite linear combinations of the same actual packet graphs. This exact saturation
is stronger than an unboundedness or factor-nonclosability statement. The proof also
identifies the nonzero skew first variation of the complete cubic and an exact
prime-tail invertibility theorem. The actual frequency-scaled matrix limit is now
certified for EVERY prime and parameter, with no nonzero or balance premise:
λ_n A_n → 8(2u−1)(1−u)J. This positive symbol retains the complete cubic and actual
Gram inverse. It is not a claim of an operator limit on the completed physical graph,
nor of a mixed-packet or Gamma–Xi limit.

## Corpus and verification

Deep searches for density/complete cubic and the actual Fourier cross-limit both
completed without errors. The later boundary-symbol search had complete inventory
but partial reranking (deadline), with mixed compiler freshness. Its available hits
include the actual rational Fourier and graph-closure arguments; no absence claim
is inferred. Source declarations and all used APIs were verified in Lean.

Foreground production checks pass for PrimeCore and the four new leaves CellCoupling,
CellCubic, CellInvertibility and CubicClosure, using `lake --old env lean <leaf> -o
<matching olean>`. Core and CellCoupling retain an informational ring_nf suggestion;
the other new leaves have no warnings/errors. All new leaves are wired into RHTower.
The scaled-symbol theorem also passes CellInvertibility's production recheck. The
separate /tmp API and axiom audit passes all 61 added declarations, with only propext,
Classical.choice and Quot.sound. All five affected production oleans are newer than
their sources. Index refresh exits zero; source whitespace checks are clean.
Formal lint exits one only for ten unrelated unwired RHTower modules:
CCMApertureChainProfile, CCMApertureTranslationChains, CCMExponentialRampPrimeMoment,
CCMExponentialRampSourceDissipation, CCMExponentialRampTerminalEntropy,
CCMRetainedChainKernelLower, MoebiusMollifiedCriticalMoment,
MoebiusMollifiedErrorThreeLines, ThetaMovingShellFirstOrderPhase,
ZetaZeroDensityPowerSaving. No new TG leaf error. No full/umbrella
build, heartbeat increase, new axiom, proof hole, numerical experiment, subagent,
commit or push. Owned temporary proofs, searches and audit logs were removed after
recording these results; all owned processes exited.

## Next mathematical target

The original all-packet closed completion is now ruled out at balancing parameters.
The next concrete conjecture, `tg-fourier-jet-two-depth-refinement.md`,
attacks arbitrary nonzero parameters through the exact
refinement defect between a two-depth packet and its singleton actions. The skew
symbol suggests an invertible defect for depths with frequencies λ and 2λ. This
requires proving the actual mixed-column Gram limit and its inverse; no numerical
test or generic matrix example replaces that step. A successful TG construction
must still identify a relative prime–Gamma datum without assuming the failed closed
source action. Gamma–Xi, Hardy-index transfer and sub-unit production remain open.

**C9.10b update:** the conjecture in the historical next-target paragraph is now
proved. The actual finite relation is single-valued exactly at zero, and all nonzero
parameters have closure G×G. See `tg-fourier-jet-two-depth-refinement.md`.
