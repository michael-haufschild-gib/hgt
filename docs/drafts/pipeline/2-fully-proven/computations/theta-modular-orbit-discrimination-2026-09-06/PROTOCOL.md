# Frozen exploratory design: actual theta ODE versus nearby trajectories

## Evidence and question

Corpus source equations and polynomial jets are in `PolynomialODEJetRankThreeLyapunovClosure`
and `PrimeArchThetaModularDifferentialClosure`. The finite static chamber admits negative D1
near R=5/2. The actual seam R0=pi*theta3(i)^4 has R0²>191/10 and positive D1. Canonical
operator stage choices are nonconstructive approximations and fixed Green-port rank estimates
already have analytic no-gos; no matrix experiment on those objects is proposed.

Discriminating alternatives: (a) D1 positivity is confined to a finely selected modular orbit;
(b) positivity is robust along a sizeable family of seam-started trajectories, suggesting a
source ODE tube estimate; (c) positive seam data lose the sign quickly, requiring a selective
first-crossing law. This is exploratory model discrimination, not a primary universal hunch
or a replacement definition of RH.

## Fixed tests

Generate H-normalized jets through10 symbolically from the exact rational vector field.
Verify their seam D1 against the independent degree12 polynomial already proved in Lean.
Do not use numerical differentiation to obtain jets.

1. Integrate initial squared scales X=6.25,10,15,18,19,19.1,19.2,20,25,40 and the actual
   theta X0, plus X0*(1+delta), delta=+-1e-6,+-1e-4,+-.01. Record every output point through
   x=.3, with the full missing interval x<=137/2000 resolved separately. Evaluate source f0,
   D1, and cancellation ratio (signed determinant / sum of absolute determinant summands).
2. Continue the state equations to x=5 or an explicit norm exit, recording S=-3 and S=0
   exits. Long-time numerical instability near a separating trajectory is a diagnostic,
   not proof of a global solution or a bifurcation.
3. Probe the fixed box S in[-1,0], A in[17,20], W in[0,6/5] with8192 deterministic Sobol
   points, seed20260906. Preserve every state and result. If this broad box fails, identify
   which source correlations the failing states violate. Do not call a narrowed box the
   same claim.

At most8 independent worker processes, BLAS/OMP/MKL1; each remote batch120-second cap.
All mathematical computation and plotting on the authorized Runpod. Independent high-
precision source/ODE checks follow any candidate sign conclusion. Finite passes are not
uniform estimates. Any dependency-closed analytic survivor must be formalized separately;
no computed number is a Lean premise.

## B1 [BRIDGE], frozen after the box/trajectory experiment

Let P(S,A,W) be the exact mass-normalized D1 polynomial above. The fresh statement is:
`P(S,A,W)>0` whenever -1<=S<=0,17<=A<=20,0<=W<=6/5.
The exploratory Sobol test found no negative value, with a nonzero normalized margin; this
motivates but does not prove B1. This is a proof-directed bridge, not a new universal law.
Attack the exact polynomial on the whole box by rational Bernstein conversion. A failure
of one coefficient test is not a counterexample. If B1 has a closed algebraic proof, prove
from the actual source ODE that its compact trajectory lies in this box; neither admission
nor the final source sign may be supplied as a premise.
