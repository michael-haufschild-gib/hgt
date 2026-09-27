# Stationary Möbius action and exact continuous long-tail symmetry — 2026-09-27

RH remains unproved; goal remains active. This turn made verified progress: a source-defined stationary coefficient action, exact long-tail symmetry, actual prime-deficit application, and a rigorous test showing symmetry alone does not bound the stationary value. No physical Noether charge bounding the short block was proved. Previous cutoff work is in `mem:research/noether_continuous_entry_boundary_and_critical_transient_mass_2026_09_27`.

## Verification and workspace
Repo /Users/michael/Documents/code/hgt/formal. Five new leaves, 29 public theorems. Every leaf passed a final foreground `lake --old env lean FILE -o .lake/build/lib/lean/...` with no warnings. All five have fresh objects, exactly one import in GaloisForLFunctions/RHTower.lean, clean whitespace and no forbidden constructs. Separate final axiom audit of all 29 passed: only [propext, Classical.choice, Quot.sound]. Temporary work/ReconstructionActionAxiomAudit.lean was deleted. No own processes remain.
No subagents, commits, full builds, numerical experiments, sorry/custom axioms, heartbeat changes. Global index refreshed successfully; final global lint reports 22 unrelated unwired modules, no stale generated metadata. Preserve concurrent work; do not claim global lint clean.

## Notation
Z_a f(T)=sum_{1<=n<=floor(exp T)} a(n) f(T-log n) = logarithmicWeightedDilation a f T.
Z=all-ones dilation; M=literal Möbius inverse.
G=ccmPrimeDeficitDilationSource, H=ZG=ccmPrimeDeficitDivisorSource.
D=literal logarithmic Chebyshev deficit primitive.
U(T)=floor(exp(T/2)).

## 1. LogarithmicReconstructionAction.lean — 8 theorems
Defines A(a;f,T)=2 Z_a f(T)-Z_a Z_a Zf(T).
Proves coefficient addition/scaling, profile addition/scaling, commutation of two weighted dilation operators, and Z_a M Zf=Z_a f for every real T (all entered delays are nonnegative).
Exact completion, all f,v,T:
A(mu+v;f,T)=Mf(T)-Z_v Z_v Zf(T).
Exact line formula, all real z:
A(mu+zv;f,T)=Mf(T)-z^2 Z_v Z_v Zf(T).
No asymptotics, prime estimate, or RH premise. This is a signed quadratic completion, not a positive-square identity.

## 2. LogarithmicReconstructionTailSymmetry.lean — 8 theorems
Defines logarithmicLongTail U v n = if U<n then v n else 0.
Defines logarithmicMobiusHeadExtension U v n = if n<=U then mu(n) else v n.
Shows head extension = mu + longTail(v-mu).
Proves Continuous (fun z => headExtension U (fun n => v n+z*w n)) in the product topology on real coefficient functions.
For N=floor(exp T)<(U+1)^2, proves Z_tail(v) Z_tail(w) f(T)=0 for arbitrary v,w,f: every potentially nonzero product index is beyond N.
Specializes to U(T), all real T.
Consequently A(mu+tail(v);f,T)=Mf(T); same for every real multiple and every translation of the tail parameter.
Finally, A(headExtension U(T) v;f,T)=Mf(T), for completely arbitrary real tail values v.
IMPORTANT SCOPE: only the Möbius prefix is fixed. This is a genuine symmetry on that affine coefficient slice. Tail directions are isotropic, not necessarily in the radical of the full Hessian. Do NOT claim invariance for arbitrary head coefficients. Do NOT claim every head extension is stationary in short directions; only their action values agree with the Möbius stationary value.

## 3. LogarithmicReconstructionVariation.lean — 3 theorems
For arbitrary coefficient direction v:
- HasDerivAt (q => A(mu+qv;f,T)) (-2*z*Z_v Z_v Zf(T)) z.
- first variation at mu (z=0) is zero, every direction.
- second variation is -2 Z_v Z_v Zf(T), all z.
This retains the signed Hessian exactly.

## 4. CCMPrimeDeficitCoefficientAction.lean — 7 theorems
Defines ccmPrimeDeficitCoefficientAction T a = A(a;G,T), using only the elementary source G in its definition, not D.
For T>=0, exact actual-source formula:
A_T(mu+zv)=D(T)-z^2 Z_v Z_v H(T).
The literal Möbius vector is stationary in every direction (all real T), and its exact Hessian is -2 Z_v Z_v H(T).
For T>=0 and any arbitrary real tail v:
A_T(headExtension U(T) v)=D(T).
Translation q->q+z of every affine tail v+q*w preserves the action. Its derivative along the tail parameter is zero.
The action value under any fixed arbitrary tail extension is continuous in T>=0, including the changing cutoff.
The stationary value remains the actual RH-hard quantity. No bound on it has been proved.

## 5. LogarithmicReconstructionSymmetryTest.lean — 3 theorems
Defines an explicit COMPARISON source f_test=Z(t -> t*exp(t/2)). This is NOT the actual prime source.
For every arbitrary tail extension and T>=0, its stationary action equals T*exp(T/2).
Its critical normalization is exactly T.
For every real C, the comparison action exceeds C*exp(T/2) at some nonnegative T (take T=max C 0+1). Entire proof is symbolic, no numerical experiment.
This proves that stationarity plus continuous tail symmetry alone cannot imply square-root growth control. It does not refute RH. A successful estimate must use additional source-specific arithmetic facts, such as the established actual remainder decay, and preserve signed short-block curvature.

## Mathematical status / next work
The actual conservation law is now an explicit stationary-value problem with a continuous symmetry on its long coefficients. This is stronger structural information than the earlier Mellin first-variation packaging (whose isolated parameter invariance was disproved). The missing step remains a source-specific bound for the short signed stationary value, equivalently |D(T)|<=C exp(T/2), or |W(T)|<=C exp(T/2) using previous polynomial boundary error.
Prior source two-point determinant -1 still blocks arbitrary-vector positive semidefinite arguments. Current full stationarity does not make the action a minimum. No physical Noether charge with coercivity on the short block has been established.
Potential next investigation: source-specific signed/minimax control using the actual H kernel and the exponentially settling R, rather than another symmetry-only estimate. Do not split away the explicit main terms or drop row-one cancellations identified in earlier memories.

## Lean lessons
- Rewriting a pointwise linearity theorem does not rewrite a partially applied dilation operator in a profile slot. Establish a function equality with funext first, then rw it into the outer operator.
- Use dsimp only to beta-reduce the coefficient lambda after logarithmicWeightedDilation_comp before rewriting an inner divisor sum.
- continuous_pi plus case split and fun_prop avoids Pi.add elaboration mismatches for affine coefficient functions.
- In HasDerivAt.congr_deriv for the quadratic polynomial, norm_num closed the derivative scalar equality; an additional sequential ring caused a no-goals error and was removed.
