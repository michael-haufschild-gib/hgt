# EDQ arithmetic primitive and critical energy transfer

Stage: 1-in-progress. Paper derivation fixed; Lean construction underway.
Full chain: Euler deletion → exact complex zero balance → signed arithmetic separation → exclusion of off-line zeros → RH.
Objective: bound the complete Möbius chronological current by a literal arithmetic primitive energy at the critical weight, without deleting cross terms or assuming an RH-strength estimate.

## Source identification

For the actual finite Möbius coefficients, write a_N(n) for the unweighted
deletion stream and A_N(K)=sum_(n<K) a_N(n). Summing each deletion stream
telescopes its modular residue. Thus A_N(K) is exactly the negative of the
corpus's bdMobiusModularApproximant N K at every K, including beyond N.
This is the full source, not just its expanding initial window.

For kernel b_s(n)=(n+1)^(-s), finite Abel summation gives
P_N(s,K)=A_N(K)b_s(K)+sum_(n<K) A_N(n+1)(b_s(n)-b_s(n+1)).
The primitive is bounded for each fixed N. At an actual zero, P_N(s,K)→0,
so the complete Abel series is zero, and
P_N(s,K)=A_N(K)b_s(K)-sum_(n>=K) A_N(n+1)(b_s(n)-b_s(n+1)).
All infinite series used here are norm summable.

## Critical Hardy–Schur transfer

For 1/2<sigma<1, the kernel increment is bounded by a constant depending
on s times (n+1)^(-sigma-1). The reflection-weight increment is bounded
by a constant depending on sigma times (k+1)^(2sigma-2).
Put B_n=abs(A_N(n+1))/(n+1). The normalized tail is bounded by the
positive triangular kernel
T_(k,n)=[k<=n](k+1)^(sigma-1)(n+1)^(-sigma).

With Schur weight w_n=(n+1)^(-1/2), its row and column bounds both reduce
to the positive gap delta=sigma-1/2. The row uses the convergent power
tail and the column the integrable power head. Weighted Cauchy–Schwarz
then bounds the full squared output by C_sigma times sum B_n^2.
Finite sums are bounded first; their limits are taken only after the
relevant norm summability or nonnegative monotone bound is established.

Consequently the actual full current at a right-half zero obeys
Re Q_N(s)<=C_s sum_(n>=1) A_N(n)^2/n^2. Reflection gives the analogous
absolute bound for off-line zeros. The arithmetic energy is comparable
within fixed constants to the existing modular approximant carrier norm.
A cofinal logarithmic ceiling on this complete arithmetic energy would
therefore supply the current ceiling in EulerDeletionMobiusLogGrowth and RH.
That ceiling remains a producer to prove, not a premise discharged here.

## Corpus evidence and limits

EulerDeletionMobiusCurrentEscape and EulerDeletionMixedCurrentGram provide
the literal source, endpoint-zero theorem, and exact complete current energy.
BaezDuarteMobiusPrefixApproximation and StepFunctionCarrier provide the full
modular primitive and its weighted carrier norm. GaussSpikeMass supplies
the power-head estimate; PowerSeriesTailBound supplies the power-tail estimate;
WeightedSchurTest supplies the corpus pattern for a weighted finite-kernel bound.

The raw modular error norm is already proved not to converge to zero in
BaezDuarteMobiusCriticalTailObstruction. No such convergence is required by
the proposed logarithmic ceiling. No full energy ceiling has been found in
the inspected corpus. A pointwise Cauchy bound alone leaves a divergent
harmonic sum, so the critical weighted Schur step must remain intact.

## Formal status

`EulerDeletionPrimitiveHardy.lean` is verified in scratch and built as the sole
new dependency (233 lines; three public definitions, three public theorems).
Its finite rectangular Schur estimate passes to genuinely summable infinite
rows and the complete square-energy bound. Final scratch exit 0 with no
diagnostics; targeted leaf build exit 0, only this leaf rebuilt (3.8 seconds).
One umbrella import added. New-only axiom audit awaits the completed application.

The application is under scratch verification in `/tmp/edq_primitive.lean`.
It identifies the complete modular primitive, proves the endpoint-retaining
finite Abel formula and the zero-endpoint infinite tail formula, and targets
`Re Q_N(rho) <= 2*(2 Re(rho)-1)*(1+norm(rho)^2*(1+1/(Re(rho)-1/2))^2)*E_N`
for `Re(rho)>1/2`, with `E_N=sum_(n>=1) norm(A_N(n))^2/n^2`.
Its Lean status is pending; this application is not yet reported as proved.

No numerical experiment is needed for these symbolic estimates. Numerical
experiments, if later justified by an unpredictable question, must run on the
user's specified RunPod host with multicore Python, bounded runtime, and results
copied into `docs/drafts/pipeline/2-fully-proven/computations`.
No route retired. RH remains open.
