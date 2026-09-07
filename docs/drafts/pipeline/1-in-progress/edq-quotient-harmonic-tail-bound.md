# EDQ quotient decomposition and harmonic tail-depth cost

Stage: 1-in-progress. [BRIDGE] from exact arithmetic and corpus estimates; RH remains the primary objective.
Full chain: Euler deletion → exact complex zero balance → signed arithmetic separation → off-line exclusion → RH.
Objective: improve the actual full-source bound by summing signed Mertens increments across quotient scales before taking absolute values.

## Paper proof

For n>=1 put J=floor(n/(N+1)). Counting the pairs (m,j) with N<m<=n and
1<=j<=floor(n/m), then reversing the finite sums, gives exactly
R_N(n)=sum_(j=1..J)(M(floor(n/j))-M(N)).
Here R_N is the literal omitted-floor residual, which is zero when n<=N.
Consequently the actual source error is
1-F_N(n)=n*H_N-J*M(N)+sum_(j=1..J)M(floor(n/j)).
The cutoff counterterm and all quotient scales remain present.

Suppose abs(M(k))<=epsilon*k for every k>=N, epsilon>=0. Each active
floor(n/j) is at least N+1, so the complete sum has the bound
abs(R_N(n))<=epsilon*n*harmonic(J)+epsilon*N*J
<=epsilon*n*(1+harmonic(J)), since N*J<=n.
For 1<=n<=N*L, J<=L; thus the existing primitive has norm at most
1+n*(abs(H_N)+epsilon*(1+harmonic(L))). The previously proved full
head/tail transfer yields
E_N<=4+2*N*L*(abs(H_N)+epsilon*(1+harmonic(L)))^2+N/L.
Since harmonic(L)<=1+log L, the old linear tail-depth loss inside the
square is replaced by 2+log L. The complete infinite tail still costs N/L.

The existing unconditional contour estimate gives one B>=0 with
abs(M(k))<=B*k*exp(-(log k)^(1/3)/108) eventually. Its saving factor decreases
for k>=N>=2. Thus, at all sufficiently large N, the improved full-energy bound
holds simultaneously for every integer L>=1 with
epsilon=B*exp(-(log N)^(1/3)/108). No Mertens premise remains in this uniform
actual-source theorem. The harmonic defect H_N is still the literal one, and
no absolute cofinal logarithmic ceiling is asserted.


## Corpus basis and remaining gap

BaezDuarteMobiusPrefixApproximation gives exact global residual identities;
EulerDeletionFirstTailMertens identifies the first quotient scale;
EulerDeletionMobiusGlobalLogSaving supplies genuine full-energy transfer.
The corpus's divisor-hyperbola/Abel channel work was inspected for signed
quotient transport; its different source field does not supply this bound.
The elementary finite hyperbola count and harmonic sum yield the improvement.

This sharpens an actual producer estimate, without proving the absolute cofinal
logarithmic ceiling required by the RH receiver. Mertens cancellation, harmonic
defect, and complete complementary tail still need a sufficiently strong joint
bound. No numerical experiment is warranted for this visible deduction. No
numerical result is used in Lean, and this bridge does not replace the RH goal.

## Status

Dependency-closed paper derivation above; scratch Lean proof and targeted audits pending.
