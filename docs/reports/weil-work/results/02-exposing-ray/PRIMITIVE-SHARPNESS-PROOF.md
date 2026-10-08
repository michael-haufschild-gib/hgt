# Cycle18 — primitive coercivity: exact loss and positive survivor

Status: dependency-closed PAPER PROOF and final installed Lean leaf audit PASS.
All17 public axiom audits PASS with only propext/Classical.choice/Quot.sound. Universal WP02 remains OPEN.

## Definitions and exact claims

For every complex C2 test f supported in [-a,a], put rho(t)=|paperFT f(t)|^2,
M=integral rho, P=integral rho/(t^2+1/4)^2, E=archEnergy f,
and C=digammaVerticalCoercivityConst(1/4)+log 2+log pi.
Define B_b(f)=(b-C)M-exp(b)^4*P/4. This is the existing primitive
surrogate whenever f=(D^2-1/4)g, since its P equals the Fourier mass of g.

1. For every real b, B_b(f)+M/4 <= E.
2. If M>0, then P>0. For ALL sources, including M=0,
   (log(M/P)/4-C)*M <= E (Lean's total logarithm at zero).
   Also 0<=P<=16*M, and for f=(D^2-1/4)g the P here equals
   the actual Fourier mass of the existing compact primitive g.
3. There is a fixed aperture constant A0>=0 such that, for every real c,
   eventually every N admits an actual finite nonnegative polar family at
   aperture <= log(N)/2+A0, satisfying the receiver level condition and
   matching every integer of the literal truncated exposing ray, for which
   FOR EVERY row-dependent parameter b_i,
       sum alpha_i B_(b_i)(f_i) < T-c*tau_N.
   The same family defeats all parameters, even if chosen after seeing N
   and the entire family. No claim is made against the sharpened bound in 2.

## Dependency-closed proof

The existing digamma source proves log(2+|t|)-C <= archSymbol(t/(2*pi)).
For positive r,q, log((r/q)^4)<= (r/q)^4-1 gives
log r-log q+1/4 <= r^4/(4*q^4). Since
(t^2+1/4)^2 <= (2+|t|)^4, multiplication gives
(log r-C+1/4)*(t^2+1/4)^2 <=
(t^2+1/4)^2*archSymbol(t/(2*pi))+r^4/4.
Divide by the strictly positive squared denominator, multiply by rho>=0,
and integrate at r=exp b. The corpus already proves integrability of rho
and rho*archSymbol. Also 0<=rho/(t^2+1/4)^2<=16*rho, so P is integrable.
This proves 1 with no polar-pole premise.

If M>0 and P=0, assertion 1 for b=C+E/M+1 contradicts M>0.
Choose b=log(M/P)/4; then exp(b)^4=M/P. The penalty is exactly M/4,
cancelling the retained quarter. This proves 2, including arbitrary signed E.
For zero mass, the integrated domination P<=16*M gives P=0.
Assertion 1 then gives E>=0, and the claimed left side is zero. This
closes the zero-source extension without adding a nonzero-mass premise.

The literal cosine-inversion formula at zero and weilTest_self_zero give
M(f)=2*pi*physicalMass(f), with this project's Fourier convention.
Apply cycle17 mass_margin_counterexample at epsilon=pi/2 and the requested c.
Multiply assertion 1 for each row by its nonnegative alpha_i and sum.
For every b_i the total surrogate is <=E_total-(pi/2)*physicalMass_total,
which is strictly below T-c*tau_N for the SAME exact matched family. This
proves 3, retaining all complex cross terms, every integer trace and zero tail.

## Hostile, novelty and utility audits

The lower estimate alone is not RH: its logarithmic mass ratio has no proved
relation to the exposing threshold. The no-go is specifically for the old
unsharpened primitive bound; it does not exclude sharper gamma estimates or
trace-dependent compensation. No implication E>=T, no absolute convergence
of E-T, and no empty/nonempty cone assertion is used.

Three cycle18 deep corpus queries (certificate, compensation, primitive ratio)
finished non-partial, each with 68,559 indexed/inventoried files. All returned
candidate and source-argument statements were inspected. Compiler coverage
mostly pending/stale and background refresh remains incomplete. The primitive
query returns the actual old overlap bound and our mass floor, not the quarter
or adaptive-parameter exclusion. Retrieval is not a global absence proof.
Exact old scalar_log_bound discards -1 from log x<=x-1; its three energy callers
were exhaustively located. Existing source APIs will retain their statements.

The scalar optimization is classical elementary convex duality. Logarithmic
Fourier forms are established literature; compare Laptev--Weth, Spectral
properties of the logarithmic Laplacian, introduction/form (1.1):
https://www.ma.imperial.ac.uk/~alaptev/Papers/laptev-weth-2020-revised.pdf
This is a corpus BRIDGE and an exact diagnostic of our previous method,
not a claim of a new general logarithmic inequality or scientific novelty.

The positive survivor is assertion 2 and the fully retained quarter in 1;
both must be formalized before closing the negative route. The spectral L1
candidate is deferred: describing the existing upper constructions adds no
control of arbitrary matched families, while this sharper source audit already
identifies a concrete unpaid loss. Next frontier: joint trace-dependent signed
gamma compensation at zero margin, with no positivity or attainment premise.
