# BAG full growing labelled near-pole source

For P_N=primes<=N, L=log N, s=1+u/L, t=1+v/L and fixed nonzero complex
u,v, the original completed labelled source satisfies

(u/L)*(v/L)*criticalCompletedConeEuler(P_N,s,t)
  -> exp(-gamma)^3 * exp(J(u,v)) * I_A(u,v)*I_B(u,v)*I_C(u,v),

where P(w)=integral_0^1 (exp(w*x)-1)/x dx, continuously extended with
value w at x=0, J=P(u)+P(v)-P(u-v)-P(v-u), and
I_A=integral_0^1 (1+exp((u-v)*x)-exp(u*x)) dx,
I_B=integral_0^1 (1+exp((v-u)*x)-exp(v*x)) dx,
I_C=integral_0^1 (1-exp(u*x)-exp(v*x)) dx.

Proof. The already audited collision-aware identity expresses the COMPLETE
original source as A_N^3*T_N times the entire unlabelled valuation trace
with both original coprime cofactors. For local z=1/p and x=logp/logN,
the four actual response ratios equal explicit rational profiles R_k(z,x).
The normalized base denominator is1 at z=0 and at every balanced point
(z,0). The profile is continuous at (0,x), x in[0,1], and at (1/p,0)
for every prime p. Its zero-z values are the three displayed leading
profiles and 1+exp((u-v)x)+exp((v-u)x)-exp(ux)-exp(vx) for the allowed
first/second coincidence.

A moving-window theorem follows from the corpus complex Mertens weak
window. Compactness makes R(z,x)-R(0,x) uniformly small in x when z is
small. The finite-prime head divided by logN tends to0. The remaining
error is bounded by the positive prime mass, whose ratio to logN tends
to1. This proves all four actual row limits without a global continuity
or response-bound premise.

Set W(z)=-z logz, continuously extended by0. At z=1/p it equals w_p=logp/p.
Apply the SAME window theorem to W*(d-a*b), W*b*c, W*a*c and
W^2*c*(2*a*b-d). All zero-z profiles vanish, proving that every exact
pair/triple collision sum divided by logN tends to0. The factor2, not3,
was forced by symbolic Lean checking of the full exclusion expansion.
Consequently T_N/L^3 -> I_A*I_B*I_C with every allowed collision retained.

Finally A_N*L->exp(-gamma) by the corpus Mertens product theorem. The
original unlabelled two-cofactor moving double-pole trace tends to exp(J),
as previously formalized. Exact cancellation of the logarithmic factors
proves the displayed full source law.

Scope. Pointwise convergence in each fixed nonzero complex displacement
pair. The nonzero domain is represented by Complex units in Lean. The
actual principal-character cofactors retain their defined analytic values;
no claim of Dirichlet-series convergence left of Re(s)=1 is made. Compact-
uniform parameter convergence, growing physical Mellin profiles, full axes
saving, moments and deterministic common-height return remain open. This
near-pole law is not an RH proof.

Lean production audits all passed with empty output: MovingResponseWindow57016,
MovingLabelRows3369, GrowingLabeledSource88601, updated MovingCofactorLimit95159
and MaskedMellinSource22902. Axiom71945 checks all30 public declarations across
these five leaves: only propext, Classical.choice, Quot.sound. Index69878 passed;
API30/30 and each umbrella import once verified. See matching P3 for lint status.
