# Exact tail repair for the exposing ray

Main WP02 inequality remains OPEN.

## Audited conjectures

1. **Ground-state identity alone supplies a positive residual.** Verdict: REDISCOVERED for the identity; no sign proof. `RiemannKernelGroundStateZeroIdentity` already provides the zero-side transform. Its complex exponential kernel has no established sign. This route has not been disproved; it has not supplied the required inequality.
2. **Exposing trace tails admit positive-mixture repair with precisely their box-tail cost.** Verdict: BRIDGE. The two-point construction is already inside the corpus linear-duality proof; the explicit tail certificate and its cofinal transport quantify the missing extension step. No claim of new scientific knowledge beyond the parent duality theory.

## Dependency-closed paper proof of the repair certificate

Write w(n)=exposingWeight(n), b(n)=(log n+C0)|w(n)| for n>=2 and b(n)=0 otherwise. Put tau(N)=sum_{n>N} b(n). The corpus proves b>=0 and sum b<infinity.

For arbitrary natural N,M, index a finite family by S={n: max(2,N+1)<=n<=M}. At n in S let s_n=1 if w(n)>=0 and s_n=-1 otherwise. Take the existing polar two-point resonator r_n=twoPointResonator(n,s_n), at atomLevel(n), with positive bump mass m_n. Give it coefficient alpha_n=|w(n)|/(4*pi*m_n)>=0. The existing exact atom formula gives

    2*pi*alpha_n*atomCoeff(r_n,j) = w(n) if j=n, 0 otherwise (j>=2).

Consequently this family realizes the tail trace w(j) 1_{N<j<=M} at every integer j>=2, including every omitted coefficient. Its total archimedean energy is at most

    sum_{n in S} (log n+C0)|w(n)| = sum_{N<n<=M} b(n).

For N<=M this equals tau(N)-tau(M), by absolute convergence. In all cases it is at most tau(N), which tends to zero as N tends to infinity, uniformly in M. The functions are smooth compactly supported polar tests; the mixture has nonnegative coefficients even when w(n)<0. No numerical computation and no positivity hypothesis for an unknown Weil producer enters.

If M<=floor(exp(2B)), the corpus `atomLevel_le` places all repair tests at level B+1. Therefore appending the family (scaled by t>=0) to any family matched to t*w_N produces a family matched to t*w_M, at level max(A,B+1), and raises its energy by at most t*(tau(N)-tau(M)).

## Cofinal implication and remaining estimate

Suppose a future proof supplies dual bounds at cutoffs M_j tending to infinity and levels C_j tending to infinity, with every repair test for n<=M_j admitted at C_j, and lower bounds E-tau(M_j)-epsilon_j where epsilon_j tends to zero. Append the repair certificate to a fixed original family at cutoff N and aperture A. For all sufficiently large j, M_j>=N and C_j>=A. Subtracting the repair upper bound gives original energy >=t*(E-tau(N)-epsilon_j). Passing to the real limit proves the exact desired bound. This step includes t=0 and arbitrary finite complex test families.

[OPEN CORE] Prove those diagonal dual lower bounds from the actual archimedean source, uniformly over the full matched-test cone. The repair theorem proves no such lower bound.


## Earlier conjecture: logarithmic cost of independent repair

For s in {-1,1}, conjecture

    archEnergy(twoPointResonator(n,s)) / (4*pi*resonatorMass(n)*log(n)) -> 1

as n tends to infinity, uniformly over these two signs. The existing corpus gives the upper bound with log(n)+C0. The proposed lower mechanism is support-measure uncertainty: a normalized Fourier density of a function supported on total measure L is bounded above by L/(2*pi), forcing its logarithmic frequency moment above log(pi/L)-1. Combine this with a uniform logarithmic lower bound for the actual digamma symbol and the exact disjoint-bump mass. Here L is of order 1/n.

[OPEN CORE] Verify all constants, Fourier conventions, support measure and logarithmic integrability, and complete the source lower bound. No theorem claimed. This would establish a sharp limitation of independent atom repair, not WP02 positivity. Its general parent is logarithmic uncertainty / the Dirichlet logarithmic Laplacian, so a routine specialization would fail the scientific-novelty gate. Seek a collective matched-trace result if that audit kills the candidate.


## Cycle 3 update

`PACKET-PROOF.md` closes the stronger, coefficient-uniform finite-size lower bound on paper and in Lean. It retains every Fourier cross term and avoids separate logarithmic integrability. The independent logarithmic cost mechanism was therefore not pursued as a separate scientific-novelty claim. No Lean limit theorem for the normalized two-point ratio is claimed here; the formal deliverable is the stronger finite-N coercivity inequality itself.


## Cycle 5: sharp literal tail

TAIL-SIGN-PROOF.md contains the complete theta-envelope and outermost-shift argument. The new source module proves eventual positive coefficients, exact logarithmic rate `-2*pi*exp(-2)`, subcritical exponential bounds for the existing box tail, and strict tail positivity at every finite cutoff. Full scratch and final installed leaf checks passed without warnings. All eight audited capstones use only propext, Classical.choice and Quot.sound. These estimates improve the previously formalized repair budget without supplying the universal energy lower bound.
